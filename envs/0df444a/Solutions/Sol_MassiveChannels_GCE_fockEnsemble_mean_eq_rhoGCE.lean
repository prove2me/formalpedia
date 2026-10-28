-- Prove2me | solution 1 for MassiveChannels.GCE.fockEnsemble_mean_eq_rhoGCE
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:20:57.912989+00:00
-- url     : https://prove2.me/submissions/b37f2c43-0a4a-424c-a516-825f46744758

import Mathlib
import Definitions.Def_MassiveChannels_GCE_Model

set_option autoImplicit false

noncomputable section

namespace MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open scoped ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section aux
variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- unitary matrix of an orthonormal basis -/
def basisMat (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) : Matrix Q Q ℂ :=
  Matrix.of fun i j => v j i

lemma basisMat_star_mul (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) :
    star (basisMat v) * basisMat v = 1 := by
  ext j k
  have h := v.orthonormal.2
  have := (orthonormal_iff_ite.1 v.orthonormal) j k
  simp only [basisMat, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← this]
  simp [PiLp.inner_apply, mul_comm]


lemma basisMat_mul_star (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) :
    basisMat v * star (basisMat v) = 1 :=
  mul_eq_one_comm.1 (basisMat_star_mul v)

lemma basisMat_diag (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (d : Q → ℝ) :
    basisMat v * Matrix.diagonal (fun s => (d s : ℂ)) * star (basisMat v) =
      ∑ j, (d j : ℂ) • pureDensity (v j) := by
  ext a b
  simp [basisMat, pureDensity, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply,
    Matrix.star_apply]
  refine Finset.sum_congr rfl fun c _ => by ring

lemma sum_pureDensity (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) :
    ∑ j, pureDensity (v j) = 1 := by
  have := basisMat_diag v (fun _ => 1)
  simp only [Complex.ofReal_one, one_smul] at this
  rw [← this]
  simp [basisMat_mul_star]

section tr
open Matrix Polynomial
noncomputable def TsumX (φ : ℝ → ℝ) (q : ℂ[X]) : ℝ := (q.roots.map fun z => φ z.re).sum

lemma trace_cfc_reX (M : Matrix Q Q ℂ) (hM : M.IsHermitian) (φ : ℝ → ℝ) :
    ((cfc φ M).trace).re = TsumX φ M.charpoly := by
  rw [TsumX, hM.roots_charpoly_eq_eigenvalues, hM.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp [Multiset.map_map, Function.comp_def, Matrix.trace_diagonal]

lemma trace_cfc_conj' (W : Matrix Q Q ℂ) (hW : star W * W = 1) (d : Q → ℝ) (φ : ℝ → ℝ) :
    (W * diagonal (fun s => (d s : ℂ)) * star W).IsHermitian ∧
    ((cfc φ (W * diagonal (fun s => (d s : ℂ)) * star W)).trace).re = ∑ s, φ (d s) := by
  have hH : (W * diagonal (fun s => (d s : ℂ)) * star W).IsHermitian := by
    unfold Matrix.IsHermitian
    simp [Matrix.mul_assoc, Matrix.conjTranspose_mul, star_eq_conjTranspose]
    have : star (fun s => (d s : ℂ)) = fun s => (d s : ℂ) := by
      funext s; simp
    rw [this]
  refine ⟨hH, ?_⟩
  rw [trace_cfc_reX _ hH]
  have hcp : (W * diagonal (fun s => (d s : ℂ)) * star W).charpoly = ∏ s, (X - C (d s : ℂ)) := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    simp [Matrix.charpoly_diagonal]
  rw [hcp, TsumX]
  have : (∏ s, (X - C (d s : ℂ))) = ((Finset.univ.val.map (fun s => (d s : ℂ))).map (fun a => X - C a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]
  simp [Multiset.map_map, Function.comp_def]

end tr


lemma vnEntropy_sum_pure (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) [Nonempty Q] (d : Q → ℝ) :
    vnEntropy (∑ j, (d j : ℂ) • pureDensity (v j)) = shannon d := by
  rw [← basisMat_diag]
  unfold vnEntropy shannon
  rw [(trace_cfc_conj' (basisMat v) (basisMat_star_mul v) d _).2]

lemma vnEntropy_pure (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) [Nonempty Q] (j : Q) :
    vnEntropy (pureDensity (v j)) = 0 := by
  have h := vnEntropy_sum_pure v (fun k => if k = j then 1 else 0)
  have h2 : (∑ k, (((if k = j then 1 else 0 : ℝ)) : ℂ) • pureDensity (v k)) = pureDensity (v j) := by
    simp [Finset.sum_ite_eq']
  rw [h2] at h
  rw [h]
  simp [shannon, Finset.sum_ite_eq']


lemma orth (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (x y : Q) :
    star (v y : Q → ℂ) ⬝ᵥ (v x : Q → ℂ) = if y = x then 1 else 0 := by
  have h := congrFun (congrFun (basisMat_star_mul v) y) x
  simp only [basisMat, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply] at h
  rw [← h]
  simp [dotProduct]

lemma pureDensity_eq (ψ : EuclideanSpace ℂ Q) :
    pureDensity ψ = Matrix.vecMulVec (ψ : Q → ℂ) (star (ψ : Q → ℂ)) := by
  ext a b; simp [pureDensity, Matrix.vecMulVec_apply]

lemma effectProb_pure (M : Matrix Q Q ℂ) (ψ : EuclideanSpace ℂ Q) :
    effectProb M (pureDensity ψ) = (star (ψ : Q → ℂ) ⬝ᵥ (M.mulVec (ψ : Q → ℂ))).re := by
  unfold effectProb
  rw [pureDensity_eq, Matrix.trace_mul_comm]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma isDensity_pure (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (j : Q) :
    IsDensityMatrix (pureDensity (v j)) := by
  refine ⟨?_, ?_⟩
  · rw [pureDensity_eq]; exact Matrix.posSemidef_vecMulVec_self_star _
  · have := orth v j j
    simp only [if_true] at this
    rw [← this, pureDensity_eq]
    simp [Matrix.trace, Matrix.vecMulVec_apply, dotProduct, mul_comm]

lemma effectProb_nonneg (M : Matrix Q Q ℂ) (hM : M.PosSemidef) (ψ : EuclideanSpace ℂ Q) :
    0 ≤ effectProb M (pureDensity ψ) := by
  rw [effectProb_pure]
  have := hM.dotProduct_mulVec_nonneg (ψ : Q → ℂ)
  exact Complex.nonneg_iff.1 this |>.1

lemma effectProb_pure_pure (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (x y : Q) :
    effectProb (pureDensity (v y)) (pureDensity (v x)) = if y = x then 1 else 0 := by
  rw [effectProb_pure, pureDensity_eq, Matrix.vecMulVec_mulVec]
  have h1 := orth v x y
  have h2 := orth v x y
  have h3 := orth v y x
  by_cases hxy : y = x
  · subst hxy; simp [h3]
  · have hyx : ¬ x = y := fun h => hxy h.symm
    simp [h3, hxy, hyx]


lemma shannon_marg_le {X Y : Type} [Fintype X] [Fintype Y] (J : X × Y → ℝ) (hJ : ∀ z, 0 ≤ J z) :
    shannon (fun y => ∑ x, J (x, y)) ≤ shannon J := by
  unfold shannon
  rw [neg_le_neg_iff, Fintype.sum_prod_type_right]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  have hle : J (x, y) ≤ ∑ x', J (x', y) :=
    Finset.single_le_sum (f := fun x' => J (x', y)) (fun x' _ => hJ _) (Finset.mem_univ x)
  rcases (hJ (x, y)).eq_or_lt with h | h
  · rw [← h]; simp
  · exact mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (by norm_num) h hle) h.le

lemma shannon_reindex {X Y : Type} [Fintype X] [Fintype Y] (e : X ≃ Y) (q : Y → ℝ) :
    shannon (fun x => q (e x)) = shannon q := by
  unfold shannon
  rw [Equiv.sum_comp e (fun y => q y * Real.logb 2 (q y))]

section ex
variable [Nonempty Q]

lemma exists_joint (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) :
    ∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v := by
  set A := Matrix.toEuclideanLin Ham with hAdef
  set B := Matrix.toEuclideanLin Nop with hBdef
  have hA : A.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hH
  have hB : B.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hN
  have hAB : Commute A B := by
    show A * B = B * A
    apply LinearMap.ext
    intro x
    apply (WithLp.equiv 2 _).injective
    simp only [hAdef, hBdef, Module.End.mul_apply, Matrix.toEuclideanLin_apply]
    simp [Matrix.mulVec_mulVec, hcomm]
  classical
  let I := Module.End.Eigenvalues A × Module.End.Eigenvalues B
  let V' : I → Submodule ℂ (EuclideanSpace ℂ Q) :=
    fun i => Module.End.eigenspace A (i.1 : ℂ) ⊓ Module.End.eigenspace B (i.2 : ℂ)
  have hort : OrthogonalFamily ℂ (fun i => V' i) fun i => (V' i).subtypeₗᵢ := by
    have := (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hA hB).comp
      (f := fun i : I => ((i.2 : ℂ), (i.1 : ℂ))) (by
        intro i j hij
        obtain ⟨h1, h2⟩ := Prod.mk.inj hij
        exact Prod.ext (Subtype.ext h2) (Subtype.ext h1))
    exact this
  have htop : (⨆ i, V' i) = ⊤ := by
    rw [eq_top_iff, ← LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hA hB hAB]
    refine iSup_le fun α => iSup_le fun γ => ?_
    by_cases hα : Module.End.eigenspace A α = ⊥
    · rw [hα]; simp
    by_cases hγ : Module.End.eigenspace B γ = ⊥
    · rw [hγ]; simp
    exact le_iSup V' (⟨⟨α, hα⟩, ⟨γ, hγ⟩⟩ : I)
  have hV : DirectSum.IsInternal V' :=
    hort.isInternal_iff.2 (by rw [htop]; exact Submodule.top_orthogonal_eq_bot)
  have hn : Module.finrank ℂ (EuclideanSpace ℂ Q) = Module.finrank ℂ (EuclideanSpace ℂ Q) := rfl
  let b := hV.subordinateOrthonormalBasis hn hort
  have hcard : Fintype.card (Fin (Module.finrank ℂ (EuclideanSpace ℂ Q))) = Fintype.card Q := by
    simp
  let e : Fin (Module.finrank ℂ (EuclideanSpace ℂ Q)) ≃ Q := Fintype.equivOfCardEq hcard
  refine ⟨b.reindex e, fun j => ?_⟩
  have hmem := hV.subordinateOrthonormalBasis_subordinate hn (e.symm j) hort
  set i := hV.subordinateOrthonormalBasisIndex hn (e.symm j) hort
  have hbj : (b.reindex e) j = b (e.symm j) := by simp
  rw [hbj]
  obtain ⟨h1, h2⟩ := hmem
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at h1 h2
  have hne : b (e.symm j) ≠ 0 := b.orthonormal.ne_zero _
  have hre : ∀ (T : EuclideanSpace ℂ Q →ₗ[ℂ] EuclideanSpace ℂ Q) (hT : T.IsSymmetric) (μ : ℂ),
      T (b (e.symm j)) = μ • b (e.symm j) → ∃ a : ℝ, μ = (a : ℂ) := by
    intro T hT μ h
    have hev : Module.End.HasEigenvalue T μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨(Module.End.mem_eigenspace_iff).2 h, hne⟩
    exact ⟨μ.re, by
      have := hT.conj_eigenvalue_eq_self hev
      exact (Complex.conj_eq_iff_re.1 this).symm⟩
  obtain ⟨c, hc⟩ := hre A hA _ h1
  obtain ⟨a, ha⟩ := hre B hB _ h2
  refine ⟨c, a, ?_, ?_⟩
  · intro k
    have := congrArg (fun w => (w : EuclideanSpace ℂ Q) k) h1
    simp only [hAdef, Matrix.toEuclideanLin_apply, hc] at this
    simpa [Matrix.mulVec, dotProduct] using this
  · intro k
    have := congrArg (fun w => (w : EuclideanSpace ℂ Q) k) h2
    simp only [hBdef, Matrix.toEuclideanLin_apply, ha] at this
    simpa [Matrix.mulVec, dotProduct] using this


lemma exp_conj_basis (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (k : Q → ℝ) (K : Matrix Q Q ℂ)
    (hK : K = basisMat v * Matrix.diagonal (fun s => (k s : ℂ)) * star (basisMat v)) :
    NormedSpace.exp K = ∑ j, (Real.exp (k j) : ℂ) • pureDensity (v j) := by
  have hU : IsUnit (basisMat v) :=
    ⟨⟨basisMat v, star (basisMat v), basisMat_mul_star v, basisMat_star_mul v⟩, rfl⟩
  have hinv : star (basisMat v) = (basisMat v)⁻¹ :=
    (Matrix.inv_eq_right_inv (basisMat_mul_star v)).symm
  rw [hK, hinv, Matrix.exp_conj _ _ hU, Matrix.exp_diagonal, ← hinv]
  rw [← basisMat_diag v (fun j => Real.exp (k j))]
  congr 3
  funext s
  simp [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]


lemma effectProb_sum_pure (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (c : Q → ℝ) (j : Q) :
    effectProb (pureDensity (v j)) (∑ l, (c l : ℂ) • pureDensity (v l)) = c j := by
  have h : ∀ l, effectProb (pureDensity (v j)) (pureDensity (v l)) = if j = l then 1 else 0 :=
    fun l => effectProb_pure_pure v l j
  unfold effectProb at h ⊢
  simp only [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.re_ofReal_mul]
  simp [h]

lemma rho_eq (Ham Nop : Matrix Q Q ℂ) (beta mu : ℝ)
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (a b : Q → ℝ)
    (hHa : ∀ j i, (∑ k : Q, Ham i k * v j k) = (a j : ℂ) * v j i)
    (hNb : ∀ j i, (∑ k : Q, Nop i k * v j k) = (b j : ℂ) * v j i) :
    rhoGCE Ham Nop beta mu = ∑ j, (((Real.exp (-beta * (a j - mu * b j)))
       / ∑ l, Real.exp (-beta * (a l - mu * b l)) : ℝ) : ℂ) • pureDensity (v j) := by
  set k : Q → ℝ := fun j => -beta * (a j - mu * b j) with hk
  set K : Matrix Q Q ℂ := (-(beta : ℂ)) • (Ham - (mu : ℂ) • Nop) with hKdef
  have h1 : K * basisMat v = basisMat v * Matrix.diagonal (fun s => (k s : ℂ)) := by
    ext i j
    have e1 := hHa j i
    have e2 := hNb j i
    rw [Matrix.mul_diagonal]
    simp only [hKdef, basisMat, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, hk]
    have : ∑ m, -(beta : ℂ) * (Ham i m - (mu : ℂ) * Nop i m) * (v j) m
        = -(beta : ℂ) * ((∑ m, Ham i m * (v j) m) - (mu : ℂ) * ∑ m, Nop i m * (v j) m) := by
      conv_rhs => rw [Finset.mul_sum (a := (mu : ℂ)), ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    rw [this, e1, e2]
    push_cast
    ring
  have hKW : K = basisMat v * Matrix.diagonal (fun s => (k s : ℂ)) * star (basisMat v) := by
    calc K = K * (basisMat v * star (basisMat v)) := by rw [basisMat_mul_star, Matrix.mul_one]
      _ = (K * basisMat v) * star (basisMat v) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [h1]
  have hexp := exp_conj_basis v k K hKW
  have htr : (NormedSpace.exp K).trace = ((∑ l, Real.exp (k l) : ℝ) : ℂ) := by
    rw [hexp]
    simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    have : ∀ j, (pureDensity (v j)).trace = 1 := fun j => (isDensity_pure v j).2
    simp [this]
  have hpos : 0 < ∑ l, Real.exp (k l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty
  unfold rhoGCE gibbsState
  change (NormedSpace.exp K).trace⁻¹ • NormedSpace.exp K = _
  rw [htr, hexp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  push_cast
  rw [div_eq_inv_mul]
  simp [hk]

end ex
end aux

theorem fock_main {Q : Type} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) (beta mu : ℝ) :
    (∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v) ∧
    ∀ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v →
      (fockEnsemble (rhoGCE Ham Nop beta mu) v).Valid ∧
      ensembleMean (fockEnsemble (rhoGCE Ham Nop beta mu) v) =
        rhoGCE Ham Nop beta mu := by
  refine ⟨exists_joint Ham Nop hH hN hcomm, fun v hv => ?_⟩
  choose a b hab using hv
  have hrho := rho_eq Ham Nop beta mu v a b (fun j => (hab j).1) (fun j => (hab j).2)
  set c : Q → ℝ := fun j => Real.exp (-beta * (a j - mu * b j))
      / ∑ l, Real.exp (-beta * (a l - mu * b l)) with hc
  have hpos : 0 < ∑ l, Real.exp (-beta * (a l - mu * b l)) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty
  have hprob : ∀ j, (fockEnsemble (rhoGCE Ham Nop beta mu) v).prob j = c j := by
    intro j
    show effectProb (pureDensity (v j)) (rhoGCE Ham Nop beta mu) = c j
    rw [hrho]
    exact effectProb_sum_pure v c j
  have hc0 : ∀ j, 0 ≤ c j := fun j => div_nonneg (Real.exp_pos _).le hpos.le
  have hc1 : ∑ j, c j = 1 := by
    rw [hc]; simp only
    rw [← Finset.sum_div, div_self hpos.ne']
  refine ⟨⟨fun j => by rw [hprob]; exact hc0 j, ?_, fun j => isDensity_pure v j⟩, ?_⟩
  · simp only [hprob]; exact hc1
  · show ∑ j, ((fockEnsemble (rhoGCE Ham Nop beta mu) v).prob j : ℂ) •
        (fockEnsemble (rhoGCE Ham Nop beta mu) v).state j = _
    have h2 : ∀ j, (((fockEnsemble (rhoGCE Ham Nop beta mu) v).prob j : ℝ) : ℂ) •
        (fockEnsemble (rhoGCE Ham Nop beta mu) v).state j = (c j : ℂ) • pureDensity (v j) :=
      fun j => by rw [hprob]; rfl
    rw [Finset.sum_congr rfl (fun j _ => h2 j)]
    exact hrho.symm

end MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07
open MassiveChannels.GCE

theorem solution {Q : Type} [Fintype Q] [DecidableEq Q]
    [Nonempty Q] (Ham Nop : Matrix Q Q ℂ) (hH : Ham.IsHermitian)
    (hN : Nop.IsHermitian) (hcomm : Ham * Nop = Nop * Ham) (beta mu : ℝ) :
    (∃ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v) ∧
    ∀ v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q), IsJointEigenbasis Ham Nop v →
      (fockEnsemble (rhoGCE Ham Nop beta mu) v).Valid ∧
      ensembleMean (fockEnsemble (rhoGCE Ham Nop beta mu) v) =
        rhoGCE Ham Nop beta mu :=
  MassiveChannels.GCE.fock_main Ham Nop hH hN hcomm beta mu
