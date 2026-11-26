-- Prove2me | solution 1 for MuirheadMST.lintegral_latentRoots_border
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:10:28.548607+00:00
-- url     : https://prove2.me/submissions/184daea5-5e31-4cd0-bdf8-9abe02bf85f7

import Mathlib
import Definitions.Def_MuirheadMST_Wishart
import Theorems.Thm_MuirheadMST_measurable_latentRoots

open MeasureTheory

open scoped Classical

noncomputable section

namespace BorderAux
open MuirheadMST

/-- Upper-triangle index set. -/
abbrev U (m : ℕ) := {p : Fin m × Fin m // p.1 ≤ p.2}

/-- Symmetric completion of upper-triangular entries. -/
def symC {m : ℕ} (a : U m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j => if h : i ≤ j then a ⟨(i, j), h⟩ else a ⟨(j, i), le_of_not_ge h⟩

lemma measurable_symC (m : ℕ) : Measurable (symC (m := m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold symC
  split_ifs <;> exact measurable_pi_apply _

/-- Block assembly `[[t, bᵀ], [b, B]]`. -/
def blk {m : ℕ} (t : ℝ) (b : Fin m → ℝ) (B : Fin m → Fin m → ℝ) :
    Fin (m + 1) → Fin (m + 1) → ℝ :=
  Fin.cons (Fin.cons t b : Fin (m + 1) → ℝ) (fun i => (Fin.cons (b i) (B i) : Fin (m + 1) → ℝ))

lemma measurable_blk (m : ℕ) :
    Measurable fun q : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) => blk q.1 q.2.1 q.2.2 := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp only [blk, Fin.cons_zero, Fin.cons_succ]
    <;> fun_prop

lemma measurable_diagArray (m : ℕ) : Measurable (diagArray (m := m)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold diagArray
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

/-! Coordinates `(a₁₁, b, A₂₂)` for symmetric `(m+1) × (m+1)` matrices (from the Γ_m proof). -/

/-- The index map `Unit ⊕ (Fin m ⊕ U m) → U (m+1)`. -/
def idxFun (m : ℕ) : Unit ⊕ (Fin m ⊕ U m) → U (m + 1)
  | .inl _ => ⟨(0, 0), le_rfl⟩
  | .inr (.inl j) => ⟨(0, j.succ), Fin.zero_le _⟩
  | .inr (.inr p) => ⟨(p.1.1.succ, p.1.2.succ), Fin.succ_le_succ_iff.2 p.2⟩

lemma idxFun_bij (m : ℕ) : Function.Bijective (idxFun m) := by
  constructor
  · rintro (_ | j | ⟨⟨i, j⟩, h⟩) (_ | j' | ⟨⟨i', j'⟩, h'⟩) e <;>
      simp [idxFun, Subtype.ext_iff, Prod.ext_iff, Fin.succ_ne_zero] at e ⊢ <;>
      first
        | exact e
        | exact (Fin.succ_ne_zero _ e.symm).elim
        | exact (Fin.succ_ne_zero _ e.1.symm).elim
  · rintro ⟨⟨i, j⟩, h⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact ⟨.inl (), rfl⟩
      | succ j => exact ⟨.inr (.inl j), rfl⟩
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd h (by simp)
      | succ j => exact ⟨.inr (.inr ⟨(i, j), Fin.succ_le_succ_iff.1 h⟩), rfl⟩

def idxEquiv (m : ℕ) : Unit ⊕ (Fin m ⊕ U m) ≃ U (m + 1) := Equiv.ofBijective _ (idxFun_bij m)

lemma symC_decomp (m : ℕ) (t : ℝ) (b : Fin m → ℝ) (y : U m → ℝ) :
    symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
      (Sum.elim (fun _ => t) (Sum.elim b y))) = blk t b (symC y) := by
  have key : ∀ (z : Unit ⊕ (Fin m ⊕ U m) → ℝ) (p : U (m + 1)),
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m) z p = z ((idxEquiv m).symm p) := by
    intro z p
    conv_lhs => rw [← (idxEquiv m).apply_symm_apply p]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) _ _ _
  have hs1 : ∀ h, (idxEquiv m).symm ⟨(0, 0), h⟩ = .inl () := fun h =>
    (Equiv.symm_apply_eq _).2 rfl
  have hs2 : ∀ (j : Fin m) h, (idxEquiv m).symm ⟨(0, j.succ), h⟩ = .inr (.inl j) := fun j h =>
    (Equiv.symm_apply_eq _).2 rfl
  have hs3 : ∀ (i j : Fin m) h, (idxEquiv m).symm ⟨(i.succ, j.succ), h⟩ =
      .inr (.inr ⟨(i, j), Fin.succ_le_succ_iff.1 h⟩) := fun i j h =>
    (Equiv.symm_apply_eq _).2 rfl
  funext i j
  simp only [symC, key]
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [hs1, blk]
    | succ j => simp [hs2, blk]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp [hs2, blk]
    | succ j =>
      by_cases h : i ≤ j
      · simp [h, hs3, blk, symC]
      · simp [h, hs3, blk, symC]

lemma lintegral_decomp (m : ℕ) (G : (Fin (m + 1) → Fin (m + 1) → ℝ) → ENNReal)
    (hG : Measurable G) :
    ∫⁻ x : U (m + 1) → ℝ, G (symC x) =
      ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, G (blk t b (symC y)) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : U (m + 1) => ℝ) (idxEquiv m)
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Unit ⊕ (Fin m ⊕ U m) => ℝ)
  have h3 := (volume_preserving_funUnique Unit ℝ).symm
  have h4 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ U m => ℝ)
  have hm : Measurable fun p : (Unit → ℝ) × (Fin m ⊕ U m → ℝ) =>
      G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
        ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm p))) :=
    hG.comp ((measurable_symC _).comp ((MeasurableEquiv.measurable _).comp
      (MeasurableEquiv.measurable _)))
  calc ∫⁻ x : U (m + 1) → ℝ, G (symC x)
      = ∫⁻ z : Unit ⊕ (Fin m ⊕ U m) → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m) z)) :=
        (h1.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ p : (Unit → ℝ) × (Fin m ⊕ U m → ℝ),
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm p))) :=
        (h2.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ u : Unit → ℝ, ∫⁻ w : Fin m ⊕ U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (u, w)))) :=
        lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ w : Fin m ⊕ U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t, w)))) :=
        (h3.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ t : ℝ, ∫⁻ q : (Fin m → ℝ) × (U m → ℝ),
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t,
                (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm q)))) := by
        refine lintegral_congr fun t => ?_
        exact (h4.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) _).symm
    _ = ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ,
          G (symC (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (idxEquiv m)
            ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
              ((MeasurableEquiv.funUnique Unit ℝ).symm t,
                (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (b, y))))) := by
        refine lintegral_congr fun t => ?_
        refine lintegral_prod _ ?_
        exact (hm.comp (measurable_prodMk_left.comp (MeasurableEquiv.measurable _))).aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, G (blk t b (symC y)) := by
        refine lintegral_congr fun t => lintegral_congr fun b => lintegral_congr fun y => ?_
        rw [← symC_decomp m t b y]
        congr 3

/-! Spectral facts. -/

/-- Latent roots depend only on the characteristic polynomial. -/
lemma latentRoots_eq_of_charpoly {n : ℕ} {A B : Fin n → Fin n → ℝ}
    (hA : (Matrix.of A).IsHermitian) (hB : (Matrix.of B).IsHermitian)
    (h : (Matrix.of A).charpoly = (Matrix.of B).charpoly) : latentRoots A = latentRoots B := by
  unfold latentRoots
  rw [dif_pos hA, dif_pos hB]
  have e : List.ofFn hA.eigenvalues₀ = List.ofFn hB.eigenvalues₀ := by
    rw [← hA.sort_roots_charpoly_eq_eigenvalues₀, ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]
  rw [List.ofFn_inj.1 e]

/-- Symmetric matrices with the same characteristic polynomial are orthogonally similar. -/
lemma exists_orth_conj {m : ℕ} {S T : Matrix (Fin m) (Fin m) ℝ} (hS : S.IsHermitian)
    (hT : T.IsHermitian) (h : S.charpoly = T.charpoly) :
    ∃ O : Matrix (Fin m) (Fin m) ℝ, O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      S = O * T * O.transpose := by
  have he := (hS.eigenvalues_eq_eigenvalues_iff hT).2 h
  have h1 := hS.spectral_theorem
  have h2 := hT.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, he] at h1 h2
  have hU1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU2 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hV1 := Unitary.coe_star_mul_self hT.eigenvectorUnitary
  have hV2 := Unitary.coe_mul_star_self hT.eigenvectorUnitary
  set U : Matrix (Fin m) (Fin m) ℝ := (hS.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  set V : Matrix (Fin m) (Fin m) ℝ := (hT.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)
  set D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at *
  refine ⟨U * V.transpose, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U.transpose,
      hU1, Matrix.one_mul, hV2]
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc V.transpose,
      hV1, Matrix.one_mul, hU2]
  · have hD : D = V.transpose * T * V := by
      rw [h2]
      simp only [← Matrix.mul_assoc, hV1, Matrix.one_mul]
      rw [Matrix.mul_assoc, hV1, Matrix.mul_one]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    conv_lhs => rw [h1, hD]
    simp only [Matrix.mul_assoc]

lemma isHermitian_symC {m : ℕ} (y : U m → ℝ) : (Matrix.of (symC y)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Matrix.of_apply, star_trivial, symC]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [dif_neg (not_le.2 hij), dif_pos hij.le]
  · rfl
  · rw [dif_pos hij.le, dif_neg (not_le.2 hij)]

lemma isHermitian_blk {m : ℕ} (t : ℝ) (b : Fin m → ℝ) {B : Fin m → Fin m → ℝ}
    (hB : (Matrix.of B).IsHermitian) : (Matrix.of (blk t b B)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [Matrix.of_apply, star_trivial, blk, Fin.cons_zero, Fin.cons_succ]
  rename_i i j
  simpa using hB.apply i j

lemma isHermitian_diagArray {m : ℕ} (l : Fin m → ℝ) : (Matrix.of (diagArray l)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Matrix.of_apply, star_trivial, diagArray]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij)]

lemma charpoly_diagArray_latentRoots {m : ℕ} {S : Fin m → Fin m → ℝ}
    (hS : (Matrix.of S).IsHermitian) :
    (Matrix.of S).charpoly = (Matrix.of (diagArray (latentRoots S))).charpoly := by
  have hd : Matrix.of (diagArray (latentRoots S)) = Matrix.diagonal (latentRoots S) := by
    ext i j; simp [diagArray, Matrix.diagonal_apply]
  rw [hd, Matrix.charpoly_diagonal, hS.charpoly_eq]
  unfold latentRoots Matrix.IsHermitian.eigenvalues
  rw [dif_pos hS]
  simp only [RCLike.ofReal_real_eq_id, id]
  exact (Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun k => Polynomial.X - Polynomial.C (hS.eigenvalues₀ k))).trans
    (Equiv.prod_comp (finCongr (Fintype.card_fin m).symm) _).symm

/-- Conjugating a bordered matrix by `diag(1, O)`. -/
lemma charpoly_blk_conj {m : ℕ} {O : Matrix (Fin m) (Fin m) ℝ} (hO1 : O.transpose * O = 1)
    (hO2 : O * O.transpose = 1) (t : ℝ) (b : Fin m → ℝ) (T : Fin m → Fin m → ℝ) :
    (Matrix.of (blk t b (Matrix.of.symm (O * Matrix.of T * O.transpose)))).charpoly =
      (Matrix.of (blk t (O.transpose.mulVec b) T)).charpoly := by
  set Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of (blk 1 0 O)
  have hQ : Q.transpose * Q = 1 := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [Q, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
    all_goals first
      | exact fun h => Fin.succ_ne_zero _ (Eq.symm h)
      | (rename_i i j; simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hO1 i) j)
  have hw : O.mulVec (O.transpose.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, hO2, Matrix.one_mulVec]
  generalize O.transpose.mulVec b = w at hw ⊢
  subst hw
  have hconj : Matrix.of (blk t (O.mulVec w) (Matrix.of.symm (O * Matrix.of T * O.transpose))) =
      Q * Matrix.of (blk t w T) * Q.transpose := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp [Q, blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.mulVec, dotProduct, mul_comm]
  rw [hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul]

lemma measurePreserving_mulVec {m : ℕ} {O : Matrix (Fin m) (Fin m) ℝ} (hO1 : O.transpose * O = 1) :
    MeasurePreserving (fun b : Fin m → ℝ => O.transpose.mulVec b) volume volume := by
  have hd : O.transpose.det * O.transpose.det = 1 := by
    have := congrArg Matrix.det hO1
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_transpose] at this
    rwa [Matrix.det_transpose]
  have habs : |O.transpose.det| = 1 := by
    have h2 : |O.transpose.det| * |O.transpose.det| = 1 := by rw [← abs_mul, hd, abs_one]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact h
    · exact absurd h (by linarith [abs_nonneg O.transpose.det])
  have hne : LinearMap.det (Matrix.toLin' O.transpose) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h0; rw [h0] at habs; simp at habs
  refine ⟨(Matrix.toLin' O.transpose).continuous_of_finiteDimensional.measurable, ?_⟩
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → ℝ))) hne
  rw [LinearMap.det_toLin', abs_inv, habs, inv_one, ENNReal.ofReal_one, one_smul] at this
  exact this

/-- The inner `(b, c)` integral only sees the latent roots of the lower-right block. -/
lemma inner_eq {m : ℕ} (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h)
    (S : Fin m → Fin m → ℝ) (hS : (Matrix.of S).IsHermitian) :
    ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots (blk p.2 p.1 S)) =
      ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots (blk p.2 p.1 (diagArray (latentRoots S)))) := by
  obtain ⟨O, hO1, hO2, hSO⟩ := exists_orth_conj hS (isHermitian_diagArray _)
    (charpoly_diagArray_latentRoots hS)
  set D := diagArray (latentRoots S)
  have hS' : S = Matrix.of.symm (O * Matrix.of D * O.transpose) := by rw [← hSO]; rfl
  have key : ∀ p : (Fin m → ℝ) × ℝ,
      latentRoots (blk p.2 p.1 S) = latentRoots (blk p.2 (O.transpose.mulVec p.1) D) := by
    intro p
    refine latentRoots_eq_of_charpoly (isHermitian_blk _ _ hS)
      (isHermitian_blk _ _ (isHermitian_diagArray _)) ?_
    calc (Matrix.of (blk p.2 p.1 S)).charpoly
        = (Matrix.of (blk p.2 p.1 (Matrix.of.symm (O * Matrix.of D * O.transpose)))).charpoly := by
          rw [← hS']
      _ = _ := charpoly_blk_conj hO1 hO2 _ _ _
  simp_rw [key]
  have hmp : MeasurePreserving (Prod.map (fun b : Fin m → ℝ => O.transpose.mulVec b) id)
      (volume : Measure ((Fin m → ℝ) × ℝ)) volume :=
    (measurePreserving_mulVec hO1).prod (MeasurePreserving.id volume)
  exact hmp.lintegral_comp (f := fun p : (Fin m → ℝ) × ℝ => h (latentRoots (blk p.2 p.1 D)))
    (hh.comp ((measurable_latentRoots _).comp ((measurable_blk m).comp
      (measurable_snd.prodMk (measurable_fst.prodMk measurable_const)))))

end BorderAux

open MuirheadMST BorderAux in
theorem solution (m : ℕ) (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h) :
    ∫⁻ A, h (latentRoots A) ∂(symVolume (m + 1)) =
      ∫⁻ A, (∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
          ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
            (fun i => (Fin.cons (p.1 i) (diagArray (latentRoots A) i) : Fin (m + 1) → ℝ)) :
              Fin (m + 1) → Fin (m + 1) → ℝ)))) ∂(symVolume m) := by
  have hG : Measurable fun A : Fin (m + 1) → Fin (m + 1) → ℝ => h (latentRoots A) :=
    hh.comp (measurable_latentRoots _)
  have hF : Measurable fun q : ℝ × (Fin m → ℝ) × (U m → ℝ) =>
      h (latentRoots (blk q.1 q.2.1 (symC q.2.2))) :=
    hG.comp ((measurable_blk m).comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_symC m).comp (measurable_snd.comp measurable_snd)))))
  have hΨ : Measurable fun A : Fin m → Fin m → ℝ =>
      ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots (blk p.2 p.1 (diagArray (latentRoots A)))) := by
    refine Measurable.lintegral_prod_right'
      (f := fun q : (Fin m → Fin m → ℝ) × ((Fin m → ℝ) × ℝ) =>
        h (latentRoots (blk q.2.2 q.2.1 (diagArray (latentRoots q.1))))) ?_
    exact hG.comp ((measurable_blk m).comp ((measurable_snd.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_diagArray m).comp ((measurable_latentRoots m).comp measurable_fst)))))
  change ∫⁻ A, h (latentRoots A) ∂(Measure.map symC volume) =
    ∫⁻ A, (∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots (blk p.2 p.1 (diagArray (latentRoots A)))))
      ∂(Measure.map symC volume)
  rw [lintegral_map hG (measurable_symC _), lintegral_map hΨ (measurable_symC _),
    lintegral_decomp m _ hG]
  calc ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ y : U m → ℝ, h (latentRoots (blk t b (symC y)))
      = ∫⁻ t : ℝ, ∫⁻ y : U m → ℝ, ∫⁻ b : Fin m → ℝ, h (latentRoots (blk t b (symC y))) := by
        refine lintegral_congr fun t => lintegral_lintegral_swap ?_
        exact (hF.comp (f := fun q : (Fin m → ℝ) × (U m → ℝ) => (t, q.1, q.2))
          (by fun_prop)).aemeasurable
    _ = ∫⁻ y : U m → ℝ, ∫⁻ t : ℝ, ∫⁻ b : Fin m → ℝ, h (latentRoots (blk t b (symC y))) := by
        refine lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        exact Measurable.lintegral_prod_right'
          (f := fun q : (ℝ × (U m → ℝ)) × (Fin m → ℝ) => h (latentRoots (blk q.1.1 q.2 (symC q.1.2))))
          (hF.comp (f := fun q : (ℝ × (U m → ℝ)) × (Fin m → ℝ) => (q.1.1, q.2, q.1.2)) (by fun_prop))
    _ = ∫⁻ y : U m → ℝ, ∫⁻ b : Fin m → ℝ, ∫⁻ t : ℝ, h (latentRoots (blk t b (symC y))) := by
        refine lintegral_congr fun y => lintegral_lintegral_swap ?_
        exact (hF.comp (f := fun q : ℝ × (Fin m → ℝ) => (q.1, q.2, y)) (by fun_prop)).aemeasurable
    _ = ∫⁻ y : U m → ℝ, ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots (blk p.2 p.1 (symC y))) := by
        refine lintegral_congr fun y => (lintegral_prod
          (f := fun p : (Fin m → ℝ) × ℝ => h (latentRoots (blk p.2 p.1 (symC y)))) ?_).symm
        exact (hF.comp (f := fun q : (Fin m → ℝ) × ℝ => (q.2, q.1, y)) (by fun_prop)).aemeasurable
    _ = _ := lintegral_congr fun y => inner_eq h hh _ (isHermitian_symC y)

end
