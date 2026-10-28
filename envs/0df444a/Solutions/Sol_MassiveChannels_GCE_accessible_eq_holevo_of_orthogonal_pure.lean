-- Prove2me | solution 1 for MassiveChannels.GCE.accessible_eq_holevo_of_orthogonal_pure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:09:42.896059+00:00
-- url     : https://prove2.me/submissions/a1ce0d55-5adb-4453-a197-b248269d6652

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

end aux

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

theorem acc_main {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q]
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (p : Q → ℝ)
    (hp : (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1) :
    let e : CQData Q Q := ⟨p, fun j => pureDensity (v j)⟩
    e.Valid ∧ accessibleInformation e = ensembleInformation e ∧
      ensembleInformation e = shannon p ∧
      shannon p = vnEntropy (ensembleMean e) := by
  intro e
  have hmean : ensembleMean e = ∑ j, (p j : ℂ) • pureDensity (v j) := rfl
  have hH : vnEntropy (ensembleMean e) = shannon p := by
    rw [hmean]; exact vnEntropy_sum_pure v p
  have hI : ensembleInformation e = shannon p := by
    have h0 : ensembleInformation e =
        vnEntropy (ensembleMean e) - ∑ i, p i * vnEntropy (pureDensity (v i)) := by
      unfold ensembleInformation QAlgorithms.Papers.Independent.Information100.P27.labelInformation
      convert rfl
      rfl
    rw [h0, hH]
    have : (∑ i, p i * vnEntropy (pureDensity (v i))) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [vnEntropy_pure]; simp
    rw [this]; ring
  have hacc : accessibleInformation e = shannon p := by
    unfold accessibleInformation
    apply IsGreatest.csSup_eq
    constructor
    · let eQ : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
      let M0 : QAlgorithms.Papers.Independent.Information100.P04.Measurement Q :=
        { outcomes := Fintype.card Q
          positive := Fintype.card_pos
          effect := fun i => pureDensity (v (eQ i))
          valid := ⟨fun i => by
              show (pureDensity (v (eQ i))).PosSemidef
              rw [pureDensity_eq]; exact Matrix.posSemidef_vecMulVec_self_star _,
            by
              show ∑ i, pureDensity (v (eQ i)) = 1
              rw [Equiv.sum_comp eQ (fun j => pureDensity (v j))]
              exact sum_pureDensity v⟩ }
      refine ⟨M0, ?_⟩
      dsimp only
      have hJ : ∀ z : Q × Fin (Fintype.card Q), e.prob z.1 * effectProb (M0.effect z.2) (e.state z.1)
          = if eQ z.2 = z.1 then p z.1 else 0 := by
        intro z
        show p z.1 * effectProb (pureDensity (v (eQ z.2))) (pureDensity (v z.1)) = _
        rw [effectProb_pure_pure]
        split_ifs <;> simp
      have hm : (fun y : Fin (Fintype.card Q) =>
          ∑ x, e.prob (x, y).1 * effectProb (M0.effect (x, y).2) (e.state (x, y).1)) = fun y => p (eQ y) := by
        funext y
        show ∑ x : Q, e.prob x * effectProb (M0.effect y) (e.state x) = p (eQ y)
        rw [Finset.sum_congr rfl (fun x _ => hJ (x, y))]
        simp
      have hs1 : shannon (fun y : Fin (Fintype.card Q) => p (eQ y)) = shannon p :=
        shannon_reindex eQ p
      have hs2 : shannon (fun z : Q × Fin (Fintype.card Q) =>
          e.prob z.1 * effectProb (M0.effect z.2) (e.state z.1)) = shannon p := by
        rw [← hs1]
        unfold shannon
        congr 1
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun y _ => ?_
        have : ∀ x : Q, (e.prob (x, y).1 * effectProb (M0.effect (x, y).2) (e.state (x, y).1)) *
            Real.logb 2 (e.prob (x, y).1 * effectProb (M0.effect (x, y).2) (e.state (x, y).1))
            = if eQ y = x then p x * Real.logb 2 (p x) else 0 := by
          intro x
          rw [hJ (x, y)]
          split_ifs <;> simp
        beta_reduce
        rw [Finset.sum_congr rfl (fun x _ => this x)]
        simp
      rw [hm, hs2, hs1]; ring
    · rintro w ⟨M, hw⟩
      dsimp only at hw
      rw [hw]
      have := shannon_marg_le (X := Q) (Y := Fin M.outcomes)
        (fun z => e.prob z.1 * effectProb (M.effect z.2) (e.state z.1)) (fun z =>
          mul_nonneg (hp.1 _) (effectProb_nonneg _ (M.valid.1 _) _))
      linarith
  refine ⟨⟨hp.1, hp.2, fun j => isDensity_pure v j⟩, ?_, hI, hH.symm⟩
  rw [hacc, hI]

end MassiveChannels.GCE

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P07
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open MassiveChannels.GCE

theorem solution {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q]
    (v : OrthonormalBasis Q ℂ (EuclideanSpace ℂ Q)) (p : Q → ℝ)
    (hp : (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1) :
    let e : CQData Q Q := ⟨p, fun j => pureDensity (v j)⟩
    e.Valid ∧ accessibleInformation e = ensembleInformation e ∧
      ensembleInformation e = shannon p ∧
      shannon p = vnEntropy (ensembleMean e) :=
  MassiveChannels.GCE.acc_main v p hp
