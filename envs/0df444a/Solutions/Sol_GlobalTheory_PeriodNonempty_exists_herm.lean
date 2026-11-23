-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.exists_herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:36.002578+00:00
-- url     : https://prove2.me/submissions/3e2e0de9-2223-4933-be4f-824ef7d7c68e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution {g : ℕ} (B : LinearMap.BilinForm ℝ (Fin g → ℂ)) (halt : ∀ x y, B x y = -B y x)
    (hI : ∀ x y, B (Complex.I • x) (Complex.I • y) = B x y) (hpos : ∀ x, x ≠ 0 → 0 < B (Complex.I • x) x) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm x y).im = B x y := by
  classical
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := fun x => by
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  let h : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => B (Complex.I • x) y + B x y * Complex.I
  have hconj : ∀ x y, h x y = conj (h y x) := fun x y => by
    have h1 : B (Complex.I • x) y = B (Complex.I • y) x := by
      rw [← hI, hII, halt]; simp
    apply Complex.ext
    · simp [h, h1]
    · simp [h, halt x y]
  have hsm : ∀ (c : ℂ) (x : Fin g → ℂ), c • x = c.re • x + c.im • (Complex.I • x) := fun c x => by
    funext k; apply Complex.ext <;> simp <;> ring
  let hl : (Fin g → ℂ) → ((Fin g → ℂ) →ₗ[ℂ] ℂ) := fun y =>
    { toFun := fun x => h x y
      map_add' := fun x x' => by simp [h]; ring
      map_smul' := fun c x => by
        simp only [h]
        rw [smul_comm Complex.I c x, hsm c x, hsm c (Complex.I • x), hII]
        apply Complex.ext <;> simp <;> ring }
  have hsum : ∀ x y, h x y = ∑ i, x i * h (Pi.single i 1) y := fun x y => by
    change hl y x = ∑ i, x i • hl y (Pi.single i 1)
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  have key : ∀ x y, hermForm (Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1)) x y = h x y := fun x y => by
    rw [hsum x y]
    unfold hermForm dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hconj, hsum y, map_sum (starRingEnd ℂ)]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hconj, mul_comm]
    rfl
  refine ⟨Matrix.of fun i j => h (Pi.single i 1) (Pi.single j 1), ?_, fun z hz => ?_, fun x y => ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, hconj (Pi.single i 1)]
    rfl
  · rw [key]; simpa [h] using hpos z hz
  · rw [key]; simp [h]
end GlobalTheory.PeriodNonempty
