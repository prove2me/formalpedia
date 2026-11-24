-- Prove2me | solution 1 for GlobalTheory.UnitaryOrbitForm.eq_zero_of_forall_dotProduct_star_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:11.250874+00:00
-- url     : https://prove2.me/submissions/faf0a563-a59a-493f-bad4-84275f2fa84b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
private lemma dotProduct_mulVec_star_add_smul_expand (C : Matrix (Fin r) (Fin r) ℂ) (a b : ℂ) (x y : Fin r → ℂ) :
    (a • x + b • y) ⬝ᵥ C *ᵥ star (a • x + b • y) =
      a * star a * (x ⬝ᵥ C *ᵥ star x) + b * star b * (y ⬝ᵥ C *ᵥ star y) +
        a * star b * (x ⬝ᵥ C *ᵥ star y) + b * star a * (y ⬝ᵥ C *ᵥ star x) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring
end GlobalTheory.UnitaryOrbitForm
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
namespace GlobalTheory.UnitaryOrbitForm
theorem _root_.solution {C : Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ u : Fin r → ℂ, u ⬝ᵥ C *ᵥ star u = 0) : C = 0 := by
  have hS : ∀ x y : Fin r → ℂ, x ⬝ᵥ C *ᵥ star y = 0 := by
    intro x y
    have h1 := h ((1 : ℂ) • x + (1 : ℂ) • y)
    have h2 := h ((1 : ℂ) • x + Complex.I • y)
    rw [dotProduct_mulVec_star_add_smul_expand, h x, h y] at h1 h2
    have hsI : star Complex.I = -Complex.I := by simp
    rw [hsI, star_one] at h2
    rw [star_one] at h1
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
      ((x ⬝ᵥ C *ᵥ star y) - (y ⬝ᵥ C *ᵥ star x)) / 2 * Complex.I_sq
  ext i j
  have := hS (Pi.single i 1) (Pi.single j 1)
  simpa using this
end GlobalTheory.UnitaryOrbitForm
