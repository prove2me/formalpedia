-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.inK_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:32.210798+00:00
-- url     : https://prove2.me/submissions/26a5f147-767e-4f1e-90dd-35301df2edfe

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inK ε X ↔ (∀ c d, ε c ≠ ε d → X c d = 0) ∧ ∀ c d, star (X d c) = -X c d := by
  unfold inK inG Jm
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply, Matrix.zero_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ∀ c d, ε c ≠ ε d → X c d = 0 := by
      intro c d h
      have := h2 c d
      cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this <;>
        first | linear_combination this / 2 | linear_combination -this / 2
    refine ⟨h3, fun c d => ?_⟩
    have := h1 c d
    by_cases h : ε c = ε d
    · cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h this ⊢ <;>
        first | linear_combination this | linear_combination -this
    · simp [h3 c d h, h3 d c (Ne.symm h)]
  · rintro ⟨h1, h2⟩
    constructor
    · intro c d
      by_cases h : ε c = ε d
      · rw [h2, h]; ring
      · simp [h1 c d h, h1 d c (Ne.symm h)]
    · intro c d
      by_cases h : ε c = ε d
      · rw [h]; ring
      · simp [h1 c d h]
end GlobalTheory.CompanionTheory.DSStabLink
