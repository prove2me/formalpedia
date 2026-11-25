-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bes.torusDiag_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:08.436864+00:00
-- url     : https://prove2.me/submissions/2bf7fa61-79b0-435b-abc4-ac5c7873dfb5

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BesselSquareIntegrable_SchurHpkAlt
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_WeylGroupActions_TorusMovesCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusTail_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Bes_torusDiag_mid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bes
open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
namespace GlobalTheory.CompanionTheory.Bes
theorem _root_.solution (k : ℕ) {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0)
    (i : Fin (2 * r + k + 1)) : star (torusDiag k c i) * torusDiag k c (tau k r i) = 1 := by
  have hi := i.isLt
  by_cases h1 : i.val < r
  · have e : (tau k r i).val = 2 * r + k - i.val := by
      unfold tau; simp only; rw [if_pos (Or.inl h1)]
    unfold torusDiag
    rw [if_pos (by omega), if_neg (by omega), e,
      show 2 * r + k - (2 * r + k - i.val) = i.val by omega]
    exact mul_inv_cancel₀ (star_ne_zero.2 (torusTail_ne hc _))
  · by_cases h2 : r + k < i.val
    · have e : (tau k r i).val = 2 * r + k - i.val := by
        unfold tau; simp only; rw [if_pos (Or.inr h2)]
      unfold torusDiag
      rw [if_neg (by omega), if_pos (by omega), e, star_inv₀, star_star]
      exact inv_mul_cancel₀ (torusTail_ne hc _)
    · have e : (tau k r i).val = i.val := by
        unfold tau; simp only; rw [if_neg (by omega)]
      rw [torusDiag_mid k c i (by omega) (by omega),
        torusDiag_mid k c (tau k r i) (by omega) (by omega)]
      simp
end GlobalTheory.CompanionTheory.Bes
