-- Prove2me | solution 1 for GlobalTheory.HL.BasicIneq.basic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:05.49415+00:00
-- url     : https://prove2.me/submissions/aea8e47d-d624-43c7-91e9-c89a6485ee75

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasicInequality
import Theorems.Thm_GlobalTheory_HL_BasicIneq_amp_le_mass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BasicIneq
namespace GlobalTheory.HL.BasicIneq
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → (∀ d P, ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P) ∧ ∀ (P : S.Datum → Submodule L.O S.V → Prop) (B ε : ℝ), 0 ≤ ε → (∀ d, S.mass d (P d) ≤ ENNReal.ofReal (B)) → (∀ d, ENNReal.ofReal (‖S.amp d (P d)‖) ≤ ENNReal.ofReal (ε) * S.mass d (P d)) → S.ampSq P ≤ ENNReal.ofReal (ε ^ 2 * B) * S.sumData fun d => S.mass d (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _
  refine ⟨amp_le_mass L r k S, fun P B ε hε hB hA => ?_⟩
  unfold Frames.ampSq Frames.sumData
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  beta_reduce
  rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (sq_nonneg ε), ENNReal.ofReal_pow hε]
  calc ENNReal.ofReal ‖S.amp o.out (P o.out)‖ ^ 2
      ≤ (ENNReal.ofReal ε * S.mass o.out (P o.out)) ^ 2 := by
        gcongr
        exact hA _
    _ = ENNReal.ofReal ε ^ 2 * S.mass o.out (P o.out) * S.mass o.out (P o.out) := by ring
    _ ≤ ENNReal.ofReal ε ^ 2 * ENNReal.ofReal B * S.mass o.out (P o.out) := by
        gcongr
        exact hB _
end GlobalTheory.HL.BasicIneq
