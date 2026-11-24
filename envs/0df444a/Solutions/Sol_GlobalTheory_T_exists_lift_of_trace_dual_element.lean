-- Prove2me | solution 1 for GlobalTheory.T.exists_lift_of_trace_dual_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:26.984479+00:00
-- url     : https://prove2.me/submissions/b518d0b4-8915-436b-bbca-80a815640c65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfTraceDualElement
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfTraceDualElementStatement
import Theorems.Thm_GlobalTheory_traceDual_integral_of_not_dvd_discr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  first | exact @GlobalTheory.traceDual_integral_of_not_dvd_discr | exact GlobalTheory.traceDual_integral_of_not_dvd_discr | (intros; apply GlobalTheory.traceDual_integral_of_not_dvd_discr <;> assumption)
end _root_.GlobalTheory.T
