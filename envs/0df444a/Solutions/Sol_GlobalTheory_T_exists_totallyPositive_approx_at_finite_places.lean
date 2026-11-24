-- Prove2me | solution 1 for GlobalTheory.T.exists_totallyPositive_approx_at_finite_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:06.6188+00:00
-- url     : https://prove2.me/submissions/e0302090-9db4-4fcc-a1e8-7d8ee7d664c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTotallyPositiveApproxAtFinitePlaces
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTotallyPositiveApproxAtFinitePlacesStatement
import Theorems.Thm_GlobalTheory_FinPlaceApproxPos_approxpos_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ), ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  first | exact @GlobalTheory.FinPlaceApproxPos.approxpos_target | exact GlobalTheory.FinPlaceApproxPos.approxpos_target | (intros; apply GlobalTheory.FinPlaceApproxPos.approxpos_target <;> assumption)
end _root_.GlobalTheory.T
