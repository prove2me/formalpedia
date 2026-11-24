-- Prove2me | solution 1 for GlobalTheory.FinPlaceApproxPos.approxpos_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:56.276848+00:00
-- url     : https://prove2.me/submissions/896a3101-607f-4b4b-977d-9be83f4f0339

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsApproxFinitePlacesNumberFieldTarget
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTotallyPositiveApproxAtFinitePlaces
import Theorems.Thm_GlobalTheory_FinPlaceApproxPos_exists_approx_totally_positive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.FinPlaceApproxPos
namespace GlobalTheory.FinPlaceApproxPos
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M
end GlobalTheory.FinPlaceApproxPos
