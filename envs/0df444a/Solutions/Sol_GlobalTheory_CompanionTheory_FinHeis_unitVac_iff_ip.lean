-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinHeis.unitVac_iff_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:34:36.018259+00:00
-- url     : https://prove2.me/submissions/f4fe27cc-c2a9-4a63-9e3d-0fab73df8301

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
namespace GlobalTheory.CompanionTheory.FinHeis
theorem _root_.solution (al : X → ℂ) (Γ : AddSubgroup X) (φ : M) :
    UnitVac S al Γ φ ↔ Law S al Γ φ ∧ ip S φ φ = 1 := Iff.rfl
end GlobalTheory.CompanionTheory.FinHeis
