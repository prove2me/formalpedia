-- Prove2me | solution 1 for GlobalTheory.sectionsOn.equivOfSMul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:07.38954+00:00
-- url     : https://prove2.me/submissions/9ab0a4e0-e915-4175-895c-97398e4838fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.sectionsOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G H : X.Modules} {U V W : X.Opens}
namespace GlobalTheory.sectionsOn
theorem _root_.solution [Module R Γ(F, U)]
    (h : ∀ (r : R) (x : Γ(F, U)), r • x = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • x)
    (x : sectionsOn F U) : equivOfSMul R F U h x = toΓ F U x := rfl
end GlobalTheory.sectionsOn
