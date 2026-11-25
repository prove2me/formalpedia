-- Prove2me | solution 1 for GlobalTheory.QCoh.exact_iff_stalkLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:58:00.093224+00:00
-- url     : https://prove2.me/submissions/f75261cc-0507-4354-9b40-637c72a95ee9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Theorems.Thm_GlobalTheory_SheafLES_exact_map_toAbSheaf_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, Function.Exact (stalkLinear S.f x) (stalkLinear S.g x) := by
  rw [← SheafLES.exact_map_toAbSheaf_iff, TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  exact forall_congr' fun x ↦ ShortComplex.ab_exact_iff_function_exact _
end GlobalTheory.QCoh
