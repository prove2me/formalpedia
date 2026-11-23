-- Prove2me | solution 1 for GlobalTheory.cochainCyclesIsoKer_hom_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:18.584793+00:00
-- url     : https://prove2.me/submissions/8058d23d-51c6-421a-9da6-d592ddfda105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    (f : K.X p →ₗ[R] K.X (p + 1)) (hf : K.d p (p + 1) = ModuleCat.ofHom f) :
    (cochainCyclesIsoKer K p f hf).hom ≫ ModuleCat.ofHom (LinearMap.ker f).subtype =
      K.iCycles p :=
  IsLimit.conePointUniqueUpToIso_hom_comp (K.cyclesIsKernel p (p + 1) (by simp))
    (ModuleCat.kernelIsLimit _) WalkingParallelPair.zero
end GlobalTheory
