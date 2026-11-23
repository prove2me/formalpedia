-- Prove2me | solution 1 for GlobalTheory.cechAugHomology_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:22.125942+00:00
-- url     : https://prove2.me/submissions/7419e2a1-14d4-402f-9bcc-c660d2748b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cechCyclesIso_hom_subtype


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι R) :
    cechAugHomology A ≫ (cechHomologyZeroIso A).hom ≫
      ModuleCat.ofHom (LinearMap.ker (Cube.d A 1)).subtype = ModuleCat.ofHom (Cube.aug A) := by
  rw [cechAugHomology, Category.assoc, homologyπ_cechHomologyZeroIso_hom_assoc]
  exact (congrArg (_ ≫ ·) (cechCyclesIso_hom_subtype A 0)).trans (liftCycles_i _ _ _ _ _)
end GlobalTheory
