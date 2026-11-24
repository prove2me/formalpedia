-- Prove2me | solution 1 for GlobalTheory.cechHMap_toCechH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:29.919948+00:00
-- url     : https://prove2.me/submissions/9a806395-c60e-450b-a444-17b49551f87a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_homologyMap_presheafToCechH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
variable {F}
namespace GlobalTheory
theorem _root_.solution (φ : F ⟶ G) (x : sectionsOn F V) :
    (cechHMap R V U φ 0).hom (toCechH R F V U x) = toCechH R G V U (sectionsOn.map R φ V x) :=
  homologyMap_presheafToCechH V U (sectionsPresheafMap R φ) x
end GlobalTheory
