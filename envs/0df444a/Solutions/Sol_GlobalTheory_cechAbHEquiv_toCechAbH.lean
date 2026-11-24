-- Prove2me | solution 1 for GlobalTheory.cechAbHEquiv_toCechAbH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:59.946663+00:00
-- url     : https://prove2.me/submissions/6871509b-502c-4b75-8a4f-777a2d11769e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechAugHomology


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
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]
variable [LinearOrder ι]
namespace GlobalTheory
theorem _root_.solution (x : sectionsOn F V) :
    cechAbHEquiv R F V U 0 (toCechAbH F.presheaf V U (sectionsOn.toΓ F V x)) =
      toCechH R F V U x :=
  (cechAbCubeToCube R F V U).homology_cechAugHomology _
end GlobalTheory
