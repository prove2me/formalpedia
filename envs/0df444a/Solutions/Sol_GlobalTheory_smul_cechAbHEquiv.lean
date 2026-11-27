-- Prove2me | solution 1 for GlobalTheory.smul_cechAbHEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:46.816773+00:00
-- url     : https://prove2.me/submissions/86b19ae8-8722-4093-a4f5-5a2975376ece

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_cechHMap_smulHom_apply
import Theorems.Thm_GlobalTheory_cechAbHEquiv_map

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
theorem _root_.solution (r : R) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    r • cechAbHEquiv R F V U n x = cechAbHEquiv R F V U n
      ((cechAbHMap V U (smulHom F (algebraMap R Γ(X, ⊤) r)).mapPresheaf n).hom x) := by
  rw [cechAbHEquiv_map, cechHMap_smulHom_apply]
end GlobalTheory
