-- Prove2me | solution 1 for GlobalTheory.cechAbHEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:59.865848+00:00
-- url     : https://prove2.me/submissions/666eda50-24cd-4993-a98b-4d056a23dacd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_naturality


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
variable {F}
namespace GlobalTheory
theorem _root_.solution (φ : F ⟶ G) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R G V U n ((cechAbHMap V U φ.mapPresheaf n).hom x) =
      (cechHMap R V U φ n).hom (cechAbHEquiv R F V U n x) :=
  (cechAbCubeToCube R F V U).homology_naturality (cechAbCubeToCube R G V U)
    (cechAbCubeMap V U φ.mapPresheaf) (cechCubeMap R V U φ) (fun _ _ _ => rfl) n x
end GlobalTheory
