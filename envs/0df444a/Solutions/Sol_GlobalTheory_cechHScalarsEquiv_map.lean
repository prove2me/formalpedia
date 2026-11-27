-- Prove2me | solution 1 for GlobalTheory.cechHScalarsEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:32.697154+00:00
-- url     : https://prove2.me/submissions/bfdeb9fc-f844-43bf-bcd7-f51ff85045ea

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
theorem _root_.solution (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHScalarsEquiv R G V U S n ((cechHMap R V U φ n).hom x) =
      (cechHMap S V U φ n).hom (cechHScalarsEquiv R F V U S n x) :=
  (cechCubeScalars R F V U S).homology_naturality (cechCubeScalars R G V U S)
    (cechCubeMap R V U φ) (cechCubeMap S V U φ) (fun _ _ _ => rfl) n x
end GlobalTheory
