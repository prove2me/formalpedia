-- Prove2me | solution 1 for GlobalTheory.cech_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:54.411239+00:00
-- url     : https://prove2.me/submissions/837a4cb4-b750-4f67-8efe-964d6867ca07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH

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
namespace GlobalTheory
theorem _root_.solution (p : ℕ)
    (x : ∀ s : {s : Finset ι // s.card = p + 1}, sectionsOn F (cechOpen V U s.1))
    (t : {s : Finset ι // s.card = p + 1 + 1}) :
    (show ∀ s : {s : Finset ι // s.card = p + 1 + 1}, sectionsOn F (cechOpen V U s.1) from
      ((cech R F V U).d p (p + 1)).hom x) t = ∑ i : t.1, cubeSign t.1 i.1 •
        sectionsOn.res R F (cechOpen_anti V U (Finset.erase_subset i.1 t.1))
          (x (Cube.eraseIdx t i)) := by
  rw [cech_d]
  exact Cube.d_apply (cechCube R F V U) (p + 1) x t
end GlobalTheory
