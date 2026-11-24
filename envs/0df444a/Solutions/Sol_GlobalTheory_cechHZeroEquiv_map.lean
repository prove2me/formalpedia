-- Prove2me | solution 1 for GlobalTheory.cechHZeroEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:10.949622+00:00
-- url     : https://prove2.me/submissions/5686f4e6-5803-40af-a430-dded7d295c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_cechHMap_toCechH

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
variable {V U} (hc : V ≤ ⨆ i, U i)
variable {F}
namespace GlobalTheory
theorem _root_.solution (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquiv R G hc ((cechHMap R V U φ 0).hom x) =
      sectionsOn.map R φ V (cechHZeroEquiv R F hc x) := by
  obtain ⟨y, rfl⟩ := (toCechH_bijective R F hc).2 x
  rw [cechHMap_toCechH, cechHZeroEquiv_toCechH, cechHZeroEquiv_toCechH]
end GlobalTheory
