-- Prove2me | solution 1 for GlobalTheory.quasiIso_extendScalars_extendScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:37.385001+00:00
-- url     : https://prove2.me/submissions/3dbc638c-096d-4efb-b8fa-7badd95e21e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexOfNoetherianModel
import Theorems.Thm_GlobalTheory_IsGradedMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R₀ R R' : Type} [CommRing R₀] [CommRing R]
    [CommRing R'] (f : R₀ →+* R) (g : R →+* R') {K L : CochainComplex (ModuleCat.{0} R₀) ℕ}
    (φ : K ⟶ L)
    (h : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (g.comp f)).mapHomologicalComplex _).map φ)) :
    QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map
      (((ModuleCat.extendScalars.{0, 0, 0} f).mapHomologicalComplex _).map φ)) := by
  let e := NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{0} f g)
    (ComplexShape.up ℕ)
  have h' : QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} f ⋙
      ModuleCat.extendScalars.{0, 0, 0} g).mapHomologicalComplex _).map φ) := by
    rw [← NatIso.naturality_1 e φ]
    infer_instance
  exact h'
end GlobalTheory
