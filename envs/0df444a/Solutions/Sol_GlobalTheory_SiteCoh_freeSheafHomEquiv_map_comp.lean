-- Prove2me | solution 1 for GlobalTheory.SiteCoh.freeSheafHomEquiv_map_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:50.737283+00:00
-- url     : https://prove2.me/submissions/db340242-a036-423d-9ff9-88e0b031a50e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Theorems.Thm_GlobalTheory_SiteCoh_freeSheaf_map_tautSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
namespace GlobalTheory.SiteCoh
theorem _root_.solution {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeSheaf J).obj U ⟶ F) :
    freeSheafHomEquiv V F ((freeSheaf J).map i ≫ φ) =
      F.obj.map i.op (freeSheafHomEquiv U F φ) := by
  change φ.hom.app (op V) (((freeSheaf J).map i).hom.app (op V) (tautSection J V)) = _
  rw [freeSheaf_map_tautSection]
  exact ConcreteCategory.congr_hom (φ.hom.naturality i.op) _
end GlobalTheory.SiteCoh
