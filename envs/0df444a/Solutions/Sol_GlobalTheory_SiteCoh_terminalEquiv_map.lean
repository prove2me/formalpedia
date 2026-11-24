-- Prove2me | solution 1 for GlobalTheory.SiteCoh.terminalEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:49:16.149348+00:00
-- url     : https://prove2.me/submissions/6f4647d1-a76f-499f-aae8-5e0813d65165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Theorems.Thm_GlobalTheory_SiteCoh_extEquiv_map
import Theorems.Thm_GlobalTheory_SiteCoh_terminalEquiv_apply

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
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.SiteCoh
theorem _root_.solution {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) {T : C}
    (hT : IsTerminal T) (x : F.H' n T) :
    terminalEquiv G n hT (map f n T x) = Sheaf.H.map f n (terminalEquiv F n hT x) := by
  rw [terminalEquiv_apply, terminalEquiv_apply, extEquiv_map, Sheaf.H.map_apply]
  symm
  apply Ext.comp_assoc
  all_goals omega
end GlobalTheory.SiteCoh
