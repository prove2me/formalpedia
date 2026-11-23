-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_f_one_injective_of_sections_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:35.713477+00:00
-- url     : https://prove2.me/submissions/a48af35f-93b4-461a-bc85-937cba61cea7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_GlobalTheory_SheafLES_map_equivZero_symm
import Theorems.Thm_GlobalTheory_SheafLES_map_f_injective_of_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
include hS
namespace GlobalTheory.SheafLES
theorem _root_.solution (U : C)
    (h : Function.Surjective (S.g.hom.app (op U))) : Function.Injective (map.{w'} S.f 1 U) := by
  refine map_f_injective_of_surjective hS 0 U fun x => ?_
  obtain ⟨s, rfl⟩ := (equivZero S.X₃ U).symm.surjective x
  obtain ⟨t, rfl⟩ := h s
  exact ⟨_, map_equivZero_symm S.g U t⟩
end GlobalTheory.SheafLES
