-- Prove2me | solution 1 for GlobalTheory.SheafLES.sections_surjective_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:01.782801+00:00
-- url     : https://prove2.me/submissions/bb0799b9-8220-4dae-8e51-736b5b8a98ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES___equivZero_symm_eq_zero_iff_47a22b9ce459

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
    (h : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U)) : Function.Surjective (S.g.hom.app (op U)) :=
  fun s => (δ_equivZero_symm_eq_zero_iff.{w'} hS U s).1 (@Subsingleton.elim _ h _ _)
end GlobalTheory.SheafLES
