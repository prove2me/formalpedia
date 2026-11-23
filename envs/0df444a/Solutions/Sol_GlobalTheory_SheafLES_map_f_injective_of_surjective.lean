-- Prove2me | solution 1 for GlobalTheory.SheafLES.map_f_injective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.913407+00:00
-- url     : https://prove2.me/submissions/4d650982-c923-4cac-982e-b17e3b2ea3a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__5aa7b67be2da
import Theorems.Thm_P2M_GlobalTheory_SheafLES___map_026ec4bafb10
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SheafLES.δ_map

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
theorem _root_.solution (n : ℕ) (U : C)
    (h : Function.Surjective (map.{w'} S.g n U)) :
    Function.Injective (map.{w'} S.f (n + 1) U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ((exact₁ hS n U) x).1 hx
  obtain ⟨z, rfl⟩ := h y
  exact δ_map hS n U z
end GlobalTheory.SheafLES
