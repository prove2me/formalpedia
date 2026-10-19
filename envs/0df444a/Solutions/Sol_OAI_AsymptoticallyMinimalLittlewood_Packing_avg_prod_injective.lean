-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:59:57.006362+00:00
-- url     : https://prove2.me/submissions/f439e4a7-d263-4760-bf3a-5b86175af549

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Averages.lean:L74-L101
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages

-- ---- from OAI.Analysis.Littlewood.Averages ----
namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

lemma avg_const (c : ℝ) : avg (fun _ : Ω ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]
lemma avg_prod_coordinate {K : Type uK} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype A] [Nonempty A]
    (f : K → A → ℝ) : avg (fun ω : K → A ↦ ∏ k, f k (ω k)) = ∏ k, avg (f k) := by
  dsimp [avg]
  rw [← Fintype.prod_sum,Finset.prod_div_distrib]
  simp

lemma avg_prod_injective {K : Type uK} {J : Type uJ} {A : Type uA} [Fintype K] [DecidableEq K] [Fintype J] [Fintype A]
    [Nonempty A] (κ : J → K) (hκ : Function.Injective κ) (f : J → A → ℝ) :
    avg (fun ω : K → A ↦ ∏ j, f j (ω (κ j))) = ∏ j, avg (f j) := by
  classical
  let g : K → A → ℝ := fun k a ↦ if h : ∃ j, κ j=k then f h.choose a else 1
  have hg (j : J) (a : A) : g (κ j) a=f j a := by
    dsimp [g]
    split_ifs with h
    · congr 1
      exact hκ h.choose_spec
    · exact (h ⟨j,rfl⟩).elim
  have hprod (ω : K → A) : (∏ k, g k (ω k)) = ∏ j, f j (ω (κ j)) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j, κ j=k from hk]
    · intro j
      exact (hg j (ω (κ j))).symm
  have hprod' : (∏ k, avg (g k)) = ∏ j, avg (f j) := by
    symm
    apply Fintype.prod_of_injective κ hκ
    · intro k hk
      simp [g,show ¬∃j,κ j=k from hk,avg_const]
    · intro j
      exact congrArg avg (funext (fun a ↦ (hg j a).symm))
  rw [← hprod']
  convert avg_prod_coordinate g using 1
  exact congrArg avg (funext (fun ω ↦ (hprod ω).symm))

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uK,uA,uJ} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective.{uK,uA,uJ} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.avg_prod_injective.{uK,uA,uJ}
