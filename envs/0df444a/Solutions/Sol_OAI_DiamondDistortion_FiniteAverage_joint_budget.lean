-- Prove2me | solution 1 for OAI.DiamondDistortion.FiniteAverage.joint_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:16:59.304788+00:00
-- url     : https://prove2.me/submissions/a691bc79-bdde-48fa-81fd-ece7a5ea1f0b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean:L127-L161
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.FiniteAverage.joint_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion

-- ---- from OAI.Analysis.DiamondDistortion.FiniteAverage ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma joint_budget (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hs : ∑ ω,w ω=1)
    (I : Ω → Type*) [∀ ω,Fintype (I ω)] (a b : ∀ ω,I ω→ℝ) {r R : ℝ}
    (he : ∀ ω,(∑ i,a ω i^2) ≤ R^2)
    (hc : (∑ ω,w ω*(∑ i,a ω i*b ω i)) = r^2) :
    (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) ≤ R^2-r^2 := by
  have hrow (ω : Ω) : (∑ i,(a ω i-b ω i)^2) + (r^2-∑ i,b ω i^2) =
      (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + r^2 := by
    have hex : (∑ i,(a ω i-b ω i)^2) =
        (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + (∑ i,b ω i^2) := by
      calc
        _ = ∑ i,(a ω i^2 - 2*(a ω i*b ω i) + b ω i^2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hex]
    ring
  have hid : (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) = (∑ ω,w ω*(∑ i,a ω i^2)) - r^2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, hrow]
    calc
      _ = (∑ ω,w ω*(∑ i,a ω i^2)) - 2*(∑ ω,w ω*(∑ i,a ω i*b ω i)) +
          r^2*(∑ ω,w ω) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by rw [hc,hs]; ring
  rw [hid]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ ω,w ω*R^2 := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (he ω) (hw ω)
    _ = R^2 := by rw [← Finset.sum_mul,hs,one_mul]

end FiniteAverage

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.FiniteAverage
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.FiniteAverage.joint_budget := @_root_.OAI.DiamondDistortion.FiniteAverage.joint_budget
