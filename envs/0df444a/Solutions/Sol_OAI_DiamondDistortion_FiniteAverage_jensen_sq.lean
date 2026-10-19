-- Prove2me | solution 1 for OAI.DiamondDistortion.FiniteAverage.jensen_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:13:12.29107+00:00
-- url     : https://prove2.me/submissions/411b0f67-d6b3-4c63-a36a-524b82bcc336

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean:L16-L33
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.FiniteAverage.jensen_sq. The node keeps its source
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

lemma jensen_sq (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1) :
    (∑ ω, w ω * f ω) ^ 2 ≤ ∑ ω, w ω * f ω ^ 2 := by
  let m := ∑ ω, w ω * f ω
  have hpos : 0 ≤ ∑ ω, w ω * (f ω - m) ^ 2 := by
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (sq_nonneg _))
  have he : (∑ ω, w ω * (f ω - m) ^ 2) =
      (∑ ω, w ω * f ω ^ 2) - 2*m*(∑ ω, w ω*f ω) + m^2*(∑ ω,w ω) := by
    calc
      _ = ∑ ω, (w ω * f ω ^ 2 - (2*m)*(w ω*f ω) + m^2*w ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, hs] at hpos
  dsimp [m] at hpos
  nlinarith

end FiniteAverage

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.FiniteAverage
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.FiniteAverage.jensen_sq := @_root_.OAI.DiamondDistortion.FiniteAverage.jensen_sq
