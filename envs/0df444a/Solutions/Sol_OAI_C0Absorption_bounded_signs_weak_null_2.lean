-- Prove2me | solution 2 for OAI.C0Absorption.bounded_signs_weak_null
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:43:17.413866+00:00
-- url     : https://prove2.me/submissions/0d718dce-4100-4f71-adf0-8715aa731d52

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Pairings.lean:L239-L263
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.bounded_signs_weak_null. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings

-- ---- from OAI.Analysis.C0Absorption.Pairings ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedPairings

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end CompletedPairings

section FurtherDetectors

theorem bounded_signs_weak_null {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (u : X →L[ℝ] ℝ) : Filter.Tendsto (fun i => u (m i)) Filter.atTop (nhds 0) := by
  classical
  have hb (n : ℕ) : ∑ i : Fin n, |u (m i)| ≤ ‖u‖ * M := by
    let ε : Fin n → Bool := fun i => if 0 ≤ u (m i) then true else false
    have hε (i : Fin n) : realSign (ε i) * u (m i) = |u (m i)| := by
      dsimp [ε]
      split
      · rw [realSign_true, one_mul, abs_of_nonneg ‹_›]
      · rw [realSign_false, neg_one_mul, abs_of_neg (lt_of_not_ge ‹_›)]
    have heq : u (∑ i : Fin n, realSign (ε i) • m i) = ∑ i : Fin n, |u (m i)| := by
      simp only [map_sum, map_smul, smul_eq_mul, hε]
    calc
      ∑ i : Fin n, |u (m i)| = ‖u (∑ i : Fin n, realSign (ε i) • m i)‖ := by
        rw [heq, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      _ ≤ ‖u‖ * ‖∑ i : Fin n, realSign (ε i) • m i‖ := u.le_opNorm _
      _ ≤ ‖u‖ * M := mul_le_mul_of_nonneg_left (hsum n ε) (norm_nonneg _)
  have hs : Summable (fun i => |u (m i)|) :=
    summable_of_sum_range_le (c := ‖u‖ * M) (fun i => abs_nonneg _) (fun n => by
      rw [Finset.sum_range]
      exact hb n)
  have hs' : Summable (fun i => u (m i)) := summable_norm_iff.mp (by simpa using hs)
  exact hs'.tendsto_atTop_zero

variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end FurtherDetectors

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution : type_of% @_root_.OAI.C0Absorption.bounded_signs_weak_null := @_root_.OAI.C0Absorption.bounded_signs_weak_null
