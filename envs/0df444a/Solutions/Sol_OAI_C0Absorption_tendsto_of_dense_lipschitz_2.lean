-- Prove2me | solution 2 for OAI.C0Absorption.tendsto_of_dense_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:39:10.006524+00:00
-- url     : https://prove2.me/submissions/c66b313e-795e-4eec-bf07-62145ca05ce2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Lists.lean:L181-L199
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.tendsto_of_dense_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

-- ---- from OAI.Analysis.C0Absorption.Lists ----
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section CompletedLists

open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)

end CompletedLists

section InterpolationAndDenseLimits

theorem tendsto_of_dense_lipschitz {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : A → X) (hd : DenseRange d) (f : ℕ → X → Y) (g : X → Y) (K : ℝ≥0)
    (hf : ∀ n, LipschitzWith K (f n)) (hg : LipschitzWith K g)
    (h : ∀ a, Filter.Tendsto (fun n => f n (d a)) Filter.atTop (nhds (g (d a))))
    (x : X) : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hK : 0 < 3 * ((K : ℝ) + 1) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x (div_pos hε hK)
  have hδ : (K : ℝ) * dist x (d a) < ε / 3 := by
    have hr := (lt_div_iff₀ hK).mp ha
    have hn := dist_nonneg (x := x) (y := d a)
    nlinarith
  filter_upwards [Metric.tendsto_nhds.mp (h a) (ε / 3) (by positivity)] with n hn
  have h₁ := (hf n).dist_le_mul x (d a)
  have h₂ := hg.dist_le_mul (d a) x
  rw [dist_comm (d a) x] at h₂
  have ht := dist_triangle4 (f n x) (f n (d a)) (g (d a)) (g x)
  linarith

end InterpolationAndDenseLimits

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution : type_of% @_root_.OAI.C0Absorption.tendsto_of_dense_lipschitz := @_root_.OAI.C0Absorption.tendsto_of_dense_lipschitz
