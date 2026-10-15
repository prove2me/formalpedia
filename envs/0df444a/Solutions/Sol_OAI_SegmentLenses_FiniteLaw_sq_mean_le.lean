-- Prove2me | solution 1 for OAI.SegmentLenses.FiniteLaw.sq_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:28:30.906887+00:00
-- url     : https://prove2.me/submissions/6183d585-ccef-4b80-831a-0bf163081c7c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/FiniteLaws.lean:L79-L91
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.FiniteLaw.sq_mean_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws

-- ---- from OAI.Analysis.SegmentLenses.FiniteLaws ----
namespace OAI

/-!
# Finite probability laws and joint square-root budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem mean_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.mean f := Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω)

theorem sq_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.mean f ^ 2 ≤ μ.mean (fun ω => f ω ^ 2) := by
  have h := μ.mean_nonneg (fun ω => sq_nonneg (f ω - μ.mean f))
  have he : μ.mean (fun ω => (f ω - μ.mean f) ^ 2) =
      μ.mean (fun ω => f ω ^ 2) - μ.mean f ^ 2 := by
    have hfun : (fun ω => (f ω - μ.mean f) ^ 2) =
        fun ω => f ω ^ 2 - (2 * μ.mean f) * f ω + μ.mean f ^ 2 := by
      funext ω
      ring
    rw [hfun, mean_add, mean_sub, mean_mul, mean_const]
    ring
  rw [he] at h
  linarith

end FiniteLaw

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses OAI.SegmentLenses.FiniteLaw
open scoped BigOperators
open Finset
variable {Ω : Type*} [Fintype Ω]

theorem solution (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.mean f ^ 2 ≤ μ.mean (fun ω => f ω ^ 2) := by
  first
    | exact OAI.SegmentLenses.FiniteLaw.sq_mean_le μ f
    | exact OAI.SegmentLenses.FiniteLaw.sq_mean_le
    | (apply OAI.SegmentLenses.FiniteLaw.sq_mean_le <;> assumption)
    | (intros; apply OAI.SegmentLenses.FiniteLaw.sq_mean_le <;> assumption)
