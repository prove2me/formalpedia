-- Prove2me | solution 1 for Kyprianou.Ch02.realMarkSimpleL2ApproxV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:45:50.77025+00:00
-- url     : https://prove2.me/submissions/2877b810-d40a-49c6-94de-c2c179d6cd62

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (B : Set ℝ)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∃ (f : ℕ → SimpleFunc ℝ ℝ),
      (∀ x : ℝ, Tendsto (fun n => (f n) x) Filter.atTop (nhds x)) ∧
      Tendsto (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
        Filter.atTop (nhds 0) := by
  classical
  let f : ℕ → SimpleFunc ℝ ℝ := fun n =>
    SimpleFunc.approxOn (fun x : ℝ => x) measurable_id Set.univ 0 (Set.mem_univ 0) n
  refine ⟨f, ?_, ?_⟩
  · intro x
    exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ (0 : ℝ))
      (by simp : (fun y : ℝ => y) x ∈ closure (Set.univ : Set ℝ))
  · have hmem : eLpNorm (fun x : ℝ => x - 0) 2 (ν.restrict B) < ⊤ := by
      simpa using hsecond.2
    have hconv := SimpleFunc.tendsto_approxOn_Lp_eLpNorm
      (f := fun x : ℝ => x) (p := (2 : ℝ≥0∞))
      measurable_id (Set.mem_univ (0 : ℝ))
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Filter.Eventually.of_forall (fun x : ℝ => by simp))
      hmem
    simpa only [f, Pi.sub_def] using hconv
