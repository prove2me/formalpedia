-- Prove2me | solution 1 for MasulloRepair.compact_window_space_complete_and_representation
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T02:12:58.304924+00:00
-- url     : https://prove2.me/submissions/ff80ce4e-9292-4dad-852e-737e03ca5080

import Definitions.Def_MasulloRepair_WindowL2

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal

theorem solution (μ : Measure ℝ) :
    CompleteSpace (windowSpace μ) ∧
    TopologicalSpace.MetrizableSpace (windowSpace μ) ∧
    LocallyConvexSpace ℝ (windowSpace μ) ∧
    (∀ u : windowSpace μ, ∃ f : ℝ → ℂ, MemLp f 2 μ ∧
      ∀ n : ℕ, MemLp f 2 (windowMeasure μ n) ∧
        (u.val n : ℝ → ℂ) =ᵐ[windowMeasure μ n] f) ∧
    (∀ f : ℝ → ℂ, (∀ n : ℕ, MemLp f 2 (windowMeasure μ n)) →
      ∃! u : windowSpace μ, ∀ n : ℕ, (u.val n : ℝ → ℂ) =ᵐ[windowMeasure μ n] f) := by
  have hc : IsClosed (windowSpace μ : Set (∀ n : ℕ, Lp ℂ 2 (windowMeasure μ n))) := by
    change IsClosed {u : ∀ n : ℕ, Lp ℂ 2 (windowMeasure μ n) |
      ∀ n, windowToBase μ n (u n) = windowToBase μ 0 (u 0)}
    simp only [ofPred_forall]
    exact isClosed_iInter fun n =>
      isClosed_eq ((windowToBase μ n).continuous.comp (continuous_apply n))
        ((windowToBase μ 0).continuous.comp (continuous_apply 0))
  have hm : TopologicalSpace.MetrizableSpace (windowSpace μ) := by
    let : (uniformity (windowSpace μ)).IsCountablyGenerated := by
      rw [uniformity_subtype]
      infer_instance
    exact UniformSpace.metrizableSpace
  have hl : LocallyConvexSpace ℝ (windowSpace μ) :=
    LocallyConvexSpace.induced ((windowSpace μ).subtype.restrictScalars ℝ)
  refine ⟨hc.isComplete.completeSpace_coe, hm, hl, ?_, ?_⟩
  · intro u
    let f : Lp ℂ 2 μ := windowToBase μ 0 (u.val 0)
    refine ⟨f, Lp.memLp f, ?_⟩
    intro n
    have hn := l2Include_coe (le_windowMeasure μ n) (u.val n)
    change (windowToBase μ n (u.val n) : ℝ → ℂ) =ᵐ[μ] (u.val n : ℝ → ℂ) at hn
    rw [u.property n] at hn
    have heq : (u.val n : ℝ → ℂ) =ᵐ[windowMeasure μ n] (f : ℝ → ℂ) :=
      (withDensity_absolutelyContinuous μ (windowWeight n)).ae_eq hn.symm
    exact ⟨(Lp.memLp (u.val n)).ae_eq heq, heq⟩
  · intro f hf
    let u : ∀ n : ℕ, Lp ℂ 2 (windowMeasure μ n) := fun n => (hf n).toLp f
    have heq (n : ℕ) : (windowToBase μ n (u n) : ℝ → ℂ) =ᵐ[μ] f := by
      exact (l2Include_coe (le_windowMeasure μ n) (u n)).trans
        ((Measure.absolutelyContinuous_of_le (le_windowMeasure μ n)).ae_eq (hf n).coeFn_toLp)
    have hu : u ∈ windowSpace μ := by
      intro n
      exact Lp.ext ((heq n).trans (heq 0).symm)
    refine ⟨⟨u, hu⟩, (fun n => (hf n).coeFn_toLp), ?_⟩
    intro v hv
    apply Subtype.ext
    funext n
    exact Lp.ext ((hv n).trans (hf n).coeFn_toLp.symm)

#print axioms solution
