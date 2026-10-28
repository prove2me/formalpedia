-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:21:20.823973+00:00
-- url     : https://prove2.me/submissions/c40e56f8-770f-4b99-aaa9-5eef447550ac

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_PhysicalPotential_expected_time_advance_s35
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_le_s35
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_expected_frozen_bound_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

omit [Fintype E] in
 theorem physical_subset (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A ⊆ S := sdiff_subset

 theorem nextAlive_subset (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAlive D x g d S A ⊆ S := by
  unfold nextAlive
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

theorem physical_restrict (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A = physical D S (A ∩ relevant D S) := by
  ext i
  simp only [physical, mem_sdiff, mem_biUnion]
  constructor
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    exact hnot ⟨e, (mem_inter.mp he).1, hie⟩
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    have hrel : e ∈ relevant D S := (mem_relevant D S e).mpr (Or.inr ⟨i, mem_inter.mpr ⟨hi, hie⟩⟩)
    exact hnot ⟨e, mem_inter.mpr ⟨he, hrel⟩, hie⟩

 theorem nextAlive_zero (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAlive D x g d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAlive, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_exists_le_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I)
    (E : I → Ω → Prop) [∀ i, DecidablePred (E i)] :
    μ.prob (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  unfold prob
  rw [← expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i ∈ s, E i ω
  · obtain ⟨i, hi, hei⟩ := h
    simp only [ite_eq_left (show ∃ i ∈ s, E i ω from ⟨i, hi, hei⟩)]
    have hsingle := Finset.single_le_sum (f := fun j => if E j ω then (1:ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi
    simpa only [ite_eq_left hei] using hsingle
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhaseBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
 theorem change_probability_le (D : Actions I E) (μ : FiniteLaw (Finset E))
    (x g : ℝ) (d : I → ℝ) (S : Finset I) {Q : ℝ}
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ Q) :
    μ.prob (fun A => nextAlive D x g d S A ≠ S) ≤ ((relevant D S).card:ℝ)*Q := by
  have hm := μ.prob_mono (E := fun A => nextAlive D x g d S A ≠ S)
    (F := fun A => ∃ e ∈ relevant D S, e ∈ A) (by
      intro A ha
      by_contra hn
      have hi : A ∩ relevant D S=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        exact hn ⟨e, (mem_inter.mp he).2, (mem_inter.mp he).1⟩)
      exact ha (nextAlive_zero D x g d S A hi))
  have hu := μ.prob_exists_le_sum (relevant D S) (fun e A => e ∈ A)
  have hs := sum_le_sum hmarg
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hm.trans (hu.trans hs)
end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedFull
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I E : Type} [DecidableEq I] [DecidableEq E] [Fintype E] {n : ℕ}

theorem expected_step_bound_s35_oai (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1) {h g φ : ℝ} {N : ℕ}
    (hprob : (p:ℝ)=2*h*g) (hh : 0 ≤ h) (hg : 0 ≤ g)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*(p:ℝ))
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
        (nextCap D d bForce A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+g*(∑ e ∈ relevant D S, charge D x g b d S e))+
      R*(16*((relevant D S).card:ℝ)*(N:ℝ)*h^2*g^2+
        8*((relevant D S).card:ℝ)*φ*h*g+
        256*((univ : Finset (relevant D S)).offDiag.card:ℝ)*h^2*g^2+
        6*h^2+8*((relevant D S).card:ℝ)*h^2*g) := by
  let μ := (SparseEnumeratedBatch.law enum Z C p q hp hq0).real
  have hpQ : (p:ℝ) ≤ 4*h*g := by rw [hprob]; nlinarith only [mul_nonneg hh hg]
  have hqQ : ∀ e, (q e:ℝ) ≤ 4*h*g := by
    intro e
    have he := mul_le_mul_of_nonneg_right hφ1 (show 0 ≤ 2*h*g by positivity)
    have heq := (hq e).2
    rw [hprob] at heq
    linarith only [he, heq]
  have hf := expected_frozen_bound_s35 enum D Z C p q hp hq0
    hφ0 (show 0 ≤ 4*h*g by positivity) hpQ hqQ hq hC hself d S hx0 hx1 hg hR
    hd0 hdR hy hb0 hbR hbf0 hbf hheavy
  have ht := expected_time_advance_s35 μ (nextAlive D x g d S) (nextCap D d bForce)
    d S hx0 hx1 hg hR hh (fun i _ => hd0 i) hdR hy (nextAlive_subset D x g d S)
  have hm : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ (4*h*g)/2 := by
    intro e _
    exact SparseEnumeratedBatch.marginal_le_s35 enum Z C p q hp hq0 hpQ hqQ e
  have hc := change_probability_le D μ x g d S hm
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*h*R by positivity)
  rw [hprob] at hf
  change μ.expect _ ≤ _ at hf ⊢
  have he : (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
      (nextCap D d bForce A)-potential x g d S b)=
      (fun A => (potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-
        potential x g d S b)+
        (potential (x*Real.exp (-h)) g d (nextAlive D x g d S A) (nextCap D d bForce A)-
        potential x g d (nextAlive D x g d S A) (nextCap D d bForce A))) := by
    funext A
    ring
  rw [he, μ.expect_add]
  calc
    _ ≤ ((2*h*g)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(2*h*g)^2/2+φ*(2*h*g)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*(4*h*g)^2+
        (h*timeRate x (mass g S)*PhysicalPotential.cost g d S+6*h^2*R+
          4*h*R*(((relevant D S).card:ℝ)*((4*h*g)/2))) := by
      exact add_le_add hf (ht.trans (add_le_add_right hmul _))
    _ = _ := by ring

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35_oai := @OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s35_oai
