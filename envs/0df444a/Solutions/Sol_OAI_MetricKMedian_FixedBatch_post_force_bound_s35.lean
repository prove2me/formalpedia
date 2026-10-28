-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.post_force_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:04:35.045057+00:00
-- url     : https://prove2.me/submissions/c92fd86e-9edc-4f59-9e90-476a17d27fd0

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_m_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_PhysicalPotential_time_increase_le_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

theorem coefficient_ge_one {x y : ℝ} (hy : 0 ≤ y) : 1 ≤ coefficient x y := by
  rw [coefficient_eq]
  have hm := m_nonneg_s35 x
  have hB : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s35 x)
  nlinarith only [hm, mul_nonneg hB hy]

end MetricKMedian.Analytic
end
end

end OAI
end

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

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

theorem cost_mono {g : ℝ} {d : I → ℝ} {S T : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ T, 0 ≤ d i) (hST : S ⊆ T) : cost g d S ≤ cost g d T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi _ => mul_nonneg hg (hd i hi))

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s35 x)

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

omit [Fintype E] in
 theorem nextCap_le_force (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) :
    nextCap D d bForce A ≤ bForce := (fold_min_le _).mpr (Or.inl le_rfl)

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_PotentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic Finset

variable {I : Type*}

theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half_s35 hx
  unfold B
  linarith only [h]

theorem m_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m x ≤ 1 := by
  have hA := A_le_two hx1
  have hBx := mul_nonneg (B_nonneg x) hx0
  unfold m
  unfold B at hBx
  linarith only [hA, hBx]

theorem coefficient_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1 ≤ coefficient x y ∧ coefficient x y ≤ 3 := by
  refine ⟨coefficient_ge_one hy0, ?_⟩
  rw [coefficient_eq]
  have hm := m_le_one hx0 hx1
  have hB := (mul_le_of_le_one_left hy0 (B_le_one hx0)).trans hy1
  linarith only [hm, hB]

end MetricKMedian.PhysicalPotential
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
-- module Solutions.OAIQ035_KM.KMedian_Process_ForceBatchBound
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

 theorem nextAliveAt_subset (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAliveAt D a d S A ⊆ S := by
  unfold nextAliveAt
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

 theorem nextAliveAt_zero (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAliveAt D a d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAliveAt, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

 theorem changeAt_probability_le (D : Actions I E) (μ : FiniteLaw (Finset E))
    (a : ℝ) (d : I → ℝ) (S : Finset I) {Q : ℝ}
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ Q) :
    μ.prob (fun A => nextAliveAt D a d S A ≠ S) ≤ ((relevant D S).card:ℝ)*Q := by
  have hm := μ.prob_mono (E := fun A => nextAliveAt D a d S A ≠ S)
    (F := fun A => ∃ e ∈ relevant D S, e ∈ A) (by
      intro A ha
      by_contra hn
      have hi : A ∩ relevant D S=∅ := eq_empty_iff_forall_notMem.mpr (by
        intro e he
        exact hn ⟨e, (mem_inter.mp he).2, (mem_inter.mp he).1⟩)
      exact ha (nextAliveAt_zero D a d S A hi))
  have hu := μ.prob_exists_le_sum (relevant D S) (fun e A => e ∈ A)
  have hs := sum_le_sum hmarg
  simp only [sum_const, nsmul_eq_mul] at hs
  exact hm.trans (hu.trans hs)

theorem post_force_bound_s35_oai (D : Actions I E) (μ : FiniteLaw (Finset E))
    {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
    (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
    (hcap : ∀ A, 0 ≤ nextCap D d b A)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      (8*((relevant D S).card:ℝ)+8)*h*V := by
  let K : ℝ := (3+1/g)*V
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpot0 : 0 ≤ potential x g d S b := by
    rw [potential, ← coefficient_eq]
    have ha := coefficient_ge_one (x := x) (mass_nonneg hg0.le S)
    exact add_nonneg (mul_nonneg (by linarith only [ha]) (cost_nonneg hg0.le hd0))
      (mul_nonneg (sub_nonneg.mpr hy) hb0)
  have hf : μ.expect (fun A => potential x g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      K*μ.prob (fun A => nextAliveAt D a d S A ≠ S) := by
    rw [FiniteLaw.prob, ← μ.expect_mul]
    apply μ.expect_mono
    intro A
    have hsub := nextAliveAt_subset D a d S A
    have hnewV := (cost_mono hg0.le hd0 hsub).trans hVS
    have hy' := (mass_mono hg0.le hsub).trans hy
    by_cases heq : nextAliveAt D a d S A=S
    · simp only [heq, ne_eq, not_true_eq_false, ite_false, mul_zero]
      have he := mul_le_mul_of_nonneg_left (nextCap_le_force D d b A) (sub_nonneg.mpr hy)
      unfold potential
      linarith only [he]
    · simp only [heq, ne_eq, not_false_eq_true, ite_true, mul_one]
      have hcoeff := (coefficient_bounds hx0 hx1 (mass_nonneg hg0.le _) hy').2
      have hprod := mul_le_mul hcoeff hnewV
        (cost_nonneg hg0.le (fun i hi => hd0 i (hsub hi))) (by norm_num : (0:ℝ) ≤ 3)
      have hcapV := (nextCap_le_force D d b A).trans hbV
      have hcap' := mul_le_mul_of_nonneg_right
        (show 1-mass g (nextAliveAt D a d S A) ≤ 1 by
          linarith only [mass_nonneg hg0.le (nextAliveAt D a d S A)]) (hcap A)
      rw [potential, ← coefficient_eq]
      dsimp only [K]
      simp only [div_eq_mul_inv, one_mul] at hcapV ⊢
      nlinarith only [hprod, hcapV, hcap', hpot0]
  have hp := changeAt_probability_le D μ a d S hmarg
  have hf' := hf.trans (mul_le_mul_of_nonneg_left hp hK)
  have ht : μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d (nextAliveAt D a d S A) (nextCap D d b A)) ≤
      (2*h+6*h^2)*V := by
    apply (μ.expect_mono (fun A => ?_)).trans_eq (μ.expect_const _)
    have hsub := nextAliveAt_subset D a d S A
    exact (time_increase_le_s35 hx0 hx1 hg0.le hh0 (fun i hi => hd0 i (hsub hi))
      ((mass_mono hg0.le hsub).trans hy)).trans
      (mul_le_mul_of_nonneg_left ((cost_mono hg0.le hd0 hsub).trans hVS) (by positivity))
  have he : (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b)=
      (fun A => (potential x g d (nextAliveAt D a d S A) (nextCap D d b A)-potential x g d S b)+
        (potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A) (nextCap D d b A)-
          potential x g d (nextAliveAt D a d S A) (nextCap D d b A))) := by
    funext A; ring
  rw [he, μ.expect_add]
  apply (add_le_add hf' ht).trans
  have hk : K*(((relevant D S).card:ℝ)*(2*h*g)) ≤
      8*((relevant D S).card:ℝ)*h*V := by
    have hid : K*(((relevant D S).card:ℝ)*(2*h*g))=
        (6*g+2)*(((relevant D S).card:ℝ)*h*V) := by
      dsimp only [K]
      field_simp
      ring
    rw [hid]
    have hg' : 6*g+2 ≤ 8 := by linarith only [hg1]
    calc
      _ ≤ 8*(((relevant D S).card:ℝ)*h*V) := mul_le_mul_of_nonneg_right hg' (by positivity)
      _ = _ := by ring
  have ht' : (2*h+6*h^2)*V ≤ 8*h*V := by
    apply mul_le_mul_of_nonneg_right _ hV
    nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh1)]
  nlinarith only [hk, ht']

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedian.FixedBatch.post_force_bound_s35_oai.{u_1, u_2} := @OAI.MetricKMedian.FixedBatch.post_force_bound_s35_oai.{u_1, u_2}
