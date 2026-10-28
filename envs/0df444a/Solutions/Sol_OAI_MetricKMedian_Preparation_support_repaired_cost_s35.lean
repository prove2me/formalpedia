-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.support_repaired_cost_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:56:45.597981+00:00
-- url     : https://prove2.me/submissions/586d9648-136a-47f2-a1d0-1ac21a0c9f0f

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K004

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_AssignmentRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem repair_assignment (B : Finset I) (y a d : I → ℝ) {Q : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hay : ∀ i, a i ≤ y i) (hd : ∀ i, 0 ≤ d i)
    (_hQ : 0 ≤ Q) (hdQ : ∀ i ∈ B, d i ≤ Q) (hB : 1 ≤ ∑ i ∈ B, y i) :
    ∃ u : I → ℝ, (∀ i, 0 ≤ u i ∧ u i ≤ y i) ∧ (∑ i, u i)=1 ∧
      (∑ i, u i*d i) ≤ (∑ i, a i*d i)+Q*max (1-∑ i, a i) 0 := by
  let m := ∑ i, a i
  have hm0 : 0 ≤ m := sum_nonneg (fun i _ => ha i)
  by_cases hm1 : 1 ≤ m
  · have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
    refine ⟨fun i => a i/m,?_,?_,?_⟩
    · intro i
      refine ⟨div_nonneg (ha i) hm.le,?_⟩
      exact (div_le_self (ha i) hm1).trans (hay i)
    · rw [← sum_div]
      exact div_self hm.ne'
    · rw [max_eq_right (sub_nonpos.mpr hm1),mul_zero,add_zero]
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (div_le_self (ha i) hm1) (hd i)
  · have hm : m < 1 := lt_of_not_ge hm1
    let v := fun i => if i ∈ B then y i-a i else 0
    let z := ∑ i, v i
    have hv : ∀ i, 0 ≤ v i := by
      intro i
      dsimp only [v]
      split_ifs <;> [exact sub_nonneg.mpr (hay i); exact le_rfl]
    have hz : 1-m ≤ z := by
      have haB : ∑ i ∈ B, a i ≤ m := sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun i _ _ => ha i)
      have hzid : z=(∑ i ∈ B, y i)-(∑ i ∈ B, a i) := by simp [z,v,sum_sub_distrib]
      rw [hzid]
      linarith only [haB,hB]
    have hz0 : 0 < z := lt_of_lt_of_le (sub_pos.mpr hm) hz
    let t := (1-m)/z
    have ht0 : 0 ≤ t := div_nonneg (sub_pos.mpr hm).le hz0.le
    have ht1 : t ≤ 1 := (div_le_one hz0).mpr hz
    have htz : t*z=1-m := div_mul_cancel₀ _ hz0.ne'
    refine ⟨fun i => a i+t*v i,?_,?_,?_⟩
    · intro i
      refine ⟨add_nonneg (ha i) (mul_nonneg ht0 (hv i)),?_⟩
      have hh := mul_le_of_le_one_left (hv i) ht1
      dsimp only [v] at hh ⊢
      split_ifs with hi
      · simp only [ite_eq_left hi] at hh
        linarith only [hh]
      · simpa using hay i
    · rw [sum_add_distrib,← mul_sum]
      change m+t*z=1
      linarith only [htz]
    · simp only [add_mul,sum_add_distrib]
      apply add_le_add le_rfl
      rw [max_eq_left (sub_pos.mpr hm).le]
      calc
        (∑ i, t*v i*d i) ≤ ∑ i, t*v i*Q := by
          apply sum_le_sum
          intro i _
          by_cases hi : i ∈ B
          · exact mul_le_mul_of_nonneg_left (hdQ i hi) (mul_nonneg ht0 (hv i))
          · simp [v,hi]
        _ = Q*(1-m) := by rw [← sum_mul,← mul_sum]; change t*z*Q=Q*(1-m); rw [htz]; ring

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupportRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {Ω I : Type} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem support_repaired_cost_s35_oai (μ : FiniteLaw Ω) (ball : Finset I)
    (y a : Ω → I → ℝ) (d : I → ℝ) {R H V : ℝ}
    (hR : 0 ≤ R) (ha : ∀ ω, 0 < μ.weight ω → ∀ i, 0 ≤ a ω i)
    (hay : ∀ ω, 0 < μ.weight ω → ∀ i, a ω i ≤ y ω i)
    (hd : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ ball, d i ≤ R)
    (hball : ∀ ω, 0 < μ.weight ω → 1 ≤ ∑ i ∈ ball, y ω i)
    (hcost : μ.expect (fun ω => ∑ i, a ω i*d i) ≤ V)
    (hshort : μ.expect (fun ω => max (1-∑ i, a ω i) 0) ≤ H) :
    ∃ r : Ω → I → ℝ,
      (∀ ω, 0 < μ.weight ω → (∀ i, 0 ≤ r ω i ∧ r ω i ≤ y ω i) ∧ (∑ i, r ω i)=1) ∧
      μ.expect (fun ω => ∑ i, r ω i*d i) ≤ V+R*H := by
  classical
  choose r hr using fun ω : {ω // 0 < μ.weight ω} => repair_assignment ball
    (y ω.1) (a ω.1) d (ha ω.1 ω.2) (hay ω.1 ω.2) hd hR hdR (hball ω.1 ω.2)
  let r' := fun ω => if h : 0 < μ.weight ω then r ⟨ω,h⟩ else fun _ => 0
  refine ⟨r',?_,?_⟩
  · intro ω hω
    simp only [r',dite_eq_left hω]
    exact ⟨(hr ⟨ω,hω⟩).1,(hr ⟨ω,hω⟩).2.1⟩
  · have he : μ.expect (fun ω => ∑ i, r' ω i*d i) ≤
        μ.expect (fun ω => (∑ i, a ω i*d i)+R*max (1-∑ i, a ω i) 0) :=
      μ.expect_mono_support (fun ω (hω : 0 < μ.weight ω) => by
        simpa only [r',dite_eq_left hω] using (hr ⟨ω,hω⟩).2.2)
    rw [FiniteLaw.expect_add,FiniteLaw.expect_mul] at he
    exact he.trans (add_le_add hcost (mul_le_mul_of_nonneg_left hshort hR))

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.support_repaired_cost_s35_oai := @OAI.MetricKMedian.Preparation.support_repaired_cost_s35_oai
