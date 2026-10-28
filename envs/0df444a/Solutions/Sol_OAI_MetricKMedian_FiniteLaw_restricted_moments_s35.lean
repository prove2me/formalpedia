-- Prove2me | solution 1 for OAI.MetricKMedian.FiniteLaw.restricted_moments_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:54:32.670037+00:00
-- url     : https://prove2.me/submissions/f84ec60b-7d11-4dd7-99d0-e5f7bf868925

import Mathlib
import Definitions.Def_OAIQ035K017

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FilteredMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem restricted_moments_s35_oai (μ : FiniteLaw Ω) (Y : Ω → I → ℝ) (q : I → ℝ)
    (A : Finset I) {g : ℝ} (hm : ∀ i, μ.expect (fun ω => Y ω i)=q i)
    (hv : ∀ i, μ.variance (fun ω => Y ω i) ≤ g*q i)
    (hp : ∀ i j, i ≠ j → μ.expect (fun ω => Y ω i*Y ω j) ≤ q i*q j) :
    μ.expect (fun ω => ∑ i ∈ A, Y ω i)=(∑ i ∈ A, q i) ∧
    μ.variance (fun ω => ∑ i ∈ A, Y ω i) ≤ g*(∑ i ∈ A, q i) := by
  let X := fun i ω => if i ∈ A then Y ω i else 0
  let m := fun i => if i ∈ A then q i else 0
  have hm' : ∀ i, μ.expect (X i)=m i := by
    intro i
    by_cases hi : i ∈ A
    · simpa only [X,m,ite_eq_left hi] using hm i
    · simp only [X,m,ite_eq_right hi,expect_const]
  have hv' : ∀ i, μ.variance (X i) ≤ g*m i := by
    intro i
    by_cases hi : i ∈ A
    · simpa only [X,m,ite_eq_left hi] using hv i
    · simp only [X,m,ite_eq_right hi,mul_zero,variance_eq,expect_const,zero_pow (by decide : 2 ≠ 0),sub_zero,le_refl]
  have hp' : ∀ i j, i ≠ j → μ.expect (fun ω => X i ω*X j ω) ≤ m i*m j := by
    intro i j hij
    by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
    · simpa only [X,m,ite_eq_left hi,ite_eq_left hj] using hp i j hij
    all_goals simp only [X,m,hi,hj,ite_true,ite_false,mul_zero,zero_mul,expect_const,le_refl]
  have he := μ.variance_sum_le X m (fun i => g*m i) hm' hv' hp'
  simp only [X,m,sum_ite_mem,univ_inter,← mul_sum] at he
  refine ⟨?_,he⟩
  rw [expect_sum]
  simp only [hm]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedian.FiniteLaw.restricted_moments_s35_oai.{u_1, u_2} := @OAI.MetricKMedian.FiniteLaw.restricted_moments_s35_oai.{u_1, u_2}
