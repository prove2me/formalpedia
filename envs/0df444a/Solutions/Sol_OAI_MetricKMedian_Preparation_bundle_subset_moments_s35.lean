-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.bundle_subset_moments_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:56:23.020989+00:00
-- url     : https://prove2.me/submissions/d71096ca-154a-4a58-81b1-8bdd0fcff091

import Mathlib
import Definitions.Def_OAIQ035K004
import Theorems.Thm_OAI_MetricKMedian_FiniteLaw_restricted_moments_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationSubsetNoise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [Fintype Ω] in

theorem bundle_subset_moments_s35_oai (μ : FiniteLaw Ξ) (Y : Ξ → T × I → ℝ)
    (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ) (F : Finset I) (g : ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (hv : ∀ a, μ.variance (fun ξ => Y ξ a) ≤ g*(if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0))
    (hc : ∀ a b, a ≠ b → μ.expect (fun ξ => Y ξ a*Y ξ b) ≤
      (if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' b.1*y b.2/p b.1 else 0)) :
    μ.expect (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i))=
      (∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) ∧
    μ.variance (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i)) ≤
      g*(∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) := by
  classical
  let A : Finset (T × I) := univ.filter (fun a => a.2 ∈ F)
  let m : T × I → ℝ := fun a => if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0
  have he := μ.restricted_moments_s35 Y m A (fun a => hm a.1 a.2) hv hc
  have hs : ∀ ξ, (∑ a ∈ A, Y ξ a)=∑ t, ∑ i ∈ F, Y ξ (t,i) := by
    intro ξ
    simp only [A,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter]
  have hs' : (∑ a ∈ A, m a)=∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t := by
    simp only [A,m,sum_filter,Fintype.sum_prod_type,sum_ite_mem,univ_inter,← sum_div,← mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  simpa only [hs,hs'] using he

end MetricKMedian.Preparation
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.bundle_subset_moments_s35_oai := @OAI.MetricKMedian.Preparation.bundle_subset_moments_s35_oai
