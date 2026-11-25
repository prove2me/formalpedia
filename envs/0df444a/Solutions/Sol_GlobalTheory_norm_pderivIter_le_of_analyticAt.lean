-- Prove2me | solution 1 for GlobalTheory.norm_pderivIter_le_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:43.449283+00:00
-- url     : https://prove2.me/submissions/520cc34c-8493-4676-b9eb-001189725fe4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_pderivIter_single
import Theorems.Thm_GlobalTheory_polyDerivLinear_apply
import Theorems.Thm_GlobalTheory_polyDeriv_zero
import Theorems.Thm_GlobalTheory_polyDeriv_monomial
import Theorems.Thm_GlobalTheory_polyDeriv_C
import Theorems.Thm_GlobalTheory_polyDeriv_one
import Theorems.Thm_GlobalTheory_polyDeriv_zero_fun
import Theorems.Thm_GlobalTheory_analyticAt_pderivIter
import Theorems.Thm_GlobalTheory_pderivIter_add_index
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


attribute [local simp] GlobalTheory.polyDerivLinear_apply
attribute [local simp] GlobalTheory.polyDeriv_zero
attribute [local simp] GlobalTheory.polyDeriv_monomial
attribute [local simp] GlobalTheory.polyDeriv_C
attribute [local simp] GlobalTheory.polyDeriv_one
attribute [local simp] GlobalTheory.polyDeriv_zero_fun
section
open Filter Topology
namespace GlobalTheory
section Def
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
end Def
section Analytic
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [CompleteSpace V]
end Analytic
section Polynomial
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
end Polynomial
section Cauchy
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
private theorem cauchy_estimate_iterated_pderiv {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ} (α : ι →₀ ℕ)
    (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) (s : Finset ι) :
    ∀ z : ι → ℂ, (∀ k ∈ s, z k = a k) → (∀ k ∉ s, ‖z k - a k‖ = r k) →
      ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F z‖
        ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
  induction s using Finset.induction_on with
  | empty => intro z _ hz; simpa using hM z fun k => hz k (by simp)
  | insert j s hj ih =>
    intro z hz hz'
    have hzj : z j = a j := hz j (Finset.mem_insert_self _ _)
    have hup : ∀ t : ℂ, ‖t - a j‖ ≤ r j → AnalyticAt ℂ F (Function.update z j t) := by
      intro t ht
      refine hF _ fun k => ?_
      by_cases hk : k = j
      · subst hk; simpa using ht
      · rw [Function.update_of_ne hk]
        by_cases hks : k ∈ s
        · simpa [hz k (Finset.mem_insert_of_mem hks)] using hr k
        · exact (hz' k (by simp [hk, hks])).le
    have hb : ∀ t : ℂ, ‖t - a j‖ = r j →
        ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F (Function.update z j t)‖
          ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
      intro t ht
      refine ih _ (fun k hk => ?_) (fun k hk => ?_)
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
        exact hz k (Finset.mem_insert_of_mem hk)
      · by_cases hkj : k = j
        · subst hkj; simpa using ht
        · rw [Function.update_of_ne hkj]
          exact hz' k (by simp [hkj, hk])
    have hza : AnalyticAt ℂ F z := by
      have := hup (z j) (by simpa [hzj] using hr j)
      rwa [Function.update_eq_self] at this
    rw [Finset.sum_insert hj, pderivIter_add_index hza, pderivIter_single, Finset.prod_insert hj,
      Finset.prod_insert hj, hzj]
    rcases (hr j).eq_or_lt with h0 | hpos
    · have hαj : α j = 0 := by
        by_contra hne
        exact (hα j hne).ne h0
      simpa [hαj] using hb (a j) (by simpa using h0)
    · have hd : DiffContOnCl ℂ (fun t => pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F
          (Function.update z j t)) (Metric.ball (a j) (r j)) := by
        refine DifferentiableOn.diffContOnCl fun t ht => ?_
        rw [closure_ball _ hpos.ne', mem_closedBall_iff_norm] at ht
        exact ((analyticAt_pderivIter (hup t ht) _).differentiableAt.comp t
          (hasDerivAt_update z j t).differentiableAt).differentiableWithinAt
      refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (α j) hpos hd
        fun t ht => hb t (mem_sphere_iff_norm.1 ht)).trans_eq ?_
      ring
end Cauchy
end GlobalTheory
end

set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k := by
  have h := cauchy_estimate_iterated_pderiv α hr hα hF hM Finset.univ a (fun _ _ => rfl) (by simp)
  rwa [Finsupp.univ_sum_single] at h
end GlobalTheory
