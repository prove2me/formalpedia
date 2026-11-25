-- Prove2me | solution 1 for GlobalTheory.PadicVal.tendsto_of_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:03:19.213067+00:00
-- url     : https://prove2.me/submissions/ef41a482-5935-422a-a330-8f3d14973968

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.PadicVal
theorem _root_.solution {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    {v : AddValuation (PadicAlgCl p) (WithTop ℚ)}
    (hv : ∀ x, x ≠ 0 → ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖)
    {I : Type} {x : I → PadicAlgCl p} (hx : ∀ q : ℚ, {i | v (x i) < (q : WithTop ℚ)}.Finite) :
    Filter.Tendsto x Filter.cofinite (nhds 0) := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  rw [tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_rat_gt (Real.log ε / Real.log ‖π‖)
  rw [Filter.eventually_cofinite]
  refine (hx q).subset ?_
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hlt
  apply hi
  rw [dist_zero_right, norm_norm]
  by_cases hxi : x i = 0
  · rw [hxi, norm_zero]
    exact hε
  obtain ⟨q', hv', hlog⟩ := hv (x i) hxi
  have hqq : q ≤ q' := by
    rw [hv', not_lt, WithTop.coe_le_coe] at hlt
    exact hlt
  have h2 : (q' : ℝ) * Real.log ‖π‖ ≤ q * Real.log ‖π‖ :=
    mul_le_mul_of_nonpos_right (by exact_mod_cast hqq) hL.le
  have h3 : (q : ℝ) * Real.log ‖π‖ < Real.log ε := (div_lt_iff_of_neg hL).1 hq
  have h4 : Real.log ‖x i‖ < Real.log ε := by linarith
  exact (Real.log_lt_log_iff (norm_pos_iff.2 hxi) hε).1 h4
end GlobalTheory.PadicVal
