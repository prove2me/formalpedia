-- Prove2me | solution 1 for OAI.SharpPlanar.analytic_taylor_error_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:02.209165+00:00
-- url     : https://prove2.me/submissions/5796648e-8887-4807-83e0-2f214692306e

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_geometric_tail_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar

lemma analytic_taylor_error_g_oai {f : ℂ → ℂ} {c z : ℂ} {R M r : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hbound : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : ‖z-c‖ ≤ r*R) (N : ℕ) :
    ‖f z-taylorPolynomial f c N z‖ ≤ M*r^N/(1-r) := by
  have hz' : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hz.trans_lt (by nlinarith)
  have hsum := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hz'
  have hs : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹*
      iteratedDeriv n f c*(z-c)^n) (f z) := by
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (funext n; simp only [smul_eq_mul]; ring)
  apply geometric_tail_error_g hs hr0 hr _ N
  intro n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf hbound
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f c‖ * ‖z-c‖^n ≤
      (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ)*M/R^n) * (r*R)^n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity))
        (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity) (by positivity)
    _ = M*r^n := by rw [mul_pow]; field_simp


end SharpPlanar


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.analytic_taylor_error_g_oai := @OAI.SharpPlanar.analytic_taylor_error_g_oai
