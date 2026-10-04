-- Prove2me | solution 1 for MDPFinance.MeanVariance.plambda_implies_qp
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:19:58.910427+00:00
-- url     : https://prove2.me/submissions/79ba16eb-c524-46c4-9638-f73fd5cb2c6d

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory MDPFinance.MeanVariance

namespace PLQPAux

theorem sq_expand {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (b : ℝ) :
    ∫ ω, (X ω - b) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ - 2 * b * ∫ ω, X ω ∂μ + b ^ 2 := by
  have h1 : Integrable X μ := hX.integrable (by norm_num)
  have h2 : Integrable (fun ω => X ω ^ 2) μ := hX.integrable_sq
  have e : (fun ω => (X ω - b) ^ 2) = fun ω => X ω ^ 2 - (2 * b) * X ω + b ^ 2 := by
    funext ω; ring
  rw [e, integral_add (f := fun ω => X ω ^ 2 - 2 * b * X ω) (g := fun _ => b ^ 2)
    (h2.sub (h1.const_mul _)) (integrable_const _),
    integral_sub (f := fun ω => X ω ^ 2) (g := fun ω => 2 * b * X ω) h2 (h1.const_mul _),
    integral_const_mul, integral_const]
  simp

end PLQPAux

open PLQPAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d) (lam : ℝ)
    (πstar : ℕ → ℝ → (Fin d → ℝ)) (hopt : M.IsOptimalPLambda lam πstar) :
    M.IsOptimalQP (M.meanXN πstar + lam) πstar := by
  have := M.isProb
  refine ⟨hopt.1, fun π hπ => ?_⟩
  have hs : MemLp (fun ω => M.terminalWealth πstar M.N 0 M.x0 ω) 2 M.measIP := by
    have := hopt.1.2
    simpa using this
  have hp : MemLp (fun ω => M.terminalWealth π M.N 0 M.x0 ω) 2 M.measIP := by
    have := hπ.2
    simpa using this
  have hle := hopt.2 π hπ
  unfold MVMarket.Lagrangian MVMarket.varXN MVMarket.meanXNsq MVMarket.meanXN at hle
  rw [sq_expand _ _ hs, sq_expand _ _ hp]
  unfold MVMarket.meanXN
  set ms := ∫ ω, M.terminalWealth πstar M.N 0 M.x0 ω ∂M.measIP
  set mp := ∫ ω, M.terminalWealth π M.N 0 M.x0 ω ∂M.measIP
  set ss := ∫ ω, M.terminalWealth πstar M.N 0 M.x0 ω ^ 2 ∂M.measIP
  set sp := ∫ ω, M.terminalWealth π M.N 0 M.x0 ω ^ 2 ∂M.measIP
  nlinarith [sq_nonneg (mp - ms)]

#print axioms solution
