-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.one_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:08.739808+00:00
-- url     : https://prove2.me/submissions/10b8e0aa-f518-4746-8608-3da6ab36dade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) {ρ : ℂ}
    (hρ : LFunction χ ρ = 0) : 1 ≤ analyticOrderNatAt (LFunction χ) ρ := by
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction h
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hd
  have h2 : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by norm_num)
  have hfin2 : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(ha 2 trivial).analyticOrderAt_eq_zero.mpr h2]
    exact ENat.zero_ne_top
  have hfin : analyticOrderAt (LFunction χ) ρ ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hfin2
  have hne : analyticOrderAt (LFunction χ) ρ ≠ 0 := (ha ρ trivial).analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← Nat.cast_analyticOrderNatAt hfin, h0]
  rfl
end GlobalTheory.ZeroFreeComplex
