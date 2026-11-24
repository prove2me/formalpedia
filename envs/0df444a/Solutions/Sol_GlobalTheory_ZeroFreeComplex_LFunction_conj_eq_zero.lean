-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.LFunction_conj_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:06.374304+00:00
-- url     : https://prove2.me/submissions/2f0140ef-c922-4068-8f96-1683c3d0c2ec

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
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
namespace GlobalTheory.ZeroFreeComplex
private theorem conj_apply_lemma {d : ℕ} {χ : DirichletCharacter ℂ d} (h2 : χ ^ 2 = 1)
    (n : ℕ) : conj (χ n) = χ n := by
  by_cases hu : IsUnit (n : ZMod d)
  · have hsq : χ n * χ n = 1 := by
      have h := congrArg (fun ψ : DirichletCharacter ℂ d => ψ n) h2
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hu] at h
      simpa [pow_two] using h
    rcases mul_self_eq_one_iff.mp hsq with h | h <;> simp [h]
  · simp [MulChar.map_nonunit χ hu]
private theorem conj_LFunction_conj_of_sq_eq_one' {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (h2 : χ ^ 2 = 1) {z : ℂ} (hz : 1 < z.re) :
    conj (LFunction χ (conj z)) = LFunction χ z := by
  have hz' : 1 < (conj z).re := by simpa using hz
  rw [LFunction_eq_LSeries χ hz, LFunction_eq_LSeries χ hz']
  unfold LSeries
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, conj_apply_lemma h2]
    congr 1
    rw [Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne), Complex.conj_conj,
      Complex.conj_natCast]
end GlobalTheory.ZeroFreeComplex
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (h₁ : χ ≠ 1)
    (h2 : χ ^ 2 = 1) {s : ℂ} (hs : LFunction χ s = 0) : LFunction χ (conj s) = 0 := by
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction h₁
  have hg : Differentiable ℂ (conj ∘ LFunction χ ∘ conj) := by
    intro z
    have h := (hd (conj z)).conj_conj
    rwa [Complex.conj_conj] at h
  have heq : (conj ∘ LFunction χ ∘ conj) = LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (analyticOnNhd_univ_iff_differentiable.mpr hg)
      (analyticOnNhd_univ_iff_differentiable.mpr hd) (z₀ := 2) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one' h2 hz
  have h := congrFun heq (conj s)
  simp only [Function.comp_apply, Complex.conj_conj, hs, _root_.map_zero] at h
  exact h.symm
end GlobalTheory.ZeroFreeComplex
