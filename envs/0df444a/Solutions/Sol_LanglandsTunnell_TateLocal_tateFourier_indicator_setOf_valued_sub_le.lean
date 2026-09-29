-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4e14163f-8549-5079-8a2a-d5d306390e92

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel

noncomputable section

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "tateFourier"
namespace FourierBallF1
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K)
      = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem measurableSet_ball [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (k : ℤ) : MeasurableSet {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  have ht : ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
    Units.ne_zero _
  have h := (isClosed_setOf_valued_le v _ ht).measurableSet
  rw [valued_uniformizerUnit_zpow, neg_neg] at h
  exact h

private theorem integral_indicator_ball_mul [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (m : ℤ) (y : v.adicCompletion K) :
    ∫ x, {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) ∂μ
      = (μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℂ)
        * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y := by
  set B : Set (v.adicCompletion K) := {x | Valued.v x ≤ WithZero.exp (-m)} with hB
  have hBmeas : MeasurableSet B := measurableSet_ball v (-m)
  have hind : ∀ x, B.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) = B.indicator (fun x => ψ (x * y)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp_rw [hind]
  by_cases hy : Valued.v y ≤ WithZero.exp (n + m)
  ·
    rw [Set.indicator_of_mem (show y ∈ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)} from hy),
      mul_one, integral_indicator hBmeas]
    have hone : Set.EqOn (fun x => ψ (x * y)) (fun _ => (1 : ℂ)) B := fun x hx => by
      show ψ (x * y) = 1
      apply hψn
      rw [map_mul]
      calc Valued.v x * Valued.v y ≤ WithZero.exp (-m) * WithZero.exp (n + m) :=
            mul_le_mul' hx hy
        _ = WithZero.exp n := by rw [← WithZero.exp_add]; congr 1; ring
    rw [setIntegral_congr_fun hBmeas hone, setIntegral_const, Complex.real_smul, mul_one]
  ·
    rw [Set.indicator_of_notMem (show y ∉ {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)} from hy),
      mul_zero]
    obtain ⟨x₁, hx₁, hne⟩ := hψn'
    rw [not_le] at hy
    have hy0 : y ≠ 0 := fun h => by
      rw [h, map_zero] at hy
      exact not_lt_zero hy
    have hvy0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    have hvy : WithZero.exp (n + m + 1) ≤ Valued.v y := by
      rw [← WithZero.exp_log hvy0] at hy ⊢
      rw [WithZero.exp_lt_exp] at hy
      exact WithZero.exp_le_exp.mpr (by omega)
    set t : v.adicCompletion K := x₁ * y⁻¹ with ht
    have htB : t ∈ B := by
      show Valued.v (x₁ * y⁻¹) ≤ WithZero.exp (-m)
      rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr hvy0)]
      calc Valued.v x₁ ≤ WithZero.exp (n + 1) := hx₁
        _ = WithZero.exp (-m) * WithZero.exp (n + m + 1) := by rw [← WithZero.exp_add]; congr 1; ring
        _ ≤ WithZero.exp (-m) * Valued.v y := mul_le_mul_right hvy _
    have hty : t * y = x₁ := by rw [ht, inv_mul_cancel_right₀ hy0]
    have hpt : ∀ x, B.indicator (fun x => ψ (x * y)) (t + x) = ψ x₁ * B.indicator (fun x => ψ (x * y)) x := by
      intro x
      by_cases hx : x ∈ B
      · have htx : t + x ∈ B := by
          show Valued.v (t + x) ≤ WithZero.exp (-m)
          exact (Valuation.map_add_le_max' _ t x).trans (max_le htB hx)
        rw [Set.indicator_of_mem htx, Set.indicator_of_mem hx, add_mul, AddChar.map_add_eq_mul, hty]
      · have htx : t + x ∉ B := fun h => hx <| by
          have hsub : Valued.v (t + x - t) ≤ WithZero.exp (-m) :=
            (Valuation.map_sub _ (t + x) t).trans (max_le h htB)
          rwa [add_sub_cancel_left] at hsub
        rw [Set.indicator_of_notMem htx, Set.indicator_of_notMem hx, mul_zero]
    have htrans : ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ = ψ x₁ * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ := by
      calc ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ
          = ∫ x, B.indicator (fun x => ψ (x * y)) (t + x) ∂μ := (integral_add_left_eq_self _ t).symm
        _ = ∫ x, ψ x₁ * B.indicator (fun x => ψ (x * y)) x ∂μ := by simp_rw [hpt]
        _ = ψ x₁ * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ := integral_const_mul _ _
    have h1ne : (1 : ℂ) - ψ x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hprod : ((1 : ℂ) - ψ x₁) * ∫ x, B.indicator (fun x => ψ (x * y)) x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← htrans, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left h1ne

end LanglandsTunnell.TateLocal.FourierBallF1

end

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le.LanglandsTunnell.TateLocal in
theorem solution (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (a : v.adicCompletion K) (m : ℤ) (y : v.adicCompletion K) :
    tateFourier ψ μ ({x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ)) y
      = ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
          * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y := by
  unfold tateFourier
  have hshift : ∀ x : v.adicCompletion K,
      {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) (a + x) * ψ ((a + x) * y)
        = ψ (a * y) * ({x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
            * ψ (x * y)) := by
    intro x
    have hmem : (a + x ∈ {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)})
        ↔ x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} := by
      simp only [Set.mem_setOf_eq, add_sub_cancel_left]
    rw [add_mul, AddChar.map_add_eq_mul]
    by_cases hx : x ∈ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}
    · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
      ring
    · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
      ring
  calc ∫ x, {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * ψ (x * y) ∂μ
      = ∫ x, {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) (a + x)
          * ψ ((a + x) * y) ∂μ :=
        (integral_add_left_eq_self
          (fun x => {x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
            * ψ (x * y)) a).symm
    _ = ∫ x, ψ (a * y) * ({x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
          * ψ (x * y)) ∂μ := by simp_rw [hshift]
    _ = ψ (a * y) * ∫ x, {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x
          * ψ (x * y) ∂μ := integral_const_mul _ _
    _ = _ := by
        rw [LanglandsTunnell.TateLocal.FourierBallF1.integral_indicator_ball_mul v μ ψ n hψn hψn' m y, mul_assoc]

end S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le (solution)
