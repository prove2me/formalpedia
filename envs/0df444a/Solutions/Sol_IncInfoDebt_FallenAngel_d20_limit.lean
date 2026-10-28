-- Prove2me | solution 1 for IncInfoDebt.FallenAngel.d20_limit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:10:57.165646+00:00
-- url     : https://prove2.me/submissions/dcc5a1d3-3936-44c0-9c87-86f0653895cd

import Mathlib
import Definitions.Def_IncInfoDebt_FallenAngel_Model

open Filter MeasureTheory

namespace Aux_IIDd20

lemma g_eq : (fun z : ℝ => Real.exp (-z ^ 2 / 2)) = fun z => Real.exp (-(1 / 2) * z ^ 2) := by
  funext z; congr 1; ring

lemma hint : Integrable (fun z : ℝ => Real.exp (-z ^ 2 / 2)) := by
  rw [g_eq]; exact integrable_exp_neg_mul_sq (by norm_num)

lemma total : ∫ z, Real.exp (-z ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  rw [g_eq, integral_gaussian]; congr 1; ring

lemma cont : Continuous (fun x : ℝ => ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2)) := by
  have h : (fun x : ℝ => ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2)) = fun x =>
      (∫ z in Set.Iic 0, Real.exp (-z ^ 2 / 2)) + ∫ z in (0 : ℝ)..x, Real.exp (-z ^ 2 / 2) := by
    funext x
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
    ring
  rw [h]
  exact continuous_const.add (hint.continuous_primitive 0)

lemma sym (x : ℝ) : (∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2))
    + (∫ z in Set.Iic (-x), Real.exp (-z ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
  have h := integral_comp_neg_Ioi x (fun z : ℝ => Real.exp (-z ^ 2 / 2))
  simp only [neg_sq] at h
  rw [← h, intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, total]

lemma N_cont : Continuous IncInfoDebt.FallenAngel.N := by
  show Continuous (fun x => (1 / Real.sqrt (2 * Real.pi)) *
    ∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2))
  exact continuous_const.mul cont

lemma N_sym (x : ℝ) : IncInfoDebt.FallenAngel.N x + IncInfoDebt.FallenAngel.N (-x) = 1 := by
  show (1 / Real.sqrt (2 * Real.pi)) * (∫ z in Set.Iic x, Real.exp (-z ^ 2 / 2))
    + (1 / Real.sqrt (2 * Real.pi)) * (∫ z in Set.Iic (-x), Real.exp (-z ^ 2 / 2)) = 1
  rw [← mul_add, sym]
  exact one_div_mul_cancel (by positivity)

end Aux_IIDd20

open IncInfoDebt.FallenAngel Aux_IIDd20 in
theorem solution (σ m L α : ℝ) (hP : Standing σ L) (hα : 0 < α) :
    Tendsto (fun h : ℝ => 1 - survival σ m h (α * σ * Real.sqrt h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 * N (-α))) := by
  obtain ⟨hσ, -⟩ := hP
  have hNc := N_cont
  set G : ℝ → ℝ := fun s => 1 - (N (α + m * s / σ) -
    Real.exp (-(2 * α * m * s / σ)) * N (-α + m * s / σ)) with hGdef
  have hGc : Continuous G := by
    rw [hGdef]
    first | fun_prop | continuity
  have hG0 : G 0 = 2 * N (-α) := by
    rw [hGdef]
    have := N_sym α
    simp only [mul_zero, zero_div, add_zero, neg_zero, Real.exp_zero, one_mul]
    linarith
  have hGt : Tendsto G (nhds 0) (nhds (2 * N (-α))) := by
    rw [← hG0]; exact hGc.tendsto 0
  have hsq : Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [Real.sqrt_zero] at this
  refine (hGt.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0 < h := hh
  show G (Real.sqrt h) = 1 - survival σ m h (α * σ * Real.sqrt h)
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt h := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hh'
  have hhs : h = s * s := by rw [hs_def, Real.mul_self_sqrt hh'.le]
  have hx : 0 < α * σ * s := mul_pos (mul_pos hα hσ) hs
  have hsig : Real.sqrt (σ ^ 2 * h) = σ * s := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le, ← hs_def]
  have hσ' : σ ≠ 0 := hσ.ne'
  have hs' : s ≠ 0 := hs.ne'
  have h1 : (α * σ * s + m * (s * s)) / (σ * s) = α + m * s / σ := by
    field_simp <;> ring
  have h2 : (-(α * σ * s) + m * (s * s)) / (σ * s) = -α + m * s / σ := by
    field_simp <;> ring
  have h3 : -(2 * (α * σ * s) * m / σ ^ 2) = -(2 * α * m * s / σ) := by
    field_simp <;> ring
  unfold survival
  rw [if_pos hx, hsig, hhs, h1, h2, h3]
  first | done | rfl
