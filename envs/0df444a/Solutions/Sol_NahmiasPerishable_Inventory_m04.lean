-- Prove2me | solution 1 for NahmiasPerishable.Inventory.m04
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:10:34.043956+00:00
-- url     : https://prove2.me/submissions/4f923445-62a1-4f1d-aeec-772ca7fbc04e

import Mathlib
import Definitions.Def_NahmiasPerishable_Inventory_Cycles

set_option autoImplicit false

open MeasureTheory Set NahmiasPerishable.Inventory

namespace NahmiasPerishable.Inventory.M04Proof

theorem batchExpiry_two (x y : ℝ) (d : Fin 2 → ℝ) :
    batchExpiry ((fun _ : Fin 1 => x), 0) y d = pos (pos (y - pos (d 0 - x)) - d 1) := by
  simp [batchExpiry, consume, List.ofFn_succ]

theorem pos_pos_sub (a b : ℝ) (hb : 0 ≤ b) : pos (pos a - b) = pos (a - b) := by
  unfold pos
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [max_eq_left h]

theorem pos_nonneg (a : ℝ) : 0 ≤ pos a := le_max_right _ _

/-- `(y - a - b)⁺ = ∫_{(0,y]} 1{a ≤ v ≤ y - b} dv` for `a, b ≥ 0`. -/
theorem integral_window (a b y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ v in Ioc 0 y, (Icc a (y - b)).indicator (fun _ => (1 : ℝ)) v = pos (y - a - b) := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply measurableSet_Icc]
  have hsub : Icc a (y - b) ⊆ Icc 0 y := Icc_subset_Icc ha (by linarith)
  have hae : (Icc a (y - b) ∩ Ioc 0 y : Set ℝ) =ᵐ[volume] Icc a (y - b) := by
    have h1 : (Ioc 0 y : Set ℝ) =ᵐ[volume] Icc 0 y := Ioc_ae_eq_Icc
    have h2 : (Icc a (y - b) ∩ Icc 0 y : Set ℝ) = Icc a (y - b) := inter_eq_left.mpr hsub
    have h3 := ae_eq_set_inter (ae_eq_refl (Icc a (y - b))) h1
    rwa [h2] at h3
  rw [measure_congr hae, Real.volume_Icc, ENNReal.toReal_ofReal', pos]
  congr 1
  ring

end NahmiasPerishable.Inventory.M04Proof

open NahmiasPerishable.Inventory.M04Proof

set_option linter.unusedVariables false in
theorem solution (D : Demand) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∀ d : Fin 2 → ℝ, (∀ i, 0 ≤ d i) →
      batchExpiry ((fun _ : Fin 1 => x),0) y d = pos (y-pos (d 0-x)-d 1)) ∧
    (∫ d, batchExpiry ((fun _ : Fin 1 => x),0) y d ∂demandPaths D.law 2) =
      ∫ v in (0 : ℝ)..y, cdf D.law (v+x)*cdf D.law (y-v) := by
  have hpt : ∀ d : Fin 2 → ℝ, (∀ i, 0 ≤ d i) →
      batchExpiry ((fun _ : Fin 1 => x),0) y d = pos (y-pos (d 0-x)-d 1) := by
    intro d hd
    rw [batchExpiry_two, pos_pos_sub _ _ (hd 1)]
  refine ⟨hpt, ?_⟩
  set π : Measure (Fin 2 → ℝ) := demandPaths D.law 2 with hπ
  have : IsProbabilityMeasure π := by
    rw [hπ]; unfold demandPaths; infer_instance
  -- Almost surely both demands are nonnegative.
  have hnn : ∀ᵐ d ∂π, ∀ i, 0 ≤ d i := by
    rw [ae_all_iff]
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually D.nonneg
  -- The window function `h(d, v) = 1{(d₀ - x)⁺ ≤ v ≤ y - d₁}`.
  set h : (Fin 2 → ℝ) → ℝ → ℝ := fun d v =>
    (Icc (pos (d 0 - x)) (y - d 1)).indicator (fun _ => (1 : ℝ)) v with hhdef
  have hrepr : ∀ᵐ d ∂π, batchExpiry ((fun _ : Fin 1 => x),0) y d = ∫ v in Ioc 0 y, h d v := by
    filter_upwards [hnn] with d hd
    rw [hpt d hd, hhdef, integral_window _ _ y (pos_nonneg _) (hd 1)]
  rw [integral_congr_ae hrepr]
  -- Fubini.
  have hmeas : Measurable (Function.uncurry h) := by
    have hS : MeasurableSet {p : (Fin 2 → ℝ) × ℝ | pos (p.1 0 - x) ≤ p.2 ∧ p.2 ≤ y - p.1 1} := by
      refine (measurableSet_le ?_ measurable_snd).inter (measurableSet_le measurable_snd ?_)
      · unfold pos; fun_prop
      · fun_prop
    have : Function.uncurry h = {p : (Fin 2 → ℝ) × ℝ | pos (p.1 0 - x) ≤ p.2 ∧ p.2 ≤ y - p.1 1}.indicator
        (fun _ => (1 : ℝ)) := by
      funext p
      simp only [Function.uncurry, hhdef, indicator, mem_Icc, mem_ofPred_eq]
    rw [this]
    exact measurable_const.indicator hS
  have hint : Integrable (Function.uncurry h) (π.prod (volume.restrict (Ioc 0 y))) := by
    have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) y)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hhdef, indicator]
    split_ifs <;> norm_num
  rw [integral_integral_swap hint, intervalIntegral.integral_of_le hy]
  refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  -- For `v ≥ 0`, the window event is the rectangle `{d₀ ≤ v + x} × {d₁ ≤ y - v}`.
  have hset : {d : Fin 2 → ℝ | pos (d 0 - x) ≤ v ∧ v ≤ y - d 1}
      = univ.pi (fun i : Fin 2 => if i = 0 then Iic (v + x) else Iic (y - v)) := by
    ext d
    simp only [mem_ofPred_eq, mem_pi, mem_univ, true_implies, Fin.forall_fin_two, ite_true,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, mem_Iic, pos]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith [le_max_left (d 0 - x) 0], by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨max_le (by linarith) hv.1.le, by linarith⟩
  have hfun : (fun d => h d v) = {d : Fin 2 → ℝ | pos (d 0 - x) ≤ v ∧ v ≤ y - d 1}.indicator
      (fun _ => (1 : ℝ)) := by
    funext d
    simp only [hhdef, indicator, mem_Icc, mem_ofPred_eq]
  have hSm : MeasurableSet {d : Fin 2 → ℝ | pos (d 0 - x) ≤ v ∧ v ≤ y - d 1} := by
    rw [hset]
    exact MeasurableSet.univ_pi fun i => by split_ifs <;> exact measurableSet_Iic
  show ∫ d, h d v ∂π = cdf D.law (v + x) * cdf D.law (y - v)
  rw [hfun, integral_indicator hSm, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    hset, hπ]
  unfold demandPaths
  rw [Measure.pi_pi, Fin.prod_univ_two]
  simp [cdf, ENNReal.toReal_mul]
