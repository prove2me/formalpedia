-- Prove2me | solution 1 for LiqProvision.Oligopoly.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:16:48.037564+00:00
-- url     : https://prove2.me/submissions/e8941565-3a94-43c4-a351-ad20eeeccc5b

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_1
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_2
import Theorems.Thm_LiqProvision_Oligopoly_proposition_D_3

open Set MeasureTheory Filter Topology
open LiqProvision.Oligopoly

namespace LiqP31Aux

theorem integrable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp (-a * |y|)) := by
  have hI : IntegrableOn (fun y : ℝ => Real.exp (-a * y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact exp_neg_integrableOn_Ioi 0 ha
  have hI' := (integrable_indicator_iff measurableSet_Ici).2 hI
  refine Integrable.mono' (hI'.add hI'.comp_neg)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, indicator_of_mem (show y ∈ Ici 0 from hy)]
    have : 0 ≤ (Ici (0:ℝ)).indicator (fun y => Real.exp (-a * y)) (-y) :=
      indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    linarith
  · rw [abs_of_nonpos hy, indicator_of_mem (show -y ∈ Ici 0 by simp; linarith)]
    have : 0 ≤ (Ici (0:ℝ)).indicator (fun y => Real.exp (-a * y)) y :=
      indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    linarith

theorem logconcave_continuous {F : ℝ → ℝ} (hpos : ∀ x, 0 < F x)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (F x))) : Continuous F := by
  have h1 : Continuous (fun x => Real.log (F x)) := by
    rw [← continuousOn_univ]; exact hc.continuousOn isOpen_univ
  have : F = fun x => Real.exp (Real.log (F x)) := funext fun x => (Real.exp_log (hpos x)).symm
  rw [this]; exact h1.rexp

/-- a function with exponential tails has an integrable first moment -/
theorem moment_integrable {F : ℝ → ℝ} (hpos : ∀ x, 0 < F x) (hFc : Continuous F) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (htail : ∀ x, F x ≤ C * Real.exp (-ε * |x|)) :
    Integrable (fun y => y * F y) := by
  have hexp := (integrable_exp_neg_abs (a := ε / 2) (by positivity)).const_mul (C * (2 / ε))
  refine Integrable.mono' hexp (continuous_id.mul hFc).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos y)]
  have h1 := htail y
  have h2 : ε / 2 * |y| ≤ Real.exp (ε / 2 * |y|) := by
    have := Real.add_one_le_exp (ε / 2 * |y|); linarith
  have h3 : Real.exp (-ε * |y|) = Real.exp (-(ε / 2) * |y|) * Real.exp (-(ε / 2) * |y|) := by
    rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp (-(ε / 2) * |y|) * Real.exp (ε / 2 * |y|) = 1 := by
    rw [← Real.exp_add]; simp
  have h5 : |y| ≤ 2 / ε * Real.exp (ε / 2 * |y|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε]; linarith
  have hE := Real.exp_pos (-(ε / 2) * |y|)
  calc |y| * F y ≤ |y| * (C * Real.exp (-ε * |y|)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg y)
    _ = C * Real.exp (-(ε / 2) * |y|) * (|y| * Real.exp (-(ε / 2) * |y|)) := by
        rw [h3]; ring
    _ ≤ C * Real.exp (-(ε / 2) * |y|) *
          (2 / ε * Real.exp (ε / 2 * |y|) * Real.exp (-(ε / 2) * |y|)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right h5 hE.le
    _ = C * (2 / ε) * Real.exp (-(ε / 2) * |y|) := by
        rw [mul_assoc (2 / ε), mul_comm (Real.exp (ε / 2 * |y|)), h4]; ring

end LiqP31Aux

open LiqP31Aux in
theorem solution (M : Params) (hγc : 0 < M.γc) (hS : IsDensity M.fS)
    (hM : IsDensity M.fM) (h21 : M.Assumption21) :
    ContDiff ℝ 1 (condMean M) ∧
      ∀ y, 0 < deriv (condMean M) y ∧ deriv (condMean M) y < 1 := by
  obtain ⟨hSpos, hSint, hSmass⟩ := hS
  obtain ⟨hMpos, hMint, hMmass⟩ := hM
  obtain ⟨hSlc, hMlc⟩ := h21
  -- density of `-γc M`
  set q : ℝ → ℝ := fun z => M.fM (-z / M.γc) / M.γc with hq
  have hqpos : ∀ z, 0 < q z := fun z => div_pos (hMpos _) hγc
  have hne : (-1 / M.γc) ≠ 0 := by
    have : 0 < 1 / M.γc := by positivity
    intro h; linarith [show -1 / M.γc = -(1 / M.γc) by ring]
  have hqeq : ∀ z, q z = M.fM ((-1 / M.γc) * z) / M.γc := by
    intro z; simp only [hq]; congr 2; ring
  have hqint : Integrable q := by
    have := (hMint.comp_mul_left' hne).div_const M.γc
    exact this.congr (Eventually.of_forall fun z => (hqeq z).symm)
  have hqmass : ∫ z, q z = 1 := by
    simp_rw [hqeq]
    rw [integral_div, Measure.integral_comp_mul_left, hMmass, smul_eq_mul, mul_one]
    have : |(-1 / M.γc)⁻¹| = M.γc := by
      rw [show (-1 / M.γc)⁻¹ = -M.γc by field_simp, abs_neg, abs_of_pos hγc]
    rw [this, div_self hγc.ne']
  have hqlc : ConcaveOn ℝ univ (fun z => Real.log (q z)) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, hq]
    rw [Real.log_div (hMpos _).ne' hγc.ne', Real.log_div (hMpos _).ne' hγc.ne',
      Real.log_div (hMpos _).ne' hγc.ne']
    have := hMlc.2 (mem_univ (-x / M.γc)) (mem_univ (-y / M.γc)) ha hb hab
    simp only [smul_eq_mul] at this
    have e : -(a * x + b * y) / M.γc = a * (-x / M.γc) + b * (-y / M.γc) := by ring
    rw [e]
    have : a * Real.log M.γc + b * Real.log M.γc = Real.log M.γc := by
      rw [← add_mul, hab, one_mul]
    nlinarith
  have hk : ∀ w s, kernel M w s = M.fS s * q (w - s) := by
    intro w s
    simp only [kernel, hq]
    rw [show -(w - s) / M.γc = (s - w) / M.γc by ring]
  -- auxiliary facts
  obtain ⟨-, ⟨CS, εS, hCS, hεS, hStail⟩, -⟩ := proposition_D_1 M.fS hSpos hSint hSmass hSlc
  obtain ⟨-, ⟨Cq, εq, hCq, hεq, hqtail⟩, ⟨q', hq', -⟩⟩ :=
    proposition_D_1 q hqpos hqint hqmass hqlc
  have hSc := logconcave_continuous hSpos hSlc
  have hqc := logconcave_continuous hqpos hqlc
  have hqB : ∀ x, ‖q x‖ ≤ Cq := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (hqpos x)]
    calc q x ≤ Cq * Real.exp (-εq * |x|) := hqtail x
      _ ≤ Cq * 1 := by
        apply mul_le_mul_of_nonneg_left _ hCq.le
        rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg x]
      _ = Cq := mul_one _
  have hsS : Integrable (fun s => s * M.fS s) := moment_integrable hSpos hSc hCS hεS hStail
  have hiK : ∀ w, Integrable (fun s => M.fS s * q (w - s)) := by
    intro w
    have := hSint.bdd_mul (c := Cq) (f := fun s => q (w - s))
      (hqc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => hqB _)
    simpa [mul_comm] using this
  have hiN : ∀ w, Integrable (fun s => s * (M.fS s * q (w - s))) := by
    intro w
    have := hsS.bdd_mul (c := Cq) (f := fun s => q (w - s))
      (hqc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun s => hqB _)
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only; ring
  obtain ⟨⟨hDpos, -⟩, -⟩ :=
    proposition_D_2 q M.fS hqpos hqint hqmass hqlc hSpos hSint hSmass hSlc q' hq'
  -- rewriting the conditional mean
  have hdens : ∀ w, dens M w = ∫ v, q (w - v) * M.fS v := by
    intro w
    simp only [dens, hk]; congr 1; funext v; ring
  have hdens2 : ∀ w, dens M w = ∫ v, M.fS (w - v) * q v := by
    intro w
    simp only [dens, hk]
    have := integral_sub_left_eq_self (fun v => M.fS (w - v) * q v) volume w
    rw [← this]; congr 1; funext v; simp only [sub_sub_cancel]
  have hnum : ∀ w, (∫ s, s * kernel M w s) = ∫ v, (w - v) * M.fS (w - v) * q v := by
    intro w
    simp only [hk]
    have := integral_sub_left_eq_self (fun v => (w - v) * M.fS (w - v) * q v) volume w
    rw [← this]; congr 1; funext v; simp only [sub_sub_cancel]; ring
  have hnum2 : ∀ w, (∫ v, (w - v) * q (w - v) * M.fS v) =
      w * dens M w - ∫ s, s * kernel M w s := by
    intro w
    simp only [hk, dens]
    rw [← integral_const_mul, ← integral_sub ((hiK w).const_mul w) (hiN w)]
    congr 1; funext v; ring
  have e1 : condMean M = fun w =>
      (∫ v, (w - v) * M.fS (w - v) * q v) / ∫ v, M.fS (w - v) * q v := by
    funext w; simp only [condMean]; rw [hnum w, hdens2 w]
  have e2 : condMean M = fun w =>
      w - (∫ v, (w - v) * q (w - v) * M.fS v) / ∫ v, q (w - v) * M.fS v := by
    funext w
    have hD : dens M w ≠ 0 := by rw [hdens w]; exact (hDpos w).ne'
    simp only [condMean]
    rw [hnum2 w, ← hdens w]
    field_simp
    ring
  have hG1 := proposition_D_3 M.fS q hSpos hSint hSmass hSlc hqpos hqint hqmass hqlc
  have hG2 := proposition_D_3 q M.fS hqpos hqint hqmass hqlc hSpos hSint hSmass hSlc
  refine ⟨e1 ▸ hG1.1, fun y => ⟨?_, ?_⟩⟩
  · rw [e1]; exact hG1.2 y
  · rw [e2]
    have hd : DifferentiableAt ℝ (fun w =>
        (∫ v, (w - v) * q (w - v) * M.fS v) / ∫ v, q (w - v) * M.fS v) y :=
      hG2.1.differentiable (by norm_num) y
    have h : HasDerivAt (fun w => w - (∫ v, (w - v) * q (w - v) * M.fS v) /
        ∫ v, q (w - v) * M.fS v) (1 - deriv (fun w =>
        (∫ v, (w - v) * q (w - v) * M.fS v) / ∫ v, q (w - v) * M.fS v) y) y :=
      (hasDerivAt_id' y).sub hd.hasDerivAt
    rw [h.deriv]
    have := hG2.2 y
    linarith
