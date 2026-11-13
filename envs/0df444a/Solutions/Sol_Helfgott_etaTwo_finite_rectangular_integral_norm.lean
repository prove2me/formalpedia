-- Prove2me | solution 1 for Helfgott.etaTwo_finite_rectangular_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-12T16:46:56.018496+00:00
-- url     : https://prove2.me/submissions/7859eea1-12d2-414c-a1fd-486e56a3feff

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set
namespace HelfgottQuadratic

theorem etaTwo_log_overlap (t : ℝ) (ht : 0<t) :
    Helfgott.etaTwo t=4*max
      (Real.log (min 1 (2*t))-Real.log (max (1/2) t)) 0 := by
  have hlog : Real.log (2*t)=Real.log 2+Real.log t :=
    Real.log_mul (by norm_num) ht.ne'
  unfold Helfgott.etaTwo
  rw [if_pos ht]
  by_cases hhalf : t≤1/2
  · have h2t : 2*t≤1 := by linarith
    have hneg : Real.log (2*t)≤0 := Real.log_nonpos (by positivity) h2t
    rw [min_eq_right h2t,max_eq_left hhalf,abs_of_nonpos hneg]
    rw [show Real.log (1/2:ℝ)= -Real.log 2 by rw [one_div,Real.log_inv]]
    congr 2
    ring
  · have ht2 : 1/2≤t := le_of_not_ge hhalf
    have h2t : 1≤2*t := by linarith
    have hpos : 0≤Real.log (2*t) := Real.log_nonneg h2t
    rw [min_eq_left h2t,max_eq_right ht2,abs_of_nonneg hpos,Real.log_one,hlog]
    congr 2
    ring

theorem integral_inv_Icc_positive (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫ u in Icc a b, u⁻¹)=max (Real.log b-Real.log a) 0 := by
  by_cases hab : a≤b
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha hb,Real.log_div hb.ne' ha.ne']
    exact (max_eq_left (sub_nonneg.mpr (Real.log_le_log ha hab))).symm
  · have hba : b<a := lt_of_not_ge hab
    simp [Icc_eq_empty_of_lt hba,max_eq_right (sub_nonpos.mpr (Real.log_le_log hb hba.le))]

theorem etaTwo_overlap_integral (t : ℝ) (ht : 0<t) :
    Helfgott.etaTwo t=4*(∫ u in Icc (max (1/2) t) (min 1 (2*t)), u⁻¹) := by
  rw [integral_inv_Icc_positive _ _ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_left _ _))
    (lt_min (by norm_num) (by positivity))]
  exact etaTwo_log_overlap t ht

theorem etaOne_product_indicator (t w : ℝ) (hw : 0<w) :
    Helfgott.etaOne (t/w)*Helfgott.etaOne w/w=
      (Icc (max (1/2) t) (min 1 (2*t))).indicator (fun u=>4*u⁻¹) w := by
  have hmem : t/w∈Icc (1/2:ℝ) 1 ∧ w∈Icc (1/2:ℝ) 1 ↔
      w∈Icc (max (1/2) t) (min 1 (2*t)) := by
    simp only [mem_Icc,max_le_iff,le_min_iff,le_div_iff₀ hw,div_le_iff₀ hw,one_mul]
    constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;> constructor <;> constructor <;> linarith
  unfold Helfgott.etaOne
  by_cases ha : t/w∈Icc (1/2:ℝ) 1 <;> by_cases hb : w∈Icc (1/2:ℝ) 1
  · rw [indicator_of_mem ha,indicator_of_mem hb,indicator_of_mem (hmem.mp ⟨ha,hb⟩)]
    norm_num [div_eq_mul_inv]
  · rw [indicator_of_mem ha,indicator_of_notMem hb,
      indicator_of_notMem (fun h=>hb (hmem.mpr h).2)]
    simp
  · rw [indicator_of_notMem ha,indicator_of_mem hb,
      indicator_of_notMem (fun h=>ha (hmem.mpr h).1)]
    simp
  · rw [indicator_of_notMem ha,indicator_of_notMem hb,
      indicator_of_notMem (fun h=>ha (hmem.mpr h).1)]
    simp

theorem etaTwo_eq_mellin_etaOne (t : ℝ) (ht : 0<t) :
    Helfgott.etaTwo t=Helfgott.mellinConv Helfgott.etaOne Helfgott.etaOne t := by
  rw [etaTwo_overlap_integral t ht]
  unfold Helfgott.mellinConv
  have he : (∫ w in Ioi (0:ℝ), Helfgott.etaOne (t/w)*Helfgott.etaOne w/w)=
      ∫ w in Ioi (0:ℝ), (Icc (max (1/2) t) (min 1 (2*t))).indicator (fun u=>4*u⁻¹) w :=
    setIntegral_congr_fun measurableSet_Ioi (fun w hw=>etaOne_product_indicator t w hw)
  rw [he,setIntegral_indicator measurableSet_Icc]
  have hsub : Icc (max (1/2:ℝ) t) (min 1 (2*t))⊆Ioi (0:ℝ) := by
    intro w hw
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) ((le_max_left _ _).trans hw.1)
  rw [inter_eq_right.mpr hsub,integral_const_mul]

theorem etaTwo_scaled_rectangle_integral (d m y : ℝ) (hd : 0<d) (hm : 0<m) (hy : 0<y) :
    Helfgott.etaTwo (d*m/y)=
      4*(∫ w in Icc (max d (y/(2*m))) (min (2*d) (y/m)), w⁻¹) := by
  let t := d*m/y
  let c := y/m
  have ht : 0<t := by dsimp [t]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hct : c*t=d := by dsimp [c,t]; field_simp
  have hlo : c*max (1/2) t=max d (y/(2*m)) := by
    rw [mul_max_of_nonneg _ _ hc.le,hct]
    have he : c*(1/2)=y/(2*m) := by dsimp [c]; ring
    rw [he,max_comm]
  have hhi : c*min 1 (2*t)=min (2*d) (y/m) := by
    rw [mul_min_of_nonneg _ _ hc.le,mul_one]
    rw [show c*(2*t)=2*d by nlinarith [hct]]
    exact min_comm _ _
  have hlow : 0<max (1/2:ℝ) t := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_left _ _)
  have hhigh : 0<min (1:ℝ) (2*t) := lt_min (by norm_num) (by positivity)
  rw [←hlo,←hhi,integral_inv_Icc_positive _ _ (mul_pos hc hlow) (mul_pos hc hhigh),
    Real.log_mul hc.ne' hhigh.ne',Real.log_mul hc.ne' hlow.ne']
  rw [show Real.log c+Real.log (min 1 (2*t))-(Real.log c+Real.log (max (1/2) t))=
    Real.log (min 1 (2*t))-Real.log (max (1/2) t) by ring]
  exact etaTwo_log_overlap t ht

end HelfgottQuadratic


open MeasureTheory Set Finset
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def etaTwoRectangleKernel (d m y w : ℝ) : ℝ :=
  (Icc (max d (y/(2*m))) (min (2*d) (y/m))).indicator (fun u=>u⁻¹) w

theorem etaTwoRectangleKernel_integrable (d m y : ℝ) (hd : 0<d) :
    Integrable (etaTwoRectangleKernel d m y) := by
  have hc : ContinuousOn (fun u : ℝ=>u⁻¹) (Icc (max d (y/(2*m))) (min (2*d) (y/m))) := by
    apply continuousOn_id.inv₀
    intro u hu
    exact ne_of_gt (hd.trans_le ((le_max_left _ _).trans hu.1))
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem etaTwoRectangleKernel_integral (d m y : ℝ) (hd : 0<d) (hm : 0<m) (hy : 0<y) :
    Helfgott.etaTwo (d*m/y)=4*∫ w, etaTwoRectangleKernel d m y w := by
  unfold etaTwoRectangleKernel
  rw [integral_indicator measurableSet_Icc]
  exact etaTwo_scaled_rectangle_integral d m y hd hm hy

theorem etaTwoRectangleKernel_complex_integral (d m y : ℝ) (hd : 0<d) (hm : 0<m) (hy : 0<y)
    (z : ℂ) :
    z*(Helfgott.etaTwo (d*m/y):ℂ)=4*∫ w, z*(etaTwoRectangleKernel d m y w:ℂ) := by
  rw [integral_const_mul,integral_complex_ofReal,etaTwoRectangleKernel_integral d m y hd hm hy]
  push_cast
  ring

theorem etaTwo_finite_bilinear_integral (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y : ℝ)
    (hS : ∀ d∈S, 0<d) (hT : ∀ m∈T, 0<m) (hy : 0<y) :
    (∑ d ∈ S, ∑ m ∈ T, z d m*(Helfgott.etaTwo ((d:ℝ)*(m:ℝ)/y):ℂ))=
      4*∫ w, ∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ) := by
  have hi : ∀ d∈S, ∀ m∈T,
      Integrable (fun w=>z d m*(etaTwoRectangleKernel d m y w:ℂ)) := by
    intro d hd m hm
    exact (etaTwoRectangleKernel_integrable d m y (by exact_mod_cast hS d hd)).ofReal.const_mul _
  rw [integral_finsetSum S (fun d hd=>integrable_finsetSum T (hi d hd)),Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [integral_finsetSum T (hi d hd),Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  exact etaTwoRectangleKernel_complex_integral d m y (by exact_mod_cast hS d hd)
    (by exact_mod_cast hT m hm) hy (z d m)

theorem etaTwo_finite_bilinear_integral_norm (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y : ℝ)
    (hS : ∀ d∈S, 0<d) (hT : ∀ m∈T, 0<m) (hy : 0<y) :
    ‖∑ d ∈ S, ∑ m ∈ T, z d m*(Helfgott.etaTwo ((d:ℝ)*(m:ℝ)/y):ℂ)‖≤
      4*∫ w, ‖∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ)‖ := by
  rw [etaTwo_finite_bilinear_integral S T z y hS hT hy,norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)

end HelfgottQuadratic


open Finset MeasureTheory
open scoped BigOperators Classical
namespace HelfgottQuadratic

noncomputable def rectangleFirstIndices (S : Finset ℕ) (w : ℝ) : Finset ℕ :=
  S.filter (fun d=>w/2≤(d:ℝ) ∧ (d:ℝ)≤w)

noncomputable def rectangleSecondIndices (T : Finset ℕ) (y w : ℝ) : Finset ℕ :=
  T.filter (fun m=>y/(2*w)≤(m:ℝ) ∧ (m:ℝ)≤y/w)

theorem rectangle_window_iff (d m y w : ℝ) (hm : 0<m) (hw : 0<w) :
    w∈Set.Icc (max d (y/(2*m))) (min (2*d) (y/m)) ↔
      (w/2≤d ∧ d≤w) ∧ (y/(2*w)≤m ∧ m≤y/w) := by
  simp only [Set.mem_Icc,max_le_iff,le_min_iff,
    div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hm),le_div_iff₀ hm,
    div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hw),le_div_iff₀ hw,
    div_le_iff₀ (by norm_num : (0:ℝ)<2)]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;> constructor <;> constructor <;> nlinarith

theorem rectangle_kernel_bilinear_sum (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y w : ℝ)
    (hT : ∀ m∈T, 0<m) (hw : 0<w) :
    (∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ))=
      (w⁻¹:ℂ)*(∑ d ∈ rectangleFirstIndices S w, ∑ m ∈ rectangleSecondIndices T y w, z d m) := by
  unfold rectangleFirstIndices rectangleSecondIndices
  simp_rw [sum_filter]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro d hd
  by_cases hD : w/2≤(d:ℝ) ∧ (d:ℝ)≤w
  · rw [if_pos hD,Finset.mul_sum]
    apply sum_congr rfl
    intro m hm
    have hiff := rectangle_window_iff (d:ℝ) m y w (by exact_mod_cast hT m hm) hw
    by_cases hM : y/(2*w)≤(m:ℝ) ∧ (m:ℝ)≤y/w
    · rw [if_pos hM]
      simp only [etaTwoRectangleKernel,Set.indicator_of_mem (hiff.mpr ⟨hD,hM⟩)]
      push_cast
      ring
    · rw [if_neg hM,mul_zero]
      have hnot := fun h=>hM (hiff.mp h).2
      simp only [etaTwoRectangleKernel,Set.indicator_of_notMem hnot,Complex.ofReal_zero,mul_zero]
  · rw [if_neg hD,mul_zero]
    apply sum_eq_zero
    intro m hm
    have hiff := rectangle_window_iff (d:ℝ) m y w (by exact_mod_cast hT m hm) hw
    have hnot := fun h=>hD (hiff.mp h).1
    simp only [etaTwoRectangleKernel,Set.indicator_of_notMem hnot,Complex.ofReal_zero,mul_zero]

theorem etaTwoRectangleKernel_zero_of_nonpos (d m y w : ℝ) (hd : 0<d) (hw : w≤0) :
    etaTwoRectangleKernel d m y w=0 := by
  apply Set.indicator_of_notMem
  intro h
  have hh := (le_max_left d (y/(2*m))).trans h.1
  linarith

theorem etaTwo_rectangular_integral_norm (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y : ℝ)
    (hS : ∀ d∈S, 0<d) (hT : ∀ m∈T, 0<m) (hy : 0<y) :
    ‖∑ d ∈ S, ∑ m ∈ T, z d m*(Helfgott.etaTwo ((d:ℝ)*(m:ℝ)/y):ℂ)‖≤
      4*∫ w in Set.Ioi (0:ℝ), (1/w)*
        ‖∑ d ∈ rectangleFirstIndices S w, ∑ m ∈ rectangleSecondIndices T y w, z d m‖ := by
  have hh := etaTwo_finite_bilinear_integral_norm S T z y hS hT hy
  have hset : (∫ w in Set.Ioi (0:ℝ), ‖∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ)‖)=
      ∫ w, ‖∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ)‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hw0 : w≤0 := le_of_not_gt hw
    have hz : (∑ d ∈ S, ∑ m ∈ T, z d m*(etaTwoRectangleKernel d m y w:ℂ))=0 := by
      apply sum_eq_zero
      intro d hd
      apply sum_eq_zero
      intro m hm
      rw [etaTwoRectangleKernel_zero_of_nonpos d m y w (by exact_mod_cast hS d hd) hw0]
      simp
    rw [hz,norm_zero]
  rw [←hset] at hh
  convert hh using 1
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  change 0 < w at hw
  dsimp only
  rw [rectangle_kernel_bilinear_sum S T z y w hT hw,norm_mul]
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw,one_div]

end HelfgottQuadratic

open Finset MeasureTheory
open scoped BigOperators Classical
theorem solution
    (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y : ℝ)
    (hS : ∀ d∈S, 0<d) (hT : ∀ m∈T, 0<m) (hy : 0<y) :
    ‖∑ d ∈ S, ∑ m ∈ T, z d m*(Helfgott.etaTwo ((d:ℝ)*(m:ℝ)/y):ℂ)‖≤
      4*∫ w in Set.Ioi (0:ℝ), (1/w)*
        ‖∑ d ∈ S.filter (fun d : ℕ=>w/2≤(d:ℝ) ∧ (d:ℝ)≤w),
          ∑ m ∈ T.filter (fun m : ℕ=>y/(2*w)≤(m:ℝ) ∧ (m:ℝ)≤y/w), z d m‖ := by
  exact HelfgottQuadratic.etaTwo_rectangular_integral_norm S T z y hS hT hy
