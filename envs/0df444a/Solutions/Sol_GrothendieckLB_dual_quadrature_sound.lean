-- Prove2me | solution 1 for GrothendieckLB.dual_quadrature_sound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:32:42.913551+00:00
-- url     : https://prove2.me/submissions/043d8130-ff63-4365-8e40-b1f35fe2a7ba

import Mathlib
import Definitions.Def_GrothendieckLB_DualQuadrature
import Definitions.Def_ABPOnline_cG
import Definitions.Def_GrothendieckLB_he
import Definitions.Def_GrothendieckLB_stdExp
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8

section

open GrothendieckLB MeasureTheory ProbabilityTheory Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian
namespace FiberChaos

noncomputable abbrev G (d : ℕ) := Measure.pi fun _ : Fin d => gaussianReal 0 1

noncomputable def coordH {d : ℕ} (κ : Fin d → ℕ) (z : Fin d → ℝ) :=
  hermite d κ (WithLp.toLp 2 z)
lemma coordH_int {d : ℕ} (κ : Fin d → ℕ) : Integrable (coordH κ) (G d) := by
  letI : IsProbabilityMeasure (gaussian d) := (inferInstance : IsProbabilityMeasure (stdGaussian (Vec d)))
  have hp : MeasurePreserving (WithLp.toLp 2) (G d) (gaussian d) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  exact hp.integrable_comp_of_integrable (((lemma_B_8 d).2.1 κ).integrable (by norm_num))

end FiberChaos

end

section

open GrothendieckLB MeasureTheory ProbabilityTheory Filter Finset Real
open PrivateAgnosticHalfspace.Gaussian
namespace FiberChaos

lemma stdExp_eq (F : ℝ → ℝ) : stdExp F = ∫ s, F s ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  unfold stdExp
  simp only [smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun s => mul_comm _ _)

lemma he_eq_normalized (j : Fin 4) (s : ℝ) : he j s = AMPLowDeg.RankOne.hermNorm j.val s := by
  fin_cases j <;> norm_num [he, AMPLowDeg.RankOne.hermNorm, Polynomial.hermite,
    Polynomial.derivative_mul, Nat.factorial] <;> ring

lemma he_meas (j : Fin 4) : Measurable (he j) := by
  simp_rw [funext (he_eq_normalized j)]
  unfold AMPLowDeg.RankOne.hermNorm; fun_prop

lemma he_int (j : Fin 4) : Integrable (he j) (gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  have T := (measurePreserving_funUnique μ (Fin 1)).symm.integrable_comp_of_integrable
    (coordH_int (d := 1) (fun _ => j.val))
  apply T.congr
  exact Eventually.of_forall fun s => by
    simpa [Function.comp_def, coordH, hermite, Fintype.prod_unique] using (he_eq_normalized j s).symm

end FiberChaos

end

section

open MeasureTheory ProbabilityTheory
namespace OneFiber
noncomputable abbrev γ := gaussianReal 0 1
end OneFiber

end

section

open MeasureTheory ProbabilityTheory GrothendieckLB FiberChaos OneFiber Filter Finset Real
namespace FiberDual

noncomputable def poly (a : Fin 4 → ℝ) (s : ℝ) : ℝ := ∑ j, a j * he j s
noncomputable def J (a : Fin 4 → ℝ) (c : ℝ) :=
  stdExp (fun s => max (|poly a s| - c*|s|) 0)
noncomputable def R := 3 * ABPOnline.cG / 2

lemma poly_int (a : Fin 4 → ℝ) : Integrable (poly a) γ :=
  integrable_finsetSum _ fun j _ => (he_int j).const_mul (a j)

end FiberDual

end

section

open MeasureTheory ProbabilityTheory Filter Set Finset Real
open scoped Topology

namespace HighBudget

noncomputable abbrev ν := ABPOnline.cG
noncomputable def E (t : ℝ) := Real.exp (-(t^2/2))
lemma ν_pos : 0 < ν := Real.sqrt_pos.mpr (by positivity)
lemma dE (t : ℝ) : HasDerivAt E (-(t * E t)) t := by
  convert! (((hasDerivAt_pow 2 t).div_const 2).neg.exp) using 1 <;> dsimp [E] <;> ring

end HighBudget

end

section

open GrothendieckLB FiberDual MeasureTheory ProbabilityTheory Real Finset Filter
namespace CubicEnvelope

noncomputable def evenP (a : Fin 4 → ℝ) (s : ℝ) := a 0 + a 2 * ((s^2-1)/Real.sqrt 2)
noncomputable def oddP (a : Fin 4 → ℝ) (s : ℝ) := a 1*s + a 3 * ((s^3-3*s)/Real.sqrt 6)
noncomputable def oddSq (a : Fin 4 → ℝ) := a 1 ^ 2 + a 3 ^ 2
noncomputable def amp (a : Fin 4 → ℝ) := Real.sqrt (3/2 * (1-oddSq a))
noncomputable def slope (a : Fin 4 → ℝ) := Real.sqrt (5/2 * oddSq a)
noncomputable def fold (a : Fin 4 → ℝ) (c s : ℝ) :=
  max (|poly a s| - c*s) 0 + max (|poly a (-s)| - c*s) 0

lemma poly_split (a : Fin 4 → ℝ) (s : ℝ) : poly a s = evenP a s + oddP a s := by
  simp [poly, Fin.sum_univ_four, he, evenP, oddP]; ring
lemma poly_neg (a : Fin 4 → ℝ) (s : ℝ) : poly a (-s) = evenP a s - oddP a s := by
  rw [poly_split]; unfold evenP oddP; ring

lemma odd_range {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) :
    0 ≤ oddSq a ∧ oddSq a ≤ 1 ∧ a 0 ^ 2 + a 2 ^ 2 = 1 - oddSq a := by
  rw [Fin.sum_univ_four] at ha
  unfold oddSq
  exact ⟨by positivity,by linarith only [ha,sq_nonneg (a 0),sq_nonneg (a 2)],by linarith only [ha]⟩

lemma amp_sq {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) :
    amp a ^ 2 = 3/2 * (1-oddSq a) := Real.sq_sqrt
  (mul_nonneg (by norm_num) (sub_nonneg.mpr (odd_range ha).2.1))
lemma slope_sq {a : Fin 4 → ℝ} : slope a ^ 2 = 5/2 * oddSq a :=
  Real.sq_sqrt (by unfold oddSq; positivity)

lemma kernel_sq (s : ℝ) : ∑ j : Fin 4, he j s ^ 2 = 3/2 + 3/2*s^2 - s^4/2 + s^6/6 := by
  simp only [Fin.sum_univ_four, he, one_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  ring

lemma poly_sq {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) (s : ℝ) :
    (poly a s)^2 ≤ 3/2 + 3/2*s^2 - s^4/2 + s^6/6 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (Fin 4))) a (fun j => he j s)
  simpa only [ha, kernel_sq, one_mul, poly] using h

lemma folded_mono (e o X Y t : ℝ) (he : |e| ≤ X) (ho : |o| ≤ Y) :
    max (|e+o|-t) 0 + max (|e-o|-t) 0 ≤ max (X+Y-t) 0 + max (|X-Y|-t) 0 := by
  have lemma1 (x y t : ℝ) :
      max (|x+y|-t) 0 + max (|x-y|-t) 0 =
      max (max (2*(|x|-t)) (2*(|y|-t))) (max (|x|+|y|-t) 0) := by
    grind [abs, max_def]
  rw [lemma1]
  have hX := (abs_nonneg e).trans he
  have hY := (abs_nonneg o).trans ho
  have hxy := lemma1 X Y t
  rw [abs_of_nonneg hX, abs_of_nonneg hY, abs_of_nonneg (add_nonneg hX hY)] at hxy
  rw [hxy]
  gcongr

lemma far_poly {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) {s : ℝ} (hs : 2 ≤ s) :
    |poly a s| ≤ s^3 ∧ |poly a (-s)| ≤ s^3 := by
  have h0 : 0 ≤ s := by linarith
  have t2 : (4:ℝ) ≤ s^2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hs 2
    norm_num at h
    exact h
  have t4 := mul_le_mul_of_nonneg_right t2 (sq_nonneg s)
  have t6 := mul_le_mul_of_nonneg_right t2 (sq_nonneg (s^2))
  constructor <;> apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (pow_nonneg h0 _)
  all_goals rw [sq_abs]
  · nlinarith only [poly_sq ha s,t2,t4,t6]
  · nlinarith only [poly_sq ha (-s),t2,t4,t6]

end CubicEnvelope

end

section

open Real Filter Set MeasureTheory ProbabilityTheory HighBudget Finset
open scoped Topology
namespace GaussianRemote

lemma gauss_tail (r : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun s : ℝ => s^3*E s) (Ioi r) ∧
    (∫ s in Ioi r, s^3*E s) = (r^2+2)*E r := by
  let F := fun s : ℝ => -((s^2+2)*E s)
  have hF (s : ℝ) : HasDerivAt F (s^3*E s) s := by
    convert! ((((hasDerivAt_pow 2 s).add_const 2).mul (dE s)).neg) using 1 <;> dsimp [F] <;> ring
  have ht : Tendsto (fun t : ℝ => t^2/2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num)
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h := ((h1.const_mul 2).add (h2.const_mul 2)).neg
    simpa only [mul_zero, add_zero, neg_zero] using h.congr (fun t => by dsimp [F,E]; ring)
  have nn (s : ℝ) (hs : s ∈ Ioi r) : 0 ≤ s^3*E s :=
    mul_nonneg (pow_nonneg (hr.trans (le_of_lt hs)) 3) (Real.exp_pos _).le
  exact ⟨integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hF s) nn hlim, by
    simpa [F] using integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => hF s) nn hlim⟩

end GaussianRemote

end

section

open Real Set Filter MeasureTheory ProbabilityTheory GrothendieckLB FiberChaos FiberDual OneFiber HighBudget
namespace CubicEnvelope

lemma density_constant : (Real.sqrt (2*π))⁻¹ * 2 = ABPOnline.cG := by
  change _ = Real.sqrt (2 / π)
  rw [← div_eq_inv_mul, div_eq_iff (by positivity), ← Real.sqrt_mul (by positivity), div_mul_eq_mul_div]
  have he : 2*(2*π)/π = 4 := by field_simp; ring
  rw [he]; norm_num

lemma folded_integral (a : Fin 4 → ℝ) (c : ℝ) :
    J a c = (ABPOnline.cG/2) * ∫ s in Ioi (0:ℝ), fold a c s * E s := by
  let g := fun s : ℝ => max (|poly a s|-c*|s|) 0
  have hg : Integrable g γ := ((poly_int a).abs.sub
    ((show Integrable (fun s : ℝ => |s|) γ from IsGaussian.integrable_id.abs).const_mul c)).sup
      (integrable_const 0)
  have hp : MeasurePreserving (fun s : ℝ => -s) γ γ :=
    ⟨measurable_neg, by simp [γ,gaussianReal_map_neg]⟩
  have hl : HasLaw (fun s : ℝ => -s) γ γ := ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have heq (s : ℝ) : g s + g (-s) = fold a c |s| := by
    by_cases hs : 0 ≤ s
    · simp [g,fold,abs_neg,abs_of_nonneg hs]
    · simp [g,fold,abs_neg,abs_of_neg (lt_of_not_ge hs),add_comm]
  have h2 : 2 * J a c = ∫ s, fold a c |s| ∂γ := by
    rw [two_mul,J,stdExp_eq]
    change (∫ s,g s ∂γ) + (∫ s,g s ∂γ) = _
    nth_rw 2 [← hl.integral_comp hg.aestronglyMeasurable]
    rw [← integral_add hg (hp.integrable_comp_of_integrable hg)]
    exact integral_congr_ae (Eventually.of_forall heq)
  have den (s) : gaussianPDFReal 0 1 s • fold a c |s| =
      (Real.sqrt (2*π))⁻¹ * (fold a c |s| * E |s|) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul,E,sq_abs,neg_div]
    ring
  change 2*J a c = ∫ s, fold a c |s| ∂(gaussianReal 0 1) at h2
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero] at h2
  simp only [den, integral_const_mul] at h2
  rw [integral_comp_abs (f := fun s => fold a c s * E s), ← mul_assoc,density_constant] at h2
  linarith only [h2]

end CubicEnvelope

end

section

open MeasureTheory ProbabilityTheory Real Filter Set Finset GrothendieckLB FiberDual
open HighBudget GaussianRemote CubicEnvelope

namespace PanelMath

noncomputable def priced (a : Fin 4 → ℝ) (z T : ℝ) := max (|poly a z|-T) 0 + max (|poly a (-z)|-T) 0

lemma poly_cont (a : Fin 4 → ℝ) : Continuous (poly a) := by
  rw [funext (poly_split a)]; unfold evenP oddP; fun_prop

lemma fold_cont (a : Fin 4 → ℝ) (c : ℝ) : Continuous (CubicEnvelope.fold a c) := by
  unfold CubicEnvelope.fold
  have hp := poly_cont a
  fun_prop

lemma cubic_chord (a : Fin 4 → ℝ) (l z h : ℝ) {v : ℝ} (hz : z = (1-v)*l+v*h) :
    poly a z - ((1-v)*poly a l+v*poly a h) =
      (z-l)*(z-h)*(a 2/Real.sqrt 2+a 3*(z+l+h)/Real.sqrt 6) := by
  rw [hz];simp only [poly_split,evenP,oddP];ring

lemma error_bound {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1)
    {l z h v : ℝ} (hl : 0 ≤ l) (hz : l ≤ z) (hh : z ≤ h) (hv : z = (1-v)*l+v*h) :
    |poly a z - ((1-v)*poly a l+v*poly a h)| ≤ (1+2*h)*(h-l)^2/4 ∧
    |poly a (-z) - ((1-v)*poly a (-l)+v*poly a (-h))| ≤ (1+2*h)*(h-l)^2/4 := by
  have h0 : 0 ≤ z := hl.trans hz
  have h1 : 0 ≤ h := h0.trans hh
  have hc (j : Fin 4) : |a j| ≤ 1 := by
    have hs := single_le_sum (s := (univ : Finset (Fin 4))) (f := fun i => a i ^ 2)
      (fun i _ => sq_nonneg (a i)) (mem_univ j)
    rw [ha] at hs
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) zero_le_one (by simpa only [sq_abs,one_pow] using hs)
  have hpos2 : (1:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hpos6 : (2:ℝ) ≤ Real.sqrt 6 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc2 : |a 2 / Real.sqrt 2| ≤ 1 := by
    rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _),div_le_one (by positivity)]; exact (hc 2).trans hpos2
  have sumpos : 0 ≤ z+l+h := by linarith only [h0,hl,h1]
  have hc3 : |a 3 * (z+l+h) / Real.sqrt 6| ≤ 2*h := by
    rw [abs_div,abs_mul,abs_of_nonneg sumpos,abs_of_nonneg (Real.sqrt_nonneg _),div_le_iff₀ (by positivity)]
    have hh1 := mul_le_mul_of_nonneg_right (hc 3) sumpos
    have hh2 := mul_le_mul_of_nonneg_left hpos6 (by linarith only [h1] : 0 ≤ 2*h)
    linarith only [hh1,hh2,hz,hh,h1]
  have q : |(z-l)*(z-h)| ≤ (h-l)^2/4 := by
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hz),abs_of_nonpos (sub_nonpos.mpr hh)]
    nlinarith only [sq_nonneg (2*z-l-h)]
  have common {w : ℝ} (hw : |w| ≤ 1+2*h) :
      |(z-l)*(z-h)*w| ≤ (1+2*h)*(h-l)^2/4 := by
    rw [abs_mul]; have h' := mul_le_mul q hw (abs_nonneg _) (by positivity)
    linarith only [h']
  constructor
  · rw [cubic_chord a l z h hv];apply common
    exact (abs_add_le _ _).trans (add_le_add hc2 hc3)
  · rw [cubic_chord a (-l) (-z) (-h) (by rw [hv];ring)]
    rw [show (-z - -l)*(-z - -h)=(z-l)*(z-h) by ring]
    apply common
    apply (abs_add_le _ _).trans
    have H : a 3 * (-z + -l + -h) / Real.sqrt 6 = -(a 3*(z+l+h)/Real.sqrt 6) := by ring
    simpa only [H,abs_neg] using add_le_add hc2 hc3

lemma convex_charge (p p₀ p₁ l z h c v δ : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (hz : z = (1-v)*l+v*h) (hp : |p - ((1-v)*p₀+v*p₁)| ≤ δ) :
    max (|p|-c*z) 0 ≤ (1-v)*max (|p₀|-(c*l-δ)) 0 + v*max (|p₁|-(c*h-δ)) 0 := by
  have w0 := sub_nonneg.mpr h1
  have H := abs_add_le (p-((1-v)*p₀+v*p₁)) ((1-v)*p₀+v*p₁)
  rw [sub_add_cancel] at H
  have Hp := (abs_add_le ((1-v)*p₀) (v*p₁))
  rw [abs_mul,abs_mul,abs_of_nonneg w0,abs_of_nonneg h0] at Hp
  have H0 := mul_le_mul_of_nonneg_left (le_max_left (|p₀|-(c*l-δ)) 0) w0
  have H1 := mul_le_mul_of_nonneg_left (le_max_left (|p₁|-(c*h-δ)) 0) h0
  rw [hz]
  apply max_le
  · nlinarith only [H,Hp,hp,H0,H1]
  · exact add_nonneg (mul_nonneg w0 (le_max_right _ _)) (mul_nonneg h0 (le_max_right _ _))

lemma interval_dom {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) (c l h L U δ : ℝ)
    (hl : 0 ≤ l) (hh : l < h) (hδ : (1+2*h)*(h-l)^2/4 ≤ δ)
    (hL : priced a l (c*l-δ) ≤ L) (hU : priced a h (c*h-δ) ≤ U) :
    (∫ s in l..h, CubicEnvelope.fold a c s * E s) ≤ ((h-l)/2*(L+U))*E l := by
  let f := fun s : ℝ => (1-(s-l)/(h-l))*L + (s-l)/(h-l)*U
  have cf : Continuous f := by dsimp [f];fun_prop
  have hfit : Continuous (fun s => CubicEnvelope.fold a c s * E s) :=
    (fold_cont a c).mul (show Continuous E by unfold E;fun_prop)
  have Hb : (∫ s in l..h, CubicEnvelope.fold a c s * E s) ≤ ∫ s in l..h, f s * E l := by
    apply intervalIntegral.integral_mono_on hh.le (hfit.intervalIntegrable _ _)
      ((cf.mul continuous_const).intervalIntegrable _ _)
    intro s hs
    let v := (s-l)/(h-l)
    have v0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hh).le
    have v1 : v ≤ 1 := (div_le_one (sub_pos.mpr hh)).mpr (by linarith only [hs.2])
    have hv : s = (1-v)*l+v*h := by dsimp [v];field_simp [sub_ne_zero.mpr hh.ne'];ring
    have err := error_bound ha hl hs.1 hs.2 hv
    have b1 := convex_charge (poly a s) (poly a l) (poly a h) l s h c v δ v0 v1 hv (err.1.trans hδ)
    have b2 := convex_charge (poly a (-s)) (poly a (-l)) (poly a (-h)) l s h c v δ v0 v1 hv (err.2.trans hδ)
    have hf : CubicEnvelope.fold a c s ≤ f s := by
      have L' := mul_le_mul_of_nonneg_left hL (sub_nonneg.mpr v1)
      have U' := mul_le_mul_of_nonneg_left hU v0
      unfold priced at L' U'
      change _ ≤ (1-v)*L+v*U
      unfold CubicEnvelope.fold
      linarith only [b1,b2,L',U']
    have he : E s ≤ E l := Real.exp_le_exp.mpr (by
      have hr := pow_le_pow_left₀ hl hs.1 2
      change -(s^2/2) ≤ -(l^2/2);linarith)
    exact mul_le_mul hf he (Real.exp_pos _).le
      ((add_nonneg (le_max_right _ _) (le_max_right _ _)).trans hf)
  have hint : (∫ s in l..h, f s) = (h-l)/2*(L+U) := by
    let F := fun s : ℝ => L*s + (U-L)/(h-l)*(s-l)^2/2
    have D (s) : HasDerivAt F (f s) s := by
      convert! (((hasDerivAt_id s).const_mul L).add
        ((((hasDerivAt_id s).sub_const l).pow 2).const_mul ((U-L)/(h-l)) |>.div_const 2)) using 1
      dsimp [f]; field_simp [sub_ne_zero.mpr hh.ne'];ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => D s) (cf.intervalIntegrable _ _)]
    dsimp [F];field_simp [sub_ne_zero.mpr hh.ne'];ring
  rw [intervalIntegral.integral_mul_const,hint] at Hb
  exact Hb

end PanelMath

end

section

open Real Finset CubicEnvelope PanelMath GrothendieckLB.DualQuadrature

namespace PanelParams

noncomputable def h₂ (s : ℝ) := (s^2-1)/Real.sqrt 2
noncomputable def kE (s : ℝ) := Real.sqrt (1+(s^2-1)^2/2)
noncomputable def kO (s : ℝ) := Real.sqrt (s^2+(s^3-3*s)^2/6)

structure Parameters (a : Fin 4 → ℝ) where
  e : ℝ
  d : ℝ
  x : ℝ
  y : ℝ
  he : 0 ≤ e
  hd : 0 ≤ d
  hx : 0 ≤ x
  heSq : e^2+d^2=1
  hxSq : x^2+y^2=1
  evenExact : ∀ s, |evenP a s| = e*|x+y*h₂ s|
  oddLe : ∀ s, |oddP a s| ≤ d*kO s

lemma parameters {a : Fin 4 → ℝ} (ha : ∑ j, a j^2 = 1) : Nonempty (Parameters a) := by
  let e := Real.sqrt (a 0^2+a 2^2)
  let d := Real.sqrt (a 1^2+a 3^2)
  have e0 : 0 ≤ e := Real.sqrt_nonneg _
  have d0 : 0 ≤ d := Real.sqrt_nonneg _
  have es : e^2=a 0^2+a 2^2 := Real.sq_sqrt (by positivity)
  have ds : d^2=a 1^2+a 3^2 := Real.sq_sqrt (by positivity)
  rw [Fin.sum_univ_four] at ha
  have ed : e^2+d^2=1 := by linarith only [es,ds,ha]
  have oddLe (s : ℝ) : |oddP a s| ≤ d*kO s := by
    apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg d0 (Real.sqrt_nonneg _))
    rw [sq_abs,mul_pow,ds,Real.sq_sqrt (by positivity)]
    let u := (s^3-3*s)/Real.sqrt 6
    have hu : u^2=(s^3-3*s)^2/6 := by simp [u,div_pow,Real.sq_sqrt]
    change (a 1*s+a 3*u)^2 ≤ _
    rw [← hu]
    nlinarith only [sq_nonneg (a 1*u-a 3*s)]
  by_cases ez : e=0
  · have a0 : a 0=0 := by nlinarith only [es,ez,sq_nonneg (a 2),sq_nonneg (a 0)]
    have a2 : a 2=0 := by nlinarith only [es,ez,sq_nonneg (a 0),sq_nonneg (a 2)]
    exact ⟨⟨e,d,1,0,e0,d0,zero_le_one,ed,by norm_num,fun s => by simp [evenP,a0,a2,ez],oddLe⟩⟩
  · have hxys : (a 0/e)^2+(a 2/e)^2=1 := by field_simp [ez];linarith only [es]
    have heq (s : ℝ) : |evenP a s|=e*|a 0/e+(a 2/e)*h₂ s| := by
      rw [← abs_of_nonneg e0,← abs_mul]
      congr 1
      change a 0+a 2*h₂ s=_
      field_simp [ez]
      rw [abs_of_nonneg e0]
    by_cases h : 0 ≤ a 0
    · exact ⟨⟨e,d,a 0/e,a 2/e,e0,d0,div_nonneg h e0,ed,hxys,heq,oddLe⟩⟩
    · refine ⟨⟨e,d,-(a 0/e),-(a 2/e),e0,d0,neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) e0),
        ed,by simpa using hxys,?_,oddLe⟩⟩
      intro s
      rw [heq,neg_mul,← neg_add,abs_neg]

lemma evenLe {a : Fin 4 → ℝ} (p : Parameters a) (s : ℝ) : |evenP a s| ≤ p.e*kE s := by
  rw [p.evenExact]
  apply mul_le_mul_of_nonneg_left _ p.he
  apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (Real.sqrt_nonneg _)
  have hu : (h₂ s)^2=(s^2-1)^2/2 := by simp [h₂,div_pow,Real.sq_sqrt]
  rw [sq_abs,Real.sq_sqrt (by positivity),← hu]
  have h := congrArg (fun t : ℝ => t*(1+(h₂ s)^2)) p.hxSq
  nlinarith only [h,sq_nonneg (p.x*h₂ s-p.y)]

noncomputable abbrev S : ℝ := 8388608
noncomputable def val (n : Int) : ℝ := (n:ℝ)/S

structure NodeBounds (n : Node) : Prop where
  h₂lo : val n.lo ≤ h₂ (val n.pos)
  h₂hi : h₂ (val n.pos) ≤ val n.hi
  even : kE (val n.pos) ≤ val n.even
  odd : kO (val n.pos) ≤ val n.odd
  dens : HighBudget.E (val n.pos) ≤ val n.dens

structure Fits {a : Fin 4 → ℝ} (p : Parameters a) (b : Box) : Prop where
  e : p.e ≤ val b.e
  d : p.d ≤ val b.d
  xmin : val b.xmin ≤ p.x
  xmax : p.x ≤ val b.xmax
  ymin : val b.ymin ≤ p.y
  ymax : p.y ≤ val b.ymax

lemma mul_box {a b c d x y : ℝ} (ha : a≤x) (hb : x≤b) (hc : c≤y) (hd : y≤d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  constructor
  · by_cases hy : 0 ≤ y
    · have H := mul_le_mul_of_nonneg_right ha hy
      by_cases ha' : 0 ≤ a
      · exact ((min_le_left _ _).trans (min_le_left _ _)).trans ((mul_le_mul_of_nonneg_left hc ha').trans H)
      · exact ((min_le_left _ _).trans (min_le_right _ _)).trans ((mul_le_mul_of_nonpos_left hd (le_of_not_ge ha')).trans H)
    · have H := mul_le_mul_of_nonpos_right hb (le_of_not_ge hy)
      by_cases hb' : 0 ≤ b
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans ((mul_le_mul_of_nonneg_left hc hb').trans H)
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans ((mul_le_mul_of_nonpos_left hd (le_of_not_ge hb')).trans H)
  · by_cases hy : 0 ≤ y
    · have H := mul_le_mul_of_nonneg_right hb hy
      by_cases hb' : 0 ≤ b
      · exact H.trans ((mul_le_mul_of_nonneg_left hd hb').trans ((le_max_right _ _).trans (le_max_right _ _)))
      · exact H.trans ((mul_le_mul_of_nonpos_left hc (le_of_not_ge hb')).trans ((le_max_left _ _).trans (le_max_right _ _)))
    · have H := mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)
      by_cases ha' : 0 ≤ a
      · exact H.trans ((mul_le_mul_of_nonneg_left hd ha').trans ((le_max_right _ _).trans (le_max_left _ _)))
      · exact H.trans ((mul_le_mul_of_nonpos_left hc (le_of_not_ge ha')).trans ((le_max_left _ _).trans (le_max_left _ _)))

end PanelParams

end

section

open Real CubicEnvelope PanelMath GrothendieckLB.DualQuadrature PanelParams
namespace PanelHeight

lemma sPos : (0:ℝ)<S := by norm_num
lemma up {v : ℝ} {n : Int} (h : v ≤ val n) : v*S ≤ (n:ℝ) := (le_div_iff₀ sPos).mp h
lemma dn {v : ℝ} {n : Int} (h : val n ≤ v) : (n:ℝ) ≤ v*S := (div_le_iff₀ sPos).mp h

lemma boundX {a : Fin 4 → ℝ} (p : Parameters a) (n : Node) (b : Box)
    (hn : NodeBounds n) (hb : Fits p b) :
    |evenP a (val n.pos)| *S^3 ≤ (xbound b n:ℝ) := by
  let z := val n.pos
  have he := up hb.e
  have be0 : 0 ≤ (b.e:ℝ) := (mul_nonneg p.he sPos.le).trans he
  cases hf : b.full
  · simp only [xbound,hf,Bool.false_eq_true,↓reduceIte,Int.cast_mul,scale,Int.cast_ofNat]
    have h := mul_le_mul he (up hn.even)
      (mul_nonneg (Real.sqrt_nonneg _) sPos.le) be0
    have h' := mul_le_mul_of_nonneg_right (evenLe p z) (sq_nonneg S)
    exact (show |evenP a z| *S^3 ≤ (b.e:ℝ)*(n.even:ℝ)*S by
      have h2 : |evenP a z| *S^2 ≤ (b.e:ℝ)*(n.even:ℝ) := by nlinarith only [h,h']
      nlinarith only [mul_le_mul_of_nonneg_right h2 sPos.le])
  · simp only [xbound,hf,↓reduceIte,Int.cast_mul,Int.cast_add,Int.cast_neg,Int.cast_max,Int.cast_min,scale,Int.cast_ofNat]
    let P : ℝ := max (max ((b.ymin:ℝ)*n.lo) ((b.ymin:ℝ)*n.hi)) (max ((b.ymax:ℝ)*n.lo) ((b.ymax:ℝ)*n.hi))
    let Q : ℝ := min (min ((b.ymin:ℝ)*n.lo) ((b.ymin:ℝ)*n.hi)) (min ((b.ymax:ℝ)*n.lo) ((b.ymax:ℝ)*n.hi))
    let X : ℝ := max ((b.xmax:ℝ)*S+P) (-((b.xmin:ℝ)*S+Q))
    have hm := mul_box (dn hb.ymin) (up hb.ymax) (dn hn.h₂lo) (up hn.h₂hi)
    change Q ≤ (p.y*S)*(h₂ z*S) ∧ (p.y*S)*(h₂ z*S) ≤ P at hm
    have hi : (p.x+p.y*h₂ z)*S^2 ≤ (b.xmax:ℝ)*S+P := by
      nlinarith only [hm.2,mul_le_mul_of_nonneg_right (up hb.xmax) sPos.le]
    have lo : (b.xmin:ℝ)*S+Q ≤ (p.x+p.y*h₂ z)*S^2 := by
      nlinarith only [hm.1,mul_le_mul_of_nonneg_right (dn hb.xmin) sPos.le]
    have ha : |p.x+p.y*h₂ z| *S^2 ≤ X := by
      rw [← abs_of_nonneg (sq_nonneg S),← abs_mul,abs_le]
      constructor
      · have H := le_max_right ((b.xmax:ℝ)*S+P) (-((b.xmin:ℝ)*S+Q))
        dsimp [X];linarith only [lo,H]
      · exact hi.trans (le_max_left _ _)
    have h := mul_le_mul he ha (mul_nonneg (abs_nonneg _) (sq_nonneg S)) be0
    change |evenP a z| *S^3 ≤ (b.e:ℝ)*X
    rw [p.evenExact]
    nlinarith only [h]

lemma boundY {a : Fin 4 → ℝ} (p : Parameters a) (n : Node) (b : Box)
    (hn : NodeBounds n) (hb : Fits p b) : |oddP a (val n.pos)| *S^3 ≤ (b.d:ℝ)*n.odd*S := by
  let z := val n.pos
  have hd := up hb.d
  have bd0 : 0 ≤ (b.d:ℝ) := (mul_nonneg p.hd sPos.le).trans hd
  have h := mul_le_mul hd (up hn.odd) (mul_nonneg (Real.sqrt_nonneg _) sPos.le) bd0
  have h' := mul_le_mul_of_nonneg_right (p.oddLe z) (sq_nonneg S)
  have h2 : |oddP a z| *S^2 ≤ (b.d:ℝ)*(n.odd:ℝ) := by nlinarith only [h,h']
  nlinarith only [mul_le_mul_of_nonneg_right h2 sPos.le]

lemma priced_formula (x y t : ℝ) :
  max (|x+y|-t) 0 + max (|x-y|-t) 0 =
    max 0 (max (|x|+|y|-t) (2*(max |x| |y|-t))) := by
  grind [abs,max_def]

lemma height_dom {a : Fin 4 → ℝ} (p : Parameters a) {n : Node} {b : Box} (hn : NodeBounds n)
    (hb : Fits p b) (c δ : ℝ) (k : Int) (hc : val k ≤ c) (hs : 0 ≤ val n.pos) (hδ : δ ≤ val n.err) :
    priced a (val n.pos) (c*val n.pos-δ) ≤ (height b k n:ℝ)/S^3 := by
  let z := val n.pos
  let T := c*z-δ
  let τ : ℝ := ((k:ℝ)*n.pos-(n.err:ℝ)*S)*S
  have hT : τ ≤ T*S^3 := by
    have H := mul_le_mul_of_nonneg_right hc hs
    change (k:ℝ)/S*z ≤ c*z at H
    change δ ≤ (n.err:ℝ)/S at hδ
    change ((k:ℝ)*n.pos-(n.err:ℝ)*S)*S ≤ (c*z-δ)*S^3
    have H' : (k:ℝ)/S*z- (n.err:ℝ)/S ≤ c*z-δ := sub_le_sub H hδ
    have hh := mul_le_mul_of_nonneg_right H' (pow_nonneg sPos.le 3)
    dsimp [z,val,S] at hh ⊢
    linarith only [hh]
  rw [le_div_iff₀ (pow_pos sPos 3),priced,poly_split,poly_neg,priced_formula]
  simp only [height,Int.cast_max,Int.cast_zero,Int.cast_mul,Int.cast_add,Int.cast_sub,Int.cast_ofNat,scale]
  let X : ℝ := xbound b n
  let Y : ℝ := (b.d:ℝ)*n.odd*S
  change max 0 (max (|evenP a z|+|oddP a z|-T) (2*(max |evenP a z| |oddP a z|-T)))*S^3 ≤ max 0 (max (X+Y-τ) (2*(max X Y-τ)))
  have hX := boundX p n b hn hb
  have hY := boundY p n b hn hb
  change |evenP a z| *S^3 ≤ X at hX
  change |oddP a z| *S^3 ≤ Y at hY
  have sc := pow_nonneg sPos.le 3
  rw [max_mul_of_nonneg _ _ sc,max_mul_of_nonneg _ _ sc,zero_mul]
  apply max_le_max le_rfl
  apply max_le_max
  · linarith only [hX,hY,hT]
  · have hh : max |evenP a z| |oddP a z| *S^3 ≤ max X Y := by
      rw [max_mul_of_nonneg _ _ sc];exact max_le_max hX hY
    linarith only [hh,hT]

end PanelHeight

end

section

open GrothendieckLB.DualQuadrature PanelParams Real HighBudget
namespace PanelAudit

@[simp, norm_cast] lemma qval_cast (n : Int) : (qval n : ℝ) = val n := by
  simp [qval,val,S]
noncomputable def price (k : Int) : ℝ := (k:ℝ)/1000000
@[simp, norm_cast] lemma qprice_cast (k : Int) : (qprice k : ℝ) = price k := by
  simp [qprice,price]

lemma taylorSum_eq (x : ℚ) (n : ℕ) :
    taylorSum x n = ∑ i ∈ Finset.range n, x^i / (i.factorial : ℚ) := by
  induction n with
  | zero => simp [taylorSum]
  | succ n ih => rw [taylorSum, Finset.sum_range_succ, ih]

lemma node_sound {n : Node} (h : nodeCheck n = true) :
    0 ≤ val n.pos ∧ NodeBounds n := by
  simp only [nodeCheck,decide_eq_true_eq] at h
  rcases h with ⟨hp,he,ho,hd,hL,hU,he2,ho2,hD⟩
  have posv {i : Int} (hi : 0 ≤ i) : 0 ≤ val i := div_nonneg (by exact_mod_cast hi) (by norm_num)
  have castL := (Rat.cast_le (K:=ℝ)).mpr hL
  have castU := (Rat.cast_le (K:=ℝ)).mpr hU
  have castE := (Rat.cast_le (K:=ℝ)).mpr he2
  have castO := (Rat.cast_le (K:=ℝ)).mpr ho2
  have castD := (Rat.cast_le (K:=ℝ)).mpr hD
  push_cast [qval_cast,taylor,taylorSum_eq] at castL castU castE castO castD
  let s := val n.pos
  let u : ℝ := (Real.sqrt 2)⁻¹
  have usq : u^2 = 1/2 := by dsimp [u];rw [inv_pow,Real.sq_sqrt (by norm_num)];norm_num
  have ulo : val 5931641 ≤ u := le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by dsimp [u];positivity)
    (by rw [usq];norm_num [val,S])
  have uhi : u ≤ val 5931642 := le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by norm_num [val,S])
    (by rw [usq];norm_num [val,S])
  have bounds : min ((s^2-1)*val 5931641) ((s^2-1)*val 5931642) ≤ h₂ s ∧
      h₂ s ≤ max ((s^2-1)*val 5931641) ((s^2-1)*val 5931642) := by
    change _ ≤ (s^2-1)*u ∧ (s^2-1)*u ≤ _
    by_cases H : 0 ≤ s^2-1
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ulo H),
        (mul_le_mul_of_nonneg_left uhi H).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left uhi (le_of_not_ge H)),
        (mul_le_mul_of_nonpos_left ulo (le_of_not_ge H)).trans (le_max_left _ _)⟩
  refine ⟨posv hp,castL.trans bounds.1,bounds.2.trans castU,
    (Real.sqrt_le_iff).mpr ⟨posv he,castE⟩,(Real.sqrt_le_iff).mpr ⟨posv ho,castO⟩,?_⟩
  have H := Real.sum_le_exp_of_nonneg (x:=s^2/2) (by positivity) 21
  have hprod := mul_le_mul_of_nonneg_left H (posv hd)
  change Real.exp (-(s^2/2)) ≤ val n.dens
  rw [Real.exp_neg,inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  exact castD.trans hprod

lemma edge_sound {n m : Node} (h : edgeCheck n m=true) :
    val n.pos < val m.pos ∧ (1+2*val m.pos)*(val m.pos-val n.pos)^2/4 ≤ val n.err ∧
    (1+2*val m.pos)*(val m.pos-val n.pos)^2/4 ≤ val m.err := by
  simp only [edgeCheck,decide_eq_true_eq] at h
  have h1 := (Rat.cast_lt (K:=ℝ)).mpr h.1
  have h2 := (Rat.cast_le (K:=ℝ)).mpr h.2.1
  have h3 := (Rat.cast_le (K:=ℝ)).mpr h.2.2
  push_cast [qval_cast] at h1 h2 h3
  exact ⟨h1,h2,h3⟩

end PanelAudit

end

section

open GrothendieckLB.DualQuadrature PanelParams Real
namespace PanelGeometry

structure InSpan {a : Fin 4 → ℝ} (p : Parameters a) (w : Span) : Prop where
  dl : (w.dl:ℝ) ≤ p.d*S
  du : p.d*S ≤ (w.du:ℝ)
  yl : (w.yl:ℝ) ≤ p.y*S
  yu : p.y*S ≤ (w.yu:ℝ)

lemma whole {a : Fin 4 → ℝ} (p : Parameters a) : InSpan p entire := by
  have dd : p.d ≤ 1 := le_of_pow_le_pow_left₀ (n:=2) (by norm_num) zero_le_one
    (by nlinarith only [p.heSq,sq_nonneg p.e])
  have yy : |p.y| ≤ 1 := le_of_pow_le_pow_left₀ (n:=2) (by norm_num) zero_le_one
    (by rw [sq_abs];nlinarith only [p.hxSq,sq_nonneg p.x])
  have yl := (abs_le.mp yy).1
  have yu := (abs_le.mp yy).2
  constructor <;> norm_num [entire,scale,S] <;> nlinarith only [p.hd,dd,yl,yu]

lemma geom_sound {a : Fin 4 → ℝ} (p : Parameters a) {w : Span} {b : Box}
    (hw : InSpan p w) (hb : geom w b=true) : Fits p b := by
  simp only [geom,decide_eq_true_eq] at hb
  rcases hb with ⟨dl0,be,hE,hD,bx,hX,hx,hyl,hyu⟩
  let q : ℝ := max 0 (max (w.yl:ℝ) (-(w.yu:ℝ)))
  let r : ℝ := max (-(w.yl:ℝ)) (w.yu:ℝ)
  have hq : q ≤ |p.y*S| :=
    max_le (abs_nonneg _) (max_le (hw.yl.trans (le_abs_self _)) ((neg_le_neg hw.yu).trans (neg_le_abs _)))
  have hr : |p.y*S| ≤ r := abs_le.mpr ⟨by
    have H := le_max_left (-(w.yl:ℝ)) (w.yu:ℝ)
    dsimp [r];linarith only [H,hw.yl],hw.yu.trans (le_max_right _ _)⟩
  have hq0 : 0 ≤ q := le_max_left _ _
  have h0 : 0 < S := by norm_num
  have eq1 : (p.e*S)^2+(p.d*S)^2=S^2 := by nlinarith only [congrArg (fun x : ℝ => x*S^2) p.heSq]
  have eq2 : (p.x*S)^2+(p.y*S)^2=S^2 := by nlinarith only [congrArg (fun x : ℝ => x*S^2) p.hxSq]
  have sq1 : (w.dl:ℝ)^2 ≤ (p.d*S)^2 := pow_le_pow_left₀ (by exact_mod_cast dl0) hw.dl 2
  have sq2 := pow_le_pow_left₀ hq0 hq 2
  have sq3 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [sq_abs] at sq2 sq3
  norm_num only [scale] at hE hX hx
  have bE : S^2 ≤ (b.e:ℝ)^2+(w.dl:ℝ)^2 := by dsimp [S];exact_mod_cast hE
  have bX : S^2 ≤ (b.xmax:ℝ)^2+q^2 := by dsimp [q,S];exact_mod_cast hX
  have bx' : (b.xmin:ℝ)^2+r^2 ≤ S^2 := by dsimp [r,S];exact_mod_cast hx
  constructor
  · apply (le_div_iff₀ h0).mpr
    exact le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by exact_mod_cast be) (by linarith only [bE,eq1,sq1])
  · apply (le_div_iff₀ h0).mpr;exact hw.du.trans (by exact_mod_cast hD)
  · apply (div_le_iff₀ h0).mpr
    exact le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg p.hx h0.le)
      (by linarith only [bx',eq2,sq3])
  · apply (le_div_iff₀ h0).mpr
    exact le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by exact_mod_cast bx)
      (by linarith only [bX,eq2,sq2])
  · apply (div_le_iff₀ h0).mpr;exact (show (b.ymin:ℝ) ≤ (w.yl:ℝ) by exact_mod_cast hyl).trans hw.yl
  · apply (le_div_iff₀ h0).mpr;exact hw.yu.trans (by exact_mod_cast hyu)

lemma tree_sound {a : Fin 4 → ℝ} (p : Parameters a) {ns : List Node} {v : Band} {w : Span}
    (t : Tree) (hw : InSpan p w) (ht : treeCheck ns v w t=true) :
    ∃ b, Fits p b ∧ endpoint ns b v.clo v.L=true ∧ endpoint ns b v.chi v.H=true := by
  induction t generalizing w with
  | leaf b =>
    simp only [treeCheck,Bool.and_eq_true] at ht
    exact ⟨b,geom_sound p hw ht.1.1,ht.1.2,ht.2⟩
  | d k l r ihl ihr =>
    simp only [treeCheck,Bool.and_eq_true] at ht
    rcases le_total (p.d*S) (k:ℝ) with h|h
    · exact ihl (w:={w with du:=k}) ⟨hw.dl,h,hw.yl,hw.yu⟩ ht.1
    · exact ihr (w:={w with dl:=k}) ⟨h,hw.du,hw.yl,hw.yu⟩ ht.2
  | y k l r ihl ihr =>
    simp only [treeCheck,Bool.and_eq_true] at ht
    rcases le_total (p.y*S) (k:ℝ) with h|h
    · exact ihl (w:={w with yu:=k}) ⟨hw.dl,hw.du,hw.yl,h⟩ ht.1
    · exact ihr (w:={w with yl:=k}) ⟨hw.dl,hw.du,h,hw.yu⟩ ht.2

end PanelGeometry

end

section

open MeasureTheory Real Set Filter HighBudget CubicEnvelope GrothendieckLB.DualQuadrature PanelMath PanelParams PanelHeight PanelAudit
namespace PanelChain

lemma chain {a : Fin 4 → ℝ} (p : Parameters a) (ha : ∑ j, a j^2=1) {b : Box}
    (hb : Fits p b) (c : ℝ) (k : Int) (hc : val k ≤ c) (n : Node) (ns : List Node)
    (hh : chainCheck (n::ns)=true) :
    (∫ s in val n.pos..(8:ℝ), fold a c s*E s) ≤ (total b k (n::ns):ℝ)/(2*S^5) := by
  induction ns generalizing n with
  | nil =>
    simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    have he : val n.pos=8 := by norm_num [val,hh.2,scale,S]
    simp [he,total,segments]
  | cons m ns ih =>
    simp only [chainCheck,Bool.and_eq_true] at hh
    have hn := node_sound hh.1.1
    have hed := edge_sound hh.1.2
    have hm : nodeCheck m=true := by
      cases ns with
      | nil => exact (Bool.and_eq_true_iff.mp hh.2).1
      | cons t ts => exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hh.2).1).1
    have hm' := node_sound hm
    let l := val n.pos
    let h := val m.pos
    let δ := (1+2*h)*(h-l)^2/4
    let L := (height b k n:ℝ)/S^3
    let U := (height b k m:ℝ)/S^3
    have hl : priced a l (c*l-δ) ≤ L := height_dom p hn.2 hb c δ k hc hn.1 hed.2.1
    have hu : priced a h (c*h-δ) ≤ U := height_dom p hm'.2 hb c δ k hc hm'.1 hed.2.2
    have i1 := interval_dom ha c l h L U δ hn.1 hed.1 le_rfl hl hu
    have i2 := ih m hh.2
    have cf : Continuous (fun s => fold a c s*E s) := (fold_cont a c).mul (show Continuous E by unfold E;fun_prop)
    have hpos : 0 ≤ (h-l)/2*(L+U) := mul_nonneg (div_nonneg (sub_nonneg.mpr hed.1.le) (by norm_num))
      (add_nonneg ((add_nonneg (le_max_right _ _) (le_max_right _ _)).trans hl)
        ((add_nonneg (le_max_right _ _) (le_max_right _ _)).trans hu))
    have ib := i1.trans (mul_le_mul_of_nonneg_left hn.2.dens hpos)
    rw [← intervalIntegral.integral_add_adjacent_intervals (b:=h)
      (cf.intervalIntegrable _ _) (cf.intervalIntegrable _ _)]
    refine (add_le_add ib i2).trans_eq ?_
    simp only [total,segments,Int.cast_add,Int.cast_mul,Int.cast_sub]
    dsimp [l,h,L,U,val,S]
    ring

lemma tail {a : Fin 4 → ℝ} (ha : ∑ j, a j^2=1) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun s => fold a c s*E s) (Ioi (8:ℝ)) ∧
    (∫ s in Ioi (8:ℝ), fold a c s*E s) ≤ 1/100000000 := by
  let f := fun s : ℝ => fold a c s * E s
  have cf : Continuous f := (fold_cont a c).mul (show Continuous E by unfold E;fun_prop)
  have hg := GaussianRemote.gauss_tail 8 (by norm_num)
  have hi := hg.1.const_mul 2
  have nn (s : ℝ) : 0 ≤ f s :=
    mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _)) (Real.exp_pos _).le
  have hmaj (s : ℝ) (hs : 8<s) : f s ≤ 2*(s^3*E s) := by
    have hz : 0 ≤ s := by linarith
    have H := far_poly ha (by linarith only [hs] : 2 ≤ s)
    have hcs := mul_nonneg hc hz
    have hsp := pow_nonneg hz 3
    have h1 : max (|FiberDual.poly a s|-c*s) 0 ≤ s^3 := max_le (by linarith only [H.1,hcs]) hsp
    have h2 : max (|FiberDual.poly a (-s)|-c*s) 0 ≤ s^3 := max_le (by linarith only [H.2,hcs]) hsp
    have H' : fold a c s ≤ 2*s^3 := by unfold fold;linarith only [h1,h2]
    have h' := mul_le_mul_of_nonneg_right H' (Real.exp_pos (-(s^2/2))).le
    change fold a c s*E s ≤ _
    calc _ ≤ (2*s^3)*E s := h'
      _ = _ := by ring
  have hAE := (ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(8:ℝ)))).mono
    (fun s hs => hmaj s hs)
  have hfi : IntegrableOn f (Ioi (8:ℝ)) :=
    hi.mono' cf.aestronglyMeasurable (hAE.mono fun s hs => by simpa [Real.norm_eq_abs,abs_of_nonneg (nn s)] using hs)
  refine ⟨hfi,?_⟩
  have H := integral_mono_ae hfi hi hAE
  change (∫ s in Ioi (8:ℝ), f s) ≤ ∫ s in Ioi (8:ℝ), 2*(s^3*E s) at H
  rw [integral_const_mul,hg.2] at H
  refine H.trans ?_
  norm_num [E,Real.exp_neg]
  have he := Real.sum_le_exp_of_nonneg (x:=(32:ℝ)) (by norm_num) 24
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  field_simp
  linarith only [he]

lemma price_endpoint {a : Fin 4 → ℝ} (p : Parameters a) (ha : ∑ j, a j^2=1) {ns : List Node}
    (h0 : start ns=true) (hns : chainCheck ns=true) {b : Box} (hb : Fits p b)
    {c : ℝ} (hpos : 0 ≤ c) {k L : Int} (hc : val k ≤ c) (hend : endpoint ns b k L=true) :
    (∫ s in Ioi (0:ℝ), fold a c s*E s) ≤ val L + 1/100000000 := by
  cases ns with
  | nil => simp [start] at h0
  | cons n ns =>
    have hfirst : val n.pos=0 := by
      simp only [start,decide_eq_true_eq] at h0
      simp [val,h0]
    have H := chain p ha hb c k hc n ns hns
    rw [hfirst] at H
    have HI : (total b k (n::ns):ℝ) ≤ 2*S^4*(L:ℝ) := by
      simp only [endpoint,decide_eq_true_eq] at hend
      norm_num only [scale] at hend
      dsimp [S];exact_mod_cast hend
    have Hbound : (total b k (n::ns):ℝ)/(2*S^5) ≤ val L := by
      apply (div_le_iff₀ (by dsimp [S];positivity)).mpr
      calc _ ≤ _ := HI
        _ = _ := by dsimp [val,S];ring
    have ht := tail ha hpos
    have cf : Continuous (fun s => fold a c s*E s) := (fold_cont a c).mul (show Continuous E by unfold E;fun_prop)
    rw [← intervalIntegral.integral_interval_add_Ioi' (b:=(8:ℝ)) (cf.intervalIntegrable _ _) ht.1]
    exact add_le_add (H.trans Hbound) ht.2

end PanelChain

end

section

open MeasureTheory ProbabilityTheory Real Set Filter HighBudget CubicEnvelope GrothendieckLB.DualQuadrature
open PanelParams PanelAudit PanelGeometry PanelChain FiberDual FiberChaos
open OneFiber (γ)
namespace PanelBand

noncomputable def charge (a : Fin 4 → ℝ) (c s : ℝ) := max (|poly a s|-c*|s|) 0

lemma charge_int (a : Fin 4 → ℝ) (c : ℝ) : Integrable (charge a c) γ :=
  ((poly_int a).abs.sub ((show Integrable (fun s : ℝ => |s|) γ from IsGaussian.integrable_id.abs).const_mul c)).sup
    (integrable_const 0)

lemma J_convex (a : Fin 4 → ℝ) (l h v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ 1) :
    J a ((1-v)*l+v*h) ≤ (1-v)*J a l+v*J a h := by
  have v0 := sub_nonneg.mpr hv'
  simp only [J,stdExp_eq]
  change (∫ s, charge a ((1-v)*l+v*h) s ∂γ) ≤ (1-v)*(∫ s,charge a l s ∂γ)+v*(∫ s,charge a h s ∂γ)
  rw [← integral_const_mul,← integral_const_mul,← integral_add ((charge_int a l).const_mul _) ((charge_int a h).const_mul _)]
  apply integral_mono (charge_int _ _) (((charge_int a l).const_mul _).add ((charge_int a h).const_mul _))
  intro s
  apply max_le
  · have h1 := mul_le_mul_of_nonneg_left (le_max_left (|poly a s|-l*|s|) 0) v0
    have h2 := mul_le_mul_of_nonneg_left (le_max_left (|poly a s|-h*|s|) 0) hv
    dsimp [charge]
    nlinarith only [h1,h2]
  · exact add_nonneg (mul_nonneg v0 (le_max_right _ _)) (mul_nonneg hv (le_max_right _ _))

lemma tangent (u v c : ℝ) (h : u^2+v^2 ≤ 1) : u+v*c ≤ Real.sqrt (1+c^2) := by
  apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity)]
  have H := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 1+c^2)
  nlinarith only [H,sq_nonneg (u*c-v)]

lemma band {a : Fin 4 → ℝ} (ha : ∑ j, a j^2=1) {c : ℝ} {ns : List Node}
    (hz : start ns=true) (hn : chainCheck ns=true) (v : Band) (t : Tree)
    (hv : bandCheck v=true) (ht : treeCheck ns v entire t=true)
    (hl : price v.lo ≤ c) (hh : c ≤ price v.hi) :
    J a c ≤ (3*ABPOnline.cG/2)*(Real.sqrt (1+c^2)-c) := by
  rcases parameters ha with ⟨p⟩
  rcases tree_sound p t (whole p) ht with ⟨b,hb,el,eh⟩
  simp only [bandCheck,decide_eq_true_eq] at hv
  rcases hv with ⟨hlt,v0,_,_,huv,clo,chi,hL,hH⟩
  have strict : price v.lo < price v.hi := div_lt_div_of_pos_right (by exact_mod_cast hlt) (by norm_num)
  have lo0 : 0 ≤ price v.lo := div_nonneg (by exact_mod_cast v0) (by norm_num)
  have b1 := (Rat.cast_le (K:=ℝ)).mpr clo
  have b2 := (Rat.cast_le (K:=ℝ)).mpr chi
  have b3 := (Rat.cast_le (K:=ℝ)).mpr hL
  have b4 := (Rat.cast_le (K:=ℝ)).mpr hH
  push_cast at b1 b2 b3 b4
  have L := (price_endpoint p ha hz hn hb lo0 b1 el).trans b3
  have U := (price_endpoint p ha hz hn hb (lo0.trans strict.le) b2 eh).trans b4
  let l := price v.lo
  let h := price v.hi
  let w := (c-l)/(h-l)
  have h0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr strict.le)
  have h1 : w ≤ 1 := (div_le_one (sub_pos.mpr strict)).mpr (by dsimp [l,h];linarith only [hh])
  have diff : h-l≠0 := sub_ne_zero.mpr strict.ne'
  have mix : (1-w)*l+w*h=c := by
    have key : w*(h-l)=c-l := div_mul_cancel₀ _ diff
    linarith only [key]
  have JL : J a l ≤ ν/2*(3*(val v.u+(val v.v-1)*l)) := by
    rw [folded_integral];exact mul_le_mul_of_nonneg_left L (by linarith only [HighBudget.ν_pos])
  have JU : J a h ≤ ν/2*(3*(val v.u+(val v.v-1)*h)) := by
    rw [folded_integral];exact mul_le_mul_of_nonneg_left U (by linarith only [HighBudget.ν_pos])
  have hconv := J_convex a l h w h0 h1
  rw [mix] at hconv
  refine hconv.trans ((add_le_add (mul_le_mul_of_nonneg_left JL (sub_nonneg.mpr h1))
    (mul_le_mul_of_nonneg_left JU h0)).trans ?_)
  have realuv : (v.u:ℝ)^2+(v.v:ℝ)^2 ≤ S^2 := by
    norm_num only [scale] at huv;dsimp [S];exact_mod_cast huv
  have unit : (val v.u)^2+(val v.v)^2 ≤ 1 := by dsimp [val,S] at *;linarith only [realuv]
  have htang := tangent (val v.u) (val v.v) c unit
  calc _ = (3*ν/2)*(val v.u+(val v.v-1)*c) := by
        nth_rw 1 [← mix];ring
    _ ≤ (3*ν/2)*(Real.sqrt (1+c^2)-c) := mul_le_mul_of_nonneg_left
      (by linarith only [htang]) (by linarith only [HighBudget.ν_pos])

end PanelBand

end

theorem solution (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (nodes : List GrothendieckLB.DualQuadrature.Node)
    (v : GrothendieckLB.DualQuadrature.Band) (t : GrothendieckLB.DualQuadrature.Tree)
    (hz : GrothendieckLB.DualQuadrature.start nodes = true)
    (hn : GrothendieckLB.DualQuadrature.chainCheck nodes = true)
    (hv : GrothendieckLB.DualQuadrature.bandCheck v = true)
    (ht : GrothendieckLB.DualQuadrature.treeCheck nodes v GrothendieckLB.DualQuadrature.entire t = true)
    (hl : (v.lo : ℝ)/1000000 ≤ c) (hh : c ≤ (v.hi : ℝ)/1000000) :
    GrothendieckLB.stdExp (fun s => max (|∑ j, a j * GrothendieckLB.he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c^2) - c) :=
  PanelBand.band ha hz hn v t hv ht hl hh
