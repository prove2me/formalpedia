-- Prove2me | solution 1 for GrothendieckLB.fiber_dual_parity_norms
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:20:08.467878+00:00
-- url     : https://prove2.me/submissions/a66e6313-70f8-4e84-832c-7bf78e7233de

import Mathlib
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
lemma ν_low : (0.7978 : ℝ) ≤ ν := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith only [Real.pi_lt_d6]
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

lemma kernel_sq (s : ℝ) : ∑ j : Fin 4, he j s ^ 2 = 3/2 + 3/2*s^2 - s^4/2 + s^6/6 := by
  simp only [Fin.sum_univ_four, he, one_pow, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  ring

lemma poly_sq {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) (s : ℝ) :
    (poly a s)^2 ≤ 3/2 + 3/2*s^2 - s^4/2 + s^6/6 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (Fin 4))) a (fun j => he j s)
  simpa only [ha, kernel_sq, one_mul, poly] using h

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

namespace GateChecker

def scale : Int := 8388608
def panels : Nat := 2048
def perUnit : Nat := 256

structure Node where
  pos : Int
  dens : Int
  lo : Int
  hi : Int
  even : Int
  odd : Int
  err : Int
  deriving Repr, DecidableEq, Inhabited

structure Box where
  full : Bool
  e : Int
  d : Int
  xmin : Int
  xmax : Int
  ymin : Int
  ymax : Int
  deriving Repr, DecidableEq, Inhabited

def xbound (b : Box) (n : Node) : Int :=
  if b.full then
    let p := b.ymin*n.lo
    let q := b.ymin*n.hi
    let r := b.ymax*n.lo
    let s := b.ymax*n.hi
    let hi := b.xmax*scale + max (max p q) (max r s)
    let lo := b.xmin*scale + min (min p q) (min r s)
    b.e * max hi (-lo)
  else b.e*n.even*scale

def height (b : Box) (c : Int) (n : Node) : Int :=
  let x := xbound b n
  let y := b.d*n.odd*scale
  let t := (c*n.pos - n.err*scale)*scale
  max 0 (max (x+y-t) (2*(max x y-t)))

def total (b : Box) (c : Int) : List Node → Int
  | [] => 0
  | [_] => 0
  | n::m::ns => (height b c n+height b c m)*(m.pos-n.pos)*n.dens + total b c (m::ns)

def endpoint (nodes : List Node) (b : Box) (c lim : Int) : Bool :=
  decide (total b c nodes ≤ 2*scale^4*lim)

end GateChecker

end

section

open Finset
namespace GateChecker

def qval (n : Int) : ℚ := (n:ℚ)/8388608
def qprice (c : Int) : ℚ := (c:ℚ)/1000000
def taylor (x : ℚ) : ℚ := ∑ k ∈ range 21, x^k / (k.factorial:ℚ)

def nodeCheck (n : Node) : Bool :=
  let s := qval n.pos
  let z := s^2-1
  let A := z*qval 5931641
  let B := z*qval 5931642
  decide (0 ≤ n.pos ∧ 0 ≤ n.even ∧ 0 ≤ n.odd ∧ 0 ≤ n.dens ∧
    qval n.lo ≤ min A B ∧ max A B ≤ qval n.hi ∧
    1+z^2/2 ≤ (qval n.even)^2 ∧ s^2+(s^3-3*s)^2/6 ≤ (qval n.odd)^2 ∧
    1 ≤ qval n.dens * taylor (s^2/2))

def edgeCheck (n m : Node) : Bool :=
  let l := qval n.pos
  let h := qval m.pos
  let err := (1+2*h)*(h-l)^2/4
  decide (l<h ∧ err ≤ qval n.err ∧ err ≤ qval m.err)

def chainCheck : List Node → Bool
  | [] => false
  | [n] => nodeCheck n && decide (n.pos=8*scale)
  | n::m::ns => nodeCheck n && edgeCheck n m && chainCheck (m::ns)

structure Span where
  dl : Int
  du : Int
  yl : Int
  yu : Int
  deriving Repr, Inhabited, DecidableEq

def entire : Span := ⟨0,scale,-scale,scale⟩

def geom (w : Span) (b : Box) : Bool :=
  let yminabs := max 0 (max w.yl (-w.yu))
  let ymaxabs := max (-w.yl) w.yu
  decide (0≤w.dl ∧ 0≤b.e ∧ scale^2≤b.e^2+w.dl^2 ∧ w.du≤b.d ∧
    0≤b.xmax ∧ scale^2 ≤ b.xmax^2+yminabs^2 ∧ b.xmin^2+ymaxabs^2≤ scale^2 ∧
    b.ymin≤w.yl ∧ w.yu≤b.ymax)

structure Band where
  lo : Int
  hi : Int
  u : Int
  v : Int
  clo : Int
  chi : Int
  L : Int
  H : Int
  deriving Repr, Inhabited, DecidableEq

def bandCheck (v : Band) : Bool := decide
  (v.lo<v.hi ∧ 0≤v.lo ∧ 0≤v.u ∧ 0≤v.v ∧ v.u^2+v.v^2≤ scale^2 ∧
   qval v.clo ≤ qprice v.lo ∧ qval v.chi ≤ qprice v.hi ∧
   qval v.L+1/100000000 ≤ 3*(qval v.u+(qval v.v-1)*qprice v.lo) ∧
   qval v.H+1/100000000 ≤ 3*(qval v.u+(qval v.v-1)*qprice v.hi))

inductive Tree where
  | leaf (b : Box)
  | d (cut : Int) (left right : Tree)
  | y (cut : Int) (left right : Tree)
  deriving Inhabited

def treeCheck (ns : List Node) (v : Band) (w : Span) : Tree → Bool
  | .leaf b => geom w b && endpoint ns b v.clo v.L && endpoint ns b v.chi v.H
  | .d k l r => treeCheck ns v {w with du:=k} l && treeCheck ns v {w with dl:=k} r
  | .y k l r => treeCheck ns v {w with yu:=k} l && treeCheck ns v {w with yl:=k} r

end GateChecker

end

section

open Real Finset CubicEnvelope PanelMath GateChecker

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

open Real CubicEnvelope PanelMath GateChecker PanelParams
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

open GateChecker PanelParams Real HighBudget
namespace PanelAudit

@[simp, norm_cast] lemma qval_cast (n : Int) : (qval n : ℝ) = val n := by
  simp [qval,val,S]
noncomputable def price (k : Int) : ℝ := (k:ℝ)/1000000
@[simp, norm_cast] lemma qprice_cast (k : Int) : (qprice k : ℝ) = price k := by
  simp [qprice,price]

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
  push_cast [qval_cast,taylor] at castL castU castE castO castD
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

open GateChecker PanelParams Real
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

open MeasureTheory Real Set Filter HighBudget CubicEnvelope GateChecker PanelMath PanelParams PanelHeight PanelAudit
namespace PanelChain

lemma chain {a : Fin 4 → ℝ} (p : Parameters a) (ha : ∑ j, a j^2=1) {b : Box}
    (hb : Fits p b) (c : ℝ) (k : Int) (hc : val k ≤ c) (n : Node) (ns : List Node)
    (hh : chainCheck (n::ns)=true) :
    (∫ s in val n.pos..(8:ℝ), fold a c s*E s) ≤ (total b k (n::ns):ℝ)/(2*S^5) := by
  induction ns generalizing n with
  | nil =>
    simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    have he : val n.pos=8 := by norm_num [val,hh.2,scale,S]
    simp [he,total]
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
    simp only [total,Int.cast_add,Int.cast_mul,Int.cast_sub]
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

def start : List Node → Bool
  | n::_ => decide (n.pos=0)
  | [] => false

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

open MeasureTheory ProbabilityTheory Real Set Filter HighBudget CubicEnvelope GateChecker
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

section

namespace GateChecker.M0
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false
def n0 : Node := ⟨0,8388608,-5931642,-5931641,10273905,0,9216⟩
def n1 : Node := ⟨524288,8372240,-5908472,-5908470,10260545,828325,10240⟩
def n2 : Node := ⟨1048576,8323328,-5838961,-5838959,10220675,1652769,11264⟩
def n3 : Node := ⟨1572864,8242441,-5723108,-5723106,10154935,2469472,12288⟩
def n4 : Node := ⟨2097152,8130518,-5560915,-5560913,10064418,3274615,13312⟩
def n5 : Node := ⟨2621440,7988848,-5352381,-5352379,9950715,4064444,14336⟩
def n6 : Node := ⟨3145728,7819043,-5097505,-5097503,9815972,4835293,15360⟩
def n7 : Node := ⟨3670016,7623012,-4796289,-4796287,9662978,5583613,16384⟩
def n8 : Node := ⟨4194304,7402921,-4448732,-4448730,9495260,6306003,17408⟩
def n9 : Node := ⟨4718592,7161157,-4054834,-4054832,9317211,6999248,18432⟩
def n10 : Node := ⟨5242880,6900281,-3614595,-3614593,9134224,7660360,19456⟩
def n11 : Node := ⟨5767168,6622987,-3128015,-3128013,8952833,8286636,20480⟩
def n12 : Node := ⟨6291456,6332054,-2595094,-2595092,8780846,8875714,21504⟩
def n13 : Node := ⟨6815744,6030299,-2015832,-2015831,8627417,9425655,22528⟩
def n14 : Node := ⟨7340032,5720534,-1390229,-1390228,8503028,9935031,23552⟩
def n15 : Node := ⟨7864320,5405525,-718285,-718284,8419304,10403042,24576⟩
def n16 : Node := ⟨8388608,5087948,0,0,8388608,10829647,58752⟩
def n17 : Node := ⟨9175040,4612316,1164316,1164317,8469025,11394162,62208⟩
def n18 : Node := ⟨9961472,4144560,2432899,2432901,8734286,11875760,65664⟩
def n19 : Node := ⟨10747904,3691652,3805750,3805751,9211541,12289988,69120⟩
def n20 : Node := ⟨11534336,3259462,5282867,5282869,9913498,12662153,72576⟩
def n21 : Node := ⟨12320768,2852687,6864252,6864254,10839129,13029630,76032⟩
def n22 : Node := ⟨13107200,2474830,8549904,8549906,11977881,13443698,79488⟩
def n23 : Node := ⟨13893632,2128235,10339823,10339826,13314681,13969798,82944⟩
def n24 : Node := ⟨14680064,1814164,12234009,12234012,14833738,14684842,86400⟩
def n25 : Node := ⟨15466496,1532910,14232462,14232466,16520648,15670764,89856⟩
def n26 : Node := ⟨16252928,1283925,16335183,16335186,18363198,17005326,89856⟩
def n27 : Node := ⟨16777216,1135275,17794923,17794926,19673030,18121465,172032⟩
def n28 : Node := ⟨17825792,877273,20853425,20853429,22477415,20962201,180224⟩
def n29 : Node := ⟨18874368,667394,24097291,24097296,25515649,24674109,188416⟩
def n30 : Node := ⟨19922944,499855,27526521,27526527,28776350,29295198,196608⟩
def n31 : Node := ⟨20971520,368570,31141115,31141121,32251171,34843136,204800⟩
def n32 : Node := ⟨22020096,267553,34941072,34941079,35933934,41329950,212992⟩
def n33 : Node := ⟨23068672,191212,38926394,38926401,39820011,48769383,221184⟩
def n34 : Node := ⟨24117248,134535,43097079,43097087,43905892,57179419,229376⟩
def n35 : Node := ⟨25165824,93190,47453128,47453136,48188885,66582512,237568⟩
def n36 : Node := ⟨26214400,63550,51994540,51994550,52666893,77004982,245760⟩
def n37 : Node := ⟨27262976,42666,56721317,56721327,57338270,88476238,253952⟩
def n38 : Node := ⟨28311552,28200,61633457,61633468,62201709,101028078,262144⟩
def n39 : Node := ⟨29360128,18351,66730961,66730973,67256159,114694117,270336⟩
def n40 : Node := ⟨30408704,11756,72013829,72013842,72500769,129509356,278528⟩
def n41 : Node := ⟨31457280,7415,77482060,77482074,77934843,145509846,286720⟩
def n42 : Node := ⟨32505856,4604,83135655,83135670,83557809,162732447,294912⟩
def n43 : Node := ⟨33554432,2815,88974615,88974630,89369192,181214645,1245184⟩
def n44 : Node := ⟨35651584,1004,101208624,101208642,101555682,222110087,1310720⟩
def n45 : Node := ⟨37748736,337,114184089,114184109,114491824,268504056,1376256⟩
def n46 : Node := ⟨39845888,107,127901009,127901031,128175818,320708414,1441792⟩
def n47 : Node := ⟨41943040,32,142359384,142359408,142606336,379037623,1507328⟩
def n48 : Node := ⟨44040192,10,157559214,157559241,157782381,443807886,1572864⟩
def n49 : Node := ⟨46137344,3,173500499,173500529,173703190,515336613,1638400⟩
def n50 : Node := ⟨48234496,1,190183239,190183272,190368172,593942065,1703936⟩
def n51 : Node := ⟨50331648,1,207607435,207607470,207776863,679943123,7340032⟩
def n52 : Node := ⟨54525952,1,244680191,244680233,244823972,875409731,7864320⟩
def n53 : Node := ⟨58720256,1,284718768,284718816,284842346,1104294744,8388608⟩
def n54 : Node := ⟨62914560,1,327723165,327723221,327830541,1369159818,8912896⟩
def n55 : Node := ⟨67108864,1,373693383,373693446,373787563,1672568674,8912896⟩
def z55 : List Node := n55 :: []
def z54 : List Node := n54 :: z55
def z53 : List Node := n53 :: z54
def z52 : List Node := n52 :: z53
def z51 : List Node := n51 :: z52
def z50 : List Node := n50 :: z51
def z49 : List Node := n49 :: z50
def z48 : List Node := n48 :: z49
def z47 : List Node := n47 :: z48
def z46 : List Node := n46 :: z47
def z45 : List Node := n45 :: z46
def z44 : List Node := n44 :: z45
def z43 : List Node := n43 :: z44
def z42 : List Node := n42 :: z43
def z41 : List Node := n41 :: z42
def z40 : List Node := n40 :: z41
def z39 : List Node := n39 :: z40
def z38 : List Node := n38 :: z39
def z37 : List Node := n37 :: z38
def z36 : List Node := n36 :: z37
def z35 : List Node := n35 :: z36
def z34 : List Node := n34 :: z35
def z33 : List Node := n33 :: z34
def z32 : List Node := n32 :: z33
def z31 : List Node := n31 :: z32
def z30 : List Node := n30 :: z31
def z29 : List Node := n29 :: z30
def z28 : List Node := n28 :: z29
def z27 : List Node := n27 :: z28
def z26 : List Node := n26 :: z27
def z25 : List Node := n25 :: z26
def z24 : List Node := n24 :: z25
def z23 : List Node := n23 :: z24
def z22 : List Node := n22 :: z23
def z21 : List Node := n21 :: z22
def z20 : List Node := n20 :: z21
def z19 : List Node := n19 :: z20
def z18 : List Node := n18 :: z19
def z17 : List Node := n17 :: z18
def z16 : List Node := n16 :: z17
def z15 : List Node := n15 :: z16
def z14 : List Node := n14 :: z15
def z13 : List Node := n13 :: z14
def z12 : List Node := n12 :: z13
def z11 : List Node := n11 :: z12
def z10 : List Node := n10 :: z11
def z9 : List Node := n9 :: z10
def z8 : List Node := n8 :: z9
def z7 : List Node := n7 :: z8
def z6 : List Node := n6 :: z7
def z5 : List Node := n5 :: z6
def z4 : List Node := n4 :: z5
def z3 : List Node := n3 :: z4
def z2 : List Node := n2 :: z3
def z1 : List Node := n1 :: z2
def z0 : List Node := n0 :: z1
def nodes := z0
lemma starts : PanelChain.start nodes=true := by decide +kernel
lemma check55 : nodeCheck n55=true := by decide +kernel
lemma ok55 : chainCheck z55=true := Bool.and_eq_true_iff.mpr ⟨check55,by decide +kernel⟩
lemma check54 : nodeCheck n54=true := by decide +kernel
lemma edge54 : edgeCheck n54 n55=true := by decide +kernel
lemma ok54 : chainCheck z54=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check54,edge54⟩,ok55⟩
lemma check53 : nodeCheck n53=true := by decide +kernel
lemma edge53 : edgeCheck n53 n54=true := by decide +kernel
lemma ok53 : chainCheck z53=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check53,edge53⟩,ok54⟩
lemma check52 : nodeCheck n52=true := by decide +kernel
lemma edge52 : edgeCheck n52 n53=true := by decide +kernel
lemma ok52 : chainCheck z52=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check52,edge52⟩,ok53⟩
lemma check51 : nodeCheck n51=true := by decide +kernel
lemma edge51 : edgeCheck n51 n52=true := by decide +kernel
lemma ok51 : chainCheck z51=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check51,edge51⟩,ok52⟩
lemma check50 : nodeCheck n50=true := by decide +kernel
lemma edge50 : edgeCheck n50 n51=true := by decide +kernel
lemma ok50 : chainCheck z50=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check50,edge50⟩,ok51⟩
lemma check49 : nodeCheck n49=true := by decide +kernel
lemma edge49 : edgeCheck n49 n50=true := by decide +kernel
lemma ok49 : chainCheck z49=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check49,edge49⟩,ok50⟩
lemma check48 : nodeCheck n48=true := by decide +kernel
lemma edge48 : edgeCheck n48 n49=true := by decide +kernel
lemma ok48 : chainCheck z48=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check48,edge48⟩,ok49⟩
lemma check47 : nodeCheck n47=true := by decide +kernel
lemma edge47 : edgeCheck n47 n48=true := by decide +kernel
lemma ok47 : chainCheck z47=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check47,edge47⟩,ok48⟩
lemma check46 : nodeCheck n46=true := by decide +kernel
lemma edge46 : edgeCheck n46 n47=true := by decide +kernel
lemma ok46 : chainCheck z46=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check46,edge46⟩,ok47⟩
lemma check45 : nodeCheck n45=true := by decide +kernel
lemma edge45 : edgeCheck n45 n46=true := by decide +kernel
lemma ok45 : chainCheck z45=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check45,edge45⟩,ok46⟩
lemma check44 : nodeCheck n44=true := by decide +kernel
lemma edge44 : edgeCheck n44 n45=true := by decide +kernel
lemma ok44 : chainCheck z44=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check44,edge44⟩,ok45⟩
lemma check43 : nodeCheck n43=true := by decide +kernel
lemma edge43 : edgeCheck n43 n44=true := by decide +kernel
lemma ok43 : chainCheck z43=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check43,edge43⟩,ok44⟩
lemma check42 : nodeCheck n42=true := by decide +kernel
lemma edge42 : edgeCheck n42 n43=true := by decide +kernel
lemma ok42 : chainCheck z42=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check42,edge42⟩,ok43⟩
lemma check41 : nodeCheck n41=true := by decide +kernel
lemma edge41 : edgeCheck n41 n42=true := by decide +kernel
lemma ok41 : chainCheck z41=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check41,edge41⟩,ok42⟩
lemma check40 : nodeCheck n40=true := by decide +kernel
lemma edge40 : edgeCheck n40 n41=true := by decide +kernel
lemma ok40 : chainCheck z40=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check40,edge40⟩,ok41⟩
lemma check39 : nodeCheck n39=true := by decide +kernel
lemma edge39 : edgeCheck n39 n40=true := by decide +kernel
lemma ok39 : chainCheck z39=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check39,edge39⟩,ok40⟩
lemma check38 : nodeCheck n38=true := by decide +kernel
lemma edge38 : edgeCheck n38 n39=true := by decide +kernel
lemma ok38 : chainCheck z38=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check38,edge38⟩,ok39⟩
lemma check37 : nodeCheck n37=true := by decide +kernel
lemma edge37 : edgeCheck n37 n38=true := by decide +kernel
lemma ok37 : chainCheck z37=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check37,edge37⟩,ok38⟩
lemma check36 : nodeCheck n36=true := by decide +kernel
lemma edge36 : edgeCheck n36 n37=true := by decide +kernel
lemma ok36 : chainCheck z36=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check36,edge36⟩,ok37⟩
lemma check35 : nodeCheck n35=true := by decide +kernel
lemma edge35 : edgeCheck n35 n36=true := by decide +kernel
lemma ok35 : chainCheck z35=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check35,edge35⟩,ok36⟩
lemma check34 : nodeCheck n34=true := by decide +kernel
lemma edge34 : edgeCheck n34 n35=true := by decide +kernel
lemma ok34 : chainCheck z34=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check34,edge34⟩,ok35⟩
lemma check33 : nodeCheck n33=true := by decide +kernel
lemma edge33 : edgeCheck n33 n34=true := by decide +kernel
lemma ok33 : chainCheck z33=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check33,edge33⟩,ok34⟩
lemma check32 : nodeCheck n32=true := by decide +kernel
lemma edge32 : edgeCheck n32 n33=true := by decide +kernel
lemma ok32 : chainCheck z32=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check32,edge32⟩,ok33⟩
lemma check31 : nodeCheck n31=true := by decide +kernel
lemma edge31 : edgeCheck n31 n32=true := by decide +kernel
lemma ok31 : chainCheck z31=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check31,edge31⟩,ok32⟩
lemma check30 : nodeCheck n30=true := by decide +kernel
lemma edge30 : edgeCheck n30 n31=true := by decide +kernel
lemma ok30 : chainCheck z30=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check30,edge30⟩,ok31⟩
lemma check29 : nodeCheck n29=true := by decide +kernel
lemma edge29 : edgeCheck n29 n30=true := by decide +kernel
lemma ok29 : chainCheck z29=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check29,edge29⟩,ok30⟩
lemma check28 : nodeCheck n28=true := by decide +kernel
lemma edge28 : edgeCheck n28 n29=true := by decide +kernel
lemma ok28 : chainCheck z28=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check28,edge28⟩,ok29⟩
lemma check27 : nodeCheck n27=true := by decide +kernel
lemma edge27 : edgeCheck n27 n28=true := by decide +kernel
lemma ok27 : chainCheck z27=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check27,edge27⟩,ok28⟩
lemma check26 : nodeCheck n26=true := by decide +kernel
lemma edge26 : edgeCheck n26 n27=true := by decide +kernel
lemma ok26 : chainCheck z26=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check26,edge26⟩,ok27⟩
lemma check25 : nodeCheck n25=true := by decide +kernel
lemma edge25 : edgeCheck n25 n26=true := by decide +kernel
lemma ok25 : chainCheck z25=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check25,edge25⟩,ok26⟩
lemma check24 : nodeCheck n24=true := by decide +kernel
lemma edge24 : edgeCheck n24 n25=true := by decide +kernel
lemma ok24 : chainCheck z24=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check24,edge24⟩,ok25⟩
lemma check23 : nodeCheck n23=true := by decide +kernel
lemma edge23 : edgeCheck n23 n24=true := by decide +kernel
lemma ok23 : chainCheck z23=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check23,edge23⟩,ok24⟩
lemma check22 : nodeCheck n22=true := by decide +kernel
lemma edge22 : edgeCheck n22 n23=true := by decide +kernel
lemma ok22 : chainCheck z22=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check22,edge22⟩,ok23⟩
lemma check21 : nodeCheck n21=true := by decide +kernel
lemma edge21 : edgeCheck n21 n22=true := by decide +kernel
lemma ok21 : chainCheck z21=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check21,edge21⟩,ok22⟩
lemma check20 : nodeCheck n20=true := by decide +kernel
lemma edge20 : edgeCheck n20 n21=true := by decide +kernel
lemma ok20 : chainCheck z20=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check20,edge20⟩,ok21⟩
lemma check19 : nodeCheck n19=true := by decide +kernel
lemma edge19 : edgeCheck n19 n20=true := by decide +kernel
lemma ok19 : chainCheck z19=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check19,edge19⟩,ok20⟩
lemma check18 : nodeCheck n18=true := by decide +kernel
lemma edge18 : edgeCheck n18 n19=true := by decide +kernel
lemma ok18 : chainCheck z18=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check18,edge18⟩,ok19⟩
lemma check17 : nodeCheck n17=true := by decide +kernel
lemma edge17 : edgeCheck n17 n18=true := by decide +kernel
lemma ok17 : chainCheck z17=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check17,edge17⟩,ok18⟩
lemma check16 : nodeCheck n16=true := by decide +kernel
lemma edge16 : edgeCheck n16 n17=true := by decide +kernel
lemma ok16 : chainCheck z16=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check16,edge16⟩,ok17⟩
lemma check15 : nodeCheck n15=true := by decide +kernel
lemma edge15 : edgeCheck n15 n16=true := by decide +kernel
lemma ok15 : chainCheck z15=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check15,edge15⟩,ok16⟩
lemma check14 : nodeCheck n14=true := by decide +kernel
lemma edge14 : edgeCheck n14 n15=true := by decide +kernel
lemma ok14 : chainCheck z14=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check14,edge14⟩,ok15⟩
lemma check13 : nodeCheck n13=true := by decide +kernel
lemma edge13 : edgeCheck n13 n14=true := by decide +kernel
lemma ok13 : chainCheck z13=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check13,edge13⟩,ok14⟩
lemma check12 : nodeCheck n12=true := by decide +kernel
lemma edge12 : edgeCheck n12 n13=true := by decide +kernel
lemma ok12 : chainCheck z12=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check12,edge12⟩,ok13⟩
lemma check11 : nodeCheck n11=true := by decide +kernel
lemma edge11 : edgeCheck n11 n12=true := by decide +kernel
lemma ok11 : chainCheck z11=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check11,edge11⟩,ok12⟩
lemma check10 : nodeCheck n10=true := by decide +kernel
lemma edge10 : edgeCheck n10 n11=true := by decide +kernel
lemma ok10 : chainCheck z10=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check10,edge10⟩,ok11⟩
lemma check9 : nodeCheck n9=true := by decide +kernel
lemma edge9 : edgeCheck n9 n10=true := by decide +kernel
lemma ok9 : chainCheck z9=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check9,edge9⟩,ok10⟩
lemma check8 : nodeCheck n8=true := by decide +kernel
lemma edge8 : edgeCheck n8 n9=true := by decide +kernel
lemma ok8 : chainCheck z8=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check8,edge8⟩,ok9⟩
lemma check7 : nodeCheck n7=true := by decide +kernel
lemma edge7 : edgeCheck n7 n8=true := by decide +kernel
lemma ok7 : chainCheck z7=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check7,edge7⟩,ok8⟩
lemma check6 : nodeCheck n6=true := by decide +kernel
lemma edge6 : edgeCheck n6 n7=true := by decide +kernel
lemma ok6 : chainCheck z6=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check6,edge6⟩,ok7⟩
lemma check5 : nodeCheck n5=true := by decide +kernel
lemma edge5 : edgeCheck n5 n6=true := by decide +kernel
lemma ok5 : chainCheck z5=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check5,edge5⟩,ok6⟩
lemma check4 : nodeCheck n4=true := by decide +kernel
lemma edge4 : edgeCheck n4 n5=true := by decide +kernel
lemma ok4 : chainCheck z4=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check4,edge4⟩,ok5⟩
lemma check3 : nodeCheck n3=true := by decide +kernel
lemma edge3 : edgeCheck n3 n4=true := by decide +kernel
lemma ok3 : chainCheck z3=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check3,edge3⟩,ok4⟩
lemma check2 : nodeCheck n2=true := by decide +kernel
lemma edge2 : edgeCheck n2 n3=true := by decide +kernel
lemma ok2 : chainCheck z2=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check2,edge2⟩,ok3⟩
lemma check1 : nodeCheck n1=true := by decide +kernel
lemma edge1 : edgeCheck n1 n2=true := by decide +kernel
lemma ok1 : chainCheck z1=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check1,edge1⟩,ok2⟩
lemma check0 : nodeCheck n0=true := by decide +kernel
lemma edge0 : edgeCheck n0 n1=true := by decide +kernel
lemma ok0 : chainCheck z0=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check0,edge0⟩,ok1⟩
def v2 : Band := ⟨1550000,1700000,4396445,7144229,13002342,14260633,7402972,6843002⟩
lemma b2ok : bandCheck v2=true := by decide +kernel
def t2x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t2x16ok : treeCheck nodes v2 ⟨0,524288,-8388608,8388608⟩ t2x16=true := by decide +kernel
def t2x34 : Tree := .leaf ⟨false,8372208,786432,0,8388608,-8388608,8388608⟩
lemma t2x34ok : treeCheck nodes v2 ⟨524288,786432,-8388608,8388608⟩ t2x34=true := by decide +kernel
def t2x35 : Tree := .leaf ⟨false,8351663,1048576,0,8388608,-8388608,8388608⟩
lemma t2x35ok : treeCheck nodes v2 ⟨786432,1048576,-8388608,8388608⟩ t2x35=true := by decide +kernel
def t2x17 : Tree := .d (786432) t2x34 t2x35
lemma t2x17ok : treeCheck nodes v2 ⟨524288,1048576,-8388608,8388608⟩ t2x17=true := Bool.and_eq_true_iff.mpr ⟨t2x34ok,t2x35ok⟩
def t2x8 : Tree := .d (524288) t2x16 t2x17
lemma t2x8ok : treeCheck nodes v2 ⟨0,1048576,-8388608,8388608⟩ t2x8=true := Bool.and_eq_true_iff.mpr ⟨t2x16ok,t2x17ok⟩
def t2x72 : Tree := .leaf ⟨false,8322814,1179648,0,8388608,-8388608,8388608⟩
lemma t2x72ok : treeCheck nodes v2 ⟨1048576,1179648,-8388608,8388608⟩ t2x72=true := by decide +kernel
def t2x73 : Tree := .leaf ⟨false,8305250,1310720,0,8388608,-8388608,8388608⟩
lemma t2x73ok : treeCheck nodes v2 ⟨1179648,1310720,-8388608,8388608⟩ t2x73=true := by decide +kernel
def t2x36 : Tree := .d (1179648) t2x72 t2x73
lemma t2x36ok : treeCheck nodes v2 ⟨1048576,1310720,-8388608,8388608⟩ t2x36=true := Bool.and_eq_true_iff.mpr ⟨t2x72ok,t2x73ok⟩
def t2x148 : Tree := .leaf ⟨false,8285576,1376256,0,8388608,-8388608,8388608⟩
lemma t2x148ok : treeCheck nodes v2 ⟨1310720,1376256,-8388608,8388608⟩ t2x148=true := by decide +kernel
def t2x149 : Tree := .leaf ⟨false,8274942,1441792,0,8388608,-8388608,8388608⟩
lemma t2x149ok : treeCheck nodes v2 ⟨1376256,1441792,-8388608,8388608⟩ t2x149=true := by decide +kernel
def t2x74 : Tree := .d (1376256) t2x148 t2x149
lemma t2x74ok : treeCheck nodes v2 ⟨1310720,1441792,-8388608,8388608⟩ t2x74=true := Bool.and_eq_true_iff.mpr ⟨t2x148ok,t2x149ok⟩
def t2x150 : Tree := .leaf ⟨false,8263776,1507328,0,8388608,-8388608,8388608⟩
lemma t2x150ok : treeCheck nodes v2 ⟨1441792,1507328,-8388608,8388608⟩ t2x150=true := by decide +kernel
def t2x151 : Tree := .leaf ⟨false,8252073,1572864,0,8388608,-8388608,8388608⟩
lemma t2x151ok : treeCheck nodes v2 ⟨1507328,1572864,-8388608,8388608⟩ t2x151=true := by decide +kernel
def t2x75 : Tree := .d (1507328) t2x150 t2x151
lemma t2x75ok : treeCheck nodes v2 ⟨1441792,1572864,-8388608,8388608⟩ t2x75=true := Bool.and_eq_true_iff.mpr ⟨t2x150ok,t2x151ok⟩
def t2x37 : Tree := .d (1441792) t2x74 t2x75
lemma t2x37ok : treeCheck nodes v2 ⟨1310720,1572864,-8388608,8388608⟩ t2x37=true := Bool.and_eq_true_iff.mpr ⟨t2x74ok,t2x75ok⟩
def t2x18 : Tree := .d (1310720) t2x36 t2x37
lemma t2x18ok : treeCheck nodes v2 ⟨1048576,1572864,-8388608,8388608⟩ t2x18=true := Bool.and_eq_true_iff.mpr ⟨t2x36ok,t2x37ok⟩
def t2x152 : Tree := .leaf ⟨false,8239833,1638400,0,8388608,-8388608,8388608⟩
lemma t2x152ok : treeCheck nodes v2 ⟨1572864,1638400,-8388608,8388608⟩ t2x152=true := by decide +kernel
def t2x153 : Tree := .leaf ⟨false,8227053,1703936,0,8388608,-8388608,8388608⟩
lemma t2x153ok : treeCheck nodes v2 ⟨1638400,1703936,-8388608,8388608⟩ t2x153=true := by decide +kernel
def t2x76 : Tree := .d (1638400) t2x152 t2x153
lemma t2x76ok : treeCheck nodes v2 ⟨1572864,1703936,-8388608,8388608⟩ t2x76=true := Bool.and_eq_true_iff.mpr ⟨t2x152ok,t2x153ok⟩
def t2x154 : Tree := .leaf ⟨false,8213730,1769472,0,8388608,-8388608,8388608⟩
lemma t2x154ok : treeCheck nodes v2 ⟨1703936,1769472,-8388608,8388608⟩ t2x154=true := by decide +kernel
def t2x155 : Tree := .leaf ⟨false,8199861,1835008,0,8388608,-8388608,8388608⟩
lemma t2x155ok : treeCheck nodes v2 ⟨1769472,1835008,-8388608,8388608⟩ t2x155=true := by decide +kernel
def t2x77 : Tree := .d (1769472) t2x154 t2x155
lemma t2x77ok : treeCheck nodes v2 ⟨1703936,1835008,-8388608,8388608⟩ t2x77=true := Bool.and_eq_true_iff.mpr ⟨t2x154ok,t2x155ok⟩
def t2x38 : Tree := .d (1703936) t2x76 t2x77
lemma t2x38ok : treeCheck nodes v2 ⟨1572864,1835008,-8388608,8388608⟩ t2x38=true := Bool.and_eq_true_iff.mpr ⟨t2x76ok,t2x77ok⟩
def t2x156 : Tree := .leaf ⟨false,8185444,1900544,0,8388608,-8388608,8388608⟩
lemma t2x156ok : treeCheck nodes v2 ⟨1835008,1900544,-8388608,8388608⟩ t2x156=true := by decide +kernel
def t2x157 : Tree := .leaf ⟨false,8170476,1966080,0,8388608,-8388608,8388608⟩
lemma t2x157ok : treeCheck nodes v2 ⟨1900544,1966080,-8388608,8388608⟩ t2x157=true := by decide +kernel
def t2x78 : Tree := .d (1900544) t2x156 t2x157
lemma t2x78ok : treeCheck nodes v2 ⟨1835008,1966080,-8388608,8388608⟩ t2x78=true := Bool.and_eq_true_iff.mpr ⟨t2x156ok,t2x157ok⟩
def t2x158 : Tree := .leaf ⟨false,8154954,2031616,0,8388608,-8388608,8388608⟩
lemma t2x158ok : treeCheck nodes v2 ⟨1966080,2031616,-8388608,8388608⟩ t2x158=true := by decide +kernel
def t2x159 : Tree := .leaf ⟨false,8138875,2097152,0,8388608,-8388608,8388608⟩
lemma t2x159ok : treeCheck nodes v2 ⟨2031616,2097152,-8388608,8388608⟩ t2x159=true := by decide +kernel
def t2x79 : Tree := .d (2031616) t2x158 t2x159
lemma t2x79ok : treeCheck nodes v2 ⟨1966080,2097152,-8388608,8388608⟩ t2x79=true := Bool.and_eq_true_iff.mpr ⟨t2x158ok,t2x159ok⟩
def t2x39 : Tree := .d (1966080) t2x78 t2x79
lemma t2x39ok : treeCheck nodes v2 ⟨1835008,2097152,-8388608,8388608⟩ t2x39=true := Bool.and_eq_true_iff.mpr ⟨t2x78ok,t2x79ok⟩
def t2x19 : Tree := .d (1835008) t2x38 t2x39
lemma t2x19ok : treeCheck nodes v2 ⟨1572864,2097152,-8388608,8388608⟩ t2x19=true := Bool.and_eq_true_iff.mpr ⟨t2x38ok,t2x39ok⟩
def t2x9 : Tree := .d (1572864) t2x18 t2x19
lemma t2x9ok : treeCheck nodes v2 ⟨1048576,2097152,-8388608,8388608⟩ t2x9=true := Bool.and_eq_true_iff.mpr ⟨t2x18ok,t2x19ok⟩
def t2x4 : Tree := .d (1048576) t2x8 t2x9
lemma t2x4ok : treeCheck nodes v2 ⟨0,2097152,-8388608,8388608⟩ t2x4=true := Bool.and_eq_true_iff.mpr ⟨t2x8ok,t2x9ok⟩
def t2x160 : Tree := .leaf ⟨false,8122235,2162688,0,8388608,-8388608,8388608⟩
lemma t2x160ok : treeCheck nodes v2 ⟨2097152,2162688,-8388608,8388608⟩ t2x160=true := by decide +kernel
def t2x161 : Tree := .leaf ⟨false,8105031,2228224,0,8388608,-8388608,8388608⟩
lemma t2x161ok : treeCheck nodes v2 ⟨2162688,2228224,-8388608,8388608⟩ t2x161=true := by decide +kernel
def t2x80 : Tree := .d (2162688) t2x160 t2x161
lemma t2x80ok : treeCheck nodes v2 ⟨2097152,2228224,-8388608,8388608⟩ t2x80=true := Bool.and_eq_true_iff.mpr ⟨t2x160ok,t2x161ok⟩
def t2x162 : Tree := .leaf ⟨false,8087260,2293760,0,8388608,-8388608,8388608⟩
lemma t2x162ok : treeCheck nodes v2 ⟨2228224,2293760,-8388608,8388608⟩ t2x162=true := by decide +kernel
def t2x163 : Tree := .leaf ⟨false,8068917,2359296,0,8388608,-8388608,8388608⟩
lemma t2x163ok : treeCheck nodes v2 ⟨2293760,2359296,-8388608,8388608⟩ t2x163=true := by decide +kernel
def t2x81 : Tree := .d (2293760) t2x162 t2x163
lemma t2x81ok : treeCheck nodes v2 ⟨2228224,2359296,-8388608,8388608⟩ t2x81=true := Bool.and_eq_true_iff.mpr ⟨t2x162ok,t2x163ok⟩
def t2x40 : Tree := .d (2228224) t2x80 t2x81
lemma t2x40ok : treeCheck nodes v2 ⟨2097152,2359296,-8388608,8388608⟩ t2x40=true := Bool.and_eq_true_iff.mpr ⟨t2x80ok,t2x81ok⟩
def t2x164 : Tree := .leaf ⟨false,8049998,2424832,0,8388608,-8388608,8388608⟩
lemma t2x164ok : treeCheck nodes v2 ⟨2359296,2424832,-8388608,8388608⟩ t2x164=true := by decide +kernel
def t2x165 : Tree := .leaf ⟨false,8030501,2490368,0,8388608,-8388608,8388608⟩
lemma t2x165ok : treeCheck nodes v2 ⟨2424832,2490368,-8388608,8388608⟩ t2x165=true := by decide +kernel
def t2x82 : Tree := .d (2424832) t2x164 t2x165
lemma t2x82ok : treeCheck nodes v2 ⟨2359296,2490368,-8388608,8388608⟩ t2x82=true := Bool.and_eq_true_iff.mpr ⟨t2x164ok,t2x165ok⟩
def t2x166 : Tree := .leaf ⟨false,8010419,2555904,0,8388608,-8388608,8388608⟩
lemma t2x166ok : treeCheck nodes v2 ⟨2490368,2555904,-8388608,8388608⟩ t2x166=true := by decide +kernel
def t2x167 : Tree := .leaf ⟨false,7989750,2621440,0,8388608,-8388608,8388608⟩
lemma t2x167ok : treeCheck nodes v2 ⟨2555904,2621440,-8388608,8388608⟩ t2x167=true := by decide +kernel
def t2x83 : Tree := .d (2555904) t2x166 t2x167
lemma t2x83ok : treeCheck nodes v2 ⟨2490368,2621440,-8388608,8388608⟩ t2x83=true := Bool.and_eq_true_iff.mpr ⟨t2x166ok,t2x167ok⟩
def t2x41 : Tree := .d (2490368) t2x82 t2x83
lemma t2x41ok : treeCheck nodes v2 ⟨2359296,2621440,-8388608,8388608⟩ t2x41=true := Bool.and_eq_true_iff.mpr ⟨t2x82ok,t2x83ok⟩
def t2x20 : Tree := .d (2359296) t2x40 t2x41
lemma t2x20ok : treeCheck nodes v2 ⟨2097152,2621440,-8388608,8388608⟩ t2x20=true := Bool.and_eq_true_iff.mpr ⟨t2x40ok,t2x41ok⟩
def t2x168 : Tree := .leaf ⟨false,7968488,2686976,0,8388608,-8388608,8388608⟩
lemma t2x168ok : treeCheck nodes v2 ⟨2621440,2686976,-8388608,8388608⟩ t2x168=true := by decide +kernel
def t2x169 : Tree := .leaf ⟨false,7946629,2752512,0,8388608,-8388608,8388608⟩
lemma t2x169ok : treeCheck nodes v2 ⟨2686976,2752512,-8388608,8388608⟩ t2x169=true := by decide +kernel
def t2x84 : Tree := .d (2686976) t2x168 t2x169
lemma t2x84ok : treeCheck nodes v2 ⟨2621440,2752512,-8388608,8388608⟩ t2x84=true := Bool.and_eq_true_iff.mpr ⟨t2x168ok,t2x169ok⟩
def t2x170 : Tree := .leaf ⟨false,7924167,2818048,0,8388608,-8388608,8388608⟩
lemma t2x170ok : treeCheck nodes v2 ⟨2752512,2818048,-8388608,8388608⟩ t2x170=true := by decide +kernel
def t2x171 : Tree := .leaf ⟨false,7901099,2883584,0,8388608,-8388608,8388608⟩
lemma t2x171ok : treeCheck nodes v2 ⟨2818048,2883584,-8388608,8388608⟩ t2x171=true := by decide +kernel
def t2x85 : Tree := .d (2818048) t2x170 t2x171
lemma t2x85ok : treeCheck nodes v2 ⟨2752512,2883584,-8388608,8388608⟩ t2x85=true := Bool.and_eq_true_iff.mpr ⟨t2x170ok,t2x171ok⟩
def t2x42 : Tree := .d (2752512) t2x84 t2x85
lemma t2x42ok : treeCheck nodes v2 ⟨2621440,2883584,-8388608,8388608⟩ t2x42=true := Bool.and_eq_true_iff.mpr ⟨t2x84ok,t2x85ok⟩
def t2x172 : Tree := .leaf ⟨false,7877417,2949120,0,8388608,-8388608,8388608⟩
lemma t2x172ok : treeCheck nodes v2 ⟨2883584,2949120,-8388608,8388608⟩ t2x172=true := by decide +kernel
def t2x173 : Tree := .leaf ⟨false,7853117,3014656,0,8388608,-8388608,8388608⟩
lemma t2x173ok : treeCheck nodes v2 ⟨2949120,3014656,-8388608,8388608⟩ t2x173=true := by decide +kernel
def t2x86 : Tree := .d (2949120) t2x172 t2x173
lemma t2x86ok : treeCheck nodes v2 ⟨2883584,3014656,-8388608,8388608⟩ t2x86=true := Bool.and_eq_true_iff.mpr ⟨t2x172ok,t2x173ok⟩
def t2x87 : Tree := .leaf ⟨false,7828193,3145728,0,8388608,-8388608,8388608⟩
lemma t2x87ok : treeCheck nodes v2 ⟨3014656,3145728,-8388608,8388608⟩ t2x87=true := by decide +kernel
def t2x43 : Tree := .d (3014656) t2x86 t2x87
lemma t2x43ok : treeCheck nodes v2 ⟨2883584,3145728,-8388608,8388608⟩ t2x43=true := Bool.and_eq_true_iff.mpr ⟨t2x86ok,t2x87ok⟩
def t2x21 : Tree := .d (2883584) t2x42 t2x43
lemma t2x21ok : treeCheck nodes v2 ⟨2621440,3145728,-8388608,8388608⟩ t2x21=true := Bool.and_eq_true_iff.mpr ⟨t2x42ok,t2x43ok⟩
def t2x10 : Tree := .d (2621440) t2x20 t2x21
lemma t2x10ok : treeCheck nodes v2 ⟨2097152,3145728,-8388608,8388608⟩ t2x10=true := Bool.and_eq_true_iff.mpr ⟨t2x20ok,t2x21ok⟩
def t2x88 : Tree := .leaf ⟨false,7776448,3276800,0,8388608,-8388608,8388608⟩
lemma t2x88ok : treeCheck nodes v2 ⟨3145728,3276800,-8388608,8388608⟩ t2x88=true := by decide +kernel
def t2x89 : Tree := .leaf ⟨false,7722133,3407872,0,8388608,-8388608,8388608⟩
lemma t2x89ok : treeCheck nodes v2 ⟨3276800,3407872,-8388608,8388608⟩ t2x89=true := by decide +kernel
def t2x44 : Tree := .d (3276800) t2x88 t2x89
lemma t2x44ok : treeCheck nodes v2 ⟨3145728,3407872,-8388608,8388608⟩ t2x44=true := Bool.and_eq_true_iff.mpr ⟨t2x88ok,t2x89ok⟩
def t2x90 : Tree := .leaf ⟨false,7665191,3538944,0,8388608,-8388608,8388608⟩
lemma t2x90ok : treeCheck nodes v2 ⟨3407872,3538944,-8388608,8388608⟩ t2x90=true := by decide +kernel
def t2x91 : Tree := .leaf ⟨false,7605566,3670016,0,8388608,-8388608,8388608⟩
lemma t2x91ok : treeCheck nodes v2 ⟨3538944,3670016,-8388608,8388608⟩ t2x91=true := by decide +kernel
def t2x45 : Tree := .d (3538944) t2x90 t2x91
lemma t2x45ok : treeCheck nodes v2 ⟨3407872,3670016,-8388608,8388608⟩ t2x45=true := Bool.and_eq_true_iff.mpr ⟨t2x90ok,t2x91ok⟩
def t2x22 : Tree := .d (3407872) t2x44 t2x45
lemma t2x22ok : treeCheck nodes v2 ⟨3145728,3670016,-8388608,8388608⟩ t2x22=true := Bool.and_eq_true_iff.mpr ⟨t2x44ok,t2x45ok⟩
def t2x46 : Tree := .leaf ⟨false,7543191,3932160,0,8388608,-8388608,8388608⟩
lemma t2x46ok : treeCheck nodes v2 ⟨3670016,3932160,-8388608,8388608⟩ t2x46=true := by decide +kernel
def t2x47 : Tree := .leaf ⟨false,7409917,4194304,0,8388608,-8388608,8388608⟩
lemma t2x47ok : treeCheck nodes v2 ⟨3932160,4194304,-8388608,8388608⟩ t2x47=true := by decide +kernel
def t2x23 : Tree := .d (3932160) t2x46 t2x47
lemma t2x23ok : treeCheck nodes v2 ⟨3670016,4194304,-8388608,8388608⟩ t2x23=true := Bool.and_eq_true_iff.mpr ⟨t2x46ok,t2x47ok⟩
def t2x11 : Tree := .d (3670016) t2x22 t2x23
lemma t2x11ok : treeCheck nodes v2 ⟨3145728,4194304,-8388608,8388608⟩ t2x11=true := Bool.and_eq_true_iff.mpr ⟨t2x22ok,t2x23ok⟩
def t2x5 : Tree := .d (3145728) t2x10 t2x11
lemma t2x5ok : treeCheck nodes v2 ⟨2097152,4194304,-8388608,8388608⟩ t2x5=true := Bool.and_eq_true_iff.mpr ⟨t2x10ok,t2x11ok⟩
def t2x2 : Tree := .d (2097152) t2x4 t2x5
lemma t2x2ok : treeCheck nodes v2 ⟨0,4194304,-8388608,8388608⟩ t2x2=true := Bool.and_eq_true_iff.mpr ⟨t2x4ok,t2x5ok⟩
def t2x48 : Tree := .leaf ⟨false,7264748,4456448,0,8388608,-8388608,8388608⟩
lemma t2x48ok : treeCheck nodes v2 ⟨4194304,4456448,-8388608,8388608⟩ t2x48=true := by decide +kernel
def t2x49 : Tree := .leaf ⟨false,7106956,4718592,0,8388608,-8388608,8388608⟩
lemma t2x49ok : treeCheck nodes v2 ⟨4456448,4718592,-8388608,8388608⟩ t2x49=true := by decide +kernel
def t2x24 : Tree := .d (4456448) t2x48 t2x49
lemma t2x24ok : treeCheck nodes v2 ⟨4194304,4718592,-8388608,8388608⟩ t2x24=true := Bool.and_eq_true_iff.mpr ⟨t2x48ok,t2x49ok⟩
def t2x25 : Tree := .leaf ⟨false,6935679,5242880,0,8388608,-8388608,8388608⟩
lemma t2x25ok : treeCheck nodes v2 ⟨4718592,5242880,-8388608,8388608⟩ t2x25=true := by decide +kernel
def t2x12 : Tree := .d (4718592) t2x24 t2x25
lemma t2x12ok : treeCheck nodes v2 ⟨4194304,5242880,-8388608,8388608⟩ t2x12=true := Bool.and_eq_true_iff.mpr ⟨t2x24ok,t2x25ok⟩
def t2x26 : Tree := .leaf ⟨false,6548356,5767168,0,8388608,-8388608,8388608⟩
lemma t2x26ok : treeCheck nodes v2 ⟨5242880,5767168,-8388608,8388608⟩ t2x26=true := by decide +kernel
def t2x27 : Tree := .leaf ⟨false,6091677,6291456,0,8388608,-8388608,8388608⟩
lemma t2x27ok : treeCheck nodes v2 ⟨5767168,6291456,-8388608,8388608⟩ t2x27=true := by decide +kernel
def t2x13 : Tree := .d (5767168) t2x26 t2x27
lemma t2x13ok : treeCheck nodes v2 ⟨5242880,6291456,-8388608,8388608⟩ t2x13=true := Bool.and_eq_true_iff.mpr ⟨t2x26ok,t2x27ok⟩
def t2x6 : Tree := .d (5242880) t2x12 t2x13
lemma t2x6ok : treeCheck nodes v2 ⟨4194304,6291456,-8388608,8388608⟩ t2x6=true := Bool.and_eq_true_iff.mpr ⟨t2x12ok,t2x13ok⟩
def t2x14 : Tree := .leaf ⟨false,5548543,7340032,0,8388608,-8388608,8388608⟩
lemma t2x14ok : treeCheck nodes v2 ⟨6291456,7340032,-8388608,8388608⟩ t2x14=true := by decide +kernel
def t2x15 : Tree := .leaf ⟨false,4061118,8388608,0,8388608,-8388608,8388608⟩
lemma t2x15ok : treeCheck nodes v2 ⟨7340032,8388608,-8388608,8388608⟩ t2x15=true := by decide +kernel
def t2x7 : Tree := .d (7340032) t2x14 t2x15
lemma t2x7ok : treeCheck nodes v2 ⟨6291456,8388608,-8388608,8388608⟩ t2x7=true := Bool.and_eq_true_iff.mpr ⟨t2x14ok,t2x15ok⟩
def t2x3 : Tree := .d (6291456) t2x6 t2x7
lemma t2x3ok : treeCheck nodes v2 ⟨4194304,8388608,-8388608,8388608⟩ t2x3=true := Bool.and_eq_true_iff.mpr ⟨t2x6ok,t2x7ok⟩
def t2x1 : Tree := .d (4194304) t2x2 t2x3
lemma t2x1ok : treeCheck nodes v2 ⟨0,8388608,-8388608,8388608⟩ t2x1=true := Bool.and_eq_true_iff.mpr ⟨t2x2ok,t2x3ok⟩
def v3 : Band := ⟨1700000,2000000,3988924,7379513,14260633,16777216,6820387,5912201⟩
lemma b3ok : bandCheck v3=true := by decide +kernel
def t3x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t3x16ok : treeCheck nodes v3 ⟨0,524288,-8388608,8388608⟩ t3x16=true := by decide +kernel
def t3x34 : Tree := .leaf ⟨false,8372208,786432,0,8388608,-8388608,8388608⟩
lemma t3x34ok : treeCheck nodes v3 ⟨524288,786432,-8388608,8388608⟩ t3x34=true := by decide +kernel
def t3x35 : Tree := .leaf ⟨false,8351663,1048576,0,8388608,-8388608,8388608⟩
lemma t3x35ok : treeCheck nodes v3 ⟨786432,1048576,-8388608,8388608⟩ t3x35=true := by decide +kernel
def t3x17 : Tree := .d (786432) t3x34 t3x35
lemma t3x17ok : treeCheck nodes v3 ⟨524288,1048576,-8388608,8388608⟩ t3x17=true := Bool.and_eq_true_iff.mpr ⟨t3x34ok,t3x35ok⟩
def t3x8 : Tree := .d (524288) t3x16 t3x17
lemma t3x8ok : treeCheck nodes v3 ⟨0,1048576,-8388608,8388608⟩ t3x8=true := Bool.and_eq_true_iff.mpr ⟨t3x16ok,t3x17ok⟩
def t3x36 : Tree := .leaf ⟨false,8322814,1310720,0,8388608,-8388608,8388608⟩
lemma t3x36ok : treeCheck nodes v3 ⟨1048576,1310720,-8388608,8388608⟩ t3x36=true := by decide +kernel
def t3x37 : Tree := .leaf ⟨false,8285576,1572864,0,8388608,-8388608,8388608⟩
lemma t3x37ok : treeCheck nodes v3 ⟨1310720,1572864,-8388608,8388608⟩ t3x37=true := by decide +kernel
def t3x18 : Tree := .d (1310720) t3x36 t3x37
lemma t3x18ok : treeCheck nodes v3 ⟨1048576,1572864,-8388608,8388608⟩ t3x18=true := Bool.and_eq_true_iff.mpr ⟨t3x36ok,t3x37ok⟩
def t3x76 : Tree := .leaf ⟨false,8239833,1703936,0,8388608,-8388608,8388608⟩
lemma t3x76ok : treeCheck nodes v3 ⟨1572864,1703936,-8388608,8388608⟩ t3x76=true := by decide +kernel
def t3x77 : Tree := .leaf ⟨false,8213730,1835008,0,8388608,-8388608,8388608⟩
lemma t3x77ok : treeCheck nodes v3 ⟨1703936,1835008,-8388608,8388608⟩ t3x77=true := by decide +kernel
def t3x38 : Tree := .d (1703936) t3x76 t3x77
lemma t3x38ok : treeCheck nodes v3 ⟨1572864,1835008,-8388608,8388608⟩ t3x38=true := Bool.and_eq_true_iff.mpr ⟨t3x76ok,t3x77ok⟩
def t3x78 : Tree := .leaf ⟨false,8185444,1966080,0,8388608,-8388608,8388608⟩
lemma t3x78ok : treeCheck nodes v3 ⟨1835008,1966080,-8388608,8388608⟩ t3x78=true := by decide +kernel
def t3x79 : Tree := .leaf ⟨false,8154954,2097152,0,8388608,-8388608,8388608⟩
lemma t3x79ok : treeCheck nodes v3 ⟨1966080,2097152,-8388608,8388608⟩ t3x79=true := by decide +kernel
def t3x39 : Tree := .d (1966080) t3x78 t3x79
lemma t3x39ok : treeCheck nodes v3 ⟨1835008,2097152,-8388608,8388608⟩ t3x39=true := Bool.and_eq_true_iff.mpr ⟨t3x78ok,t3x79ok⟩
def t3x19 : Tree := .d (1835008) t3x38 t3x39
lemma t3x19ok : treeCheck nodes v3 ⟨1572864,2097152,-8388608,8388608⟩ t3x19=true := Bool.and_eq_true_iff.mpr ⟨t3x38ok,t3x39ok⟩
def t3x9 : Tree := .d (1572864) t3x18 t3x19
lemma t3x9ok : treeCheck nodes v3 ⟨1048576,2097152,-8388608,8388608⟩ t3x9=true := Bool.and_eq_true_iff.mpr ⟨t3x18ok,t3x19ok⟩
def t3x4 : Tree := .d (1048576) t3x8 t3x9
lemma t3x4ok : treeCheck nodes v3 ⟨0,2097152,-8388608,8388608⟩ t3x4=true := Bool.and_eq_true_iff.mpr ⟨t3x8ok,t3x9ok⟩
def t3x80 : Tree := .leaf ⟨false,8122235,2228224,0,8388608,-8388608,8388608⟩
lemma t3x80ok : treeCheck nodes v3 ⟨2097152,2228224,-8388608,8388608⟩ t3x80=true := by decide +kernel
def t3x81 : Tree := .leaf ⟨false,8087260,2359296,0,8388608,-8388608,8388608⟩
lemma t3x81ok : treeCheck nodes v3 ⟨2228224,2359296,-8388608,8388608⟩ t3x81=true := by decide +kernel
def t3x40 : Tree := .d (2228224) t3x80 t3x81
lemma t3x40ok : treeCheck nodes v3 ⟨2097152,2359296,-8388608,8388608⟩ t3x40=true := Bool.and_eq_true_iff.mpr ⟨t3x80ok,t3x81ok⟩
def t3x41 : Tree := .leaf ⟨false,8049998,2621440,0,8388608,-8388608,8388608⟩
lemma t3x41ok : treeCheck nodes v3 ⟨2359296,2621440,-8388608,8388608⟩ t3x41=true := by decide +kernel
def t3x20 : Tree := .d (2359296) t3x40 t3x41
lemma t3x20ok : treeCheck nodes v3 ⟨2097152,2621440,-8388608,8388608⟩ t3x20=true := Bool.and_eq_true_iff.mpr ⟨t3x40ok,t3x41ok⟩
def t3x42 : Tree := .leaf ⟨false,7968488,2883584,0,8388608,-8388608,8388608⟩
lemma t3x42ok : treeCheck nodes v3 ⟨2621440,2883584,-8388608,8388608⟩ t3x42=true := by decide +kernel
def t3x43 : Tree := .leaf ⟨false,7877417,3145728,0,8388608,-8388608,8388608⟩
lemma t3x43ok : treeCheck nodes v3 ⟨2883584,3145728,-8388608,8388608⟩ t3x43=true := by decide +kernel
def t3x21 : Tree := .d (2883584) t3x42 t3x43
lemma t3x21ok : treeCheck nodes v3 ⟨2621440,3145728,-8388608,8388608⟩ t3x21=true := Bool.and_eq_true_iff.mpr ⟨t3x42ok,t3x43ok⟩
def t3x10 : Tree := .d (2621440) t3x20 t3x21
lemma t3x10ok : treeCheck nodes v3 ⟨2097152,3145728,-8388608,8388608⟩ t3x10=true := Bool.and_eq_true_iff.mpr ⟨t3x20ok,t3x21ok⟩
def t3x44 : Tree := .leaf ⟨false,7776448,3407872,0,8388608,-8388608,8388608⟩
lemma t3x44ok : treeCheck nodes v3 ⟨3145728,3407872,-8388608,8388608⟩ t3x44=true := by decide +kernel
def t3x45 : Tree := .leaf ⟨false,7665191,3670016,0,8388608,-8388608,8388608⟩
lemma t3x45ok : treeCheck nodes v3 ⟨3407872,3670016,-8388608,8388608⟩ t3x45=true := by decide +kernel
def t3x22 : Tree := .d (3407872) t3x44 t3x45
lemma t3x22ok : treeCheck nodes v3 ⟨3145728,3670016,-8388608,8388608⟩ t3x22=true := Bool.and_eq_true_iff.mpr ⟨t3x44ok,t3x45ok⟩
def t3x23 : Tree := .leaf ⟨false,7543191,4194304,0,8388608,-8388608,8388608⟩
lemma t3x23ok : treeCheck nodes v3 ⟨3670016,4194304,-8388608,8388608⟩ t3x23=true := by decide +kernel
def t3x11 : Tree := .d (3670016) t3x22 t3x23
lemma t3x11ok : treeCheck nodes v3 ⟨3145728,4194304,-8388608,8388608⟩ t3x11=true := Bool.and_eq_true_iff.mpr ⟨t3x22ok,t3x23ok⟩
def t3x5 : Tree := .d (3145728) t3x10 t3x11
lemma t3x5ok : treeCheck nodes v3 ⟨2097152,4194304,-8388608,8388608⟩ t3x5=true := Bool.and_eq_true_iff.mpr ⟨t3x10ok,t3x11ok⟩
def t3x2 : Tree := .d (2097152) t3x4 t3x5
lemma t3x2ok : treeCheck nodes v3 ⟨0,4194304,-8388608,8388608⟩ t3x2=true := Bool.and_eq_true_iff.mpr ⟨t3x4ok,t3x5ok⟩
def t3x24 : Tree := .leaf ⟨false,7264748,4718592,0,8388608,-8388608,8388608⟩
lemma t3x24ok : treeCheck nodes v3 ⟨4194304,4718592,-8388608,8388608⟩ t3x24=true := by decide +kernel
def t3x25 : Tree := .leaf ⟨false,6935679,5242880,0,8388608,-8388608,8388608⟩
lemma t3x25ok : treeCheck nodes v3 ⟨4718592,5242880,-8388608,8388608⟩ t3x25=true := by decide +kernel
def t3x12 : Tree := .d (4718592) t3x24 t3x25
lemma t3x12ok : treeCheck nodes v3 ⟨4194304,5242880,-8388608,8388608⟩ t3x12=true := Bool.and_eq_true_iff.mpr ⟨t3x24ok,t3x25ok⟩
def t3x13 : Tree := .leaf ⟨false,6548356,6291456,0,8388608,-8388608,8388608⟩
lemma t3x13ok : treeCheck nodes v3 ⟨5242880,6291456,-8388608,8388608⟩ t3x13=true := by decide +kernel
def t3x6 : Tree := .d (5242880) t3x12 t3x13
lemma t3x6ok : treeCheck nodes v3 ⟨4194304,6291456,-8388608,8388608⟩ t3x6=true := Bool.and_eq_true_iff.mpr ⟨t3x12ok,t3x13ok⟩
def t3x14 : Tree := .leaf ⟨false,5548543,7340032,0,8388608,-8388608,8388608⟩
lemma t3x14ok : treeCheck nodes v3 ⟨6291456,7340032,-8388608,8388608⟩ t3x14=true := by decide +kernel
def t3x15 : Tree := .leaf ⟨false,4061118,8388608,0,8388608,-8388608,8388608⟩
lemma t3x15ok : treeCheck nodes v3 ⟨7340032,8388608,-8388608,8388608⟩ t3x15=true := by decide +kernel
def t3x7 : Tree := .d (7340032) t3x14 t3x15
lemma t3x7ok : treeCheck nodes v3 ⟨6291456,8388608,-8388608,8388608⟩ t3x7=true := Bool.and_eq_true_iff.mpr ⟨t3x14ok,t3x15ok⟩
def t3x3 : Tree := .d (6291456) t3x6 t3x7
lemma t3x3ok : treeCheck nodes v3 ⟨4194304,8388608,-8388608,8388608⟩ t3x3=true := Bool.and_eq_true_iff.mpr ⟨t3x6ok,t3x7ok⟩
def t3x1 : Tree := .d (4194304) t3x2 t3x3
lemma t3x1ok : treeCheck nodes v3 ⟨0,8388608,-8388608,8388608⟩ t3x1=true := Bool.and_eq_true_iff.mpr ⟨t3x2ok,t3x3ok⟩
def v4 : Band := ⟨2000000,2500000,3406929,7665609,16777216,20971520,5882792,4798294⟩
lemma b4ok : bandCheck v4=true := by decide +kernel
def t4x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t4x16ok : treeCheck nodes v4 ⟨0,524288,-8388608,8388608⟩ t4x16=true := by decide +kernel
def t4x17 : Tree := .leaf ⟨false,8372208,1048576,0,8388608,-8388608,8388608⟩
lemma t4x17ok : treeCheck nodes v4 ⟨524288,1048576,-8388608,8388608⟩ t4x17=true := by decide +kernel
def t4x8 : Tree := .d (524288) t4x16 t4x17
lemma t4x8ok : treeCheck nodes v4 ⟨0,1048576,-8388608,8388608⟩ t4x8=true := Bool.and_eq_true_iff.mpr ⟨t4x16ok,t4x17ok⟩
def t4x36 : Tree := .leaf ⟨false,8322814,1310720,0,8388608,-8388608,8388608⟩
lemma t4x36ok : treeCheck nodes v4 ⟨1048576,1310720,-8388608,8388608⟩ t4x36=true := by decide +kernel
def t4x37 : Tree := .leaf ⟨false,8285576,1572864,0,8388608,-8388608,8388608⟩
lemma t4x37ok : treeCheck nodes v4 ⟨1310720,1572864,-8388608,8388608⟩ t4x37=true := by decide +kernel
def t4x18 : Tree := .d (1310720) t4x36 t4x37
lemma t4x18ok : treeCheck nodes v4 ⟨1048576,1572864,-8388608,8388608⟩ t4x18=true := Bool.and_eq_true_iff.mpr ⟨t4x36ok,t4x37ok⟩
def t4x38 : Tree := .leaf ⟨false,8239833,1835008,0,8388608,-8388608,8388608⟩
lemma t4x38ok : treeCheck nodes v4 ⟨1572864,1835008,-8388608,8388608⟩ t4x38=true := by decide +kernel
def t4x39 : Tree := .leaf ⟨false,8185444,2097152,0,8388608,-8388608,8388608⟩
lemma t4x39ok : treeCheck nodes v4 ⟨1835008,2097152,-8388608,8388608⟩ t4x39=true := by decide +kernel
def t4x19 : Tree := .d (1835008) t4x38 t4x39
lemma t4x19ok : treeCheck nodes v4 ⟨1572864,2097152,-8388608,8388608⟩ t4x19=true := Bool.and_eq_true_iff.mpr ⟨t4x38ok,t4x39ok⟩
def t4x9 : Tree := .d (1572864) t4x18 t4x19
lemma t4x9ok : treeCheck nodes v4 ⟨1048576,2097152,-8388608,8388608⟩ t4x9=true := Bool.and_eq_true_iff.mpr ⟨t4x18ok,t4x19ok⟩
def t4x4 : Tree := .d (1048576) t4x8 t4x9
lemma t4x4ok : treeCheck nodes v4 ⟨0,2097152,-8388608,8388608⟩ t4x4=true := Bool.and_eq_true_iff.mpr ⟨t4x8ok,t4x9ok⟩
def t4x20 : Tree := .leaf ⟨false,8122235,2621440,0,8388608,-8388608,8388608⟩
lemma t4x20ok : treeCheck nodes v4 ⟨2097152,2621440,-8388608,8388608⟩ t4x20=true := by decide +kernel
def t4x21 : Tree := .leaf ⟨false,7968488,3145728,0,8388608,-8388608,8388608⟩
lemma t4x21ok : treeCheck nodes v4 ⟨2621440,3145728,-8388608,8388608⟩ t4x21=true := by decide +kernel
def t4x10 : Tree := .d (2621440) t4x20 t4x21
lemma t4x10ok : treeCheck nodes v4 ⟨2097152,3145728,-8388608,8388608⟩ t4x10=true := Bool.and_eq_true_iff.mpr ⟨t4x20ok,t4x21ok⟩
def t4x22 : Tree := .leaf ⟨false,7776448,3670016,0,8388608,-8388608,8388608⟩
lemma t4x22ok : treeCheck nodes v4 ⟨3145728,3670016,-8388608,8388608⟩ t4x22=true := by decide +kernel
def t4x23 : Tree := .leaf ⟨false,7543191,4194304,0,8388608,-8388608,8388608⟩
lemma t4x23ok : treeCheck nodes v4 ⟨3670016,4194304,-8388608,8388608⟩ t4x23=true := by decide +kernel
def t4x11 : Tree := .d (3670016) t4x22 t4x23
lemma t4x11ok : treeCheck nodes v4 ⟨3145728,4194304,-8388608,8388608⟩ t4x11=true := Bool.and_eq_true_iff.mpr ⟨t4x22ok,t4x23ok⟩
def t4x5 : Tree := .d (3145728) t4x10 t4x11
lemma t4x5ok : treeCheck nodes v4 ⟨2097152,4194304,-8388608,8388608⟩ t4x5=true := Bool.and_eq_true_iff.mpr ⟨t4x10ok,t4x11ok⟩
def t4x2 : Tree := .d (2097152) t4x4 t4x5
lemma t4x2ok : treeCheck nodes v4 ⟨0,4194304,-8388608,8388608⟩ t4x2=true := Bool.and_eq_true_iff.mpr ⟨t4x4ok,t4x5ok⟩
def t4x12 : Tree := .leaf ⟨false,7264748,5242880,0,8388608,-8388608,8388608⟩
lemma t4x12ok : treeCheck nodes v4 ⟨4194304,5242880,-8388608,8388608⟩ t4x12=true := by decide +kernel
def t4x13 : Tree := .leaf ⟨false,6548356,6291456,0,8388608,-8388608,8388608⟩
lemma t4x13ok : treeCheck nodes v4 ⟨5242880,6291456,-8388608,8388608⟩ t4x13=true := by decide +kernel
def t4x6 : Tree := .d (5242880) t4x12 t4x13
lemma t4x6ok : treeCheck nodes v4 ⟨4194304,6291456,-8388608,8388608⟩ t4x6=true := Bool.and_eq_true_iff.mpr ⟨t4x12ok,t4x13ok⟩
def t4x7 : Tree := .leaf ⟨false,5548543,8388608,0,8388608,-8388608,8388608⟩
lemma t4x7ok : treeCheck nodes v4 ⟨6291456,8388608,-8388608,8388608⟩ t4x7=true := by decide +kernel
def t4x3 : Tree := .d (6291456) t4x6 t4x7
lemma t4x3ok : treeCheck nodes v4 ⟨4194304,8388608,-8388608,8388608⟩ t4x3=true := Bool.and_eq_true_iff.mpr ⟨t4x6ok,t4x7ok⟩
def t4x1 : Tree := .d (4194304) t4x2 t4x3
lemma t4x1ok : treeCheck nodes v4 ⟨0,8388608,-8388608,8388608⟩ t4x1=true := Bool.and_eq_true_iff.mpr ⟨t4x2ok,t4x3ok⟩
def v5 : Band := ⟨2500000,3000000,2866748,7883558,20971520,25165824,4812368,4054793⟩
lemma b5ok : bandCheck v5=true := by decide +kernel
def t5x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t5x16ok : treeCheck nodes v5 ⟨0,524288,-8388608,8388608⟩ t5x16=true := by decide +kernel
def t5x17 : Tree := .leaf ⟨false,8372208,1048576,0,8388608,-8388608,8388608⟩
lemma t5x17ok : treeCheck nodes v5 ⟨524288,1048576,-8388608,8388608⟩ t5x17=true := by decide +kernel
def t5x8 : Tree := .d (524288) t5x16 t5x17
lemma t5x8ok : treeCheck nodes v5 ⟨0,1048576,-8388608,8388608⟩ t5x8=true := Bool.and_eq_true_iff.mpr ⟨t5x16ok,t5x17ok⟩
def t5x18 : Tree := .leaf ⟨false,8322814,1572864,0,8388608,-8388608,8388608⟩
lemma t5x18ok : treeCheck nodes v5 ⟨1048576,1572864,-8388608,8388608⟩ t5x18=true := by decide +kernel
def t5x19 : Tree := .leaf ⟨false,8239833,2097152,0,8388608,-8388608,8388608⟩
lemma t5x19ok : treeCheck nodes v5 ⟨1572864,2097152,-8388608,8388608⟩ t5x19=true := by decide +kernel
def t5x9 : Tree := .d (1572864) t5x18 t5x19
lemma t5x9ok : treeCheck nodes v5 ⟨1048576,2097152,-8388608,8388608⟩ t5x9=true := Bool.and_eq_true_iff.mpr ⟨t5x18ok,t5x19ok⟩
def t5x4 : Tree := .d (1048576) t5x8 t5x9
lemma t5x4ok : treeCheck nodes v5 ⟨0,2097152,-8388608,8388608⟩ t5x4=true := Bool.and_eq_true_iff.mpr ⟨t5x8ok,t5x9ok⟩
def t5x10 : Tree := .leaf ⟨false,8122235,3145728,0,8388608,-8388608,8388608⟩
lemma t5x10ok : treeCheck nodes v5 ⟨2097152,3145728,-8388608,8388608⟩ t5x10=true := by decide +kernel
def t5x11 : Tree := .leaf ⟨false,7776448,4194304,0,8388608,-8388608,8388608⟩
lemma t5x11ok : treeCheck nodes v5 ⟨3145728,4194304,-8388608,8388608⟩ t5x11=true := by decide +kernel
def t5x5 : Tree := .d (3145728) t5x10 t5x11
lemma t5x5ok : treeCheck nodes v5 ⟨2097152,4194304,-8388608,8388608⟩ t5x5=true := Bool.and_eq_true_iff.mpr ⟨t5x10ok,t5x11ok⟩
def t5x2 : Tree := .d (2097152) t5x4 t5x5
lemma t5x2ok : treeCheck nodes v5 ⟨0,4194304,-8388608,8388608⟩ t5x2=true := Bool.and_eq_true_iff.mpr ⟨t5x4ok,t5x5ok⟩
def t5x6 : Tree := .leaf ⟨false,7264748,6291456,0,8388608,-8388608,8388608⟩
lemma t5x6ok : treeCheck nodes v5 ⟨4194304,6291456,-8388608,8388608⟩ t5x6=true := by decide +kernel
def t5x7 : Tree := .leaf ⟨false,5548543,8388608,0,8388608,-8388608,8388608⟩
lemma t5x7ok : treeCheck nodes v5 ⟨6291456,8388608,-8388608,8388608⟩ t5x7=true := by decide +kernel
def t5x3 : Tree := .d (6291456) t5x6 t5x7
lemma t5x3ok : treeCheck nodes v5 ⟨4194304,8388608,-8388608,8388608⟩ t5x3=true := Bool.and_eq_true_iff.mpr ⟨t5x6ok,t5x7ok⟩
def t5x1 : Tree := .d (4194304) t5x2 t5x3
lemma t5x1ok : treeCheck nodes v5 ⟨0,8388608,-8388608,8388608⟩ t5x1=true := Bool.and_eq_true_iff.mpr ⟨t5x2ok,t5x3ok⟩
end GateChecker.M0

end

section

namespace GateChecker.M1
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false
def n0 : Node := ⟨0,8388608,-5931642,-5931641,10273905,0,528⟩
def n1 : Node := ⟨131072,8387585,-5930194,-5930192,10273069,207233,544⟩
def n2 : Node := ⟨262144,8384513,-5925850,-5925848,10270562,414406,560⟩
def n3 : Node := ⟨393216,8379398,-5918609,-5918607,10266386,621456,576⟩
def n4 : Node := ⟨524288,8372240,-5908472,-5908470,10260545,828325,592⟩
def n5 : Node := ⟨655360,8363048,-5895439,-5895437,10253045,1034951,608⟩
def n6 : Node := ⟨786432,8351825,-5879509,-5879507,10243894,1241274,624⟩
def n7 : Node := ⟨917504,8338582,-5860683,-5860681,10233101,1447234,640⟩
def n8 : Node := ⟨1048576,8323328,-5838961,-5838959,10220675,1652769,656⟩
def n9 : Node := ⟨1179648,8306073,-5814342,-5814340,10206631,1857821,672⟩
def n10 : Node := ⟨1310720,8286831,-5786827,-5786825,10190982,2062328,688⟩
def n11 : Node := ⟨1441792,8265615,-5756416,-5756414,10173744,2266232,704⟩
def n12 : Node := ⟨1572864,8242441,-5723108,-5723106,10154935,2469472,720⟩
def n13 : Node := ⟨1703936,8217325,-5686904,-5686902,10134576,2671989,736⟩
def n14 : Node := ⟨1835008,8190286,-5647804,-5647802,10112687,2873725,752⟩
def n15 : Node := ⟨1966080,8161344,-5605808,-5605806,10089293,3074620,768⟩
def n16 : Node := ⟨2097152,8130518,-5560915,-5560913,10064418,3274615,784⟩
def n17 : Node := ⟨2228224,8097832,-5513126,-5513124,10038092,3473653,800⟩
def n18 : Node := ⟨2359296,8063308,-5462440,-5462438,10010345,3671676,816⟩
def n19 : Node := ⟨2490368,8026971,-5408859,-5408857,9981207,3868625,832⟩
def n20 : Node := ⟨2621440,7988848,-5352381,-5352379,9950715,4064444,848⟩
def n21 : Node := ⟨2752512,7948964,-5293006,-5293004,9918904,4259077,864⟩
def n22 : Node := ⟨2883584,7907349,-5230736,-5230734,9885815,4452466,880⟩
def n23 : Node := ⟨3014656,7864032,-5165569,-5165567,9851489,4644557,896⟩
def n24 : Node := ⟨3145728,7819043,-5097505,-5097503,9815972,4835293,912⟩
def n25 : Node := ⟨3276800,7772413,-5026546,-5026544,9779310,5024621,928⟩
def n26 : Node := ⟨3407872,7724176,-4952690,-4952688,9741554,5212486,944⟩
def n27 : Node := ⟨3538944,7674364,-4875938,-4875936,9702758,5398834,960⟩
def n28 : Node := ⟨3670016,7623012,-4796289,-4796287,9662978,5583613,976⟩
def n29 : Node := ⟨3801088,7570155,-4713744,-4713743,9622273,5766771,992⟩
def n30 : Node := ⟨3932160,7515829,-4628303,-4628301,9580706,5948255,1008⟩
def n31 : Node := ⟨4063232,7460072,-4539966,-4539964,9538346,6128016,1024⟩
def n32 : Node := ⟨4194304,7402921,-4448732,-4448730,9495260,6306003,4224⟩
def n33 : Node := ⟨4456448,7284592,-4257576,-4257574,9407215,6656461,4352⟩
def n34 : Node := ⟨4718592,7161157,-4054834,-4054832,9317211,6999248,4480⟩
def n35 : Node := ⟨4980736,7032942,-3840507,-3840505,9225955,7333997,4608⟩
def n36 : Node := ⟨5242880,6900281,-3614595,-3614593,9134224,7660360,4736⟩
def n37 : Node := ⟨5505024,6763514,-3377097,-3377096,9042872,7978009,4864⟩
def n38 : Node := ⟨5767168,6622987,-3128015,-3128013,8952833,8286636,4992⟩
def n39 : Node := ⟨6029312,6479050,-2867347,-2867345,8865124,8585957,5120⟩
def n40 : Node := ⟨6291456,6332054,-2595094,-2595092,8780846,8875714,5248⟩
def n41 : Node := ⟨6553600,6182353,-2311256,-2311254,8701187,9155679,5376⟩
def n42 : Node := ⟨6815744,6030299,-2015832,-2015831,8627417,9425655,5504⟩
def n43 : Node := ⟨7077888,5876243,-1708823,-1708822,8560889,9685480,5632⟩
def n44 : Node := ⟨7340032,5720534,-1390229,-1390228,8503028,9935031,5760⟩
def n45 : Node := ⟨7602176,5563515,-1060050,-1060049,8455321,10174229,5888⟩
def n46 : Node := ⟨7864320,5405525,-718285,-718284,8419304,10403042,6016⟩
def n47 : Node := ⟨8126464,5246895,-364936,-364934,8396543,10621488,6144⟩
def n48 : Node := ⟨8388608,5087948,0,0,8388608,10829647,25600⟩
def n49 : Node := ⟨8912896,4770359,764625,764626,8423384,11215734,26624⟩
def n50 : Node := ⟨9437184,4455157,1575592,1575593,8535294,11563315,27648⟩
def n51 : Node := ⟨9961472,4144560,2432899,2432901,8734286,11875760,28672⟩
def n52 : Node := ⟨10485760,3840585,3336548,3336549,9027808,12158062,29696⟩
def n53 : Node := ⟨11010048,3545030,4286537,4286539,9420359,12417141,30720⟩
def n54 : Node := ⟨11534336,3259462,5282867,5282869,9913498,12662153,31744⟩
def n55 : Node := ⟨12058624,2985215,6325539,6325541,10506246,12904792,32768⟩
def n56 : Node := ⟨12582912,2723383,7414551,7414553,11195729,13159525,33792⟩
def n57 : Node := ⟨13107200,2474830,8549904,8549906,11977881,13443698,34816⟩
def n58 : Node := ⟨13631488,2240194,9731598,9731601,12848065,13777417,35840⟩
def n59 : Node := ⟨14155776,2019897,10959633,10959636,13801534,14183128,36864⟩
def n60 : Node := ⟨14680064,1814164,12234009,12234012,14833738,14684842,37888⟩
def n61 : Node := ⟨15204352,1623033,13554726,13554729,15940496,15307033,38912⟩
def n62 : Node := ⟨15728640,1446378,14921784,14921787,17118074,16073343,39936⟩
def n63 : Node := ⟨16252928,1283925,16335183,16335186,18363198,17005326,40960⟩
def n64 : Node := ⟨16777216,1135275,17794923,17794926,19673030,18121465,172032⟩
def n65 : Node := ⟨17825792,877273,20853425,20853429,22477415,20962201,180224⟩
def n66 : Node := ⟨18874368,667394,24097291,24097296,25515649,24674109,188416⟩
def n67 : Node := ⟨19922944,499855,27526521,27526527,28776350,29295198,196608⟩
def n68 : Node := ⟨20971520,368570,31141115,31141121,32251171,34843136,204800⟩
def n69 : Node := ⟨22020096,267553,34941072,34941079,35933934,41329950,212992⟩
def n70 : Node := ⟨23068672,191212,38926394,38926401,39820011,48769383,221184⟩
def n71 : Node := ⟨24117248,134535,43097079,43097087,43905892,57179419,229376⟩
def n72 : Node := ⟨25165824,93190,47453128,47453136,48188885,66582512,237568⟩
def n73 : Node := ⟨26214400,63550,51994540,51994550,52666893,77004982,245760⟩
def n74 : Node := ⟨27262976,42666,56721317,56721327,57338270,88476238,253952⟩
def n75 : Node := ⟨28311552,28200,61633457,61633468,62201709,101028078,262144⟩
def n76 : Node := ⟨29360128,18351,66730961,66730973,67256159,114694117,270336⟩
def n77 : Node := ⟨30408704,11756,72013829,72013842,72500769,129509356,278528⟩
def n78 : Node := ⟨31457280,7415,77482060,77482074,77934843,145509846,286720⟩
def n79 : Node := ⟨32505856,4604,83135655,83135670,83557809,162732447,294912⟩
def n80 : Node := ⟨33554432,2815,88974615,88974630,89369192,181214645,947072⟩
def n81 : Node := ⟨35389440,1146,99638825,99638842,99991331,216703816,990976⟩
def n82 : Node := ⟨37224448,445,110870711,110870731,111187616,256373074,1034880⟩
def n83 : Node := ⟨39059456,166,122670274,122670296,122956774,300430959,1078784⟩
def n84 : Node := ⟨40894464,59,135037514,135037538,135297831,349087683,1122688⟩
def n85 : Node := ⟨42729472,20,147972431,147972456,148210032,402554634,1166592⟩
def n86 : Node := ⟨44564480,7,161475023,161475052,161692788,461044042,1210496⟩
def n87 : Node := ⟨46399488,3,175545293,175545324,175745626,524768751,1254400⟩
def n88 : Node := ⟨48234496,1,190183239,190183272,190368172,593942065,1298304⟩
def n89 : Node := ⟨50069504,1,205388862,205388897,205560118,668777632,1298304⟩
def n90 : Node := ⟨50331648,1,207607435,207607470,207776863,679943123,4055040⟩
def n91 : Node := ⟨53477376,1,235133956,235133997,235283569,823510107,4276224⟩
def n92 : Node := ⟨56623104,1,264328752,264328797,264461854,985514893,4497408⟩
def n93 : Node := ⟨59768832,1,295191821,295191872,295311020,1167037765,4718592⟩
def n94 : Node := ⟨62914560,1,327723165,327723221,327830541,1369159818,4939776⟩
def n95 : Node := ⟨66060288,1,361922782,361922844,362020022,1592962722,4939776⟩
def n96 : Node := ⟨67108864,1,373693383,373693446,373787563,1672568674,557056⟩
def z96 : List Node := n96 :: []
def z95 : List Node := n95 :: z96
def z94 : List Node := n94 :: z95
def z93 : List Node := n93 :: z94
def z92 : List Node := n92 :: z93
def z91 : List Node := n91 :: z92
def z90 : List Node := n90 :: z91
def z89 : List Node := n89 :: z90
def z88 : List Node := n88 :: z89
def z87 : List Node := n87 :: z88
def z86 : List Node := n86 :: z87
def z85 : List Node := n85 :: z86
def z84 : List Node := n84 :: z85
def z83 : List Node := n83 :: z84
def z82 : List Node := n82 :: z83
def z81 : List Node := n81 :: z82
def z80 : List Node := n80 :: z81
def z79 : List Node := n79 :: z80
def z78 : List Node := n78 :: z79
def z77 : List Node := n77 :: z78
def z76 : List Node := n76 :: z77
def z75 : List Node := n75 :: z76
def z74 : List Node := n74 :: z75
def z73 : List Node := n73 :: z74
def z72 : List Node := n72 :: z73
def z71 : List Node := n71 :: z72
def z70 : List Node := n70 :: z71
def z69 : List Node := n69 :: z70
def z68 : List Node := n68 :: z69
def z67 : List Node := n67 :: z68
def z66 : List Node := n66 :: z67
def z65 : List Node := n65 :: z66
def z64 : List Node := n64 :: z65
def z63 : List Node := n63 :: z64
def z62 : List Node := n62 :: z63
def z61 : List Node := n61 :: z62
def z60 : List Node := n60 :: z61
def z59 : List Node := n59 :: z60
def z58 : List Node := n58 :: z59
def z57 : List Node := n57 :: z58
def z56 : List Node := n56 :: z57
def z55 : List Node := n55 :: z56
def z54 : List Node := n54 :: z55
def z53 : List Node := n53 :: z54
def z52 : List Node := n52 :: z53
def z51 : List Node := n51 :: z52
def z50 : List Node := n50 :: z51
def z49 : List Node := n49 :: z50
def z48 : List Node := n48 :: z49
def z47 : List Node := n47 :: z48
def z46 : List Node := n46 :: z47
def z45 : List Node := n45 :: z46
def z44 : List Node := n44 :: z45
def z43 : List Node := n43 :: z44
def z42 : List Node := n42 :: z43
def z41 : List Node := n41 :: z42
def z40 : List Node := n40 :: z41
def z39 : List Node := n39 :: z40
def z38 : List Node := n38 :: z39
def z37 : List Node := n37 :: z38
def z36 : List Node := n36 :: z37
def z35 : List Node := n35 :: z36
def z34 : List Node := n34 :: z35
def z33 : List Node := n33 :: z34
def z32 : List Node := n32 :: z33
def z31 : List Node := n31 :: z32
def z30 : List Node := n30 :: z31
def z29 : List Node := n29 :: z30
def z28 : List Node := n28 :: z29
def z27 : List Node := n27 :: z28
def z26 : List Node := n26 :: z27
def z25 : List Node := n25 :: z26
def z24 : List Node := n24 :: z25
def z23 : List Node := n23 :: z24
def z22 : List Node := n22 :: z23
def z21 : List Node := n21 :: z22
def z20 : List Node := n20 :: z21
def z19 : List Node := n19 :: z20
def z18 : List Node := n18 :: z19
def z17 : List Node := n17 :: z18
def z16 : List Node := n16 :: z17
def z15 : List Node := n15 :: z16
def z14 : List Node := n14 :: z15
def z13 : List Node := n13 :: z14
def z12 : List Node := n12 :: z13
def z11 : List Node := n11 :: z12
def z10 : List Node := n10 :: z11
def z9 : List Node := n9 :: z10
def z8 : List Node := n8 :: z9
def z7 : List Node := n7 :: z8
def z6 : List Node := n6 :: z7
def z5 : List Node := n5 :: z6
def z4 : List Node := n4 :: z5
def z3 : List Node := n3 :: z4
def z2 : List Node := n2 :: z3
def z1 : List Node := n1 :: z2
def z0 : List Node := n0 :: z1
def nodes := z0
lemma starts : PanelChain.start nodes=true := by decide +kernel
lemma check96 : nodeCheck n96=true := by decide +kernel
lemma ok96 : chainCheck z96=true := Bool.and_eq_true_iff.mpr ⟨check96,by decide +kernel⟩
lemma check95 : nodeCheck n95=true := by decide +kernel
lemma edge95 : edgeCheck n95 n96=true := by decide +kernel
lemma ok95 : chainCheck z95=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check95,edge95⟩,ok96⟩
lemma check94 : nodeCheck n94=true := by decide +kernel
lemma edge94 : edgeCheck n94 n95=true := by decide +kernel
lemma ok94 : chainCheck z94=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check94,edge94⟩,ok95⟩
lemma check93 : nodeCheck n93=true := by decide +kernel
lemma edge93 : edgeCheck n93 n94=true := by decide +kernel
lemma ok93 : chainCheck z93=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check93,edge93⟩,ok94⟩
lemma check92 : nodeCheck n92=true := by decide +kernel
lemma edge92 : edgeCheck n92 n93=true := by decide +kernel
lemma ok92 : chainCheck z92=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check92,edge92⟩,ok93⟩
lemma check91 : nodeCheck n91=true := by decide +kernel
lemma edge91 : edgeCheck n91 n92=true := by decide +kernel
lemma ok91 : chainCheck z91=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check91,edge91⟩,ok92⟩
lemma check90 : nodeCheck n90=true := by decide +kernel
lemma edge90 : edgeCheck n90 n91=true := by decide +kernel
lemma ok90 : chainCheck z90=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check90,edge90⟩,ok91⟩
lemma check89 : nodeCheck n89=true := by decide +kernel
lemma edge89 : edgeCheck n89 n90=true := by decide +kernel
lemma ok89 : chainCheck z89=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check89,edge89⟩,ok90⟩
lemma check88 : nodeCheck n88=true := by decide +kernel
lemma edge88 : edgeCheck n88 n89=true := by decide +kernel
lemma ok88 : chainCheck z88=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check88,edge88⟩,ok89⟩
lemma check87 : nodeCheck n87=true := by decide +kernel
lemma edge87 : edgeCheck n87 n88=true := by decide +kernel
lemma ok87 : chainCheck z87=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check87,edge87⟩,ok88⟩
lemma check86 : nodeCheck n86=true := by decide +kernel
lemma edge86 : edgeCheck n86 n87=true := by decide +kernel
lemma ok86 : chainCheck z86=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check86,edge86⟩,ok87⟩
lemma check85 : nodeCheck n85=true := by decide +kernel
lemma edge85 : edgeCheck n85 n86=true := by decide +kernel
lemma ok85 : chainCheck z85=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check85,edge85⟩,ok86⟩
lemma check84 : nodeCheck n84=true := by decide +kernel
lemma edge84 : edgeCheck n84 n85=true := by decide +kernel
lemma ok84 : chainCheck z84=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check84,edge84⟩,ok85⟩
lemma check83 : nodeCheck n83=true := by decide +kernel
lemma edge83 : edgeCheck n83 n84=true := by decide +kernel
lemma ok83 : chainCheck z83=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check83,edge83⟩,ok84⟩
lemma check82 : nodeCheck n82=true := by decide +kernel
lemma edge82 : edgeCheck n82 n83=true := by decide +kernel
lemma ok82 : chainCheck z82=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check82,edge82⟩,ok83⟩
lemma check81 : nodeCheck n81=true := by decide +kernel
lemma edge81 : edgeCheck n81 n82=true := by decide +kernel
lemma ok81 : chainCheck z81=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check81,edge81⟩,ok82⟩
lemma check80 : nodeCheck n80=true := by decide +kernel
lemma edge80 : edgeCheck n80 n81=true := by decide +kernel
lemma ok80 : chainCheck z80=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check80,edge80⟩,ok81⟩
lemma check79 : nodeCheck n79=true := by decide +kernel
lemma edge79 : edgeCheck n79 n80=true := by decide +kernel
lemma ok79 : chainCheck z79=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check79,edge79⟩,ok80⟩
lemma check78 : nodeCheck n78=true := by decide +kernel
lemma edge78 : edgeCheck n78 n79=true := by decide +kernel
lemma ok78 : chainCheck z78=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check78,edge78⟩,ok79⟩
lemma check77 : nodeCheck n77=true := by decide +kernel
lemma edge77 : edgeCheck n77 n78=true := by decide +kernel
lemma ok77 : chainCheck z77=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check77,edge77⟩,ok78⟩
lemma check76 : nodeCheck n76=true := by decide +kernel
lemma edge76 : edgeCheck n76 n77=true := by decide +kernel
lemma ok76 : chainCheck z76=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check76,edge76⟩,ok77⟩
lemma check75 : nodeCheck n75=true := by decide +kernel
lemma edge75 : edgeCheck n75 n76=true := by decide +kernel
lemma ok75 : chainCheck z75=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check75,edge75⟩,ok76⟩
lemma check74 : nodeCheck n74=true := by decide +kernel
lemma edge74 : edgeCheck n74 n75=true := by decide +kernel
lemma ok74 : chainCheck z74=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check74,edge74⟩,ok75⟩
lemma check73 : nodeCheck n73=true := by decide +kernel
lemma edge73 : edgeCheck n73 n74=true := by decide +kernel
lemma ok73 : chainCheck z73=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check73,edge73⟩,ok74⟩
lemma check72 : nodeCheck n72=true := by decide +kernel
lemma edge72 : edgeCheck n72 n73=true := by decide +kernel
lemma ok72 : chainCheck z72=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check72,edge72⟩,ok73⟩
lemma check71 : nodeCheck n71=true := by decide +kernel
lemma edge71 : edgeCheck n71 n72=true := by decide +kernel
lemma ok71 : chainCheck z71=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check71,edge71⟩,ok72⟩
lemma check70 : nodeCheck n70=true := by decide +kernel
lemma edge70 : edgeCheck n70 n71=true := by decide +kernel
lemma ok70 : chainCheck z70=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check70,edge70⟩,ok71⟩
lemma check69 : nodeCheck n69=true := by decide +kernel
lemma edge69 : edgeCheck n69 n70=true := by decide +kernel
lemma ok69 : chainCheck z69=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check69,edge69⟩,ok70⟩
lemma check68 : nodeCheck n68=true := by decide +kernel
lemma edge68 : edgeCheck n68 n69=true := by decide +kernel
lemma ok68 : chainCheck z68=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check68,edge68⟩,ok69⟩
lemma check67 : nodeCheck n67=true := by decide +kernel
lemma edge67 : edgeCheck n67 n68=true := by decide +kernel
lemma ok67 : chainCheck z67=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check67,edge67⟩,ok68⟩
lemma check66 : nodeCheck n66=true := by decide +kernel
lemma edge66 : edgeCheck n66 n67=true := by decide +kernel
lemma ok66 : chainCheck z66=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check66,edge66⟩,ok67⟩
lemma check65 : nodeCheck n65=true := by decide +kernel
lemma edge65 : edgeCheck n65 n66=true := by decide +kernel
lemma ok65 : chainCheck z65=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check65,edge65⟩,ok66⟩
lemma check64 : nodeCheck n64=true := by decide +kernel
lemma edge64 : edgeCheck n64 n65=true := by decide +kernel
lemma ok64 : chainCheck z64=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check64,edge64⟩,ok65⟩
lemma check63 : nodeCheck n63=true := by decide +kernel
lemma edge63 : edgeCheck n63 n64=true := by decide +kernel
lemma ok63 : chainCheck z63=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check63,edge63⟩,ok64⟩
lemma check62 : nodeCheck n62=true := by decide +kernel
lemma edge62 : edgeCheck n62 n63=true := by decide +kernel
lemma ok62 : chainCheck z62=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check62,edge62⟩,ok63⟩
lemma check61 : nodeCheck n61=true := by decide +kernel
lemma edge61 : edgeCheck n61 n62=true := by decide +kernel
lemma ok61 : chainCheck z61=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check61,edge61⟩,ok62⟩
lemma check60 : nodeCheck n60=true := by decide +kernel
lemma edge60 : edgeCheck n60 n61=true := by decide +kernel
lemma ok60 : chainCheck z60=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check60,edge60⟩,ok61⟩
lemma check59 : nodeCheck n59=true := by decide +kernel
lemma edge59 : edgeCheck n59 n60=true := by decide +kernel
lemma ok59 : chainCheck z59=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check59,edge59⟩,ok60⟩
lemma check58 : nodeCheck n58=true := by decide +kernel
lemma edge58 : edgeCheck n58 n59=true := by decide +kernel
lemma ok58 : chainCheck z58=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check58,edge58⟩,ok59⟩
lemma check57 : nodeCheck n57=true := by decide +kernel
lemma edge57 : edgeCheck n57 n58=true := by decide +kernel
lemma ok57 : chainCheck z57=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check57,edge57⟩,ok58⟩
lemma check56 : nodeCheck n56=true := by decide +kernel
lemma edge56 : edgeCheck n56 n57=true := by decide +kernel
lemma ok56 : chainCheck z56=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check56,edge56⟩,ok57⟩
lemma check55 : nodeCheck n55=true := by decide +kernel
lemma edge55 : edgeCheck n55 n56=true := by decide +kernel
lemma ok55 : chainCheck z55=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check55,edge55⟩,ok56⟩
lemma check54 : nodeCheck n54=true := by decide +kernel
lemma edge54 : edgeCheck n54 n55=true := by decide +kernel
lemma ok54 : chainCheck z54=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check54,edge54⟩,ok55⟩
lemma check53 : nodeCheck n53=true := by decide +kernel
lemma edge53 : edgeCheck n53 n54=true := by decide +kernel
lemma ok53 : chainCheck z53=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check53,edge53⟩,ok54⟩
lemma check52 : nodeCheck n52=true := by decide +kernel
lemma edge52 : edgeCheck n52 n53=true := by decide +kernel
lemma ok52 : chainCheck z52=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check52,edge52⟩,ok53⟩
lemma check51 : nodeCheck n51=true := by decide +kernel
lemma edge51 : edgeCheck n51 n52=true := by decide +kernel
lemma ok51 : chainCheck z51=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check51,edge51⟩,ok52⟩
lemma check50 : nodeCheck n50=true := by decide +kernel
lemma edge50 : edgeCheck n50 n51=true := by decide +kernel
lemma ok50 : chainCheck z50=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check50,edge50⟩,ok51⟩
lemma check49 : nodeCheck n49=true := by decide +kernel
lemma edge49 : edgeCheck n49 n50=true := by decide +kernel
lemma ok49 : chainCheck z49=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check49,edge49⟩,ok50⟩
lemma check48 : nodeCheck n48=true := by decide +kernel
lemma edge48 : edgeCheck n48 n49=true := by decide +kernel
lemma ok48 : chainCheck z48=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check48,edge48⟩,ok49⟩
lemma check47 : nodeCheck n47=true := by decide +kernel
lemma edge47 : edgeCheck n47 n48=true := by decide +kernel
lemma ok47 : chainCheck z47=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check47,edge47⟩,ok48⟩
lemma check46 : nodeCheck n46=true := by decide +kernel
lemma edge46 : edgeCheck n46 n47=true := by decide +kernel
lemma ok46 : chainCheck z46=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check46,edge46⟩,ok47⟩
lemma check45 : nodeCheck n45=true := by decide +kernel
lemma edge45 : edgeCheck n45 n46=true := by decide +kernel
lemma ok45 : chainCheck z45=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check45,edge45⟩,ok46⟩
lemma check44 : nodeCheck n44=true := by decide +kernel
lemma edge44 : edgeCheck n44 n45=true := by decide +kernel
lemma ok44 : chainCheck z44=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check44,edge44⟩,ok45⟩
lemma check43 : nodeCheck n43=true := by decide +kernel
lemma edge43 : edgeCheck n43 n44=true := by decide +kernel
lemma ok43 : chainCheck z43=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check43,edge43⟩,ok44⟩
lemma check42 : nodeCheck n42=true := by decide +kernel
lemma edge42 : edgeCheck n42 n43=true := by decide +kernel
lemma ok42 : chainCheck z42=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check42,edge42⟩,ok43⟩
lemma check41 : nodeCheck n41=true := by decide +kernel
lemma edge41 : edgeCheck n41 n42=true := by decide +kernel
lemma ok41 : chainCheck z41=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check41,edge41⟩,ok42⟩
lemma check40 : nodeCheck n40=true := by decide +kernel
lemma edge40 : edgeCheck n40 n41=true := by decide +kernel
lemma ok40 : chainCheck z40=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check40,edge40⟩,ok41⟩
lemma check39 : nodeCheck n39=true := by decide +kernel
lemma edge39 : edgeCheck n39 n40=true := by decide +kernel
lemma ok39 : chainCheck z39=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check39,edge39⟩,ok40⟩
lemma check38 : nodeCheck n38=true := by decide +kernel
lemma edge38 : edgeCheck n38 n39=true := by decide +kernel
lemma ok38 : chainCheck z38=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check38,edge38⟩,ok39⟩
lemma check37 : nodeCheck n37=true := by decide +kernel
lemma edge37 : edgeCheck n37 n38=true := by decide +kernel
lemma ok37 : chainCheck z37=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check37,edge37⟩,ok38⟩
lemma check36 : nodeCheck n36=true := by decide +kernel
lemma edge36 : edgeCheck n36 n37=true := by decide +kernel
lemma ok36 : chainCheck z36=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check36,edge36⟩,ok37⟩
lemma check35 : nodeCheck n35=true := by decide +kernel
lemma edge35 : edgeCheck n35 n36=true := by decide +kernel
lemma ok35 : chainCheck z35=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check35,edge35⟩,ok36⟩
lemma check34 : nodeCheck n34=true := by decide +kernel
lemma edge34 : edgeCheck n34 n35=true := by decide +kernel
lemma ok34 : chainCheck z34=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check34,edge34⟩,ok35⟩
lemma check33 : nodeCheck n33=true := by decide +kernel
lemma edge33 : edgeCheck n33 n34=true := by decide +kernel
lemma ok33 : chainCheck z33=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check33,edge33⟩,ok34⟩
lemma check32 : nodeCheck n32=true := by decide +kernel
lemma edge32 : edgeCheck n32 n33=true := by decide +kernel
lemma ok32 : chainCheck z32=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check32,edge32⟩,ok33⟩
lemma check31 : nodeCheck n31=true := by decide +kernel
lemma edge31 : edgeCheck n31 n32=true := by decide +kernel
lemma ok31 : chainCheck z31=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check31,edge31⟩,ok32⟩
lemma check30 : nodeCheck n30=true := by decide +kernel
lemma edge30 : edgeCheck n30 n31=true := by decide +kernel
lemma ok30 : chainCheck z30=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check30,edge30⟩,ok31⟩
lemma check29 : nodeCheck n29=true := by decide +kernel
lemma edge29 : edgeCheck n29 n30=true := by decide +kernel
lemma ok29 : chainCheck z29=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check29,edge29⟩,ok30⟩
lemma check28 : nodeCheck n28=true := by decide +kernel
lemma edge28 : edgeCheck n28 n29=true := by decide +kernel
lemma ok28 : chainCheck z28=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check28,edge28⟩,ok29⟩
lemma check27 : nodeCheck n27=true := by decide +kernel
lemma edge27 : edgeCheck n27 n28=true := by decide +kernel
lemma ok27 : chainCheck z27=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check27,edge27⟩,ok28⟩
lemma check26 : nodeCheck n26=true := by decide +kernel
lemma edge26 : edgeCheck n26 n27=true := by decide +kernel
lemma ok26 : chainCheck z26=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check26,edge26⟩,ok27⟩
lemma check25 : nodeCheck n25=true := by decide +kernel
lemma edge25 : edgeCheck n25 n26=true := by decide +kernel
lemma ok25 : chainCheck z25=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check25,edge25⟩,ok26⟩
lemma check24 : nodeCheck n24=true := by decide +kernel
lemma edge24 : edgeCheck n24 n25=true := by decide +kernel
lemma ok24 : chainCheck z24=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check24,edge24⟩,ok25⟩
lemma check23 : nodeCheck n23=true := by decide +kernel
lemma edge23 : edgeCheck n23 n24=true := by decide +kernel
lemma ok23 : chainCheck z23=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check23,edge23⟩,ok24⟩
lemma check22 : nodeCheck n22=true := by decide +kernel
lemma edge22 : edgeCheck n22 n23=true := by decide +kernel
lemma ok22 : chainCheck z22=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check22,edge22⟩,ok23⟩
lemma check21 : nodeCheck n21=true := by decide +kernel
lemma edge21 : edgeCheck n21 n22=true := by decide +kernel
lemma ok21 : chainCheck z21=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check21,edge21⟩,ok22⟩
lemma check20 : nodeCheck n20=true := by decide +kernel
lemma edge20 : edgeCheck n20 n21=true := by decide +kernel
lemma ok20 : chainCheck z20=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check20,edge20⟩,ok21⟩
lemma check19 : nodeCheck n19=true := by decide +kernel
lemma edge19 : edgeCheck n19 n20=true := by decide +kernel
lemma ok19 : chainCheck z19=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check19,edge19⟩,ok20⟩
lemma check18 : nodeCheck n18=true := by decide +kernel
lemma edge18 : edgeCheck n18 n19=true := by decide +kernel
lemma ok18 : chainCheck z18=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check18,edge18⟩,ok19⟩
lemma check17 : nodeCheck n17=true := by decide +kernel
lemma edge17 : edgeCheck n17 n18=true := by decide +kernel
lemma ok17 : chainCheck z17=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check17,edge17⟩,ok18⟩
lemma check16 : nodeCheck n16=true := by decide +kernel
lemma edge16 : edgeCheck n16 n17=true := by decide +kernel
lemma ok16 : chainCheck z16=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check16,edge16⟩,ok17⟩
lemma check15 : nodeCheck n15=true := by decide +kernel
lemma edge15 : edgeCheck n15 n16=true := by decide +kernel
lemma ok15 : chainCheck z15=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check15,edge15⟩,ok16⟩
lemma check14 : nodeCheck n14=true := by decide +kernel
lemma edge14 : edgeCheck n14 n15=true := by decide +kernel
lemma ok14 : chainCheck z14=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check14,edge14⟩,ok15⟩
lemma check13 : nodeCheck n13=true := by decide +kernel
lemma edge13 : edgeCheck n13 n14=true := by decide +kernel
lemma ok13 : chainCheck z13=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check13,edge13⟩,ok14⟩
lemma check12 : nodeCheck n12=true := by decide +kernel
lemma edge12 : edgeCheck n12 n13=true := by decide +kernel
lemma ok12 : chainCheck z12=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check12,edge12⟩,ok13⟩
lemma check11 : nodeCheck n11=true := by decide +kernel
lemma edge11 : edgeCheck n11 n12=true := by decide +kernel
lemma ok11 : chainCheck z11=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check11,edge11⟩,ok12⟩
lemma check10 : nodeCheck n10=true := by decide +kernel
lemma edge10 : edgeCheck n10 n11=true := by decide +kernel
lemma ok10 : chainCheck z10=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check10,edge10⟩,ok11⟩
lemma check9 : nodeCheck n9=true := by decide +kernel
lemma edge9 : edgeCheck n9 n10=true := by decide +kernel
lemma ok9 : chainCheck z9=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check9,edge9⟩,ok10⟩
lemma check8 : nodeCheck n8=true := by decide +kernel
lemma edge8 : edgeCheck n8 n9=true := by decide +kernel
lemma ok8 : chainCheck z8=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check8,edge8⟩,ok9⟩
lemma check7 : nodeCheck n7=true := by decide +kernel
lemma edge7 : edgeCheck n7 n8=true := by decide +kernel
lemma ok7 : chainCheck z7=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check7,edge7⟩,ok8⟩
lemma check6 : nodeCheck n6=true := by decide +kernel
lemma edge6 : edgeCheck n6 n7=true := by decide +kernel
lemma ok6 : chainCheck z6=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check6,edge6⟩,ok7⟩
lemma check5 : nodeCheck n5=true := by decide +kernel
lemma edge5 : edgeCheck n5 n6=true := by decide +kernel
lemma ok5 : chainCheck z5=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check5,edge5⟩,ok6⟩
lemma check4 : nodeCheck n4=true := by decide +kernel
lemma edge4 : edgeCheck n4 n5=true := by decide +kernel
lemma ok4 : chainCheck z4=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check4,edge4⟩,ok5⟩
lemma check3 : nodeCheck n3=true := by decide +kernel
lemma edge3 : edgeCheck n3 n4=true := by decide +kernel
lemma ok3 : chainCheck z3=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check3,edge3⟩,ok4⟩
lemma check2 : nodeCheck n2=true := by decide +kernel
lemma edge2 : edgeCheck n2 n3=true := by decide +kernel
lemma ok2 : chainCheck z2=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check2,edge2⟩,ok3⟩
lemma check1 : nodeCheck n1=true := by decide +kernel
lemma edge1 : edgeCheck n1 n2=true := by decide +kernel
lemma ok1 : chainCheck z1=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check1,edge1⟩,ok2⟩
lemma check0 : nodeCheck n0=true := by decide +kernel
lemma edge0 : edgeCheck n0 n1=true := by decide +kernel
lemma ok0 : chainCheck z0=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check0,edge0⟩,ok1⟩
def v6 : Band := ⟨3000000,3500000,2466976,8017653,25165824,29360128,4062332,3505900⟩
lemma b6ok : bandCheck v6=true := by decide +kernel
def t6x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t6x8ok : treeCheck nodes v6 ⟨0,1048576,-8388608,8388608⟩ t6x8=true := by decide +kernel
def t6x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t6x9ok : treeCheck nodes v6 ⟨1048576,2097152,-8388608,8388608⟩ t6x9=true := by decide +kernel
def t6x4 : Tree := .d (1048576) t6x8 t6x9
lemma t6x4ok : treeCheck nodes v6 ⟨0,2097152,-8388608,8388608⟩ t6x4=true := Bool.and_eq_true_iff.mpr ⟨t6x8ok,t6x9ok⟩
def t6x10 : Tree := .leaf ⟨false,8122235,3145728,0,8388608,-8388608,8388608⟩
lemma t6x10ok : treeCheck nodes v6 ⟨2097152,3145728,-8388608,8388608⟩ t6x10=true := by decide +kernel
def t6x11 : Tree := .leaf ⟨false,7776448,4194304,0,8388608,-8388608,8388608⟩
lemma t6x11ok : treeCheck nodes v6 ⟨3145728,4194304,-8388608,8388608⟩ t6x11=true := by decide +kernel
def t6x5 : Tree := .d (3145728) t6x10 t6x11
lemma t6x5ok : treeCheck nodes v6 ⟨2097152,4194304,-8388608,8388608⟩ t6x5=true := Bool.and_eq_true_iff.mpr ⟨t6x10ok,t6x11ok⟩
def t6x2 : Tree := .d (2097152) t6x4 t6x5
lemma t6x2ok : treeCheck nodes v6 ⟨0,4194304,-8388608,8388608⟩ t6x2=true := Bool.and_eq_true_iff.mpr ⟨t6x4ok,t6x5ok⟩
def t6x6 : Tree := .leaf ⟨false,7264748,6291456,0,8388608,-8388608,8388608⟩
lemma t6x6ok : treeCheck nodes v6 ⟨4194304,6291456,-8388608,8388608⟩ t6x6=true := by decide +kernel
def t6x7 : Tree := .leaf ⟨false,5548543,8388608,0,8388608,-8388608,8388608⟩
lemma t6x7ok : treeCheck nodes v6 ⟨6291456,8388608,-8388608,8388608⟩ t6x7=true := by decide +kernel
def t6x3 : Tree := .d (6291456) t6x6 t6x7
lemma t6x3ok : treeCheck nodes v6 ⟨4194304,8388608,-8388608,8388608⟩ t6x3=true := Bool.and_eq_true_iff.mpr ⟨t6x6ok,t6x7ok⟩
def t6x1 : Tree := .d (4194304) t6x2 t6x3
lemma t6x1ok : treeCheck nodes v6 ⟨0,8388608,-8388608,8388608⟩ t6x1=true := Bool.and_eq_true_iff.mpr ⟨t6x2ok,t6x3ok⟩
def v7 : Band := ⟨3500000,4000000,2161436,8105364,29360128,33554432,3510245,3085379⟩
lemma b7ok : bandCheck v7=true := by decide +kernel
def t7x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t7x8ok : treeCheck nodes v7 ⟨0,1048576,-8388608,8388608⟩ t7x8=true := by decide +kernel
def t7x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t7x9ok : treeCheck nodes v7 ⟨1048576,2097152,-8388608,8388608⟩ t7x9=true := by decide +kernel
def t7x4 : Tree := .d (1048576) t7x8 t7x9
lemma t7x4ok : treeCheck nodes v7 ⟨0,2097152,-8388608,8388608⟩ t7x4=true := Bool.and_eq_true_iff.mpr ⟨t7x8ok,t7x9ok⟩
def t7x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t7x5ok : treeCheck nodes v7 ⟨2097152,4194304,-8388608,8388608⟩ t7x5=true := by decide +kernel
def t7x2 : Tree := .d (2097152) t7x4 t7x5
lemma t7x2ok : treeCheck nodes v7 ⟨0,4194304,-8388608,8388608⟩ t7x2=true := Bool.and_eq_true_iff.mpr ⟨t7x4ok,t7x5ok⟩
def t7x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t7x3ok : treeCheck nodes v7 ⟨4194304,8388608,-8388608,8388608⟩ t7x3=true := by decide +kernel
def t7x1 : Tree := .d (4194304) t7x2 t7x3
lemma t7x1ok : treeCheck nodes v7 ⟨0,8388608,-8388608,8388608⟩ t7x1=true := Bool.and_eq_true_iff.mpr ⟨t7x2ok,t7x3ok⟩
def v8 : Band := ⟨4000000,4500000,1921316,8165616,33554432,37748736,3088043,2753555⟩
lemma b8ok : bandCheck v8=true := by decide +kernel
def t8x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t8x8ok : treeCheck nodes v8 ⟨0,1048576,-8388608,8388608⟩ t8x8=true := by decide +kernel
def t8x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t8x9ok : treeCheck nodes v8 ⟨1048576,2097152,-8388608,8388608⟩ t8x9=true := by decide +kernel
def t8x4 : Tree := .d (1048576) t8x8 t8x9
lemma t8x4ok : treeCheck nodes v8 ⟨0,2097152,-8388608,8388608⟩ t8x4=true := Bool.and_eq_true_iff.mpr ⟨t8x8ok,t8x9ok⟩
def t8x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t8x5ok : treeCheck nodes v8 ⟨2097152,4194304,-8388608,8388608⟩ t8x5=true := by decide +kernel
def t8x2 : Tree := .d (2097152) t8x4 t8x5
lemma t8x2ok : treeCheck nodes v8 ⟨0,4194304,-8388608,8388608⟩ t8x2=true := Bool.and_eq_true_iff.mpr ⟨t8x4ok,t8x5ok⟩
def t8x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t8x3ok : treeCheck nodes v8 ⟨4194304,8388608,-8388608,8388608⟩ t8x3=true := by decide +kernel
def t8x1 : Tree := .d (4194304) t8x2 t8x3
lemma t8x1ok : treeCheck nodes v8 ⟨0,8388608,-8388608,8388608⟩ t8x1=true := Bool.and_eq_true_iff.mpr ⟨t8x2ok,t8x3ok⟩
def v9 : Band := ⟨4500000,5000000,1728141,8208670,37748736,41943040,2755259,2485352⟩
lemma b9ok : bandCheck v9=true := by decide +kernel
def t9x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t9x8ok : treeCheck nodes v9 ⟨0,1048576,-8388608,8388608⟩ t9x8=true := by decide +kernel
def t9x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t9x9ok : treeCheck nodes v9 ⟨1048576,2097152,-8388608,8388608⟩ t9x9=true := by decide +kernel
def t9x4 : Tree := .d (1048576) t9x8 t9x9
lemma t9x4ok : treeCheck nodes v9 ⟨0,2097152,-8388608,8388608⟩ t9x4=true := Bool.and_eq_true_iff.mpr ⟨t9x8ok,t9x9ok⟩
def t9x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t9x5ok : treeCheck nodes v9 ⟨2097152,4194304,-8388608,8388608⟩ t9x5=true := by decide +kernel
def t9x2 : Tree := .d (2097152) t9x4 t9x5
lemma t9x2ok : treeCheck nodes v9 ⟨0,4194304,-8388608,8388608⟩ t9x2=true := Bool.and_eq_true_iff.mpr ⟨t9x4ok,t9x5ok⟩
def t9x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t9x3ok : treeCheck nodes v9 ⟨4194304,8388608,-8388608,8388608⟩ t9x3=true := by decide +kernel
def t9x1 : Tree := .d (4194304) t9x2 t9x3
lemma t9x1ok : treeCheck nodes v9 ⟨0,8388608,-8388608,8388608⟩ t9x1=true := Bool.and_eq_true_iff.mpr ⟨t9x2ok,t9x3ok⟩
def v10 : Band := ⟨5000000,5500000,1569616,8240451,41943040,46137344,2486492,2264257⟩
lemma b10ok : bandCheck v10=true := by decide +kernel
def t10x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t10x8ok : treeCheck nodes v10 ⟨0,1048576,-8388608,8388608⟩ t10x8=true := by decide +kernel
def t10x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t10x9ok : treeCheck nodes v10 ⟨1048576,2097152,-8388608,8388608⟩ t10x9=true := by decide +kernel
def t10x4 : Tree := .d (1048576) t10x8 t10x9
lemma t10x4ok : treeCheck nodes v10 ⟨0,2097152,-8388608,8388608⟩ t10x4=true := Bool.and_eq_true_iff.mpr ⟨t10x8ok,t10x9ok⟩
def t10x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t10x5ok : treeCheck nodes v10 ⟨2097152,4194304,-8388608,8388608⟩ t10x5=true := by decide +kernel
def t10x2 : Tree := .d (2097152) t10x4 t10x5
lemma t10x2ok : treeCheck nodes v10 ⟨0,4194304,-8388608,8388608⟩ t10x2=true := Bool.and_eq_true_iff.mpr ⟨t10x4ok,t10x5ok⟩
def t10x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t10x3ok : treeCheck nodes v10 ⟨4194304,8388608,-8388608,8388608⟩ t10x3=true := by decide +kernel
def t10x1 : Tree := .d (4194304) t10x2 t10x3
lemma t10x1ok : treeCheck nodes v10 ⟨0,8388608,-8388608,8388608⟩ t10x1=true := Bool.and_eq_true_iff.mpr ⟨t10x2ok,t10x3ok⟩
def v11 : Band := ⟨5500000,6000000,1437317,8264554,46137344,50331648,2265059,2078978⟩
lemma b11ok : bandCheck v11=true := by decide +kernel
def t11x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t11x8ok : treeCheck nodes v11 ⟨0,1048576,-8388608,8388608⟩ t11x8=true := by decide +kernel
def t11x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t11x9ok : treeCheck nodes v11 ⟨1048576,2097152,-8388608,8388608⟩ t11x9=true := by decide +kernel
def t11x4 : Tree := .d (1048576) t11x8 t11x9
lemma t11x4ok : treeCheck nodes v11 ⟨0,2097152,-8388608,8388608⟩ t11x4=true := Bool.and_eq_true_iff.mpr ⟨t11x8ok,t11x9ok⟩
def t11x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t11x5ok : treeCheck nodes v11 ⟨2097152,4194304,-8388608,8388608⟩ t11x5=true := by decide +kernel
def t11x2 : Tree := .d (2097152) t11x4 t11x5
lemma t11x2ok : treeCheck nodes v11 ⟨0,4194304,-8388608,8388608⟩ t11x2=true := Bool.and_eq_true_iff.mpr ⟨t11x4ok,t11x5ok⟩
def t11x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t11x3ok : treeCheck nodes v11 ⟨4194304,8388608,-8388608,8388608⟩ t11x3=true := by decide +kernel
def t11x1 : Tree := .d (4194304) t11x2 t11x3
lemma t11x1ok : treeCheck nodes v11 ⟨0,8388608,-8388608,8388608⟩ t11x1=true := Bool.and_eq_true_iff.mpr ⟨t11x2ok,t11x3ok⟩
def v12 : Band := ⟨6000000,6500000,1325312,8283253,50331648,54525952,2079545,1921513⟩
lemma b12ok : bandCheck v12=true := by decide +kernel
def t12x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t12x8ok : treeCheck nodes v12 ⟨0,1048576,-8388608,8388608⟩ t12x8=true := by decide +kernel
def t12x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t12x9ok : treeCheck nodes v12 ⟨1048576,2097152,-8388608,8388608⟩ t12x9=true := by decide +kernel
def t12x4 : Tree := .d (1048576) t12x8 t12x9
lemma t12x4ok : treeCheck nodes v12 ⟨0,2097152,-8388608,8388608⟩ t12x4=true := Bool.and_eq_true_iff.mpr ⟨t12x8ok,t12x9ok⟩
def t12x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t12x5ok : treeCheck nodes v12 ⟨2097152,4194304,-8388608,8388608⟩ t12x5=true := by decide +kernel
def t12x2 : Tree := .d (2097152) t12x4 t12x5
lemma t12x2ok : treeCheck nodes v12 ⟨0,4194304,-8388608,8388608⟩ t12x2=true := Bool.and_eq_true_iff.mpr ⟨t12x4ok,t12x5ok⟩
def t12x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t12x3ok : treeCheck nodes v12 ⟨4194304,8388608,-8388608,8388608⟩ t12x3=true := by decide +kernel
def t12x1 : Tree := .d (4194304) t12x2 t12x3
lemma t12x1ok : treeCheck nodes v12 ⟨0,8388608,-8388608,8388608⟩ t12x1=true := Bool.and_eq_true_iff.mpr ⟨t12x2ok,t12x3ok⟩
def v13 : Band := ⟨6500000,7000000,1229338,8298040,54525952,58720256,1921937,1786085⟩
lemma b13ok : bandCheck v13=true := by decide +kernel
def t13x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t13x16ok : treeCheck nodes v13 ⟨0,524288,-8388608,8388608⟩ t13x16=true := by decide +kernel
def t13x17 : Tree := .leaf ⟨false,8372208,1048576,0,8388608,-8388608,8388608⟩
lemma t13x17ok : treeCheck nodes v13 ⟨524288,1048576,-8388608,8388608⟩ t13x17=true := by decide +kernel
def t13x8 : Tree := .d (524288) t13x16 t13x17
lemma t13x8ok : treeCheck nodes v13 ⟨0,1048576,-8388608,8388608⟩ t13x8=true := Bool.and_eq_true_iff.mpr ⟨t13x16ok,t13x17ok⟩
def t13x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t13x9ok : treeCheck nodes v13 ⟨1048576,2097152,-8388608,8388608⟩ t13x9=true := by decide +kernel
def t13x4 : Tree := .d (1048576) t13x8 t13x9
lemma t13x4ok : treeCheck nodes v13 ⟨0,2097152,-8388608,8388608⟩ t13x4=true := Bool.and_eq_true_iff.mpr ⟨t13x8ok,t13x9ok⟩
def t13x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t13x5ok : treeCheck nodes v13 ⟨2097152,4194304,-8388608,8388608⟩ t13x5=true := by decide +kernel
def t13x2 : Tree := .d (2097152) t13x4 t13x5
lemma t13x2ok : treeCheck nodes v13 ⟨0,4194304,-8388608,8388608⟩ t13x2=true := Bool.and_eq_true_iff.mpr ⟨t13x4ok,t13x5ok⟩
def t13x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t13x3ok : treeCheck nodes v13 ⟨4194304,8388608,-8388608,8388608⟩ t13x3=true := by decide +kernel
def t13x1 : Tree := .d (4194304) t13x2 t13x3
lemma t13x1ok : treeCheck nodes v13 ⟨0,8388608,-8388608,8388608⟩ t13x1=true := Bool.and_eq_true_iff.mpr ⟨t13x2ok,t13x3ok⟩
end GateChecker.M1

end

section

namespace GateChecker.M2
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false
def n0 : Node := ⟨0,8388608,-5931642,-5931641,10273905,0,130⟩
def n1 : Node := ⟨65536,8388353,-5931280,-5931278,10273696,103621,132⟩
def n2 : Node := ⟨131072,8387585,-5930194,-5930192,10273069,207233,134⟩
def n3 : Node := ⟨196608,8386305,-5928384,-5928382,10272024,310831,136⟩
def n4 : Node := ⟨262144,8384513,-5925850,-5925848,10270562,414406,138⟩
def n5 : Node := ⟨327680,8382211,-5922592,-5922590,10268682,517950,140⟩
def n6 : Node := ⟨393216,8379398,-5918609,-5918607,10266386,621456,142⟩
def n7 : Node := ⟨458752,8376074,-5913903,-5913901,10263673,724917,144⟩
def n8 : Node := ⟨524288,8372240,-5908472,-5908470,10260545,828325,146⟩
def n9 : Node := ⟨589824,8367898,-5902317,-5902315,10257002,931672,148⟩
def n10 : Node := ⟨655360,8363048,-5895439,-5895437,10253045,1034951,150⟩
def n11 : Node := ⟨720896,8357690,-5887836,-5887834,10248676,1138154,152⟩
def n12 : Node := ⟨786432,8351825,-5879509,-5879507,10243894,1241274,154⟩
def n13 : Node := ⟨851968,8345456,-5870458,-5870456,10238702,1344303,156⟩
def n14 : Node := ⟨917504,8338582,-5860683,-5860681,10233101,1447234,158⟩
def n15 : Node := ⟨983040,8331206,-5850184,-5850182,10227091,1550058,160⟩
def n16 : Node := ⟨1048576,8323328,-5838961,-5838959,10220675,1652769,162⟩
def n17 : Node := ⟨1114112,8314950,-5827013,-5827011,10213855,1755359,164⟩
def n18 : Node := ⟨1179648,8306073,-5814342,-5814340,10206631,1857821,166⟩
def n19 : Node := ⟨1245184,8296700,-5800947,-5800945,10199006,1960146,168⟩
def n20 : Node := ⟨1310720,8286831,-5786827,-5786825,10190982,2062328,170⟩
def n21 : Node := ⟨1376256,8276469,-5771983,-5771981,10182560,2164359,172⟩
def n22 : Node := ⟨1441792,8265615,-5756416,-5756414,10173744,2266232,174⟩
def n23 : Node := ⟨1507328,8254272,-5740124,-5740122,10164535,2367939,176⟩
def n24 : Node := ⟨1572864,8242441,-5723108,-5723106,10154935,2469472,178⟩
def n25 : Node := ⟨1638400,8230125,-5705368,-5705366,10144948,2570825,180⟩
def n26 : Node := ⟨1703936,8217325,-5686904,-5686902,10134576,2671989,182⟩
def n27 : Node := ⟨1769472,8204045,-5667716,-5667714,10123821,2772959,184⟩
def n28 : Node := ⟨1835008,8190286,-5647804,-5647802,10112687,2873725,186⟩
def n29 : Node := ⟨1900544,8176052,-5627168,-5627166,10101176,2974281,188⟩
def n30 : Node := ⟨1966080,8161344,-5605808,-5605806,10089293,3074620,190⟩
def n31 : Node := ⟨2031616,8146165,-5583723,-5583721,10077039,3174734,192⟩
def n32 : Node := ⟨2097152,8130518,-5560915,-5560913,10064418,3274615,1782⟩
def n33 : Node := ⟨2293760,8080798,-5488145,-5488143,10024394,3572795,1836⟩
def n34 : Node := ⟨2490368,8026971,-5408859,-5408857,9981207,3868625,1890⟩
def n35 : Node := ⟨2686976,7969124,-5323055,-5323054,9934972,4161912,1944⟩
def n36 : Node := ⟨2883584,7907349,-5230736,-5230734,9885815,4452466,1998⟩
def n37 : Node := ⟨3080192,7841745,-5131899,-5131897,9833877,4740098,2052⟩
def n38 : Node := ⟨3276800,7772413,-5026546,-5026544,9779310,5024621,2106⟩
def n39 : Node := ⟨3473408,7699465,-4914676,-4914674,9722283,5305853,2160⟩
def n40 : Node := ⟨3670016,7623012,-4796289,-4796287,9662978,5583613,2214⟩
def n41 : Node := ⟨3866624,7543173,-4671386,-4671384,9601593,5857725,2268⟩
def n42 : Node := ⟨4063232,7460072,-4539966,-4539964,9538346,6128016,2322⟩
def n43 : Node := ⟨4259840,7373835,-4402029,-4402027,9473469,6394316,2376⟩
def n44 : Node := ⟨4456448,7284592,-4257576,-4257574,9407215,6656461,2430⟩
def n45 : Node := ⟨4653056,7192477,-4106605,-4106604,9339858,6914291,2484⟩
def n46 : Node := ⟨4849664,7097626,-3949119,-3949117,9271693,7167649,2538⟩
def n47 : Node := ⟨5046272,7000181,-3785115,-3785113,9203034,7416387,2592⟩
def n48 : Node := ⟨5242880,6900281,-3614595,-3614593,9134224,7660360,2646⟩
def n49 : Node := ⟨5439488,6798072,-3437558,-3437556,9065625,7899431,2700⟩
def n50 : Node := ⟨5636096,6693699,-3254004,-3254003,8997627,8133468,2754⟩
def n51 : Node := ⟨5832704,6587309,-3063934,-3063932,8930646,8362349,2808⟩
def n52 : Node := ⟨6029312,6479050,-2867347,-2867345,8865124,8585957,2862⟩
def n53 : Node := ⟨6225920,6369070,-2664243,-2664242,8801531,8804184,2916⟩
def n54 : Node := ⟨6422528,6257519,-2454623,-2454621,8740362,9016934,2970⟩
def n55 : Node := ⟨6619136,6144546,-2238486,-2238484,8682141,9224116,3024⟩
def n56 : Node := ⟨6815744,6030299,-2015832,-2015831,8627417,9425655,3078⟩
def n57 : Node := ⟨7012352,5914926,-1786661,-1786660,8576766,9621483,3132⟩
def n58 : Node := ⟨7208960,5798574,-1550974,-1550973,8530784,9811546,3186⟩
def n59 : Node := ⟨7405568,5681389,-1308770,-1308769,8490090,9995803,3240⟩
def n60 : Node := ⟨7602176,5563515,-1060050,-1060049,8455321,10174229,3294⟩
def n61 : Node := ⟨7798784,5445095,-804813,-804811,8427127,10346812,3348⟩
def n62 : Node := ⟨7995392,5326269,-543059,-543057,8406168,10513557,3402⟩
def n63 : Node := ⟨8192000,5207175,-274788,-274787,8393108,10674488,3456⟩
def n64 : Node := ⟨8388608,5087948,0,0,8388608,10829647,14256⟩
def n65 : Node := ⟨8781824,4849623,569124,569125,8407892,11122922,14688⟩
def n66 : Node := ⟨9175040,4612316,1164316,1164317,8469025,11394162,15120⟩
def n67 : Node := ⟨9568256,4376993,1785574,1785575,8576540,11644555,15552⟩
def n68 : Node := ⟨9961472,4144560,2432899,2432901,8734286,11875760,15984⟩
def n69 : Node := ⟨10354688,3915856,3106291,3106293,8945267,12089970,16416⟩
def n70 : Node := ⟨10747904,3691652,3805750,3805751,9211541,12289988,16848⟩
def n71 : Node := ⟨11141120,3472646,4531275,4531277,9534213,12479301,17280⟩
def n72 : Node := ⟨11534336,3259462,5282867,5282869,9913498,12662153,17712⟩
def n73 : Node := ⟨11927552,3052651,6060526,6060528,10348852,12843612,18144⟩
def n74 : Node := ⟨12320768,2852687,6864252,6864254,10839129,13029630,18576⟩
def n75 : Node := ⟨12713984,2659971,7694045,7694047,11382754,13227068,19008⟩
def n76 : Node := ⟨13107200,2474830,8549904,8549906,11977881,13443698,19440⟩
def n77 : Node := ⟨13500416,2297521,9431830,9431833,12622528,13688148,19872⟩
def n78 : Node := ⟨13893632,2128235,10339823,10339826,13314681,13969798,20304⟩
def n79 : Node := ⟨14286848,1967094,11273883,11273886,14052374,14298599,20736⟩
def n80 : Node := ⟨14680064,1814164,12234009,12234012,14833738,14684842,21168⟩
def n81 : Node := ⟨15073280,1669451,13220202,13220206,15657029,15138871,21600⟩
def n82 : Node := ⟨15466496,1532910,14232462,14232466,16520648,15670764,22032⟩
def n83 : Node := ⟨15859712,1404447,15270789,15270793,17423141,16290027,22464⟩
def n84 : Node := ⟨16252928,1283925,16335183,16335186,18363198,17005326,22896⟩
def n85 : Node := ⟨16646144,1171170,17425643,17425647,19339645,17824288,22896⟩
def n86 : Node := ⟨16777216,1135275,17794923,17794926,19673030,18121465,95616⟩
def n87 : Node := ⟨17563648,937049,20071421,20071426,21753869,20172562,99072⟩
def n88 : Node := ⟨18350080,766667,22452188,22452192,23968096,22706180,102528⟩
def n89 : Node := ⟨19136512,621776,24937221,24937226,26310338,25743249,105984⟩
def n90 : Node := ⟨19922944,499855,27526521,27526527,28776350,29295198,109440⟩
def n91 : Node := ⟨20709376,398325,30220088,30220095,31362760,33368596,112896⟩
def n92 : Node := ⟨21495808,314640,33017923,33017930,34066879,37968411,116352⟩
def n93 : Node := ⟨22282240,246361,35920025,35920032,36886546,43099877,119808⟩
def n94 : Node := ⟨23068672,191212,38926394,38926401,39820011,48769383,123264⟩
def n95 : Node := ⟨23855104,147109,42037030,42037038,42865849,54984760,126720⟩
def n96 : Node := ⟨24641536,112189,45251933,45251941,46022893,61755270,130176⟩
def n97 : Node := ⟨25427968,84809,48571103,48571112,49290175,69091461,133632⟩
def n98 : Node := ⟨26214400,63550,51994540,51994550,52666893,77004982,137088⟩
def n99 : Node := ⟨27000832,47203,55522245,55522255,56152374,85508396,140544⟩
def n100 : Node := ⟨27787264,34755,59154216,59154227,59746053,94615021,144000⟩
def n101 : Node := ⟨28573696,25365,62890455,62890467,63447451,104338785,147456⟩
def n102 : Node := ⟨29360128,18351,66730961,66730973,67256159,114694117,150912⟩
def n103 : Node := ⟨30146560,13160,70675734,70675747,71171829,125695852,154368⟩
def n104 : Node := ⟨30932992,9355,74724774,74724787,75194161,137359157,157824⟩
def n105 : Node := ⟨31719424,6592,78878081,78878095,79322896,149699468,161280⟩
def n106 : Node := ⟨32505856,4604,83135655,83135670,83557809,162732447,164736⟩
def n107 : Node := ⟨33292288,3188,87497497,87497513,87898706,176473939,164736⟩
def n108 : Node := ⟨33554432,2815,88974615,88974630,89369192,181214645,691200⟩
def n109 : Node := ⟨35127296,1307,98080610,98080628,98438697,211382848,718848⟩
def n110 : Node := ⟨36700160,586,107603675,107603694,107930172,244600338,746496⟩
def n111 : Node := ⟨38273024,254,117543807,117543828,117842770,280998174,774144⟩
def n112 : Node := ⟨39845888,107,127901009,127901031,128175818,320708414,801792⟩
def n113 : Node := ⟨41418752,44,138675278,138675303,138928779,363863848,829440⟩
def n114 : Node := ⟨42991616,18,149866617,149866643,150101220,410597808,857088⟩
def n115 : Node := ⟨44564480,7,161475023,161475052,161692788,461044042,884736⟩
def n116 : Node := ⟨46137344,3,173500499,173500529,173703190,515336613,912384⟩
def n117 : Node := ⟨47710208,1,185943043,185943075,186132187,573609829,940032⟩
def n118 : Node := ⟨49283072,1,198802655,198802689,198979579,635998194,940032⟩
def n119 : Node := ⟨50331648,1,207607435,207607470,207776863,679943123,4055040⟩
def n120 : Node := ⟨53477376,1,235133956,235133997,235283569,823510107,4276224⟩
def n121 : Node := ⟨56623104,1,264328752,264328797,264461854,985514893,4497408⟩
def n122 : Node := ⟨59768832,1,295191821,295191872,295311020,1167037765,4718592⟩
def n123 : Node := ⟨62914560,1,327723165,327723221,327830541,1369159818,4939776⟩
def n124 : Node := ⟨66060288,1,361922782,361922844,362020022,1592962722,4939776⟩
def n125 : Node := ⟨67108864,1,373693383,373693446,373787563,1672568674,557056⟩
def z125 : List Node := n125 :: []
def z124 : List Node := n124 :: z125
def z123 : List Node := n123 :: z124
def z122 : List Node := n122 :: z123
def z121 : List Node := n121 :: z122
def z120 : List Node := n120 :: z121
def z119 : List Node := n119 :: z120
def z118 : List Node := n118 :: z119
def z117 : List Node := n117 :: z118
def z116 : List Node := n116 :: z117
def z115 : List Node := n115 :: z116
def z114 : List Node := n114 :: z115
def z113 : List Node := n113 :: z114
def z112 : List Node := n112 :: z113
def z111 : List Node := n111 :: z112
def z110 : List Node := n110 :: z111
def z109 : List Node := n109 :: z110
def z108 : List Node := n108 :: z109
def z107 : List Node := n107 :: z108
def z106 : List Node := n106 :: z107
def z105 : List Node := n105 :: z106
def z104 : List Node := n104 :: z105
def z103 : List Node := n103 :: z104
def z102 : List Node := n102 :: z103
def z101 : List Node := n101 :: z102
def z100 : List Node := n100 :: z101
def z99 : List Node := n99 :: z100
def z98 : List Node := n98 :: z99
def z97 : List Node := n97 :: z98
def z96 : List Node := n96 :: z97
def z95 : List Node := n95 :: z96
def z94 : List Node := n94 :: z95
def z93 : List Node := n93 :: z94
def z92 : List Node := n92 :: z93
def z91 : List Node := n91 :: z92
def z90 : List Node := n90 :: z91
def z89 : List Node := n89 :: z90
def z88 : List Node := n88 :: z89
def z87 : List Node := n87 :: z88
def z86 : List Node := n86 :: z87
def z85 : List Node := n85 :: z86
def z84 : List Node := n84 :: z85
def z83 : List Node := n83 :: z84
def z82 : List Node := n82 :: z83
def z81 : List Node := n81 :: z82
def z80 : List Node := n80 :: z81
def z79 : List Node := n79 :: z80
def z78 : List Node := n78 :: z79
def z77 : List Node := n77 :: z78
def z76 : List Node := n76 :: z77
def z75 : List Node := n75 :: z76
def z74 : List Node := n74 :: z75
def z73 : List Node := n73 :: z74
def z72 : List Node := n72 :: z73
def z71 : List Node := n71 :: z72
def z70 : List Node := n70 :: z71
def z69 : List Node := n69 :: z70
def z68 : List Node := n68 :: z69
def z67 : List Node := n67 :: z68
def z66 : List Node := n66 :: z67
def z65 : List Node := n65 :: z66
def z64 : List Node := n64 :: z65
def z63 : List Node := n63 :: z64
def z62 : List Node := n62 :: z63
def z61 : List Node := n61 :: z62
def z60 : List Node := n60 :: z61
def z59 : List Node := n59 :: z60
def z58 : List Node := n58 :: z59
def z57 : List Node := n57 :: z58
def z56 : List Node := n56 :: z57
def z55 : List Node := n55 :: z56
def z54 : List Node := n54 :: z55
def z53 : List Node := n53 :: z54
def z52 : List Node := n52 :: z53
def z51 : List Node := n51 :: z52
def z50 : List Node := n50 :: z51
def z49 : List Node := n49 :: z50
def z48 : List Node := n48 :: z49
def z47 : List Node := n47 :: z48
def z46 : List Node := n46 :: z47
def z45 : List Node := n45 :: z46
def z44 : List Node := n44 :: z45
def z43 : List Node := n43 :: z44
def z42 : List Node := n42 :: z43
def z41 : List Node := n41 :: z42
def z40 : List Node := n40 :: z41
def z39 : List Node := n39 :: z40
def z38 : List Node := n38 :: z39
def z37 : List Node := n37 :: z38
def z36 : List Node := n36 :: z37
def z35 : List Node := n35 :: z36
def z34 : List Node := n34 :: z35
def z33 : List Node := n33 :: z34
def z32 : List Node := n32 :: z33
def z31 : List Node := n31 :: z32
def z30 : List Node := n30 :: z31
def z29 : List Node := n29 :: z30
def z28 : List Node := n28 :: z29
def z27 : List Node := n27 :: z28
def z26 : List Node := n26 :: z27
def z25 : List Node := n25 :: z26
def z24 : List Node := n24 :: z25
def z23 : List Node := n23 :: z24
def z22 : List Node := n22 :: z23
def z21 : List Node := n21 :: z22
def z20 : List Node := n20 :: z21
def z19 : List Node := n19 :: z20
def z18 : List Node := n18 :: z19
def z17 : List Node := n17 :: z18
def z16 : List Node := n16 :: z17
def z15 : List Node := n15 :: z16
def z14 : List Node := n14 :: z15
def z13 : List Node := n13 :: z14
def z12 : List Node := n12 :: z13
def z11 : List Node := n11 :: z12
def z10 : List Node := n10 :: z11
def z9 : List Node := n9 :: z10
def z8 : List Node := n8 :: z9
def z7 : List Node := n7 :: z8
def z6 : List Node := n6 :: z7
def z5 : List Node := n5 :: z6
def z4 : List Node := n4 :: z5
def z3 : List Node := n3 :: z4
def z2 : List Node := n2 :: z3
def z1 : List Node := n1 :: z2
def z0 : List Node := n0 :: z1
def nodes := z0
lemma starts : PanelChain.start nodes=true := by decide +kernel
lemma check125 : nodeCheck n125=true := by decide +kernel
lemma ok125 : chainCheck z125=true := Bool.and_eq_true_iff.mpr ⟨check125,by decide +kernel⟩
lemma check124 : nodeCheck n124=true := by decide +kernel
lemma edge124 : edgeCheck n124 n125=true := by decide +kernel
lemma ok124 : chainCheck z124=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check124,edge124⟩,ok125⟩
lemma check123 : nodeCheck n123=true := by decide +kernel
lemma edge123 : edgeCheck n123 n124=true := by decide +kernel
lemma ok123 : chainCheck z123=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check123,edge123⟩,ok124⟩
lemma check122 : nodeCheck n122=true := by decide +kernel
lemma edge122 : edgeCheck n122 n123=true := by decide +kernel
lemma ok122 : chainCheck z122=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check122,edge122⟩,ok123⟩
lemma check121 : nodeCheck n121=true := by decide +kernel
lemma edge121 : edgeCheck n121 n122=true := by decide +kernel
lemma ok121 : chainCheck z121=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check121,edge121⟩,ok122⟩
lemma check120 : nodeCheck n120=true := by decide +kernel
lemma edge120 : edgeCheck n120 n121=true := by decide +kernel
lemma ok120 : chainCheck z120=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check120,edge120⟩,ok121⟩
lemma check119 : nodeCheck n119=true := by decide +kernel
lemma edge119 : edgeCheck n119 n120=true := by decide +kernel
lemma ok119 : chainCheck z119=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check119,edge119⟩,ok120⟩
lemma check118 : nodeCheck n118=true := by decide +kernel
lemma edge118 : edgeCheck n118 n119=true := by decide +kernel
lemma ok118 : chainCheck z118=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check118,edge118⟩,ok119⟩
lemma check117 : nodeCheck n117=true := by decide +kernel
lemma edge117 : edgeCheck n117 n118=true := by decide +kernel
lemma ok117 : chainCheck z117=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check117,edge117⟩,ok118⟩
lemma check116 : nodeCheck n116=true := by decide +kernel
lemma edge116 : edgeCheck n116 n117=true := by decide +kernel
lemma ok116 : chainCheck z116=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check116,edge116⟩,ok117⟩
lemma check115 : nodeCheck n115=true := by decide +kernel
lemma edge115 : edgeCheck n115 n116=true := by decide +kernel
lemma ok115 : chainCheck z115=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check115,edge115⟩,ok116⟩
lemma check114 : nodeCheck n114=true := by decide +kernel
lemma edge114 : edgeCheck n114 n115=true := by decide +kernel
lemma ok114 : chainCheck z114=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check114,edge114⟩,ok115⟩
lemma check113 : nodeCheck n113=true := by decide +kernel
lemma edge113 : edgeCheck n113 n114=true := by decide +kernel
lemma ok113 : chainCheck z113=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check113,edge113⟩,ok114⟩
lemma check112 : nodeCheck n112=true := by decide +kernel
lemma edge112 : edgeCheck n112 n113=true := by decide +kernel
lemma ok112 : chainCheck z112=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check112,edge112⟩,ok113⟩
lemma check111 : nodeCheck n111=true := by decide +kernel
lemma edge111 : edgeCheck n111 n112=true := by decide +kernel
lemma ok111 : chainCheck z111=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check111,edge111⟩,ok112⟩
lemma check110 : nodeCheck n110=true := by decide +kernel
lemma edge110 : edgeCheck n110 n111=true := by decide +kernel
lemma ok110 : chainCheck z110=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check110,edge110⟩,ok111⟩
lemma check109 : nodeCheck n109=true := by decide +kernel
lemma edge109 : edgeCheck n109 n110=true := by decide +kernel
lemma ok109 : chainCheck z109=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check109,edge109⟩,ok110⟩
lemma check108 : nodeCheck n108=true := by decide +kernel
lemma edge108 : edgeCheck n108 n109=true := by decide +kernel
lemma ok108 : chainCheck z108=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check108,edge108⟩,ok109⟩
lemma check107 : nodeCheck n107=true := by decide +kernel
lemma edge107 : edgeCheck n107 n108=true := by decide +kernel
lemma ok107 : chainCheck z107=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check107,edge107⟩,ok108⟩
lemma check106 : nodeCheck n106=true := by decide +kernel
lemma edge106 : edgeCheck n106 n107=true := by decide +kernel
lemma ok106 : chainCheck z106=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check106,edge106⟩,ok107⟩
lemma check105 : nodeCheck n105=true := by decide +kernel
lemma edge105 : edgeCheck n105 n106=true := by decide +kernel
lemma ok105 : chainCheck z105=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check105,edge105⟩,ok106⟩
lemma check104 : nodeCheck n104=true := by decide +kernel
lemma edge104 : edgeCheck n104 n105=true := by decide +kernel
lemma ok104 : chainCheck z104=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check104,edge104⟩,ok105⟩
lemma check103 : nodeCheck n103=true := by decide +kernel
lemma edge103 : edgeCheck n103 n104=true := by decide +kernel
lemma ok103 : chainCheck z103=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check103,edge103⟩,ok104⟩
lemma check102 : nodeCheck n102=true := by decide +kernel
lemma edge102 : edgeCheck n102 n103=true := by decide +kernel
lemma ok102 : chainCheck z102=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check102,edge102⟩,ok103⟩
lemma check101 : nodeCheck n101=true := by decide +kernel
lemma edge101 : edgeCheck n101 n102=true := by decide +kernel
lemma ok101 : chainCheck z101=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check101,edge101⟩,ok102⟩
lemma check100 : nodeCheck n100=true := by decide +kernel
lemma edge100 : edgeCheck n100 n101=true := by decide +kernel
lemma ok100 : chainCheck z100=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check100,edge100⟩,ok101⟩
lemma check99 : nodeCheck n99=true := by decide +kernel
lemma edge99 : edgeCheck n99 n100=true := by decide +kernel
lemma ok99 : chainCheck z99=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check99,edge99⟩,ok100⟩
lemma check98 : nodeCheck n98=true := by decide +kernel
lemma edge98 : edgeCheck n98 n99=true := by decide +kernel
lemma ok98 : chainCheck z98=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check98,edge98⟩,ok99⟩
lemma check97 : nodeCheck n97=true := by decide +kernel
lemma edge97 : edgeCheck n97 n98=true := by decide +kernel
lemma ok97 : chainCheck z97=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check97,edge97⟩,ok98⟩
lemma check96 : nodeCheck n96=true := by decide +kernel
lemma edge96 : edgeCheck n96 n97=true := by decide +kernel
lemma ok96 : chainCheck z96=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check96,edge96⟩,ok97⟩
lemma check95 : nodeCheck n95=true := by decide +kernel
lemma edge95 : edgeCheck n95 n96=true := by decide +kernel
lemma ok95 : chainCheck z95=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check95,edge95⟩,ok96⟩
lemma check94 : nodeCheck n94=true := by decide +kernel
lemma edge94 : edgeCheck n94 n95=true := by decide +kernel
lemma ok94 : chainCheck z94=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check94,edge94⟩,ok95⟩
lemma check93 : nodeCheck n93=true := by decide +kernel
lemma edge93 : edgeCheck n93 n94=true := by decide +kernel
lemma ok93 : chainCheck z93=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check93,edge93⟩,ok94⟩
lemma check92 : nodeCheck n92=true := by decide +kernel
lemma edge92 : edgeCheck n92 n93=true := by decide +kernel
lemma ok92 : chainCheck z92=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check92,edge92⟩,ok93⟩
lemma check91 : nodeCheck n91=true := by decide +kernel
lemma edge91 : edgeCheck n91 n92=true := by decide +kernel
lemma ok91 : chainCheck z91=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check91,edge91⟩,ok92⟩
lemma check90 : nodeCheck n90=true := by decide +kernel
lemma edge90 : edgeCheck n90 n91=true := by decide +kernel
lemma ok90 : chainCheck z90=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check90,edge90⟩,ok91⟩
lemma check89 : nodeCheck n89=true := by decide +kernel
lemma edge89 : edgeCheck n89 n90=true := by decide +kernel
lemma ok89 : chainCheck z89=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check89,edge89⟩,ok90⟩
lemma check88 : nodeCheck n88=true := by decide +kernel
lemma edge88 : edgeCheck n88 n89=true := by decide +kernel
lemma ok88 : chainCheck z88=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check88,edge88⟩,ok89⟩
lemma check87 : nodeCheck n87=true := by decide +kernel
lemma edge87 : edgeCheck n87 n88=true := by decide +kernel
lemma ok87 : chainCheck z87=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check87,edge87⟩,ok88⟩
lemma check86 : nodeCheck n86=true := by decide +kernel
lemma edge86 : edgeCheck n86 n87=true := by decide +kernel
lemma ok86 : chainCheck z86=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check86,edge86⟩,ok87⟩
lemma check85 : nodeCheck n85=true := by decide +kernel
lemma edge85 : edgeCheck n85 n86=true := by decide +kernel
lemma ok85 : chainCheck z85=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check85,edge85⟩,ok86⟩
lemma check84 : nodeCheck n84=true := by decide +kernel
lemma edge84 : edgeCheck n84 n85=true := by decide +kernel
lemma ok84 : chainCheck z84=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check84,edge84⟩,ok85⟩
lemma check83 : nodeCheck n83=true := by decide +kernel
lemma edge83 : edgeCheck n83 n84=true := by decide +kernel
lemma ok83 : chainCheck z83=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check83,edge83⟩,ok84⟩
lemma check82 : nodeCheck n82=true := by decide +kernel
lemma edge82 : edgeCheck n82 n83=true := by decide +kernel
lemma ok82 : chainCheck z82=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check82,edge82⟩,ok83⟩
lemma check81 : nodeCheck n81=true := by decide +kernel
lemma edge81 : edgeCheck n81 n82=true := by decide +kernel
lemma ok81 : chainCheck z81=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check81,edge81⟩,ok82⟩
lemma check80 : nodeCheck n80=true := by decide +kernel
lemma edge80 : edgeCheck n80 n81=true := by decide +kernel
lemma ok80 : chainCheck z80=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check80,edge80⟩,ok81⟩
lemma check79 : nodeCheck n79=true := by decide +kernel
lemma edge79 : edgeCheck n79 n80=true := by decide +kernel
lemma ok79 : chainCheck z79=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check79,edge79⟩,ok80⟩
lemma check78 : nodeCheck n78=true := by decide +kernel
lemma edge78 : edgeCheck n78 n79=true := by decide +kernel
lemma ok78 : chainCheck z78=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check78,edge78⟩,ok79⟩
lemma check77 : nodeCheck n77=true := by decide +kernel
lemma edge77 : edgeCheck n77 n78=true := by decide +kernel
lemma ok77 : chainCheck z77=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check77,edge77⟩,ok78⟩
lemma check76 : nodeCheck n76=true := by decide +kernel
lemma edge76 : edgeCheck n76 n77=true := by decide +kernel
lemma ok76 : chainCheck z76=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check76,edge76⟩,ok77⟩
lemma check75 : nodeCheck n75=true := by decide +kernel
lemma edge75 : edgeCheck n75 n76=true := by decide +kernel
lemma ok75 : chainCheck z75=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check75,edge75⟩,ok76⟩
lemma check74 : nodeCheck n74=true := by decide +kernel
lemma edge74 : edgeCheck n74 n75=true := by decide +kernel
lemma ok74 : chainCheck z74=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check74,edge74⟩,ok75⟩
lemma check73 : nodeCheck n73=true := by decide +kernel
lemma edge73 : edgeCheck n73 n74=true := by decide +kernel
lemma ok73 : chainCheck z73=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check73,edge73⟩,ok74⟩
lemma check72 : nodeCheck n72=true := by decide +kernel
lemma edge72 : edgeCheck n72 n73=true := by decide +kernel
lemma ok72 : chainCheck z72=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check72,edge72⟩,ok73⟩
lemma check71 : nodeCheck n71=true := by decide +kernel
lemma edge71 : edgeCheck n71 n72=true := by decide +kernel
lemma ok71 : chainCheck z71=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check71,edge71⟩,ok72⟩
lemma check70 : nodeCheck n70=true := by decide +kernel
lemma edge70 : edgeCheck n70 n71=true := by decide +kernel
lemma ok70 : chainCheck z70=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check70,edge70⟩,ok71⟩
lemma check69 : nodeCheck n69=true := by decide +kernel
lemma edge69 : edgeCheck n69 n70=true := by decide +kernel
lemma ok69 : chainCheck z69=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check69,edge69⟩,ok70⟩
lemma check68 : nodeCheck n68=true := by decide +kernel
lemma edge68 : edgeCheck n68 n69=true := by decide +kernel
lemma ok68 : chainCheck z68=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check68,edge68⟩,ok69⟩
lemma check67 : nodeCheck n67=true := by decide +kernel
lemma edge67 : edgeCheck n67 n68=true := by decide +kernel
lemma ok67 : chainCheck z67=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check67,edge67⟩,ok68⟩
lemma check66 : nodeCheck n66=true := by decide +kernel
lemma edge66 : edgeCheck n66 n67=true := by decide +kernel
lemma ok66 : chainCheck z66=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check66,edge66⟩,ok67⟩
lemma check65 : nodeCheck n65=true := by decide +kernel
lemma edge65 : edgeCheck n65 n66=true := by decide +kernel
lemma ok65 : chainCheck z65=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check65,edge65⟩,ok66⟩
lemma check64 : nodeCheck n64=true := by decide +kernel
lemma edge64 : edgeCheck n64 n65=true := by decide +kernel
lemma ok64 : chainCheck z64=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check64,edge64⟩,ok65⟩
lemma check63 : nodeCheck n63=true := by decide +kernel
lemma edge63 : edgeCheck n63 n64=true := by decide +kernel
lemma ok63 : chainCheck z63=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check63,edge63⟩,ok64⟩
lemma check62 : nodeCheck n62=true := by decide +kernel
lemma edge62 : edgeCheck n62 n63=true := by decide +kernel
lemma ok62 : chainCheck z62=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check62,edge62⟩,ok63⟩
lemma check61 : nodeCheck n61=true := by decide +kernel
lemma edge61 : edgeCheck n61 n62=true := by decide +kernel
lemma ok61 : chainCheck z61=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check61,edge61⟩,ok62⟩
lemma check60 : nodeCheck n60=true := by decide +kernel
lemma edge60 : edgeCheck n60 n61=true := by decide +kernel
lemma ok60 : chainCheck z60=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check60,edge60⟩,ok61⟩
lemma check59 : nodeCheck n59=true := by decide +kernel
lemma edge59 : edgeCheck n59 n60=true := by decide +kernel
lemma ok59 : chainCheck z59=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check59,edge59⟩,ok60⟩
lemma check58 : nodeCheck n58=true := by decide +kernel
lemma edge58 : edgeCheck n58 n59=true := by decide +kernel
lemma ok58 : chainCheck z58=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check58,edge58⟩,ok59⟩
lemma check57 : nodeCheck n57=true := by decide +kernel
lemma edge57 : edgeCheck n57 n58=true := by decide +kernel
lemma ok57 : chainCheck z57=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check57,edge57⟩,ok58⟩
lemma check56 : nodeCheck n56=true := by decide +kernel
lemma edge56 : edgeCheck n56 n57=true := by decide +kernel
lemma ok56 : chainCheck z56=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check56,edge56⟩,ok57⟩
lemma check55 : nodeCheck n55=true := by decide +kernel
lemma edge55 : edgeCheck n55 n56=true := by decide +kernel
lemma ok55 : chainCheck z55=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check55,edge55⟩,ok56⟩
lemma check54 : nodeCheck n54=true := by decide +kernel
lemma edge54 : edgeCheck n54 n55=true := by decide +kernel
lemma ok54 : chainCheck z54=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check54,edge54⟩,ok55⟩
lemma check53 : nodeCheck n53=true := by decide +kernel
lemma edge53 : edgeCheck n53 n54=true := by decide +kernel
lemma ok53 : chainCheck z53=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check53,edge53⟩,ok54⟩
lemma check52 : nodeCheck n52=true := by decide +kernel
lemma edge52 : edgeCheck n52 n53=true := by decide +kernel
lemma ok52 : chainCheck z52=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check52,edge52⟩,ok53⟩
lemma check51 : nodeCheck n51=true := by decide +kernel
lemma edge51 : edgeCheck n51 n52=true := by decide +kernel
lemma ok51 : chainCheck z51=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check51,edge51⟩,ok52⟩
lemma check50 : nodeCheck n50=true := by decide +kernel
lemma edge50 : edgeCheck n50 n51=true := by decide +kernel
lemma ok50 : chainCheck z50=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check50,edge50⟩,ok51⟩
lemma check49 : nodeCheck n49=true := by decide +kernel
lemma edge49 : edgeCheck n49 n50=true := by decide +kernel
lemma ok49 : chainCheck z49=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check49,edge49⟩,ok50⟩
lemma check48 : nodeCheck n48=true := by decide +kernel
lemma edge48 : edgeCheck n48 n49=true := by decide +kernel
lemma ok48 : chainCheck z48=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check48,edge48⟩,ok49⟩
lemma check47 : nodeCheck n47=true := by decide +kernel
lemma edge47 : edgeCheck n47 n48=true := by decide +kernel
lemma ok47 : chainCheck z47=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check47,edge47⟩,ok48⟩
lemma check46 : nodeCheck n46=true := by decide +kernel
lemma edge46 : edgeCheck n46 n47=true := by decide +kernel
lemma ok46 : chainCheck z46=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check46,edge46⟩,ok47⟩
lemma check45 : nodeCheck n45=true := by decide +kernel
lemma edge45 : edgeCheck n45 n46=true := by decide +kernel
lemma ok45 : chainCheck z45=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check45,edge45⟩,ok46⟩
lemma check44 : nodeCheck n44=true := by decide +kernel
lemma edge44 : edgeCheck n44 n45=true := by decide +kernel
lemma ok44 : chainCheck z44=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check44,edge44⟩,ok45⟩
lemma check43 : nodeCheck n43=true := by decide +kernel
lemma edge43 : edgeCheck n43 n44=true := by decide +kernel
lemma ok43 : chainCheck z43=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check43,edge43⟩,ok44⟩
lemma check42 : nodeCheck n42=true := by decide +kernel
lemma edge42 : edgeCheck n42 n43=true := by decide +kernel
lemma ok42 : chainCheck z42=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check42,edge42⟩,ok43⟩
lemma check41 : nodeCheck n41=true := by decide +kernel
lemma edge41 : edgeCheck n41 n42=true := by decide +kernel
lemma ok41 : chainCheck z41=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check41,edge41⟩,ok42⟩
lemma check40 : nodeCheck n40=true := by decide +kernel
lemma edge40 : edgeCheck n40 n41=true := by decide +kernel
lemma ok40 : chainCheck z40=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check40,edge40⟩,ok41⟩
lemma check39 : nodeCheck n39=true := by decide +kernel
lemma edge39 : edgeCheck n39 n40=true := by decide +kernel
lemma ok39 : chainCheck z39=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check39,edge39⟩,ok40⟩
lemma check38 : nodeCheck n38=true := by decide +kernel
lemma edge38 : edgeCheck n38 n39=true := by decide +kernel
lemma ok38 : chainCheck z38=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check38,edge38⟩,ok39⟩
lemma check37 : nodeCheck n37=true := by decide +kernel
lemma edge37 : edgeCheck n37 n38=true := by decide +kernel
lemma ok37 : chainCheck z37=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check37,edge37⟩,ok38⟩
lemma check36 : nodeCheck n36=true := by decide +kernel
lemma edge36 : edgeCheck n36 n37=true := by decide +kernel
lemma ok36 : chainCheck z36=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check36,edge36⟩,ok37⟩
lemma check35 : nodeCheck n35=true := by decide +kernel
lemma edge35 : edgeCheck n35 n36=true := by decide +kernel
lemma ok35 : chainCheck z35=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check35,edge35⟩,ok36⟩
lemma check34 : nodeCheck n34=true := by decide +kernel
lemma edge34 : edgeCheck n34 n35=true := by decide +kernel
lemma ok34 : chainCheck z34=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check34,edge34⟩,ok35⟩
lemma check33 : nodeCheck n33=true := by decide +kernel
lemma edge33 : edgeCheck n33 n34=true := by decide +kernel
lemma ok33 : chainCheck z33=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check33,edge33⟩,ok34⟩
lemma check32 : nodeCheck n32=true := by decide +kernel
lemma edge32 : edgeCheck n32 n33=true := by decide +kernel
lemma ok32 : chainCheck z32=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check32,edge32⟩,ok33⟩
lemma check31 : nodeCheck n31=true := by decide +kernel
lemma edge31 : edgeCheck n31 n32=true := by decide +kernel
lemma ok31 : chainCheck z31=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check31,edge31⟩,ok32⟩
lemma check30 : nodeCheck n30=true := by decide +kernel
lemma edge30 : edgeCheck n30 n31=true := by decide +kernel
lemma ok30 : chainCheck z30=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check30,edge30⟩,ok31⟩
lemma check29 : nodeCheck n29=true := by decide +kernel
lemma edge29 : edgeCheck n29 n30=true := by decide +kernel
lemma ok29 : chainCheck z29=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check29,edge29⟩,ok30⟩
lemma check28 : nodeCheck n28=true := by decide +kernel
lemma edge28 : edgeCheck n28 n29=true := by decide +kernel
lemma ok28 : chainCheck z28=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check28,edge28⟩,ok29⟩
lemma check27 : nodeCheck n27=true := by decide +kernel
lemma edge27 : edgeCheck n27 n28=true := by decide +kernel
lemma ok27 : chainCheck z27=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check27,edge27⟩,ok28⟩
lemma check26 : nodeCheck n26=true := by decide +kernel
lemma edge26 : edgeCheck n26 n27=true := by decide +kernel
lemma ok26 : chainCheck z26=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check26,edge26⟩,ok27⟩
lemma check25 : nodeCheck n25=true := by decide +kernel
lemma edge25 : edgeCheck n25 n26=true := by decide +kernel
lemma ok25 : chainCheck z25=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check25,edge25⟩,ok26⟩
lemma check24 : nodeCheck n24=true := by decide +kernel
lemma edge24 : edgeCheck n24 n25=true := by decide +kernel
lemma ok24 : chainCheck z24=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check24,edge24⟩,ok25⟩
lemma check23 : nodeCheck n23=true := by decide +kernel
lemma edge23 : edgeCheck n23 n24=true := by decide +kernel
lemma ok23 : chainCheck z23=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check23,edge23⟩,ok24⟩
lemma check22 : nodeCheck n22=true := by decide +kernel
lemma edge22 : edgeCheck n22 n23=true := by decide +kernel
lemma ok22 : chainCheck z22=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check22,edge22⟩,ok23⟩
lemma check21 : nodeCheck n21=true := by decide +kernel
lemma edge21 : edgeCheck n21 n22=true := by decide +kernel
lemma ok21 : chainCheck z21=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check21,edge21⟩,ok22⟩
lemma check20 : nodeCheck n20=true := by decide +kernel
lemma edge20 : edgeCheck n20 n21=true := by decide +kernel
lemma ok20 : chainCheck z20=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check20,edge20⟩,ok21⟩
lemma check19 : nodeCheck n19=true := by decide +kernel
lemma edge19 : edgeCheck n19 n20=true := by decide +kernel
lemma ok19 : chainCheck z19=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check19,edge19⟩,ok20⟩
lemma check18 : nodeCheck n18=true := by decide +kernel
lemma edge18 : edgeCheck n18 n19=true := by decide +kernel
lemma ok18 : chainCheck z18=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check18,edge18⟩,ok19⟩
lemma check17 : nodeCheck n17=true := by decide +kernel
lemma edge17 : edgeCheck n17 n18=true := by decide +kernel
lemma ok17 : chainCheck z17=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check17,edge17⟩,ok18⟩
lemma check16 : nodeCheck n16=true := by decide +kernel
lemma edge16 : edgeCheck n16 n17=true := by decide +kernel
lemma ok16 : chainCheck z16=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check16,edge16⟩,ok17⟩
lemma check15 : nodeCheck n15=true := by decide +kernel
lemma edge15 : edgeCheck n15 n16=true := by decide +kernel
lemma ok15 : chainCheck z15=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check15,edge15⟩,ok16⟩
lemma check14 : nodeCheck n14=true := by decide +kernel
lemma edge14 : edgeCheck n14 n15=true := by decide +kernel
lemma ok14 : chainCheck z14=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check14,edge14⟩,ok15⟩
lemma check13 : nodeCheck n13=true := by decide +kernel
lemma edge13 : edgeCheck n13 n14=true := by decide +kernel
lemma ok13 : chainCheck z13=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check13,edge13⟩,ok14⟩
lemma check12 : nodeCheck n12=true := by decide +kernel
lemma edge12 : edgeCheck n12 n13=true := by decide +kernel
lemma ok12 : chainCheck z12=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check12,edge12⟩,ok13⟩
lemma check11 : nodeCheck n11=true := by decide +kernel
lemma edge11 : edgeCheck n11 n12=true := by decide +kernel
lemma ok11 : chainCheck z11=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check11,edge11⟩,ok12⟩
lemma check10 : nodeCheck n10=true := by decide +kernel
lemma edge10 : edgeCheck n10 n11=true := by decide +kernel
lemma ok10 : chainCheck z10=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check10,edge10⟩,ok11⟩
lemma check9 : nodeCheck n9=true := by decide +kernel
lemma edge9 : edgeCheck n9 n10=true := by decide +kernel
lemma ok9 : chainCheck z9=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check9,edge9⟩,ok10⟩
lemma check8 : nodeCheck n8=true := by decide +kernel
lemma edge8 : edgeCheck n8 n9=true := by decide +kernel
lemma ok8 : chainCheck z8=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check8,edge8⟩,ok9⟩
lemma check7 : nodeCheck n7=true := by decide +kernel
lemma edge7 : edgeCheck n7 n8=true := by decide +kernel
lemma ok7 : chainCheck z7=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check7,edge7⟩,ok8⟩
lemma check6 : nodeCheck n6=true := by decide +kernel
lemma edge6 : edgeCheck n6 n7=true := by decide +kernel
lemma ok6 : chainCheck z6=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check6,edge6⟩,ok7⟩
lemma check5 : nodeCheck n5=true := by decide +kernel
lemma edge5 : edgeCheck n5 n6=true := by decide +kernel
lemma ok5 : chainCheck z5=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check5,edge5⟩,ok6⟩
lemma check4 : nodeCheck n4=true := by decide +kernel
lemma edge4 : edgeCheck n4 n5=true := by decide +kernel
lemma ok4 : chainCheck z4=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check4,edge4⟩,ok5⟩
lemma check3 : nodeCheck n3=true := by decide +kernel
lemma edge3 : edgeCheck n3 n4=true := by decide +kernel
lemma ok3 : chainCheck z3=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check3,edge3⟩,ok4⟩
lemma check2 : nodeCheck n2=true := by decide +kernel
lemma edge2 : edgeCheck n2 n3=true := by decide +kernel
lemma ok2 : chainCheck z2=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check2,edge2⟩,ok3⟩
lemma check1 : nodeCheck n1=true := by decide +kernel
lemma edge1 : edgeCheck n1 n2=true := by decide +kernel
lemma ok1 : chainCheck z1=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check1,edge1⟩,ok2⟩
lemma check0 : nodeCheck n0=true := by decide +kernel
lemma edge0 : edgeCheck n0 n1=true := by decide +kernel
lemma ok0 : chainCheck z0=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check0,edge0⟩,ok1⟩
def v14 : Band := ⟨7000000,7500000,1146204,8309931,58720256,62914560,1786394,1668379⟩
lemma b14ok : bandCheck v14=true := by decide +kernel
def t14x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t14x8ok : treeCheck nodes v14 ⟨0,1048576,-8388608,8388608⟩ t14x8=true := by decide +kernel
def t14x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t14x9ok : treeCheck nodes v14 ⟨1048576,2097152,-8388608,8388608⟩ t14x9=true := by decide +kernel
def t14x4 : Tree := .d (1048576) t14x8 t14x9
lemma t14x4ok : treeCheck nodes v14 ⟨0,2097152,-8388608,8388608⟩ t14x4=true := Bool.and_eq_true_iff.mpr ⟨t14x8ok,t14x9ok⟩
def t14x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t14x5ok : treeCheck nodes v14 ⟨2097152,4194304,-8388608,8388608⟩ t14x5=true := by decide +kernel
def t14x2 : Tree := .d (2097152) t14x4 t14x5
lemma t14x2ok : treeCheck nodes v14 ⟨0,4194304,-8388608,8388608⟩ t14x2=true := Bool.and_eq_true_iff.mpr ⟨t14x4ok,t14x5ok⟩
def t14x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t14x3ok : treeCheck nodes v14 ⟨4194304,8388608,-8388608,8388608⟩ t14x3=true := by decide +kernel
def t14x1 : Tree := .d (4194304) t14x2 t14x3
lemma t14x1ok : treeCheck nodes v14 ⟨0,8388608,-8388608,8388608⟩ t14x1=true := Bool.and_eq_true_iff.mpr ⟨t14x2ok,t14x3ok⟩
def v15 : Band := ⟨7500000,8000000,1073504,8319635,62914560,67108864,1668619,1565159⟩
lemma b15ok : bandCheck v15=true := by decide +kernel
def t15x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t15x8ok : treeCheck nodes v15 ⟨0,1048576,-8388608,8388608⟩ t15x8=true := by decide +kernel
def t15x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t15x9ok : treeCheck nodes v15 ⟨1048576,2097152,-8388608,8388608⟩ t15x9=true := by decide +kernel
def t15x4 : Tree := .d (1048576) t15x8 t15x9
lemma t15x4ok : treeCheck nodes v15 ⟨0,2097152,-8388608,8388608⟩ t15x4=true := Bool.and_eq_true_iff.mpr ⟨t15x8ok,t15x9ok⟩
def t15x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t15x5ok : treeCheck nodes v15 ⟨2097152,4194304,-8388608,8388608⟩ t15x5=true := by decide +kernel
def t15x2 : Tree := .d (2097152) t15x4 t15x5
lemma t15x2ok : treeCheck nodes v15 ⟨0,4194304,-8388608,8388608⟩ t15x2=true := Bool.and_eq_true_iff.mpr ⟨t15x4ok,t15x5ok⟩
def t15x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t15x3ok : treeCheck nodes v15 ⟨4194304,8388608,-8388608,8388608⟩ t15x3=true := by decide +kernel
def t15x1 : Tree := .d (4194304) t15x2 t15x3
lemma t15x1ok : treeCheck nodes v15 ⟨0,8388608,-8388608,8388608⟩ t15x1=true := Bool.and_eq_true_iff.mpr ⟨t15x2ok,t15x3ok⟩
def v16 : Band := ⟨8000000,8500000,1009411,8327654,67108864,71303168,1565336,1473905⟩
lemma b16ok : bandCheck v16=true := by decide +kernel
def t16x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t16x8ok : treeCheck nodes v16 ⟨0,1048576,-8388608,8388608⟩ t16x8=true := by decide +kernel
def t16x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t16x9ok : treeCheck nodes v16 ⟨1048576,2097152,-8388608,8388608⟩ t16x9=true := by decide +kernel
def t16x4 : Tree := .d (1048576) t16x8 t16x9
lemma t16x4ok : treeCheck nodes v16 ⟨0,2097152,-8388608,8388608⟩ t16x4=true := Bool.and_eq_true_iff.mpr ⟨t16x8ok,t16x9ok⟩
def t16x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t16x5ok : treeCheck nodes v16 ⟨2097152,4194304,-8388608,8388608⟩ t16x5=true := by decide +kernel
def t16x2 : Tree := .d (2097152) t16x4 t16x5
lemma t16x2ok : treeCheck nodes v16 ⟨0,4194304,-8388608,8388608⟩ t16x2=true := Bool.and_eq_true_iff.mpr ⟨t16x4ok,t16x5ok⟩
def t16x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t16x3ok : treeCheck nodes v16 ⟨4194304,8388608,-8388608,8388608⟩ t16x3=true := by decide +kernel
def t16x1 : Tree := .d (4194304) t16x2 t16x3
lemma t16x1ok : treeCheck nodes v16 ⟨0,8388608,-8388608,8388608⟩ t16x1=true := Bool.and_eq_true_iff.mpr ⟨t16x2ok,t16x3ok⟩
def v17 : Band := ⟨8500000,9000000,952489,8334357,71303168,75497472,1474066,1392689⟩
lemma b17ok : bandCheck v17=true := by decide +kernel
def t17x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t17x8ok : treeCheck nodes v17 ⟨0,1048576,-8388608,8388608⟩ t17x8=true := by decide +kernel
def t17x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t17x9ok : treeCheck nodes v17 ⟨1048576,2097152,-8388608,8388608⟩ t17x9=true := by decide +kernel
def t17x4 : Tree := .d (1048576) t17x8 t17x9
lemma t17x4ok : treeCheck nodes v17 ⟨0,2097152,-8388608,8388608⟩ t17x4=true := Bool.and_eq_true_iff.mpr ⟨t17x8ok,t17x9ok⟩
def t17x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t17x5ok : treeCheck nodes v17 ⟨2097152,4194304,-8388608,8388608⟩ t17x5=true := by decide +kernel
def t17x2 : Tree := .d (2097152) t17x4 t17x5
lemma t17x2ok : treeCheck nodes v17 ⟨0,4194304,-8388608,8388608⟩ t17x2=true := Bool.and_eq_true_iff.mpr ⟨t17x4ok,t17x5ok⟩
def t17x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t17x3ok : treeCheck nodes v17 ⟨4194304,8388608,-8388608,8388608⟩ t17x3=true := by decide +kernel
def t17x1 : Tree := .d (4194304) t17x2 t17x3
lemma t17x1ok : treeCheck nodes v17 ⟨0,8388608,-8388608,8388608⟩ t17x1=true := Bool.and_eq_true_iff.mpr ⟨t17x2ok,t17x3ok⟩
def v18 : Band := ⟨9000000,9500000,901622,8340013,75497472,79691776,1392800,1319908⟩
lemma b18ok : bandCheck v18=true := by decide +kernel
def t18x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t18x8ok : treeCheck nodes v18 ⟨0,1048576,-8388608,8388608⟩ t18x8=true := by decide +kernel
def t18x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t18x9ok : treeCheck nodes v18 ⟨1048576,2097152,-8388608,8388608⟩ t18x9=true := by decide +kernel
def t18x4 : Tree := .d (1048576) t18x8 t18x9
lemma t18x4ok : treeCheck nodes v18 ⟨0,2097152,-8388608,8388608⟩ t18x4=true := Bool.and_eq_true_iff.mpr ⟨t18x8ok,t18x9ok⟩
def t18x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t18x5ok : treeCheck nodes v18 ⟨2097152,4194304,-8388608,8388608⟩ t18x5=true := by decide +kernel
def t18x2 : Tree := .d (2097152) t18x4 t18x5
lemma t18x2ok : treeCheck nodes v18 ⟨0,4194304,-8388608,8388608⟩ t18x2=true := Bool.and_eq_true_iff.mpr ⟨t18x4ok,t18x5ok⟩
def t18x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t18x3ok : treeCheck nodes v18 ⟨4194304,8388608,-8388608,8388608⟩ t18x3=true := by decide +kernel
def t18x1 : Tree := .d (4194304) t18x2 t18x3
lemma t18x1ok : treeCheck nodes v18 ⟨0,8388608,-8388608,8388608⟩ t18x1=true := Bool.and_eq_true_iff.mpr ⟨t18x2ok,t18x3ok⟩
def v19 : Band := ⟨9500000,10000000,855881,8344831,79691776,83886080,1319998,1254332⟩
lemma b19ok : bandCheck v19=true := by decide +kernel
def t19x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t19x8ok : treeCheck nodes v19 ⟨0,1048576,-8388608,8388608⟩ t19x8=true := by decide +kernel
def t19x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t19x9ok : treeCheck nodes v19 ⟨1048576,2097152,-8388608,8388608⟩ t19x9=true := by decide +kernel
def t19x4 : Tree := .d (1048576) t19x8 t19x9
lemma t19x4ok : treeCheck nodes v19 ⟨0,2097152,-8388608,8388608⟩ t19x4=true := Bool.and_eq_true_iff.mpr ⟨t19x8ok,t19x9ok⟩
def t19x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t19x5ok : treeCheck nodes v19 ⟨2097152,4194304,-8388608,8388608⟩ t19x5=true := by decide +kernel
def t19x2 : Tree := .d (2097152) t19x4 t19x5
lemma t19x2ok : treeCheck nodes v19 ⟨0,4194304,-8388608,8388608⟩ t19x2=true := Bool.and_eq_true_iff.mpr ⟨t19x4ok,t19x5ok⟩
def t19x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t19x3ok : treeCheck nodes v19 ⟨4194304,8388608,-8388608,8388608⟩ t19x3=true := by decide +kernel
def t19x1 : Tree := .d (4194304) t19x2 t19x3
lemma t19x1ok : treeCheck nodes v19 ⟨0,8388608,-8388608,8388608⟩ t19x1=true := Bool.and_eq_true_iff.mpr ⟨t19x2ok,t19x3ok⟩
def v20 : Band := ⟨10000000,10500000,814534,8348968,83886080,88080384,1254401,1194941⟩
lemma b20ok : bandCheck v20=true := by decide +kernel
def t20x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t20x16ok : treeCheck nodes v20 ⟨0,524288,-8388608,8388608⟩ t20x16=true := by decide +kernel
def t20x17 : Tree := .leaf ⟨false,8372208,1048576,0,8388608,-8388608,8388608⟩
lemma t20x17ok : treeCheck nodes v20 ⟨524288,1048576,-8388608,8388608⟩ t20x17=true := by decide +kernel
def t20x8 : Tree := .d (524288) t20x16 t20x17
lemma t20x8ok : treeCheck nodes v20 ⟨0,1048576,-8388608,8388608⟩ t20x8=true := Bool.and_eq_true_iff.mpr ⟨t20x16ok,t20x17ok⟩
def t20x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t20x9ok : treeCheck nodes v20 ⟨1048576,2097152,-8388608,8388608⟩ t20x9=true := by decide +kernel
def t20x4 : Tree := .d (1048576) t20x8 t20x9
lemma t20x4ok : treeCheck nodes v20 ⟨0,2097152,-8388608,8388608⟩ t20x4=true := Bool.and_eq_true_iff.mpr ⟨t20x8ok,t20x9ok⟩
def t20x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t20x5ok : treeCheck nodes v20 ⟨2097152,4194304,-8388608,8388608⟩ t20x5=true := by decide +kernel
def t20x2 : Tree := .d (2097152) t20x4 t20x5
lemma t20x2ok : treeCheck nodes v20 ⟨0,4194304,-8388608,8388608⟩ t20x2=true := Bool.and_eq_true_iff.mpr ⟨t20x4ok,t20x5ok⟩
def t20x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t20x3ok : treeCheck nodes v20 ⟨4194304,8388608,-8388608,8388608⟩ t20x3=true := by decide +kernel
def t20x1 : Tree := .d (4194304) t20x2 t20x3
lemma t20x1ok : treeCheck nodes v20 ⟨0,8388608,-8388608,8388608⟩ t20x1=true := Bool.and_eq_true_iff.mpr ⟨t20x2ok,t20x3ok⟩
def v21 : Band := ⟨10500000,11000000,776973,8352547,88080384,92274688,1194997,1140905⟩
lemma b21ok : bandCheck v21=true := by decide +kernel
def t21x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t21x16ok : treeCheck nodes v21 ⟨0,524288,-8388608,8388608⟩ t21x16=true := by decide +kernel
def t21x17 : Tree := .leaf ⟨false,8372208,1048576,0,8388608,-8388608,8388608⟩
lemma t21x17ok : treeCheck nodes v21 ⟨524288,1048576,-8388608,8388608⟩ t21x17=true := by decide +kernel
def t21x8 : Tree := .d (524288) t21x16 t21x17
lemma t21x8ok : treeCheck nodes v21 ⟨0,1048576,-8388608,8388608⟩ t21x8=true := Bool.and_eq_true_iff.mpr ⟨t21x16ok,t21x17ok⟩
def t21x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t21x9ok : treeCheck nodes v21 ⟨1048576,2097152,-8388608,8388608⟩ t21x9=true := by decide +kernel
def t21x4 : Tree := .d (1048576) t21x8 t21x9
lemma t21x4ok : treeCheck nodes v21 ⟨0,2097152,-8388608,8388608⟩ t21x4=true := Bool.and_eq_true_iff.mpr ⟨t21x8ok,t21x9ok⟩
def t21x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t21x5ok : treeCheck nodes v21 ⟨2097152,4194304,-8388608,8388608⟩ t21x5=true := by decide +kernel
def t21x2 : Tree := .d (2097152) t21x4 t21x5
lemma t21x2ok : treeCheck nodes v21 ⟨0,4194304,-8388608,8388608⟩ t21x2=true := Bool.and_eq_true_iff.mpr ⟨t21x4ok,t21x5ok⟩
def t21x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t21x3ok : treeCheck nodes v21 ⟨4194304,8388608,-8388608,8388608⟩ t21x3=true := by decide +kernel
def t21x1 : Tree := .d (4194304) t21x2 t21x3
lemma t21x1ok : treeCheck nodes v21 ⟨0,8388608,-8388608,8388608⟩ t21x1=true := Bool.and_eq_true_iff.mpr ⟨t21x2ok,t21x3ok⟩
end GateChecker.M2

end

section

namespace GateChecker.M3
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false
def n0 : Node := ⟨0,8388608,-5931642,-5931641,10273905,0,33⟩
def n1 : Node := ⟨32768,8388545,-5931552,-5931550,10273853,51811,33⟩
def n2 : Node := ⟨65536,8388353,-5931280,-5931278,10273696,103621,33⟩
def n3 : Node := ⟨98304,8388033,-5930828,-5930826,10273435,155429,33⟩
def n4 : Node := ⟨131072,8387585,-5930194,-5930192,10273069,207233,34⟩
def n5 : Node := ⟨163840,8387009,-5929380,-5929378,10272599,259035,34⟩
def n6 : Node := ⟨196608,8386305,-5928384,-5928382,10272024,310831,34⟩
def n7 : Node := ⟨229376,8385473,-5927208,-5927206,10271345,362622,34⟩
def n8 : Node := ⟨262144,8384513,-5925850,-5925848,10270562,414406,35⟩
def n9 : Node := ⟨294912,8383426,-5924311,-5924309,10269674,466182,35⟩
def n10 : Node := ⟨327680,8382211,-5922592,-5922590,10268682,517950,35⟩
def n11 : Node := ⟨360448,8380868,-5920691,-5920689,10267586,569708,35⟩
def n12 : Node := ⟨393216,8379398,-5918609,-5918607,10266386,621456,36⟩
def n13 : Node := ⟨425984,8377799,-5916346,-5916344,10265081,673193,36⟩
def n14 : Node := ⟨458752,8376074,-5913903,-5913901,10263673,724917,36⟩
def n15 : Node := ⟨491520,8374221,-5911278,-5911276,10262161,776628,36⟩
def n16 : Node := ⟨524288,8372240,-5908472,-5908470,10260545,828325,37⟩
def n17 : Node := ⟨557056,8370133,-5905485,-5905483,10258825,880007,37⟩
def n18 : Node := ⟨589824,8367898,-5902317,-5902315,10257002,931672,37⟩
def n19 : Node := ⟨622592,8365536,-5898969,-5898967,10255075,983321,37⟩
def n20 : Node := ⟨655360,8363048,-5895439,-5895437,10253045,1034951,38⟩
def n21 : Node := ⟨688128,8360432,-5891728,-5891726,10250912,1086563,38⟩
def n22 : Node := ⟨720896,8357690,-5887836,-5887834,10248676,1138154,38⟩
def n23 : Node := ⟨753664,8354821,-5883763,-5883761,10246336,1189725,38⟩
def n24 : Node := ⟨786432,8351825,-5879509,-5879507,10243894,1241274,39⟩
def n25 : Node := ⟨819200,8348704,-5875074,-5875072,10241349,1292800,39⟩
def n26 : Node := ⟨851968,8345456,-5870458,-5870456,10238702,1344303,39⟩
def n27 : Node := ⟨884736,8342082,-5865661,-5865659,10235952,1395781,39⟩
def n28 : Node := ⟨917504,8338582,-5860683,-5860681,10233101,1447234,40⟩
def n29 : Node := ⟨950272,8334957,-5855524,-5855522,10230147,1498660,40⟩
def n30 : Node := ⟨983040,8331206,-5850184,-5850182,10227091,1550058,40⟩
def n31 : Node := ⟨1015808,8327329,-5844663,-5844661,10223934,1601428,40⟩
def n32 : Node := ⟨1048576,8323328,-5838961,-5838959,10220675,1652769,41⟩
def n33 : Node := ⟨1081344,8319201,-5833077,-5833075,10217316,1704080,41⟩
def n34 : Node := ⟨1114112,8314950,-5827013,-5827011,10213855,1755359,41⟩
def n35 : Node := ⟨1146880,8310574,-5820768,-5820766,10210293,1806606,41⟩
def n36 : Node := ⟨1179648,8306073,-5814342,-5814340,10206631,1857821,42⟩
def n37 : Node := ⟨1212416,8301448,-5807735,-5807733,10202869,1909001,42⟩
def n38 : Node := ⟨1245184,8296700,-5800947,-5800945,10199006,1960146,42⟩
def n39 : Node := ⟨1277952,8291827,-5793977,-5793975,10195044,2011255,42⟩
def n40 : Node := ⟨1310720,8286831,-5786827,-5786825,10190982,2062328,43⟩
def n41 : Node := ⟨1343488,8281711,-5779496,-5779494,10186821,2113363,43⟩
def n42 : Node := ⟨1376256,8276469,-5771983,-5771981,10182560,2164359,43⟩
def n43 : Node := ⟨1409024,8271103,-5764290,-5764288,10178201,2215316,43⟩
def n44 : Node := ⟨1441792,8265615,-5756416,-5756414,10173744,2266232,44⟩
def n45 : Node := ⟨1474560,8260004,-5748360,-5748358,10169188,2317106,44⟩
def n46 : Node := ⟨1507328,8254272,-5740124,-5740122,10164535,2367939,44⟩
def n47 : Node := ⟨1540096,8248417,-5731707,-5731705,10159784,2418727,44⟩
def n48 : Node := ⟨1572864,8242441,-5723108,-5723106,10154935,2469472,45⟩
def n49 : Node := ⟨1605632,8236343,-5714329,-5714327,10149990,2520171,45⟩
def n50 : Node := ⟨1638400,8230125,-5705368,-5705366,10144948,2570825,45⟩
def n51 : Node := ⟨1671168,8223785,-5696227,-5696225,10139810,2621431,45⟩
def n52 : Node := ⟨1703936,8217325,-5686904,-5686902,10134576,2671989,46⟩
def n53 : Node := ⟨1736704,8210745,-5677401,-5677399,10129246,2722499,46⟩
def n54 : Node := ⟨1769472,8204045,-5667716,-5667714,10123821,2772959,46⟩
def n55 : Node := ⟨1802240,8197225,-5657851,-5657849,10118301,2823368,46⟩
def n56 : Node := ⟨1835008,8190286,-5647804,-5647802,10112687,2873725,47⟩
def n57 : Node := ⟨1867776,8183228,-5637577,-5637575,10106978,2924030,47⟩
def n58 : Node := ⟨1900544,8176052,-5627168,-5627166,10101176,2974281,47⟩
def n59 : Node := ⟨1933312,8168757,-5616578,-5616576,10095281,3024478,47⟩
def n60 : Node := ⟨1966080,8161344,-5605808,-5605806,10089293,3074620,48⟩
def n61 : Node := ⟨1998848,8153813,-5594856,-5594854,10083212,3124705,48⟩
def n62 : Node := ⟨2031616,8146165,-5583723,-5583721,10077039,3174734,48⟩
def n63 : Node := ⟨2064384,8138400,-5572410,-5572408,10070774,3224704,48⟩
def n64 : Node := ⟨2097152,8130518,-5560915,-5560913,10064418,3274615,784⟩
def n65 : Node := ⟨2228224,8097832,-5513126,-5513124,10038092,3473653,800⟩
def n66 : Node := ⟨2359296,8063308,-5462440,-5462438,10010345,3671676,816⟩
def n67 : Node := ⟨2490368,8026971,-5408859,-5408857,9981207,3868625,832⟩
def n68 : Node := ⟨2621440,7988848,-5352381,-5352379,9950715,4064444,848⟩
def n69 : Node := ⟨2752512,7948964,-5293006,-5293004,9918904,4259077,864⟩
def n70 : Node := ⟨2883584,7907349,-5230736,-5230734,9885815,4452466,880⟩
def n71 : Node := ⟨3014656,7864032,-5165569,-5165567,9851489,4644557,896⟩
def n72 : Node := ⟨3145728,7819043,-5097505,-5097503,9815972,4835293,912⟩
def n73 : Node := ⟨3276800,7772413,-5026546,-5026544,9779310,5024621,928⟩
def n74 : Node := ⟨3407872,7724176,-4952690,-4952688,9741554,5212486,944⟩
def n75 : Node := ⟨3538944,7674364,-4875938,-4875936,9702758,5398834,960⟩
def n76 : Node := ⟨3670016,7623012,-4796289,-4796287,9662978,5583613,976⟩
def n77 : Node := ⟨3801088,7570155,-4713744,-4713743,9622273,5766771,992⟩
def n78 : Node := ⟨3932160,7515829,-4628303,-4628301,9580706,5948255,1008⟩
def n79 : Node := ⟨4063232,7460072,-4539966,-4539964,9538346,6128016,1024⟩
def n80 : Node := ⟨4194304,7402921,-4448732,-4448730,9495260,6306003,1040⟩
def n81 : Node := ⟨4325376,7344415,-4354602,-4354600,9451524,6482168,1056⟩
def n82 : Node := ⟨4456448,7284592,-4257576,-4257574,9407215,6656461,1072⟩
def n83 : Node := ⟨4587520,7223492,-4157653,-4157651,9362416,6828837,1088⟩
def n84 : Node := ⟨4718592,7161157,-4054834,-4054832,9317211,6999248,1104⟩
def n85 : Node := ⟨4849664,7097626,-3949119,-3949117,9271693,7167649,1120⟩
def n86 : Node := ⟨4980736,7032942,-3840507,-3840505,9225955,7333997,1136⟩
def n87 : Node := ⟨5111808,6967146,-3728999,-3728997,9180097,7498248,1152⟩
def n88 : Node := ⟨5242880,6900281,-3614595,-3614593,9134224,7660360,1168⟩
def n89 : Node := ⟨5373952,6832390,-3497294,-3497293,9088444,7820294,1184⟩
def n90 : Node := ⟨5505024,6763514,-3377097,-3377096,9042872,7978009,1200⟩
def n91 : Node := ⟨5636096,6693699,-3254004,-3254003,8997627,8133468,1216⟩
def n92 : Node := ⟨5767168,6622987,-3128015,-3128013,8952833,8286636,1232⟩
def n93 : Node := ⟨5898240,6551423,-2999129,-2999128,8908621,8437476,1248⟩
def n94 : Node := ⟨6029312,6479050,-2867347,-2867345,8865124,8585957,1264⟩
def n95 : Node := ⟨6160384,6405912,-2732669,-2732667,8822484,8732046,1280⟩
def n96 : Node := ⟨6291456,6332054,-2595094,-2595092,8780846,8875714,1296⟩
def n97 : Node := ⟨6422528,6257519,-2454623,-2454621,8740362,9016934,1312⟩
def n98 : Node := ⟨6553600,6182353,-2311256,-2311254,8701187,9155679,1328⟩
def n99 : Node := ⟨6684672,6106598,-2164992,-2164991,8663483,9291927,1344⟩
def n100 : Node := ⟨6815744,6030299,-2015832,-2015831,8627417,9425655,1360⟩
def n101 : Node := ⟨6946816,5953499,-1863776,-1863774,8593161,9556845,1376⟩
def n102 : Node := ⟨7077888,5876243,-1708823,-1708822,8560889,9685480,1392⟩
def n103 : Node := ⟨7208960,5798574,-1550974,-1550973,8530784,9811546,1408⟩
def n104 : Node := ⟨7340032,5720534,-1390229,-1390228,8503028,9935031,1424⟩
def n105 : Node := ⟨7471104,5642167,-1226588,-1226586,8477810,10055928,1440⟩
def n106 : Node := ⟨7602176,5563515,-1060050,-1060049,8455321,10174229,1456⟩
def n107 : Node := ⟨7733248,5484621,-890616,-890615,8435754,10289934,1472⟩
def n108 : Node := ⟨7864320,5405525,-718285,-718284,8419304,10403042,1488⟩
def n109 : Node := ⟨7995392,5326269,-543059,-543057,8406168,10513557,1504⟩
def n110 : Node := ⟨8126464,5246895,-364936,-364934,8396543,10621488,1520⟩
def n111 : Node := ⟨8257536,5167441,-183916,-183915,8390624,10726846,1536⟩
def n112 : Node := ⟨8388608,5087948,0,0,8388608,10829647,6272⟩
def n113 : Node := ⟨8650752,4929001,376520,376521,8397054,11027658,6400⟩
def n114 : Node := ⟨8912896,4770359,764625,764626,8423384,11215734,6528⟩
def n115 : Node := ⟨9175040,4612316,1164316,1164317,8469025,11394162,6656⟩
def n116 : Node := ⟨9437184,4455157,1575592,1575593,8535294,11563315,6784⟩
def n117 : Node := ⟨9699328,4299152,1998453,1998454,8623373,11723659,6912⟩
def n118 : Node := ⟨9961472,4144560,2432899,2432901,8734286,11875760,7040⟩
def n119 : Node := ⟨10223616,3991627,2878931,2878932,8868878,12020295,7168⟩
def n120 : Node := ⟨10485760,3840585,3336548,3336549,9027808,12158062,7296⟩
def n121 : Node := ⟨10747904,3691652,3805750,3805751,9211541,12289988,7424⟩
def n122 : Node := ⟨11010048,3545030,4286537,4286539,9420359,12417141,7552⟩
def n123 : Node := ⟨11272192,3400909,4778909,4778911,9654364,12540737,7680⟩
def n124 : Node := ⟨11534336,3259462,5282867,5282869,9913498,12662153,7808⟩
def n125 : Node := ⟨11796480,3120849,5798410,5798412,10197565,12782932,7936⟩
def n126 : Node := ⟨12058624,2985215,6325539,6325541,10506246,12904792,8064⟩
def n127 : Node := ⟨12320768,2852687,6864252,6864254,10839129,13029630,8192⟩
def n128 : Node := ⟨12582912,2723383,7414551,7414553,11195729,13159525,8320⟩
def n129 : Node := ⟨12845056,2597401,7976435,7976437,11575504,13296736,8448⟩
def n130 : Node := ⟨13107200,2474830,8549904,8549906,11977881,13443698,8576⟩
def n131 : Node := ⟨13369344,2355741,9134958,9134961,12402268,13603009,8704⟩
def n132 : Node := ⟨13631488,2240194,9731598,9731601,12848065,13777417,8832⟩
def n133 : Node := ⟨13893632,2128235,10339823,10339826,13314681,13969798,8960⟩
def n134 : Node := ⟨14155776,2019897,10959633,10959636,13801534,14183128,9088⟩
def n135 : Node := ⟨14417920,1915204,11591028,11591031,14308065,14420451,9216⟩
def n136 : Node := ⟨14680064,1814164,12234009,12234012,14833738,14684842,9344⟩
def n137 : Node := ⟨14942208,1716778,12888575,12888578,15378042,14979365,9472⟩
def n138 : Node := ⟨15204352,1623033,13554726,13554729,15940496,15307033,9600⟩
def n139 : Node := ⟨15466496,1532910,14232462,14232466,16520648,15670764,9728⟩
def n140 : Node := ⟨15728640,1446378,14921784,14921787,17118074,16073343,9856⟩
def n141 : Node := ⟨15990784,1363398,15622691,15622694,17732380,16517390,9984⟩
def n142 : Node := ⟨16252928,1283925,16335183,16335186,18363198,17005326,10112⟩
def n143 : Node := ⟨16515072,1207904,17059260,17059264,19010187,17539358,10240⟩
def n144 : Node := ⟨16777216,1135275,17794923,17794926,19673030,18121465,41984⟩
def n145 : Node := ⟨17301504,999922,19301003,19301007,21045132,19436658,43008⟩
def n146 : Node := ⟨17825792,877273,20853425,20853429,22477415,20962201,44032⟩
def n147 : Node := ⟨18350080,766667,22452188,22452192,23968096,22706180,45056⟩
def n148 : Node := ⟨18874368,667394,24097291,24097296,25515649,24674109,46080⟩
def n149 : Node := ⟨19398656,578711,25788736,25788741,27118772,26869637,47104⟩
def n150 : Node := ⟨19922944,499855,27526521,27526527,28776350,29295198,48128⟩
def n151 : Node := ⟨20447232,430061,29310647,29310653,30487424,31952544,49152⟩
def n152 : Node := ⟨20971520,368570,31141115,31141121,32251171,34843136,50176⟩
def n153 : Node := ⟨21495808,314640,33017923,33017930,34066879,37968411,51200⟩
def n154 : Node := ⟨22020096,267553,34941072,34941079,35933934,41329950,52224⟩
def n155 : Node := ⟨22544384,226627,36910562,36910570,37851799,44929574,53248⟩
def n156 : Node := ⟨23068672,191212,38926394,38926401,39820011,48769383,54272⟩
def n157 : Node := ⟨23592960,160703,40988566,40988574,41838161,52851772,55296⟩
def n158 : Node := ⟨24117248,134535,43097079,43097087,43905892,57179419,56320⟩
def n159 : Node := ⟨24641536,112189,45251933,45251941,46022893,61755270,57344⟩
def n160 : Node := ⟨25165824,93190,47453128,47453136,48188885,66582512,58368⟩
def n161 : Node := ⟨25690112,77106,49700663,49700673,50403624,71664551,59392⟩
def n162 : Node := ⟨26214400,63550,51994540,51994550,52666893,77004982,60416⟩
def n163 : Node := ⟨26738688,52173,54334758,54334768,54978499,82607573,61440⟩
def n164 : Node := ⟨27262976,42666,56721317,56721327,57338270,88476238,62464⟩
def n165 : Node := ⟨27787264,34755,59154216,59154227,59746053,94615021,63488⟩
def n166 : Node := ⟨28311552,28200,61633457,61633468,62201709,101028078,64512⟩
def n167 : Node := ⟨28835840,22793,64159038,64159050,64705115,107719663,65536⟩
def n168 : Node := ⟨29360128,18351,66730961,66730973,67256159,114694117,66560⟩
def n169 : Node := ⟨29884416,14716,69349224,69349237,69854740,121955855,67584⟩
def n170 : Node := ⟨30408704,11756,72013829,72013842,72500769,129509356,68608⟩
def n171 : Node := ⟨30932992,9355,74724774,74724787,75194161,137359157,69632⟩
def n172 : Node := ⟨31457280,7415,77482060,77482074,77934843,145509846,70656⟩
def n173 : Node := ⟨31981568,5854,80285687,80285702,80722746,153966053,71680⟩
def n174 : Node := ⟨32505856,4604,83135655,83135670,83557809,162732447,72704⟩
def n175 : Node := ⟨33030144,3607,86031964,86031980,86439975,171813734,73728⟩
def n176 : Node := ⟨33554432,2815,88974615,88974630,89369192,181214645,303104⟩
def n177 : Node := ⟨34603008,1694,94998937,94998954,95368595,200994407,311296⟩
def n178 : Node := ⟨35651584,1004,101208624,101208642,101555682,222110087,319488⟩
def n179 : Node := ⟨36700160,586,107603675,107603694,107930172,244600338,327680⟩
def n180 : Node := ⟨37748736,337,114184089,114184109,114491824,268504056,335872⟩
def n181 : Node := ⟨38797312,191,120949867,120949888,121240431,293860332,344064⟩
def n182 : Node := ⟨39845888,107,127901009,127901031,128175818,320708414,352256⟩
def n183 : Node := ⟨40894464,59,135037514,135037538,135297831,349087683,360448⟩
def n184 : Node := ⟨41943040,32,142359384,142359408,142606336,379037623,368640⟩
def n185 : Node := ⟨42991616,18,149866617,149866643,150101220,410597808,376832⟩
def n186 : Node := ⟨44040192,10,157559214,157559241,157782381,443807886,385024⟩
def n187 : Node := ⟨45088768,5,165437174,165437203,165649731,478707567,393216⟩
def n188 : Node := ⟨46137344,3,173500499,173500529,173703190,515336613,401408⟩
def n189 : Node := ⟨47185920,2,181749187,181749219,181942691,553734830,409600⟩
def n190 : Node := ⟨48234496,1,190183239,190183272,190368172,593942065,417792⟩
def n191 : Node := ⟨49283072,1,198802655,198802689,198979579,635998194,425984⟩
def n192 : Node := ⟨50331648,1,207607435,207607470,207776863,679943123,1769472⟩
def n193 : Node := ⟨52428800,1,225773085,225773124,225928895,773659119,1835008⟩
def n194 : Node := ⟨54525952,1,244680191,244680233,244823972,875409731,1900544⟩
def n195 : Node := ⟨56623104,1,264328752,264328797,264461854,985514893,1966080⟩
def n196 : Node := ⟨58720256,1,284718768,284718816,284842346,1104294744,2031616⟩
def n197 : Node := ⟨60817408,1,305850239,305850291,305965287,1232069579,2097152⟩
def n198 : Node := ⟨62914560,1,327723165,327723221,327830541,1369159818,2162688⟩
def n199 : Node := ⟨65011712,1,350337546,350337606,350437998,1515885983,2228224⟩
def n200 : Node := ⟨67108864,1,373693383,373693446,373787563,1672568674,2228224⟩
def z200 : List Node := n200 :: []
def z199 : List Node := n199 :: z200
def z198 : List Node := n198 :: z199
def z197 : List Node := n197 :: z198
def z196 : List Node := n196 :: z197
def z195 : List Node := n195 :: z196
def z194 : List Node := n194 :: z195
def z193 : List Node := n193 :: z194
def z192 : List Node := n192 :: z193
def z191 : List Node := n191 :: z192
def z190 : List Node := n190 :: z191
def z189 : List Node := n189 :: z190
def z188 : List Node := n188 :: z189
def z187 : List Node := n187 :: z188
def z186 : List Node := n186 :: z187
def z185 : List Node := n185 :: z186
def z184 : List Node := n184 :: z185
def z183 : List Node := n183 :: z184
def z182 : List Node := n182 :: z183
def z181 : List Node := n181 :: z182
def z180 : List Node := n180 :: z181
def z179 : List Node := n179 :: z180
def z178 : List Node := n178 :: z179
def z177 : List Node := n177 :: z178
def z176 : List Node := n176 :: z177
def z175 : List Node := n175 :: z176
def z174 : List Node := n174 :: z175
def z173 : List Node := n173 :: z174
def z172 : List Node := n172 :: z173
def z171 : List Node := n171 :: z172
def z170 : List Node := n170 :: z171
def z169 : List Node := n169 :: z170
def z168 : List Node := n168 :: z169
def z167 : List Node := n167 :: z168
def z166 : List Node := n166 :: z167
def z165 : List Node := n165 :: z166
def z164 : List Node := n164 :: z165
def z163 : List Node := n163 :: z164
def z162 : List Node := n162 :: z163
def z161 : List Node := n161 :: z162
def z160 : List Node := n160 :: z161
def z159 : List Node := n159 :: z160
def z158 : List Node := n158 :: z159
def z157 : List Node := n157 :: z158
def z156 : List Node := n156 :: z157
def z155 : List Node := n155 :: z156
def z154 : List Node := n154 :: z155
def z153 : List Node := n153 :: z154
def z152 : List Node := n152 :: z153
def z151 : List Node := n151 :: z152
def z150 : List Node := n150 :: z151
def z149 : List Node := n149 :: z150
def z148 : List Node := n148 :: z149
def z147 : List Node := n147 :: z148
def z146 : List Node := n146 :: z147
def z145 : List Node := n145 :: z146
def z144 : List Node := n144 :: z145
def z143 : List Node := n143 :: z144
def z142 : List Node := n142 :: z143
def z141 : List Node := n141 :: z142
def z140 : List Node := n140 :: z141
def z139 : List Node := n139 :: z140
def z138 : List Node := n138 :: z139
def z137 : List Node := n137 :: z138
def z136 : List Node := n136 :: z137
def z135 : List Node := n135 :: z136
def z134 : List Node := n134 :: z135
def z133 : List Node := n133 :: z134
def z132 : List Node := n132 :: z133
def z131 : List Node := n131 :: z132
def z130 : List Node := n130 :: z131
def z129 : List Node := n129 :: z130
def z128 : List Node := n128 :: z129
def z127 : List Node := n127 :: z128
def z126 : List Node := n126 :: z127
def z125 : List Node := n125 :: z126
def z124 : List Node := n124 :: z125
def z123 : List Node := n123 :: z124
def z122 : List Node := n122 :: z123
def z121 : List Node := n121 :: z122
def z120 : List Node := n120 :: z121
def z119 : List Node := n119 :: z120
def z118 : List Node := n118 :: z119
def z117 : List Node := n117 :: z118
def z116 : List Node := n116 :: z117
def z115 : List Node := n115 :: z116
def z114 : List Node := n114 :: z115
def z113 : List Node := n113 :: z114
def z112 : List Node := n112 :: z113
def z111 : List Node := n111 :: z112
def z110 : List Node := n110 :: z111
def z109 : List Node := n109 :: z110
def z108 : List Node := n108 :: z109
def z107 : List Node := n107 :: z108
def z106 : List Node := n106 :: z107
def z105 : List Node := n105 :: z106
def z104 : List Node := n104 :: z105
def z103 : List Node := n103 :: z104
def z102 : List Node := n102 :: z103
def z101 : List Node := n101 :: z102
def z100 : List Node := n100 :: z101
def z99 : List Node := n99 :: z100
def z98 : List Node := n98 :: z99
def z97 : List Node := n97 :: z98
def z96 : List Node := n96 :: z97
def z95 : List Node := n95 :: z96
def z94 : List Node := n94 :: z95
def z93 : List Node := n93 :: z94
def z92 : List Node := n92 :: z93
def z91 : List Node := n91 :: z92
def z90 : List Node := n90 :: z91
def z89 : List Node := n89 :: z90
def z88 : List Node := n88 :: z89
def z87 : List Node := n87 :: z88
def z86 : List Node := n86 :: z87
def z85 : List Node := n85 :: z86
def z84 : List Node := n84 :: z85
def z83 : List Node := n83 :: z84
def z82 : List Node := n82 :: z83
def z81 : List Node := n81 :: z82
def z80 : List Node := n80 :: z81
def z79 : List Node := n79 :: z80
def z78 : List Node := n78 :: z79
def z77 : List Node := n77 :: z78
def z76 : List Node := n76 :: z77
def z75 : List Node := n75 :: z76
def z74 : List Node := n74 :: z75
def z73 : List Node := n73 :: z74
def z72 : List Node := n72 :: z73
def z71 : List Node := n71 :: z72
def z70 : List Node := n70 :: z71
def z69 : List Node := n69 :: z70
def z68 : List Node := n68 :: z69
def z67 : List Node := n67 :: z68
def z66 : List Node := n66 :: z67
def z65 : List Node := n65 :: z66
def z64 : List Node := n64 :: z65
def z63 : List Node := n63 :: z64
def z62 : List Node := n62 :: z63
def z61 : List Node := n61 :: z62
def z60 : List Node := n60 :: z61
def z59 : List Node := n59 :: z60
def z58 : List Node := n58 :: z59
def z57 : List Node := n57 :: z58
def z56 : List Node := n56 :: z57
def z55 : List Node := n55 :: z56
def z54 : List Node := n54 :: z55
def z53 : List Node := n53 :: z54
def z52 : List Node := n52 :: z53
def z51 : List Node := n51 :: z52
def z50 : List Node := n50 :: z51
def z49 : List Node := n49 :: z50
def z48 : List Node := n48 :: z49
def z47 : List Node := n47 :: z48
def z46 : List Node := n46 :: z47
def z45 : List Node := n45 :: z46
def z44 : List Node := n44 :: z45
def z43 : List Node := n43 :: z44
def z42 : List Node := n42 :: z43
def z41 : List Node := n41 :: z42
def z40 : List Node := n40 :: z41
def z39 : List Node := n39 :: z40
def z38 : List Node := n38 :: z39
def z37 : List Node := n37 :: z38
def z36 : List Node := n36 :: z37
def z35 : List Node := n35 :: z36
def z34 : List Node := n34 :: z35
def z33 : List Node := n33 :: z34
def z32 : List Node := n32 :: z33
def z31 : List Node := n31 :: z32
def z30 : List Node := n30 :: z31
def z29 : List Node := n29 :: z30
def z28 : List Node := n28 :: z29
def z27 : List Node := n27 :: z28
def z26 : List Node := n26 :: z27
def z25 : List Node := n25 :: z26
def z24 : List Node := n24 :: z25
def z23 : List Node := n23 :: z24
def z22 : List Node := n22 :: z23
def z21 : List Node := n21 :: z22
def z20 : List Node := n20 :: z21
def z19 : List Node := n19 :: z20
def z18 : List Node := n18 :: z19
def z17 : List Node := n17 :: z18
def z16 : List Node := n16 :: z17
def z15 : List Node := n15 :: z16
def z14 : List Node := n14 :: z15
def z13 : List Node := n13 :: z14
def z12 : List Node := n12 :: z13
def z11 : List Node := n11 :: z12
def z10 : List Node := n10 :: z11
def z9 : List Node := n9 :: z10
def z8 : List Node := n8 :: z9
def z7 : List Node := n7 :: z8
def z6 : List Node := n6 :: z7
def z5 : List Node := n5 :: z6
def z4 : List Node := n4 :: z5
def z3 : List Node := n3 :: z4
def z2 : List Node := n2 :: z3
def z1 : List Node := n1 :: z2
def z0 : List Node := n0 :: z1
def nodes := z0
lemma starts : PanelChain.start nodes=true := by decide +kernel
lemma check200 : nodeCheck n200=true := by decide +kernel
lemma ok200 : chainCheck z200=true := Bool.and_eq_true_iff.mpr ⟨check200,by decide +kernel⟩
lemma check199 : nodeCheck n199=true := by decide +kernel
lemma edge199 : edgeCheck n199 n200=true := by decide +kernel
lemma ok199 : chainCheck z199=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check199,edge199⟩,ok200⟩
lemma check198 : nodeCheck n198=true := by decide +kernel
lemma edge198 : edgeCheck n198 n199=true := by decide +kernel
lemma ok198 : chainCheck z198=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check198,edge198⟩,ok199⟩
lemma check197 : nodeCheck n197=true := by decide +kernel
lemma edge197 : edgeCheck n197 n198=true := by decide +kernel
lemma ok197 : chainCheck z197=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check197,edge197⟩,ok198⟩
lemma check196 : nodeCheck n196=true := by decide +kernel
lemma edge196 : edgeCheck n196 n197=true := by decide +kernel
lemma ok196 : chainCheck z196=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check196,edge196⟩,ok197⟩
lemma check195 : nodeCheck n195=true := by decide +kernel
lemma edge195 : edgeCheck n195 n196=true := by decide +kernel
lemma ok195 : chainCheck z195=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check195,edge195⟩,ok196⟩
lemma check194 : nodeCheck n194=true := by decide +kernel
lemma edge194 : edgeCheck n194 n195=true := by decide +kernel
lemma ok194 : chainCheck z194=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check194,edge194⟩,ok195⟩
lemma check193 : nodeCheck n193=true := by decide +kernel
lemma edge193 : edgeCheck n193 n194=true := by decide +kernel
lemma ok193 : chainCheck z193=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check193,edge193⟩,ok194⟩
lemma check192 : nodeCheck n192=true := by decide +kernel
lemma edge192 : edgeCheck n192 n193=true := by decide +kernel
lemma ok192 : chainCheck z192=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check192,edge192⟩,ok193⟩
lemma check191 : nodeCheck n191=true := by decide +kernel
lemma edge191 : edgeCheck n191 n192=true := by decide +kernel
lemma ok191 : chainCheck z191=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check191,edge191⟩,ok192⟩
lemma check190 : nodeCheck n190=true := by decide +kernel
lemma edge190 : edgeCheck n190 n191=true := by decide +kernel
lemma ok190 : chainCheck z190=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check190,edge190⟩,ok191⟩
lemma check189 : nodeCheck n189=true := by decide +kernel
lemma edge189 : edgeCheck n189 n190=true := by decide +kernel
lemma ok189 : chainCheck z189=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check189,edge189⟩,ok190⟩
lemma check188 : nodeCheck n188=true := by decide +kernel
lemma edge188 : edgeCheck n188 n189=true := by decide +kernel
lemma ok188 : chainCheck z188=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check188,edge188⟩,ok189⟩
lemma check187 : nodeCheck n187=true := by decide +kernel
lemma edge187 : edgeCheck n187 n188=true := by decide +kernel
lemma ok187 : chainCheck z187=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check187,edge187⟩,ok188⟩
lemma check186 : nodeCheck n186=true := by decide +kernel
lemma edge186 : edgeCheck n186 n187=true := by decide +kernel
lemma ok186 : chainCheck z186=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check186,edge186⟩,ok187⟩
lemma check185 : nodeCheck n185=true := by decide +kernel
lemma edge185 : edgeCheck n185 n186=true := by decide +kernel
lemma ok185 : chainCheck z185=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check185,edge185⟩,ok186⟩
lemma check184 : nodeCheck n184=true := by decide +kernel
lemma edge184 : edgeCheck n184 n185=true := by decide +kernel
lemma ok184 : chainCheck z184=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check184,edge184⟩,ok185⟩
lemma check183 : nodeCheck n183=true := by decide +kernel
lemma edge183 : edgeCheck n183 n184=true := by decide +kernel
lemma ok183 : chainCheck z183=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check183,edge183⟩,ok184⟩
lemma check182 : nodeCheck n182=true := by decide +kernel
lemma edge182 : edgeCheck n182 n183=true := by decide +kernel
lemma ok182 : chainCheck z182=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check182,edge182⟩,ok183⟩
lemma check181 : nodeCheck n181=true := by decide +kernel
lemma edge181 : edgeCheck n181 n182=true := by decide +kernel
lemma ok181 : chainCheck z181=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check181,edge181⟩,ok182⟩
lemma check180 : nodeCheck n180=true := by decide +kernel
lemma edge180 : edgeCheck n180 n181=true := by decide +kernel
lemma ok180 : chainCheck z180=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check180,edge180⟩,ok181⟩
lemma check179 : nodeCheck n179=true := by decide +kernel
lemma edge179 : edgeCheck n179 n180=true := by decide +kernel
lemma ok179 : chainCheck z179=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check179,edge179⟩,ok180⟩
lemma check178 : nodeCheck n178=true := by decide +kernel
lemma edge178 : edgeCheck n178 n179=true := by decide +kernel
lemma ok178 : chainCheck z178=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check178,edge178⟩,ok179⟩
lemma check177 : nodeCheck n177=true := by decide +kernel
lemma edge177 : edgeCheck n177 n178=true := by decide +kernel
lemma ok177 : chainCheck z177=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check177,edge177⟩,ok178⟩
lemma check176 : nodeCheck n176=true := by decide +kernel
lemma edge176 : edgeCheck n176 n177=true := by decide +kernel
lemma ok176 : chainCheck z176=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check176,edge176⟩,ok177⟩
lemma check175 : nodeCheck n175=true := by decide +kernel
lemma edge175 : edgeCheck n175 n176=true := by decide +kernel
lemma ok175 : chainCheck z175=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check175,edge175⟩,ok176⟩
lemma check174 : nodeCheck n174=true := by decide +kernel
lemma edge174 : edgeCheck n174 n175=true := by decide +kernel
lemma ok174 : chainCheck z174=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check174,edge174⟩,ok175⟩
lemma check173 : nodeCheck n173=true := by decide +kernel
lemma edge173 : edgeCheck n173 n174=true := by decide +kernel
lemma ok173 : chainCheck z173=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check173,edge173⟩,ok174⟩
lemma check172 : nodeCheck n172=true := by decide +kernel
lemma edge172 : edgeCheck n172 n173=true := by decide +kernel
lemma ok172 : chainCheck z172=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check172,edge172⟩,ok173⟩
lemma check171 : nodeCheck n171=true := by decide +kernel
lemma edge171 : edgeCheck n171 n172=true := by decide +kernel
lemma ok171 : chainCheck z171=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check171,edge171⟩,ok172⟩
lemma check170 : nodeCheck n170=true := by decide +kernel
lemma edge170 : edgeCheck n170 n171=true := by decide +kernel
lemma ok170 : chainCheck z170=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check170,edge170⟩,ok171⟩
lemma check169 : nodeCheck n169=true := by decide +kernel
lemma edge169 : edgeCheck n169 n170=true := by decide +kernel
lemma ok169 : chainCheck z169=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check169,edge169⟩,ok170⟩
lemma check168 : nodeCheck n168=true := by decide +kernel
lemma edge168 : edgeCheck n168 n169=true := by decide +kernel
lemma ok168 : chainCheck z168=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check168,edge168⟩,ok169⟩
lemma check167 : nodeCheck n167=true := by decide +kernel
lemma edge167 : edgeCheck n167 n168=true := by decide +kernel
lemma ok167 : chainCheck z167=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check167,edge167⟩,ok168⟩
lemma check166 : nodeCheck n166=true := by decide +kernel
lemma edge166 : edgeCheck n166 n167=true := by decide +kernel
lemma ok166 : chainCheck z166=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check166,edge166⟩,ok167⟩
lemma check165 : nodeCheck n165=true := by decide +kernel
lemma edge165 : edgeCheck n165 n166=true := by decide +kernel
lemma ok165 : chainCheck z165=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check165,edge165⟩,ok166⟩
lemma check164 : nodeCheck n164=true := by decide +kernel
lemma edge164 : edgeCheck n164 n165=true := by decide +kernel
lemma ok164 : chainCheck z164=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check164,edge164⟩,ok165⟩
lemma check163 : nodeCheck n163=true := by decide +kernel
lemma edge163 : edgeCheck n163 n164=true := by decide +kernel
lemma ok163 : chainCheck z163=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check163,edge163⟩,ok164⟩
lemma check162 : nodeCheck n162=true := by decide +kernel
lemma edge162 : edgeCheck n162 n163=true := by decide +kernel
lemma ok162 : chainCheck z162=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check162,edge162⟩,ok163⟩
lemma check161 : nodeCheck n161=true := by decide +kernel
lemma edge161 : edgeCheck n161 n162=true := by decide +kernel
lemma ok161 : chainCheck z161=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check161,edge161⟩,ok162⟩
lemma check160 : nodeCheck n160=true := by decide +kernel
lemma edge160 : edgeCheck n160 n161=true := by decide +kernel
lemma ok160 : chainCheck z160=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check160,edge160⟩,ok161⟩
lemma check159 : nodeCheck n159=true := by decide +kernel
lemma edge159 : edgeCheck n159 n160=true := by decide +kernel
lemma ok159 : chainCheck z159=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check159,edge159⟩,ok160⟩
lemma check158 : nodeCheck n158=true := by decide +kernel
lemma edge158 : edgeCheck n158 n159=true := by decide +kernel
lemma ok158 : chainCheck z158=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check158,edge158⟩,ok159⟩
lemma check157 : nodeCheck n157=true := by decide +kernel
lemma edge157 : edgeCheck n157 n158=true := by decide +kernel
lemma ok157 : chainCheck z157=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check157,edge157⟩,ok158⟩
lemma check156 : nodeCheck n156=true := by decide +kernel
lemma edge156 : edgeCheck n156 n157=true := by decide +kernel
lemma ok156 : chainCheck z156=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check156,edge156⟩,ok157⟩
lemma check155 : nodeCheck n155=true := by decide +kernel
lemma edge155 : edgeCheck n155 n156=true := by decide +kernel
lemma ok155 : chainCheck z155=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check155,edge155⟩,ok156⟩
lemma check154 : nodeCheck n154=true := by decide +kernel
lemma edge154 : edgeCheck n154 n155=true := by decide +kernel
lemma ok154 : chainCheck z154=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check154,edge154⟩,ok155⟩
lemma check153 : nodeCheck n153=true := by decide +kernel
lemma edge153 : edgeCheck n153 n154=true := by decide +kernel
lemma ok153 : chainCheck z153=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check153,edge153⟩,ok154⟩
lemma check152 : nodeCheck n152=true := by decide +kernel
lemma edge152 : edgeCheck n152 n153=true := by decide +kernel
lemma ok152 : chainCheck z152=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check152,edge152⟩,ok153⟩
lemma check151 : nodeCheck n151=true := by decide +kernel
lemma edge151 : edgeCheck n151 n152=true := by decide +kernel
lemma ok151 : chainCheck z151=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check151,edge151⟩,ok152⟩
lemma check150 : nodeCheck n150=true := by decide +kernel
lemma edge150 : edgeCheck n150 n151=true := by decide +kernel
lemma ok150 : chainCheck z150=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check150,edge150⟩,ok151⟩
lemma check149 : nodeCheck n149=true := by decide +kernel
lemma edge149 : edgeCheck n149 n150=true := by decide +kernel
lemma ok149 : chainCheck z149=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check149,edge149⟩,ok150⟩
lemma check148 : nodeCheck n148=true := by decide +kernel
lemma edge148 : edgeCheck n148 n149=true := by decide +kernel
lemma ok148 : chainCheck z148=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check148,edge148⟩,ok149⟩
lemma check147 : nodeCheck n147=true := by decide +kernel
lemma edge147 : edgeCheck n147 n148=true := by decide +kernel
lemma ok147 : chainCheck z147=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check147,edge147⟩,ok148⟩
lemma check146 : nodeCheck n146=true := by decide +kernel
lemma edge146 : edgeCheck n146 n147=true := by decide +kernel
lemma ok146 : chainCheck z146=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check146,edge146⟩,ok147⟩
lemma check145 : nodeCheck n145=true := by decide +kernel
lemma edge145 : edgeCheck n145 n146=true := by decide +kernel
lemma ok145 : chainCheck z145=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check145,edge145⟩,ok146⟩
lemma check144 : nodeCheck n144=true := by decide +kernel
lemma edge144 : edgeCheck n144 n145=true := by decide +kernel
lemma ok144 : chainCheck z144=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check144,edge144⟩,ok145⟩
lemma check143 : nodeCheck n143=true := by decide +kernel
lemma edge143 : edgeCheck n143 n144=true := by decide +kernel
lemma ok143 : chainCheck z143=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check143,edge143⟩,ok144⟩
lemma check142 : nodeCheck n142=true := by decide +kernel
lemma edge142 : edgeCheck n142 n143=true := by decide +kernel
lemma ok142 : chainCheck z142=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check142,edge142⟩,ok143⟩
lemma check141 : nodeCheck n141=true := by decide +kernel
lemma edge141 : edgeCheck n141 n142=true := by decide +kernel
lemma ok141 : chainCheck z141=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check141,edge141⟩,ok142⟩
lemma check140 : nodeCheck n140=true := by decide +kernel
lemma edge140 : edgeCheck n140 n141=true := by decide +kernel
lemma ok140 : chainCheck z140=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check140,edge140⟩,ok141⟩
lemma check139 : nodeCheck n139=true := by decide +kernel
lemma edge139 : edgeCheck n139 n140=true := by decide +kernel
lemma ok139 : chainCheck z139=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check139,edge139⟩,ok140⟩
lemma check138 : nodeCheck n138=true := by decide +kernel
lemma edge138 : edgeCheck n138 n139=true := by decide +kernel
lemma ok138 : chainCheck z138=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check138,edge138⟩,ok139⟩
lemma check137 : nodeCheck n137=true := by decide +kernel
lemma edge137 : edgeCheck n137 n138=true := by decide +kernel
lemma ok137 : chainCheck z137=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check137,edge137⟩,ok138⟩
lemma check136 : nodeCheck n136=true := by decide +kernel
lemma edge136 : edgeCheck n136 n137=true := by decide +kernel
lemma ok136 : chainCheck z136=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check136,edge136⟩,ok137⟩
lemma check135 : nodeCheck n135=true := by decide +kernel
lemma edge135 : edgeCheck n135 n136=true := by decide +kernel
lemma ok135 : chainCheck z135=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check135,edge135⟩,ok136⟩
lemma check134 : nodeCheck n134=true := by decide +kernel
lemma edge134 : edgeCheck n134 n135=true := by decide +kernel
lemma ok134 : chainCheck z134=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check134,edge134⟩,ok135⟩
lemma check133 : nodeCheck n133=true := by decide +kernel
lemma edge133 : edgeCheck n133 n134=true := by decide +kernel
lemma ok133 : chainCheck z133=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check133,edge133⟩,ok134⟩
lemma check132 : nodeCheck n132=true := by decide +kernel
lemma edge132 : edgeCheck n132 n133=true := by decide +kernel
lemma ok132 : chainCheck z132=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check132,edge132⟩,ok133⟩
lemma check131 : nodeCheck n131=true := by decide +kernel
lemma edge131 : edgeCheck n131 n132=true := by decide +kernel
lemma ok131 : chainCheck z131=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check131,edge131⟩,ok132⟩
lemma check130 : nodeCheck n130=true := by decide +kernel
lemma edge130 : edgeCheck n130 n131=true := by decide +kernel
lemma ok130 : chainCheck z130=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check130,edge130⟩,ok131⟩
lemma check129 : nodeCheck n129=true := by decide +kernel
lemma edge129 : edgeCheck n129 n130=true := by decide +kernel
lemma ok129 : chainCheck z129=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check129,edge129⟩,ok130⟩
lemma check128 : nodeCheck n128=true := by decide +kernel
lemma edge128 : edgeCheck n128 n129=true := by decide +kernel
lemma ok128 : chainCheck z128=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check128,edge128⟩,ok129⟩
lemma check127 : nodeCheck n127=true := by decide +kernel
lemma edge127 : edgeCheck n127 n128=true := by decide +kernel
lemma ok127 : chainCheck z127=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check127,edge127⟩,ok128⟩
lemma check126 : nodeCheck n126=true := by decide +kernel
lemma edge126 : edgeCheck n126 n127=true := by decide +kernel
lemma ok126 : chainCheck z126=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check126,edge126⟩,ok127⟩
lemma check125 : nodeCheck n125=true := by decide +kernel
lemma edge125 : edgeCheck n125 n126=true := by decide +kernel
lemma ok125 : chainCheck z125=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check125,edge125⟩,ok126⟩
lemma check124 : nodeCheck n124=true := by decide +kernel
lemma edge124 : edgeCheck n124 n125=true := by decide +kernel
lemma ok124 : chainCheck z124=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check124,edge124⟩,ok125⟩
lemma check123 : nodeCheck n123=true := by decide +kernel
lemma edge123 : edgeCheck n123 n124=true := by decide +kernel
lemma ok123 : chainCheck z123=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check123,edge123⟩,ok124⟩
lemma check122 : nodeCheck n122=true := by decide +kernel
lemma edge122 : edgeCheck n122 n123=true := by decide +kernel
lemma ok122 : chainCheck z122=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check122,edge122⟩,ok123⟩
lemma check121 : nodeCheck n121=true := by decide +kernel
lemma edge121 : edgeCheck n121 n122=true := by decide +kernel
lemma ok121 : chainCheck z121=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check121,edge121⟩,ok122⟩
lemma check120 : nodeCheck n120=true := by decide +kernel
lemma edge120 : edgeCheck n120 n121=true := by decide +kernel
lemma ok120 : chainCheck z120=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check120,edge120⟩,ok121⟩
lemma check119 : nodeCheck n119=true := by decide +kernel
lemma edge119 : edgeCheck n119 n120=true := by decide +kernel
lemma ok119 : chainCheck z119=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check119,edge119⟩,ok120⟩
lemma check118 : nodeCheck n118=true := by decide +kernel
lemma edge118 : edgeCheck n118 n119=true := by decide +kernel
lemma ok118 : chainCheck z118=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check118,edge118⟩,ok119⟩
lemma check117 : nodeCheck n117=true := by decide +kernel
lemma edge117 : edgeCheck n117 n118=true := by decide +kernel
lemma ok117 : chainCheck z117=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check117,edge117⟩,ok118⟩
lemma check116 : nodeCheck n116=true := by decide +kernel
lemma edge116 : edgeCheck n116 n117=true := by decide +kernel
lemma ok116 : chainCheck z116=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check116,edge116⟩,ok117⟩
lemma check115 : nodeCheck n115=true := by decide +kernel
lemma edge115 : edgeCheck n115 n116=true := by decide +kernel
lemma ok115 : chainCheck z115=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check115,edge115⟩,ok116⟩
lemma check114 : nodeCheck n114=true := by decide +kernel
lemma edge114 : edgeCheck n114 n115=true := by decide +kernel
lemma ok114 : chainCheck z114=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check114,edge114⟩,ok115⟩
lemma check113 : nodeCheck n113=true := by decide +kernel
lemma edge113 : edgeCheck n113 n114=true := by decide +kernel
lemma ok113 : chainCheck z113=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check113,edge113⟩,ok114⟩
lemma check112 : nodeCheck n112=true := by decide +kernel
lemma edge112 : edgeCheck n112 n113=true := by decide +kernel
lemma ok112 : chainCheck z112=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check112,edge112⟩,ok113⟩
lemma check111 : nodeCheck n111=true := by decide +kernel
lemma edge111 : edgeCheck n111 n112=true := by decide +kernel
lemma ok111 : chainCheck z111=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check111,edge111⟩,ok112⟩
lemma check110 : nodeCheck n110=true := by decide +kernel
lemma edge110 : edgeCheck n110 n111=true := by decide +kernel
lemma ok110 : chainCheck z110=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check110,edge110⟩,ok111⟩
lemma check109 : nodeCheck n109=true := by decide +kernel
lemma edge109 : edgeCheck n109 n110=true := by decide +kernel
lemma ok109 : chainCheck z109=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check109,edge109⟩,ok110⟩
lemma check108 : nodeCheck n108=true := by decide +kernel
lemma edge108 : edgeCheck n108 n109=true := by decide +kernel
lemma ok108 : chainCheck z108=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check108,edge108⟩,ok109⟩
lemma check107 : nodeCheck n107=true := by decide +kernel
lemma edge107 : edgeCheck n107 n108=true := by decide +kernel
lemma ok107 : chainCheck z107=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check107,edge107⟩,ok108⟩
lemma check106 : nodeCheck n106=true := by decide +kernel
lemma edge106 : edgeCheck n106 n107=true := by decide +kernel
lemma ok106 : chainCheck z106=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check106,edge106⟩,ok107⟩
lemma check105 : nodeCheck n105=true := by decide +kernel
lemma edge105 : edgeCheck n105 n106=true := by decide +kernel
lemma ok105 : chainCheck z105=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check105,edge105⟩,ok106⟩
lemma check104 : nodeCheck n104=true := by decide +kernel
lemma edge104 : edgeCheck n104 n105=true := by decide +kernel
lemma ok104 : chainCheck z104=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check104,edge104⟩,ok105⟩
lemma check103 : nodeCheck n103=true := by decide +kernel
lemma edge103 : edgeCheck n103 n104=true := by decide +kernel
lemma ok103 : chainCheck z103=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check103,edge103⟩,ok104⟩
lemma check102 : nodeCheck n102=true := by decide +kernel
lemma edge102 : edgeCheck n102 n103=true := by decide +kernel
lemma ok102 : chainCheck z102=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check102,edge102⟩,ok103⟩
lemma check101 : nodeCheck n101=true := by decide +kernel
lemma edge101 : edgeCheck n101 n102=true := by decide +kernel
lemma ok101 : chainCheck z101=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check101,edge101⟩,ok102⟩
lemma check100 : nodeCheck n100=true := by decide +kernel
lemma edge100 : edgeCheck n100 n101=true := by decide +kernel
lemma ok100 : chainCheck z100=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check100,edge100⟩,ok101⟩
lemma check99 : nodeCheck n99=true := by decide +kernel
lemma edge99 : edgeCheck n99 n100=true := by decide +kernel
lemma ok99 : chainCheck z99=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check99,edge99⟩,ok100⟩
lemma check98 : nodeCheck n98=true := by decide +kernel
lemma edge98 : edgeCheck n98 n99=true := by decide +kernel
lemma ok98 : chainCheck z98=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check98,edge98⟩,ok99⟩
lemma check97 : nodeCheck n97=true := by decide +kernel
lemma edge97 : edgeCheck n97 n98=true := by decide +kernel
lemma ok97 : chainCheck z97=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check97,edge97⟩,ok98⟩
lemma check96 : nodeCheck n96=true := by decide +kernel
lemma edge96 : edgeCheck n96 n97=true := by decide +kernel
lemma ok96 : chainCheck z96=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check96,edge96⟩,ok97⟩
lemma check95 : nodeCheck n95=true := by decide +kernel
lemma edge95 : edgeCheck n95 n96=true := by decide +kernel
lemma ok95 : chainCheck z95=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check95,edge95⟩,ok96⟩
lemma check94 : nodeCheck n94=true := by decide +kernel
lemma edge94 : edgeCheck n94 n95=true := by decide +kernel
lemma ok94 : chainCheck z94=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check94,edge94⟩,ok95⟩
lemma check93 : nodeCheck n93=true := by decide +kernel
lemma edge93 : edgeCheck n93 n94=true := by decide +kernel
lemma ok93 : chainCheck z93=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check93,edge93⟩,ok94⟩
lemma check92 : nodeCheck n92=true := by decide +kernel
lemma edge92 : edgeCheck n92 n93=true := by decide +kernel
lemma ok92 : chainCheck z92=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check92,edge92⟩,ok93⟩
lemma check91 : nodeCheck n91=true := by decide +kernel
lemma edge91 : edgeCheck n91 n92=true := by decide +kernel
lemma ok91 : chainCheck z91=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check91,edge91⟩,ok92⟩
lemma check90 : nodeCheck n90=true := by decide +kernel
lemma edge90 : edgeCheck n90 n91=true := by decide +kernel
lemma ok90 : chainCheck z90=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check90,edge90⟩,ok91⟩
lemma check89 : nodeCheck n89=true := by decide +kernel
lemma edge89 : edgeCheck n89 n90=true := by decide +kernel
lemma ok89 : chainCheck z89=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check89,edge89⟩,ok90⟩
lemma check88 : nodeCheck n88=true := by decide +kernel
lemma edge88 : edgeCheck n88 n89=true := by decide +kernel
lemma ok88 : chainCheck z88=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check88,edge88⟩,ok89⟩
lemma check87 : nodeCheck n87=true := by decide +kernel
lemma edge87 : edgeCheck n87 n88=true := by decide +kernel
lemma ok87 : chainCheck z87=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check87,edge87⟩,ok88⟩
lemma check86 : nodeCheck n86=true := by decide +kernel
lemma edge86 : edgeCheck n86 n87=true := by decide +kernel
lemma ok86 : chainCheck z86=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check86,edge86⟩,ok87⟩
lemma check85 : nodeCheck n85=true := by decide +kernel
lemma edge85 : edgeCheck n85 n86=true := by decide +kernel
lemma ok85 : chainCheck z85=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check85,edge85⟩,ok86⟩
lemma check84 : nodeCheck n84=true := by decide +kernel
lemma edge84 : edgeCheck n84 n85=true := by decide +kernel
lemma ok84 : chainCheck z84=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check84,edge84⟩,ok85⟩
lemma check83 : nodeCheck n83=true := by decide +kernel
lemma edge83 : edgeCheck n83 n84=true := by decide +kernel
lemma ok83 : chainCheck z83=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check83,edge83⟩,ok84⟩
lemma check82 : nodeCheck n82=true := by decide +kernel
lemma edge82 : edgeCheck n82 n83=true := by decide +kernel
lemma ok82 : chainCheck z82=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check82,edge82⟩,ok83⟩
lemma check81 : nodeCheck n81=true := by decide +kernel
lemma edge81 : edgeCheck n81 n82=true := by decide +kernel
lemma ok81 : chainCheck z81=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check81,edge81⟩,ok82⟩
lemma check80 : nodeCheck n80=true := by decide +kernel
lemma edge80 : edgeCheck n80 n81=true := by decide +kernel
lemma ok80 : chainCheck z80=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check80,edge80⟩,ok81⟩
lemma check79 : nodeCheck n79=true := by decide +kernel
lemma edge79 : edgeCheck n79 n80=true := by decide +kernel
lemma ok79 : chainCheck z79=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check79,edge79⟩,ok80⟩
lemma check78 : nodeCheck n78=true := by decide +kernel
lemma edge78 : edgeCheck n78 n79=true := by decide +kernel
lemma ok78 : chainCheck z78=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check78,edge78⟩,ok79⟩
lemma check77 : nodeCheck n77=true := by decide +kernel
lemma edge77 : edgeCheck n77 n78=true := by decide +kernel
lemma ok77 : chainCheck z77=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check77,edge77⟩,ok78⟩
lemma check76 : nodeCheck n76=true := by decide +kernel
lemma edge76 : edgeCheck n76 n77=true := by decide +kernel
lemma ok76 : chainCheck z76=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check76,edge76⟩,ok77⟩
lemma check75 : nodeCheck n75=true := by decide +kernel
lemma edge75 : edgeCheck n75 n76=true := by decide +kernel
lemma ok75 : chainCheck z75=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check75,edge75⟩,ok76⟩
lemma check74 : nodeCheck n74=true := by decide +kernel
lemma edge74 : edgeCheck n74 n75=true := by decide +kernel
lemma ok74 : chainCheck z74=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check74,edge74⟩,ok75⟩
lemma check73 : nodeCheck n73=true := by decide +kernel
lemma edge73 : edgeCheck n73 n74=true := by decide +kernel
lemma ok73 : chainCheck z73=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check73,edge73⟩,ok74⟩
lemma check72 : nodeCheck n72=true := by decide +kernel
lemma edge72 : edgeCheck n72 n73=true := by decide +kernel
lemma ok72 : chainCheck z72=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check72,edge72⟩,ok73⟩
lemma check71 : nodeCheck n71=true := by decide +kernel
lemma edge71 : edgeCheck n71 n72=true := by decide +kernel
lemma ok71 : chainCheck z71=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check71,edge71⟩,ok72⟩
lemma check70 : nodeCheck n70=true := by decide +kernel
lemma edge70 : edgeCheck n70 n71=true := by decide +kernel
lemma ok70 : chainCheck z70=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check70,edge70⟩,ok71⟩
lemma check69 : nodeCheck n69=true := by decide +kernel
lemma edge69 : edgeCheck n69 n70=true := by decide +kernel
lemma ok69 : chainCheck z69=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check69,edge69⟩,ok70⟩
lemma check68 : nodeCheck n68=true := by decide +kernel
lemma edge68 : edgeCheck n68 n69=true := by decide +kernel
lemma ok68 : chainCheck z68=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check68,edge68⟩,ok69⟩
lemma check67 : nodeCheck n67=true := by decide +kernel
lemma edge67 : edgeCheck n67 n68=true := by decide +kernel
lemma ok67 : chainCheck z67=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check67,edge67⟩,ok68⟩
lemma check66 : nodeCheck n66=true := by decide +kernel
lemma edge66 : edgeCheck n66 n67=true := by decide +kernel
lemma ok66 : chainCheck z66=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check66,edge66⟩,ok67⟩
lemma check65 : nodeCheck n65=true := by decide +kernel
lemma edge65 : edgeCheck n65 n66=true := by decide +kernel
lemma ok65 : chainCheck z65=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check65,edge65⟩,ok66⟩
lemma check64 : nodeCheck n64=true := by decide +kernel
lemma edge64 : edgeCheck n64 n65=true := by decide +kernel
lemma ok64 : chainCheck z64=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check64,edge64⟩,ok65⟩
lemma check63 : nodeCheck n63=true := by decide +kernel
lemma edge63 : edgeCheck n63 n64=true := by decide +kernel
lemma ok63 : chainCheck z63=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check63,edge63⟩,ok64⟩
lemma check62 : nodeCheck n62=true := by decide +kernel
lemma edge62 : edgeCheck n62 n63=true := by decide +kernel
lemma ok62 : chainCheck z62=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check62,edge62⟩,ok63⟩
lemma check61 : nodeCheck n61=true := by decide +kernel
lemma edge61 : edgeCheck n61 n62=true := by decide +kernel
lemma ok61 : chainCheck z61=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check61,edge61⟩,ok62⟩
lemma check60 : nodeCheck n60=true := by decide +kernel
lemma edge60 : edgeCheck n60 n61=true := by decide +kernel
lemma ok60 : chainCheck z60=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check60,edge60⟩,ok61⟩
lemma check59 : nodeCheck n59=true := by decide +kernel
lemma edge59 : edgeCheck n59 n60=true := by decide +kernel
lemma ok59 : chainCheck z59=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check59,edge59⟩,ok60⟩
lemma check58 : nodeCheck n58=true := by decide +kernel
lemma edge58 : edgeCheck n58 n59=true := by decide +kernel
lemma ok58 : chainCheck z58=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check58,edge58⟩,ok59⟩
lemma check57 : nodeCheck n57=true := by decide +kernel
lemma edge57 : edgeCheck n57 n58=true := by decide +kernel
lemma ok57 : chainCheck z57=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check57,edge57⟩,ok58⟩
lemma check56 : nodeCheck n56=true := by decide +kernel
lemma edge56 : edgeCheck n56 n57=true := by decide +kernel
lemma ok56 : chainCheck z56=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check56,edge56⟩,ok57⟩
lemma check55 : nodeCheck n55=true := by decide +kernel
lemma edge55 : edgeCheck n55 n56=true := by decide +kernel
lemma ok55 : chainCheck z55=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check55,edge55⟩,ok56⟩
lemma check54 : nodeCheck n54=true := by decide +kernel
lemma edge54 : edgeCheck n54 n55=true := by decide +kernel
lemma ok54 : chainCheck z54=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check54,edge54⟩,ok55⟩
lemma check53 : nodeCheck n53=true := by decide +kernel
lemma edge53 : edgeCheck n53 n54=true := by decide +kernel
lemma ok53 : chainCheck z53=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check53,edge53⟩,ok54⟩
lemma check52 : nodeCheck n52=true := by decide +kernel
lemma edge52 : edgeCheck n52 n53=true := by decide +kernel
lemma ok52 : chainCheck z52=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check52,edge52⟩,ok53⟩
lemma check51 : nodeCheck n51=true := by decide +kernel
lemma edge51 : edgeCheck n51 n52=true := by decide +kernel
lemma ok51 : chainCheck z51=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check51,edge51⟩,ok52⟩
lemma check50 : nodeCheck n50=true := by decide +kernel
lemma edge50 : edgeCheck n50 n51=true := by decide +kernel
lemma ok50 : chainCheck z50=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check50,edge50⟩,ok51⟩
lemma check49 : nodeCheck n49=true := by decide +kernel
lemma edge49 : edgeCheck n49 n50=true := by decide +kernel
lemma ok49 : chainCheck z49=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check49,edge49⟩,ok50⟩
lemma check48 : nodeCheck n48=true := by decide +kernel
lemma edge48 : edgeCheck n48 n49=true := by decide +kernel
lemma ok48 : chainCheck z48=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check48,edge48⟩,ok49⟩
lemma check47 : nodeCheck n47=true := by decide +kernel
lemma edge47 : edgeCheck n47 n48=true := by decide +kernel
lemma ok47 : chainCheck z47=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check47,edge47⟩,ok48⟩
lemma check46 : nodeCheck n46=true := by decide +kernel
lemma edge46 : edgeCheck n46 n47=true := by decide +kernel
lemma ok46 : chainCheck z46=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check46,edge46⟩,ok47⟩
lemma check45 : nodeCheck n45=true := by decide +kernel
lemma edge45 : edgeCheck n45 n46=true := by decide +kernel
lemma ok45 : chainCheck z45=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check45,edge45⟩,ok46⟩
lemma check44 : nodeCheck n44=true := by decide +kernel
lemma edge44 : edgeCheck n44 n45=true := by decide +kernel
lemma ok44 : chainCheck z44=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check44,edge44⟩,ok45⟩
lemma check43 : nodeCheck n43=true := by decide +kernel
lemma edge43 : edgeCheck n43 n44=true := by decide +kernel
lemma ok43 : chainCheck z43=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check43,edge43⟩,ok44⟩
lemma check42 : nodeCheck n42=true := by decide +kernel
lemma edge42 : edgeCheck n42 n43=true := by decide +kernel
lemma ok42 : chainCheck z42=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check42,edge42⟩,ok43⟩
lemma check41 : nodeCheck n41=true := by decide +kernel
lemma edge41 : edgeCheck n41 n42=true := by decide +kernel
lemma ok41 : chainCheck z41=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check41,edge41⟩,ok42⟩
lemma check40 : nodeCheck n40=true := by decide +kernel
lemma edge40 : edgeCheck n40 n41=true := by decide +kernel
lemma ok40 : chainCheck z40=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check40,edge40⟩,ok41⟩
lemma check39 : nodeCheck n39=true := by decide +kernel
lemma edge39 : edgeCheck n39 n40=true := by decide +kernel
lemma ok39 : chainCheck z39=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check39,edge39⟩,ok40⟩
lemma check38 : nodeCheck n38=true := by decide +kernel
lemma edge38 : edgeCheck n38 n39=true := by decide +kernel
lemma ok38 : chainCheck z38=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check38,edge38⟩,ok39⟩
lemma check37 : nodeCheck n37=true := by decide +kernel
lemma edge37 : edgeCheck n37 n38=true := by decide +kernel
lemma ok37 : chainCheck z37=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check37,edge37⟩,ok38⟩
lemma check36 : nodeCheck n36=true := by decide +kernel
lemma edge36 : edgeCheck n36 n37=true := by decide +kernel
lemma ok36 : chainCheck z36=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check36,edge36⟩,ok37⟩
lemma check35 : nodeCheck n35=true := by decide +kernel
lemma edge35 : edgeCheck n35 n36=true := by decide +kernel
lemma ok35 : chainCheck z35=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check35,edge35⟩,ok36⟩
lemma check34 : nodeCheck n34=true := by decide +kernel
lemma edge34 : edgeCheck n34 n35=true := by decide +kernel
lemma ok34 : chainCheck z34=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check34,edge34⟩,ok35⟩
lemma check33 : nodeCheck n33=true := by decide +kernel
lemma edge33 : edgeCheck n33 n34=true := by decide +kernel
lemma ok33 : chainCheck z33=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check33,edge33⟩,ok34⟩
lemma check32 : nodeCheck n32=true := by decide +kernel
lemma edge32 : edgeCheck n32 n33=true := by decide +kernel
lemma ok32 : chainCheck z32=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check32,edge32⟩,ok33⟩
lemma check31 : nodeCheck n31=true := by decide +kernel
lemma edge31 : edgeCheck n31 n32=true := by decide +kernel
lemma ok31 : chainCheck z31=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check31,edge31⟩,ok32⟩
lemma check30 : nodeCheck n30=true := by decide +kernel
lemma edge30 : edgeCheck n30 n31=true := by decide +kernel
lemma ok30 : chainCheck z30=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check30,edge30⟩,ok31⟩
lemma check29 : nodeCheck n29=true := by decide +kernel
lemma edge29 : edgeCheck n29 n30=true := by decide +kernel
lemma ok29 : chainCheck z29=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check29,edge29⟩,ok30⟩
lemma check28 : nodeCheck n28=true := by decide +kernel
lemma edge28 : edgeCheck n28 n29=true := by decide +kernel
lemma ok28 : chainCheck z28=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check28,edge28⟩,ok29⟩
lemma check27 : nodeCheck n27=true := by decide +kernel
lemma edge27 : edgeCheck n27 n28=true := by decide +kernel
lemma ok27 : chainCheck z27=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check27,edge27⟩,ok28⟩
lemma check26 : nodeCheck n26=true := by decide +kernel
lemma edge26 : edgeCheck n26 n27=true := by decide +kernel
lemma ok26 : chainCheck z26=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check26,edge26⟩,ok27⟩
lemma check25 : nodeCheck n25=true := by decide +kernel
lemma edge25 : edgeCheck n25 n26=true := by decide +kernel
lemma ok25 : chainCheck z25=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check25,edge25⟩,ok26⟩
lemma check24 : nodeCheck n24=true := by decide +kernel
lemma edge24 : edgeCheck n24 n25=true := by decide +kernel
lemma ok24 : chainCheck z24=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check24,edge24⟩,ok25⟩
lemma check23 : nodeCheck n23=true := by decide +kernel
lemma edge23 : edgeCheck n23 n24=true := by decide +kernel
lemma ok23 : chainCheck z23=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check23,edge23⟩,ok24⟩
lemma check22 : nodeCheck n22=true := by decide +kernel
lemma edge22 : edgeCheck n22 n23=true := by decide +kernel
lemma ok22 : chainCheck z22=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check22,edge22⟩,ok23⟩
lemma check21 : nodeCheck n21=true := by decide +kernel
lemma edge21 : edgeCheck n21 n22=true := by decide +kernel
lemma ok21 : chainCheck z21=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check21,edge21⟩,ok22⟩
lemma check20 : nodeCheck n20=true := by decide +kernel
lemma edge20 : edgeCheck n20 n21=true := by decide +kernel
lemma ok20 : chainCheck z20=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check20,edge20⟩,ok21⟩
lemma check19 : nodeCheck n19=true := by decide +kernel
lemma edge19 : edgeCheck n19 n20=true := by decide +kernel
lemma ok19 : chainCheck z19=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check19,edge19⟩,ok20⟩
lemma check18 : nodeCheck n18=true := by decide +kernel
lemma edge18 : edgeCheck n18 n19=true := by decide +kernel
lemma ok18 : chainCheck z18=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check18,edge18⟩,ok19⟩
lemma check17 : nodeCheck n17=true := by decide +kernel
lemma edge17 : edgeCheck n17 n18=true := by decide +kernel
lemma ok17 : chainCheck z17=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check17,edge17⟩,ok18⟩
lemma check16 : nodeCheck n16=true := by decide +kernel
lemma edge16 : edgeCheck n16 n17=true := by decide +kernel
lemma ok16 : chainCheck z16=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check16,edge16⟩,ok17⟩
lemma check15 : nodeCheck n15=true := by decide +kernel
lemma edge15 : edgeCheck n15 n16=true := by decide +kernel
lemma ok15 : chainCheck z15=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check15,edge15⟩,ok16⟩
lemma check14 : nodeCheck n14=true := by decide +kernel
lemma edge14 : edgeCheck n14 n15=true := by decide +kernel
lemma ok14 : chainCheck z14=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check14,edge14⟩,ok15⟩
lemma check13 : nodeCheck n13=true := by decide +kernel
lemma edge13 : edgeCheck n13 n14=true := by decide +kernel
lemma ok13 : chainCheck z13=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check13,edge13⟩,ok14⟩
lemma check12 : nodeCheck n12=true := by decide +kernel
lemma edge12 : edgeCheck n12 n13=true := by decide +kernel
lemma ok12 : chainCheck z12=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check12,edge12⟩,ok13⟩
lemma check11 : nodeCheck n11=true := by decide +kernel
lemma edge11 : edgeCheck n11 n12=true := by decide +kernel
lemma ok11 : chainCheck z11=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check11,edge11⟩,ok12⟩
lemma check10 : nodeCheck n10=true := by decide +kernel
lemma edge10 : edgeCheck n10 n11=true := by decide +kernel
lemma ok10 : chainCheck z10=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check10,edge10⟩,ok11⟩
lemma check9 : nodeCheck n9=true := by decide +kernel
lemma edge9 : edgeCheck n9 n10=true := by decide +kernel
lemma ok9 : chainCheck z9=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check9,edge9⟩,ok10⟩
lemma check8 : nodeCheck n8=true := by decide +kernel
lemma edge8 : edgeCheck n8 n9=true := by decide +kernel
lemma ok8 : chainCheck z8=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check8,edge8⟩,ok9⟩
lemma check7 : nodeCheck n7=true := by decide +kernel
lemma edge7 : edgeCheck n7 n8=true := by decide +kernel
lemma ok7 : chainCheck z7=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check7,edge7⟩,ok8⟩
lemma check6 : nodeCheck n6=true := by decide +kernel
lemma edge6 : edgeCheck n6 n7=true := by decide +kernel
lemma ok6 : chainCheck z6=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check6,edge6⟩,ok7⟩
lemma check5 : nodeCheck n5=true := by decide +kernel
lemma edge5 : edgeCheck n5 n6=true := by decide +kernel
lemma ok5 : chainCheck z5=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check5,edge5⟩,ok6⟩
lemma check4 : nodeCheck n4=true := by decide +kernel
lemma edge4 : edgeCheck n4 n5=true := by decide +kernel
lemma ok4 : chainCheck z4=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check4,edge4⟩,ok5⟩
lemma check3 : nodeCheck n3=true := by decide +kernel
lemma edge3 : edgeCheck n3 n4=true := by decide +kernel
lemma ok3 : chainCheck z3=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check3,edge3⟩,ok4⟩
lemma check2 : nodeCheck n2=true := by decide +kernel
lemma edge2 : edgeCheck n2 n3=true := by decide +kernel
lemma ok2 : chainCheck z2=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check2,edge2⟩,ok3⟩
lemma check1 : nodeCheck n1=true := by decide +kernel
lemma edge1 : edgeCheck n1 n2=true := by decide +kernel
lemma ok1 : chainCheck z1=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check1,edge1⟩,ok2⟩
lemma check0 : nodeCheck n0=true := by decide +kernel
lemma edge0 : edgeCheck n0 n1=true := by decide +kernel
lemma ok0 : chainCheck z0=true := Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨check0,edge0⟩,ok1⟩
def v1 : Band := ⟨1400000,1550000,4707332,6943325,11744051,13002342,8051807,7401429⟩
lemma b1ok : bandCheck v1=true := by decide +kernel
def t1x16 : Tree := .leaf ⟨false,8388608,524288,0,8388608,-8388608,8388608⟩
lemma t1x16ok : treeCheck nodes v1 ⟨0,524288,-8388608,8388608⟩ t1x16=true := by decide +kernel
def t1x34 : Tree := .leaf ⟨false,8372208,786432,0,8388608,-8388608,8388608⟩
lemma t1x34ok : treeCheck nodes v1 ⟨524288,786432,-8388608,8388608⟩ t1x34=true := by decide +kernel
def t1x35 : Tree := .leaf ⟨false,8351663,1048576,0,8388608,-8388608,8388608⟩
lemma t1x35ok : treeCheck nodes v1 ⟨786432,1048576,-8388608,8388608⟩ t1x35=true := by decide +kernel
def t1x17 : Tree := .d (786432) t1x34 t1x35
lemma t1x17ok : treeCheck nodes v1 ⟨524288,1048576,-8388608,8388608⟩ t1x17=true := Bool.and_eq_true_iff.mpr ⟨t1x34ok,t1x35ok⟩
def t1x8 : Tree := .d (524288) t1x16 t1x17
lemma t1x8ok : treeCheck nodes v1 ⟨0,1048576,-8388608,8388608⟩ t1x8=true := Bool.and_eq_true_iff.mpr ⟨t1x16ok,t1x17ok⟩
def t1x72 : Tree := .leaf ⟨false,8322814,1179648,0,8388608,-8388608,8388608⟩
lemma t1x72ok : treeCheck nodes v1 ⟨1048576,1179648,-8388608,8388608⟩ t1x72=true := by decide +kernel
def t1x73 : Tree := .leaf ⟨false,8305250,1310720,0,8388608,-8388608,8388608⟩
lemma t1x73ok : treeCheck nodes v1 ⟨1179648,1310720,-8388608,8388608⟩ t1x73=true := by decide +kernel
def t1x36 : Tree := .d (1179648) t1x72 t1x73
lemma t1x36ok : treeCheck nodes v1 ⟨1048576,1310720,-8388608,8388608⟩ t1x36=true := Bool.and_eq_true_iff.mpr ⟨t1x72ok,t1x73ok⟩
def t1x74 : Tree := .leaf ⟨false,8285576,1441792,0,8388608,-8388608,8388608⟩
lemma t1x74ok : treeCheck nodes v1 ⟨1310720,1441792,-8388608,8388608⟩ t1x74=true := by decide +kernel
def t1x75 : Tree := .leaf ⟨false,8263776,1572864,0,8388608,-8388608,8388608⟩
lemma t1x75ok : treeCheck nodes v1 ⟨1441792,1572864,-8388608,8388608⟩ t1x75=true := by decide +kernel
def t1x37 : Tree := .d (1441792) t1x74 t1x75
lemma t1x37ok : treeCheck nodes v1 ⟨1310720,1572864,-8388608,8388608⟩ t1x37=true := Bool.and_eq_true_iff.mpr ⟨t1x74ok,t1x75ok⟩
def t1x18 : Tree := .d (1310720) t1x36 t1x37
lemma t1x18ok : treeCheck nodes v1 ⟨1048576,1572864,-8388608,8388608⟩ t1x18=true := Bool.and_eq_true_iff.mpr ⟨t1x36ok,t1x37ok⟩
def t1x76 : Tree := .leaf ⟨false,8239833,1703936,0,8388608,-8388608,8388608⟩
lemma t1x76ok : treeCheck nodes v1 ⟨1572864,1703936,-8388608,8388608⟩ t1x76=true := by decide +kernel
def t1x154 : Tree := .leaf ⟨false,8213730,1769472,0,8388608,-8388608,8388608⟩
lemma t1x154ok : treeCheck nodes v1 ⟨1703936,1769472,-8388608,8388608⟩ t1x154=true := by decide +kernel
def t1x155 : Tree := .leaf ⟨false,8199861,1835008,0,8388608,-8388608,8388608⟩
lemma t1x155ok : treeCheck nodes v1 ⟨1769472,1835008,-8388608,8388608⟩ t1x155=true := by decide +kernel
def t1x77 : Tree := .d (1769472) t1x154 t1x155
lemma t1x77ok : treeCheck nodes v1 ⟨1703936,1835008,-8388608,8388608⟩ t1x77=true := Bool.and_eq_true_iff.mpr ⟨t1x154ok,t1x155ok⟩
def t1x38 : Tree := .d (1703936) t1x76 t1x77
lemma t1x38ok : treeCheck nodes v1 ⟨1572864,1835008,-8388608,8388608⟩ t1x38=true := Bool.and_eq_true_iff.mpr ⟨t1x76ok,t1x77ok⟩
def t1x156 : Tree := .leaf ⟨false,8185444,1900544,0,8388608,-8388608,8388608⟩
lemma t1x156ok : treeCheck nodes v1 ⟨1835008,1900544,-8388608,8388608⟩ t1x156=true := by decide +kernel
def t1x157 : Tree := .leaf ⟨false,8170476,1966080,0,8388608,-8388608,8388608⟩
lemma t1x157ok : treeCheck nodes v1 ⟨1900544,1966080,-8388608,8388608⟩ t1x157=true := by decide +kernel
def t1x78 : Tree := .d (1900544) t1x156 t1x157
lemma t1x78ok : treeCheck nodes v1 ⟨1835008,1966080,-8388608,8388608⟩ t1x78=true := Bool.and_eq_true_iff.mpr ⟨t1x156ok,t1x157ok⟩
def t1x158 : Tree := .leaf ⟨false,8154954,2031616,0,8388608,-8388608,8388608⟩
lemma t1x158ok : treeCheck nodes v1 ⟨1966080,2031616,-8388608,8388608⟩ t1x158=true := by decide +kernel
def t1x159 : Tree := .leaf ⟨false,8138875,2097152,0,8388608,-8388608,8388608⟩
lemma t1x159ok : treeCheck nodes v1 ⟨2031616,2097152,-8388608,8388608⟩ t1x159=true := by decide +kernel
def t1x79 : Tree := .d (2031616) t1x158 t1x159
lemma t1x79ok : treeCheck nodes v1 ⟨1966080,2097152,-8388608,8388608⟩ t1x79=true := Bool.and_eq_true_iff.mpr ⟨t1x158ok,t1x159ok⟩
def t1x39 : Tree := .d (1966080) t1x78 t1x79
lemma t1x39ok : treeCheck nodes v1 ⟨1835008,2097152,-8388608,8388608⟩ t1x39=true := Bool.and_eq_true_iff.mpr ⟨t1x78ok,t1x79ok⟩
def t1x19 : Tree := .d (1835008) t1x38 t1x39
lemma t1x19ok : treeCheck nodes v1 ⟨1572864,2097152,-8388608,8388608⟩ t1x19=true := Bool.and_eq_true_iff.mpr ⟨t1x38ok,t1x39ok⟩
def t1x9 : Tree := .d (1572864) t1x18 t1x19
lemma t1x9ok : treeCheck nodes v1 ⟨1048576,2097152,-8388608,8388608⟩ t1x9=true := Bool.and_eq_true_iff.mpr ⟨t1x18ok,t1x19ok⟩
def t1x4 : Tree := .d (1048576) t1x8 t1x9
lemma t1x4ok : treeCheck nodes v1 ⟨0,2097152,-8388608,8388608⟩ t1x4=true := Bool.and_eq_true_iff.mpr ⟨t1x8ok,t1x9ok⟩
def t1x160 : Tree := .leaf ⟨false,8122235,2162688,0,8388608,-8388608,8388608⟩
lemma t1x160ok : treeCheck nodes v1 ⟨2097152,2162688,-8388608,8388608⟩ t1x160=true := by decide +kernel
def t1x161 : Tree := .leaf ⟨false,8105031,2228224,0,8388608,-8388608,8388608⟩
lemma t1x161ok : treeCheck nodes v1 ⟨2162688,2228224,-8388608,8388608⟩ t1x161=true := by decide +kernel
def t1x80 : Tree := .d (2162688) t1x160 t1x161
lemma t1x80ok : treeCheck nodes v1 ⟨2097152,2228224,-8388608,8388608⟩ t1x80=true := Bool.and_eq_true_iff.mpr ⟨t1x160ok,t1x161ok⟩
def t1x162 : Tree := .leaf ⟨false,8087260,2293760,0,8388608,-8388608,8388608⟩
lemma t1x162ok : treeCheck nodes v1 ⟨2228224,2293760,-8388608,8388608⟩ t1x162=true := by decide +kernel
def t1x163 : Tree := .leaf ⟨false,8068917,2359296,0,8388608,-8388608,8388608⟩
lemma t1x163ok : treeCheck nodes v1 ⟨2293760,2359296,-8388608,8388608⟩ t1x163=true := by decide +kernel
def t1x81 : Tree := .d (2293760) t1x162 t1x163
lemma t1x81ok : treeCheck nodes v1 ⟨2228224,2359296,-8388608,8388608⟩ t1x81=true := Bool.and_eq_true_iff.mpr ⟨t1x162ok,t1x163ok⟩
def t1x40 : Tree := .d (2228224) t1x80 t1x81
lemma t1x40ok : treeCheck nodes v1 ⟨2097152,2359296,-8388608,8388608⟩ t1x40=true := Bool.and_eq_true_iff.mpr ⟨t1x80ok,t1x81ok⟩
def t1x164 : Tree := .leaf ⟨false,8049998,2424832,0,8388608,-8388608,8388608⟩
lemma t1x164ok : treeCheck nodes v1 ⟨2359296,2424832,-8388608,8388608⟩ t1x164=true := by decide +kernel
def t1x330 : Tree := .leaf ⟨false,8030501,2457600,0,8388608,-8388608,8388608⟩
lemma t1x330ok : treeCheck nodes v1 ⟨2424832,2457600,-8388608,8388608⟩ t1x330=true := by decide +kernel
def t1x331 : Tree := .leaf ⟨false,8020533,2490368,0,8388608,-8388608,8388608⟩
lemma t1x331ok : treeCheck nodes v1 ⟨2457600,2490368,-8388608,8388608⟩ t1x331=true := by decide +kernel
def t1x165 : Tree := .d (2457600) t1x330 t1x331
lemma t1x165ok : treeCheck nodes v1 ⟨2424832,2490368,-8388608,8388608⟩ t1x165=true := Bool.and_eq_true_iff.mpr ⟨t1x330ok,t1x331ok⟩
def t1x82 : Tree := .d (2424832) t1x164 t1x165
lemma t1x82ok : treeCheck nodes v1 ⟨2359296,2490368,-8388608,8388608⟩ t1x82=true := Bool.and_eq_true_iff.mpr ⟨t1x164ok,t1x165ok⟩
def t1x332 : Tree := .leaf ⟨false,8010419,2523136,0,8388608,-8388608,8388608⟩
lemma t1x332ok : treeCheck nodes v1 ⟨2490368,2523136,-8388608,8388608⟩ t1x332=true := by decide +kernel
def t1x333 : Tree := .leaf ⟨false,8000159,2555904,0,8388608,-8388608,8388608⟩
lemma t1x333ok : treeCheck nodes v1 ⟨2523136,2555904,-8388608,8388608⟩ t1x333=true := by decide +kernel
def t1x166 : Tree := .d (2523136) t1x332 t1x333
lemma t1x166ok : treeCheck nodes v1 ⟨2490368,2555904,-8388608,8388608⟩ t1x166=true := Bool.and_eq_true_iff.mpr ⟨t1x332ok,t1x333ok⟩
def t1x167 : Tree := .leaf ⟨false,7989750,2621440,0,8388608,-8388608,8388608⟩
lemma t1x167ok : treeCheck nodes v1 ⟨2555904,2621440,-8388608,8388608⟩ t1x167=true := by decide +kernel
def t1x83 : Tree := .d (2555904) t1x166 t1x167
lemma t1x83ok : treeCheck nodes v1 ⟨2490368,2621440,-8388608,8388608⟩ t1x83=true := Bool.and_eq_true_iff.mpr ⟨t1x166ok,t1x167ok⟩
def t1x41 : Tree := .d (2490368) t1x82 t1x83
lemma t1x41ok : treeCheck nodes v1 ⟨2359296,2621440,-8388608,8388608⟩ t1x41=true := Bool.and_eq_true_iff.mpr ⟨t1x82ok,t1x83ok⟩
def t1x20 : Tree := .d (2359296) t1x40 t1x41
lemma t1x20ok : treeCheck nodes v1 ⟨2097152,2621440,-8388608,8388608⟩ t1x20=true := Bool.and_eq_true_iff.mpr ⟨t1x40ok,t1x41ok⟩
def t1x168 : Tree := .leaf ⟨false,7968488,2686976,0,8388608,-8388608,8388608⟩
lemma t1x168ok : treeCheck nodes v1 ⟨2621440,2686976,-8388608,8388608⟩ t1x168=true := by decide +kernel
def t1x169 : Tree := .leaf ⟨false,7946629,2752512,0,8388608,-8388608,8388608⟩
lemma t1x169ok : treeCheck nodes v1 ⟨2686976,2752512,-8388608,8388608⟩ t1x169=true := by decide +kernel
def t1x84 : Tree := .d (2686976) t1x168 t1x169
lemma t1x84ok : treeCheck nodes v1 ⟨2621440,2752512,-8388608,8388608⟩ t1x84=true := Bool.and_eq_true_iff.mpr ⟨t1x168ok,t1x169ok⟩
def t1x170 : Tree := .leaf ⟨false,7924167,2818048,0,8388608,-8388608,8388608⟩
lemma t1x170ok : treeCheck nodes v1 ⟨2752512,2818048,-8388608,8388608⟩ t1x170=true := by decide +kernel
def t1x171 : Tree := .leaf ⟨false,7901099,2883584,0,8388608,-8388608,8388608⟩
lemma t1x171ok : treeCheck nodes v1 ⟨2818048,2883584,-8388608,8388608⟩ t1x171=true := by decide +kernel
def t1x85 : Tree := .d (2818048) t1x170 t1x171
lemma t1x85ok : treeCheck nodes v1 ⟨2752512,2883584,-8388608,8388608⟩ t1x85=true := Bool.and_eq_true_iff.mpr ⟨t1x170ok,t1x171ok⟩
def t1x42 : Tree := .d (2752512) t1x84 t1x85
lemma t1x42ok : treeCheck nodes v1 ⟨2621440,2883584,-8388608,8388608⟩ t1x42=true := Bool.and_eq_true_iff.mpr ⟨t1x84ok,t1x85ok⟩
def t1x172 : Tree := .leaf ⟨false,7877417,2949120,0,8388608,-8388608,8388608⟩
lemma t1x172ok : treeCheck nodes v1 ⟨2883584,2949120,-8388608,8388608⟩ t1x172=true := by decide +kernel
def t1x173 : Tree := .leaf ⟨false,7853117,3014656,0,8388608,-8388608,8388608⟩
lemma t1x173ok : treeCheck nodes v1 ⟨2949120,3014656,-8388608,8388608⟩ t1x173=true := by decide +kernel
def t1x86 : Tree := .d (2949120) t1x172 t1x173
lemma t1x86ok : treeCheck nodes v1 ⟨2883584,3014656,-8388608,8388608⟩ t1x86=true := Bool.and_eq_true_iff.mpr ⟨t1x172ok,t1x173ok⟩
def t1x174 : Tree := .leaf ⟨false,7828193,3080192,0,8388608,-8388608,8388608⟩
lemma t1x174ok : treeCheck nodes v1 ⟨3014656,3080192,-8388608,8388608⟩ t1x174=true := by decide +kernel
def t1x175 : Tree := .leaf ⟨false,7802639,3145728,0,8388608,-8388608,8388608⟩
lemma t1x175ok : treeCheck nodes v1 ⟨3080192,3145728,-8388608,8388608⟩ t1x175=true := by decide +kernel
def t1x87 : Tree := .d (3080192) t1x174 t1x175
lemma t1x87ok : treeCheck nodes v1 ⟨3014656,3145728,-8388608,8388608⟩ t1x87=true := Bool.and_eq_true_iff.mpr ⟨t1x174ok,t1x175ok⟩
def t1x43 : Tree := .d (3014656) t1x86 t1x87
lemma t1x43ok : treeCheck nodes v1 ⟨2883584,3145728,-8388608,8388608⟩ t1x43=true := Bool.and_eq_true_iff.mpr ⟨t1x86ok,t1x87ok⟩
def t1x21 : Tree := .d (2883584) t1x42 t1x43
lemma t1x21ok : treeCheck nodes v1 ⟨2621440,3145728,-8388608,8388608⟩ t1x21=true := Bool.and_eq_true_iff.mpr ⟨t1x42ok,t1x43ok⟩
def t1x10 : Tree := .d (2621440) t1x20 t1x21
lemma t1x10ok : treeCheck nodes v1 ⟨2097152,3145728,-8388608,8388608⟩ t1x10=true := Bool.and_eq_true_iff.mpr ⟨t1x20ok,t1x21ok⟩
def t1x176 : Tree := .leaf ⟨false,7776448,3211264,0,8388608,-8388608,8388608⟩
lemma t1x176ok : treeCheck nodes v1 ⟨3145728,3211264,-8388608,8388608⟩ t1x176=true := by decide +kernel
def t1x177 : Tree := .leaf ⟨false,7749615,3276800,0,8388608,-8388608,8388608⟩
lemma t1x177ok : treeCheck nodes v1 ⟨3211264,3276800,-8388608,8388608⟩ t1x177=true := by decide +kernel
def t1x88 : Tree := .d (3211264) t1x176 t1x177
lemma t1x88ok : treeCheck nodes v1 ⟨3145728,3276800,-8388608,8388608⟩ t1x88=true := Bool.and_eq_true_iff.mpr ⟨t1x176ok,t1x177ok⟩
def t1x178 : Tree := .leaf ⟨false,7722133,3342336,0,8388608,-8388608,8388608⟩
lemma t1x178ok : treeCheck nodes v1 ⟨3276800,3342336,-8388608,8388608⟩ t1x178=true := by decide +kernel
def t1x179 : Tree := .leaf ⟨false,7693994,3407872,0,8388608,-8388608,8388608⟩
lemma t1x179ok : treeCheck nodes v1 ⟨3342336,3407872,-8388608,8388608⟩ t1x179=true := by decide +kernel
def t1x89 : Tree := .d (3342336) t1x178 t1x179
lemma t1x89ok : treeCheck nodes v1 ⟨3276800,3407872,-8388608,8388608⟩ t1x89=true := Bool.and_eq_true_iff.mpr ⟨t1x178ok,t1x179ok⟩
def t1x44 : Tree := .d (3276800) t1x88 t1x89
lemma t1x44ok : treeCheck nodes v1 ⟨3145728,3407872,-8388608,8388608⟩ t1x44=true := Bool.and_eq_true_iff.mpr ⟨t1x88ok,t1x89ok⟩
def t1x90 : Tree := .leaf ⟨false,7665191,3538944,0,8388608,-8388608,8388608⟩
lemma t1x90ok : treeCheck nodes v1 ⟨3407872,3538944,-8388608,8388608⟩ t1x90=true := by decide +kernel
def t1x91 : Tree := .leaf ⟨false,7605566,3670016,0,8388608,-8388608,8388608⟩
lemma t1x91ok : treeCheck nodes v1 ⟨3538944,3670016,-8388608,8388608⟩ t1x91=true := by decide +kernel
def t1x45 : Tree := .d (3538944) t1x90 t1x91
lemma t1x45ok : treeCheck nodes v1 ⟨3407872,3670016,-8388608,8388608⟩ t1x45=true := Bool.and_eq_true_iff.mpr ⟨t1x90ok,t1x91ok⟩
def t1x22 : Tree := .d (3407872) t1x44 t1x45
lemma t1x22ok : treeCheck nodes v1 ⟨3145728,3670016,-8388608,8388608⟩ t1x22=true := Bool.and_eq_true_iff.mpr ⟨t1x44ok,t1x45ok⟩
def t1x92 : Tree := .leaf ⟨false,7543191,3801088,0,8388608,-8388608,8388608⟩
lemma t1x92ok : treeCheck nodes v1 ⟨3670016,3801088,-8388608,8388608⟩ t1x92=true := by decide +kernel
def t1x93 : Tree := .leaf ⟨false,7478000,3932160,0,8388608,-8388608,8388608⟩
lemma t1x93ok : treeCheck nodes v1 ⟨3801088,3932160,-8388608,8388608⟩ t1x93=true := by decide +kernel
def t1x46 : Tree := .d (3801088) t1x92 t1x93
lemma t1x46ok : treeCheck nodes v1 ⟨3670016,3932160,-8388608,8388608⟩ t1x46=true := Bool.and_eq_true_iff.mpr ⟨t1x92ok,t1x93ok⟩
def t1x94 : Tree := .leaf ⟨false,7409917,4063232,0,8388608,-8388608,8388608⟩
lemma t1x94ok : treeCheck nodes v1 ⟨3932160,4063232,-8388608,8388608⟩ t1x94=true := by decide +kernel
def t1x95 : Tree := .leaf ⟨false,7338862,4194304,0,8388608,-8388608,8388608⟩
lemma t1x95ok : treeCheck nodes v1 ⟨4063232,4194304,-8388608,8388608⟩ t1x95=true := by decide +kernel
def t1x47 : Tree := .d (4063232) t1x94 t1x95
lemma t1x47ok : treeCheck nodes v1 ⟨3932160,4194304,-8388608,8388608⟩ t1x47=true := Bool.and_eq_true_iff.mpr ⟨t1x94ok,t1x95ok⟩
def t1x23 : Tree := .d (3932160) t1x46 t1x47
lemma t1x23ok : treeCheck nodes v1 ⟨3670016,4194304,-8388608,8388608⟩ t1x23=true := Bool.and_eq_true_iff.mpr ⟨t1x46ok,t1x47ok⟩
def t1x11 : Tree := .d (3670016) t1x22 t1x23
lemma t1x11ok : treeCheck nodes v1 ⟨3145728,4194304,-8388608,8388608⟩ t1x11=true := Bool.and_eq_true_iff.mpr ⟨t1x22ok,t1x23ok⟩
def t1x5 : Tree := .d (3145728) t1x10 t1x11
lemma t1x5ok : treeCheck nodes v1 ⟨2097152,4194304,-8388608,8388608⟩ t1x5=true := Bool.and_eq_true_iff.mpr ⟨t1x10ok,t1x11ok⟩
def t1x2 : Tree := .d (2097152) t1x4 t1x5
lemma t1x2ok : treeCheck nodes v1 ⟨0,4194304,-8388608,8388608⟩ t1x2=true := Bool.and_eq_true_iff.mpr ⟨t1x4ok,t1x5ok⟩
def t1x48 : Tree := .leaf ⟨false,7264748,4456448,0,8388608,-8388608,8388608⟩
lemma t1x48ok : treeCheck nodes v1 ⟨4194304,4456448,-8388608,8388608⟩ t1x48=true := by decide +kernel
def t1x49 : Tree := .leaf ⟨false,7106956,4718592,0,8388608,-8388608,8388608⟩
lemma t1x49ok : treeCheck nodes v1 ⟨4456448,4718592,-8388608,8388608⟩ t1x49=true := by decide +kernel
def t1x24 : Tree := .d (4456448) t1x48 t1x49
lemma t1x24ok : treeCheck nodes v1 ⟨4194304,4718592,-8388608,8388608⟩ t1x24=true := Bool.and_eq_true_iff.mpr ⟨t1x48ok,t1x49ok⟩
def t1x50 : Tree := .leaf ⟨false,6935679,4980736,0,8388608,-8388608,8388608⟩
lemma t1x50ok : treeCheck nodes v1 ⟨4718592,4980736,-8388608,8388608⟩ t1x50=true := by decide +kernel
def t1x51 : Tree := .leaf ⟨false,6749890,5242880,0,8388608,-8388608,8388608⟩
lemma t1x51ok : treeCheck nodes v1 ⟨4980736,5242880,-8388608,8388608⟩ t1x51=true := by decide +kernel
def t1x25 : Tree := .d (4980736) t1x50 t1x51
lemma t1x25ok : treeCheck nodes v1 ⟨4718592,5242880,-8388608,8388608⟩ t1x25=true := Bool.and_eq_true_iff.mpr ⟨t1x50ok,t1x51ok⟩
def t1x12 : Tree := .d (4718592) t1x24 t1x25
lemma t1x12ok : treeCheck nodes v1 ⟨4194304,5242880,-8388608,8388608⟩ t1x12=true := Bool.and_eq_true_iff.mpr ⟨t1x24ok,t1x25ok⟩
def t1x26 : Tree := .leaf ⟨false,6548356,5767168,0,8388608,-8388608,8388608⟩
lemma t1x26ok : treeCheck nodes v1 ⟨5242880,5767168,-8388608,8388608⟩ t1x26=true := by decide +kernel
def t1x27 : Tree := .leaf ⟨false,6091677,6291456,0,8388608,-8388608,8388608⟩
lemma t1x27ok : treeCheck nodes v1 ⟨5767168,6291456,-8388608,8388608⟩ t1x27=true := by decide +kernel
def t1x13 : Tree := .d (5767168) t1x26 t1x27
lemma t1x13ok : treeCheck nodes v1 ⟨5242880,6291456,-8388608,8388608⟩ t1x13=true := Bool.and_eq_true_iff.mpr ⟨t1x26ok,t1x27ok⟩
def t1x6 : Tree := .d (5242880) t1x12 t1x13
lemma t1x6ok : treeCheck nodes v1 ⟨4194304,6291456,-8388608,8388608⟩ t1x6=true := Bool.and_eq_true_iff.mpr ⟨t1x12ok,t1x13ok⟩
def t1x14 : Tree := .leaf ⟨false,5548543,7340032,0,8388608,-8388608,8388608⟩
lemma t1x14ok : treeCheck nodes v1 ⟨6291456,7340032,-8388608,8388608⟩ t1x14=true := by decide +kernel
def t1x15 : Tree := .leaf ⟨false,4061118,8388608,0,8388608,-8388608,8388608⟩
lemma t1x15ok : treeCheck nodes v1 ⟨7340032,8388608,-8388608,8388608⟩ t1x15=true := by decide +kernel
def t1x7 : Tree := .d (7340032) t1x14 t1x15
lemma t1x7ok : treeCheck nodes v1 ⟨6291456,8388608,-8388608,8388608⟩ t1x7=true := Bool.and_eq_true_iff.mpr ⟨t1x14ok,t1x15ok⟩
def t1x3 : Tree := .d (6291456) t1x6 t1x7
lemma t1x3ok : treeCheck nodes v1 ⟨4194304,8388608,-8388608,8388608⟩ t1x3=true := Bool.and_eq_true_iff.mpr ⟨t1x6ok,t1x7ok⟩
def t1x1 : Tree := .d (4194304) t1x2 t1x3
lemma t1x1ok : treeCheck nodes v1 ⟨0,8388608,-8388608,8388608⟩ t1x1=true := Bool.and_eq_true_iff.mpr ⟨t1x2ok,t1x3ok⟩
def v22 : Band := ⟨11000000,11500000,742725,8355662,92274688,96468992,1140956,1091537⟩
lemma b22ok : bandCheck v22=true := by decide +kernel
def t22x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t22x8ok : treeCheck nodes v22 ⟨0,1048576,-8388608,8388608⟩ t22x8=true := by decide +kernel
def t22x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t22x9ok : treeCheck nodes v22 ⟨1048576,2097152,-8388608,8388608⟩ t22x9=true := by decide +kernel
def t22x4 : Tree := .d (1048576) t22x8 t22x9
lemma t22x4ok : treeCheck nodes v22 ⟨0,2097152,-8388608,8388608⟩ t22x4=true := Bool.and_eq_true_iff.mpr ⟨t22x8ok,t22x9ok⟩
def t22x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t22x5ok : treeCheck nodes v22 ⟨2097152,4194304,-8388608,8388608⟩ t22x5=true := by decide +kernel
def t22x2 : Tree := .d (2097152) t22x4 t22x5
lemma t22x2ok : treeCheck nodes v22 ⟨0,4194304,-8388608,8388608⟩ t22x2=true := Bool.and_eq_true_iff.mpr ⟨t22x4ok,t22x5ok⟩
def t22x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t22x3ok : treeCheck nodes v22 ⟨4194304,8388608,-8388608,8388608⟩ t22x3=true := by decide +kernel
def t22x1 : Tree := .d (4194304) t22x2 t22x3
lemma t22x1ok : treeCheck nodes v22 ⟨0,8388608,-8388608,8388608⟩ t22x1=true := Bool.and_eq_true_iff.mpr ⟨t22x2ok,t22x3ok⟩
def v23 : Band := ⟨11500000,12000000,711345,8358392,96468992,100663296,1091582,1046258⟩
lemma b23ok : bandCheck v23=true := by decide +kernel
def t23x8 : Tree := .leaf ⟨false,8388608,1048576,0,8388608,-8388608,8388608⟩
lemma t23x8ok : treeCheck nodes v23 ⟨0,1048576,-8388608,8388608⟩ t23x8=true := by decide +kernel
def t23x9 : Tree := .leaf ⟨false,8322814,2097152,0,8388608,-8388608,8388608⟩
lemma t23x9ok : treeCheck nodes v23 ⟨1048576,2097152,-8388608,8388608⟩ t23x9=true := by decide +kernel
def t23x4 : Tree := .d (1048576) t23x8 t23x9
lemma t23x4ok : treeCheck nodes v23 ⟨0,2097152,-8388608,8388608⟩ t23x4=true := Bool.and_eq_true_iff.mpr ⟨t23x8ok,t23x9ok⟩
def t23x5 : Tree := .leaf ⟨false,8122235,4194304,0,8388608,-8388608,8388608⟩
lemma t23x5ok : treeCheck nodes v23 ⟨2097152,4194304,-8388608,8388608⟩ t23x5=true := by decide +kernel
def t23x2 : Tree := .d (2097152) t23x4 t23x5
lemma t23x2ok : treeCheck nodes v23 ⟨0,4194304,-8388608,8388608⟩ t23x2=true := Bool.and_eq_true_iff.mpr ⟨t23x4ok,t23x5ok⟩
def t23x3 : Tree := .leaf ⟨false,7264748,8388608,0,8388608,-8388608,8388608⟩
lemma t23x3ok : treeCheck nodes v23 ⟨4194304,8388608,-8388608,8388608⟩ t23x3=true := by decide +kernel
def t23x1 : Tree := .d (4194304) t23x2 t23x3
lemma t23x1ok : treeCheck nodes v23 ⟨0,8388608,-8388608,8388608⟩ t23x1=true := Bool.and_eq_true_iff.mpr ⟨t23x2ok,t23x3ok⟩
end GateChecker.M3

end

section

open GrothendieckLB FiberDual GateChecker PanelAudit PanelBand PanelChain

theorem solution (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (7 : ℝ) / 5 ≤ c) (hhi : c ≤ 12) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c):= by
  have l1 : price M3.v1.lo ≤ c := by convert hlo using 1 <;> norm_num [price,M3.v1]
  by_cases h1 : c ≤ price M3.v1.hi
  · exact band ha M3.starts M3.ok0 M3.v1 M3.t1x1 M3.b1ok M3.t1x1ok l1 h1
  have l2 : price M0.v2.lo ≤ c := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : c ≤ price M0.v2.hi
  · exact band ha M0.starts M0.ok0 M0.v2 M0.t2x1 M0.b2ok M0.t2x1ok l2 h2
  have l3 : price M0.v3.lo ≤ c := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : c ≤ price M0.v3.hi
  · exact band ha M0.starts M0.ok0 M0.v3 M0.t3x1 M0.b3ok M0.t3x1ok l3 h3
  have l4 : price M0.v4.lo ≤ c := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : c ≤ price M0.v4.hi
  · exact band ha M0.starts M0.ok0 M0.v4 M0.t4x1 M0.b4ok M0.t4x1ok l4 h4
  have l5 : price M0.v5.lo ≤ c := le_of_lt (lt_of_not_ge h4)
  by_cases h5 : c ≤ price M0.v5.hi
  · exact band ha M0.starts M0.ok0 M0.v5 M0.t5x1 M0.b5ok M0.t5x1ok l5 h5
  have l6 : price M1.v6.lo ≤ c := le_of_lt (lt_of_not_ge h5)
  by_cases h6 : c ≤ price M1.v6.hi
  · exact band ha M1.starts M1.ok0 M1.v6 M1.t6x1 M1.b6ok M1.t6x1ok l6 h6
  have l7 : price M1.v7.lo ≤ c := le_of_lt (lt_of_not_ge h6)
  by_cases h7 : c ≤ price M1.v7.hi
  · exact band ha M1.starts M1.ok0 M1.v7 M1.t7x1 M1.b7ok M1.t7x1ok l7 h7
  have l8 : price M1.v8.lo ≤ c := le_of_lt (lt_of_not_ge h7)
  by_cases h8 : c ≤ price M1.v8.hi
  · exact band ha M1.starts M1.ok0 M1.v8 M1.t8x1 M1.b8ok M1.t8x1ok l8 h8
  have l9 : price M1.v9.lo ≤ c := le_of_lt (lt_of_not_ge h8)
  by_cases h9 : c ≤ price M1.v9.hi
  · exact band ha M1.starts M1.ok0 M1.v9 M1.t9x1 M1.b9ok M1.t9x1ok l9 h9
  have l10 : price M1.v10.lo ≤ c := le_of_lt (lt_of_not_ge h9)
  by_cases h10 : c ≤ price M1.v10.hi
  · exact band ha M1.starts M1.ok0 M1.v10 M1.t10x1 M1.b10ok M1.t10x1ok l10 h10
  have l11 : price M1.v11.lo ≤ c := le_of_lt (lt_of_not_ge h10)
  by_cases h11 : c ≤ price M1.v11.hi
  · exact band ha M1.starts M1.ok0 M1.v11 M1.t11x1 M1.b11ok M1.t11x1ok l11 h11
  have l12 : price M1.v12.lo ≤ c := le_of_lt (lt_of_not_ge h11)
  by_cases h12 : c ≤ price M1.v12.hi
  · exact band ha M1.starts M1.ok0 M1.v12 M1.t12x1 M1.b12ok M1.t12x1ok l12 h12
  have l13 : price M1.v13.lo ≤ c := le_of_lt (lt_of_not_ge h12)
  by_cases h13 : c ≤ price M1.v13.hi
  · exact band ha M1.starts M1.ok0 M1.v13 M1.t13x1 M1.b13ok M1.t13x1ok l13 h13
  have l14 : price M2.v14.lo ≤ c := le_of_lt (lt_of_not_ge h13)
  by_cases h14 : c ≤ price M2.v14.hi
  · exact band ha M2.starts M2.ok0 M2.v14 M2.t14x1 M2.b14ok M2.t14x1ok l14 h14
  have l15 : price M2.v15.lo ≤ c := le_of_lt (lt_of_not_ge h14)
  by_cases h15 : c ≤ price M2.v15.hi
  · exact band ha M2.starts M2.ok0 M2.v15 M2.t15x1 M2.b15ok M2.t15x1ok l15 h15
  have l16 : price M2.v16.lo ≤ c := le_of_lt (lt_of_not_ge h15)
  by_cases h16 : c ≤ price M2.v16.hi
  · exact band ha M2.starts M2.ok0 M2.v16 M2.t16x1 M2.b16ok M2.t16x1ok l16 h16
  have l17 : price M2.v17.lo ≤ c := le_of_lt (lt_of_not_ge h16)
  by_cases h17 : c ≤ price M2.v17.hi
  · exact band ha M2.starts M2.ok0 M2.v17 M2.t17x1 M2.b17ok M2.t17x1ok l17 h17
  have l18 : price M2.v18.lo ≤ c := le_of_lt (lt_of_not_ge h17)
  by_cases h18 : c ≤ price M2.v18.hi
  · exact band ha M2.starts M2.ok0 M2.v18 M2.t18x1 M2.b18ok M2.t18x1ok l18 h18
  have l19 : price M2.v19.lo ≤ c := le_of_lt (lt_of_not_ge h18)
  by_cases h19 : c ≤ price M2.v19.hi
  · exact band ha M2.starts M2.ok0 M2.v19 M2.t19x1 M2.b19ok M2.t19x1ok l19 h19
  have l20 : price M2.v20.lo ≤ c := le_of_lt (lt_of_not_ge h19)
  by_cases h20 : c ≤ price M2.v20.hi
  · exact band ha M2.starts M2.ok0 M2.v20 M2.t20x1 M2.b20ok M2.t20x1ok l20 h20
  have l21 : price M2.v21.lo ≤ c := le_of_lt (lt_of_not_ge h20)
  by_cases h21 : c ≤ price M2.v21.hi
  · exact band ha M2.starts M2.ok0 M2.v21 M2.t21x1 M2.b21ok M2.t21x1ok l21 h21
  have l22 : price M3.v22.lo ≤ c := le_of_lt (lt_of_not_ge h21)
  by_cases h22 : c ≤ price M3.v22.hi
  · exact band ha M3.starts M3.ok0 M3.v22 M3.t22x1 M3.b22ok M3.t22x1ok l22 h22
  have l23 : price M3.v23.lo ≤ c := le_of_lt (lt_of_not_ge h22)
  exact band ha M3.starts M3.ok0 M3.v23 M3.t23x1 M3.b23ok M3.t23x1ok l23 (by convert hhi using 1 <;> norm_num [price,M3.v23])

end
