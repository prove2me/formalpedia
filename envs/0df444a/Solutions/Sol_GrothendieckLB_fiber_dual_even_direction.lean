-- Prove2me | solution 1 for GrothendieckLB.fiber_dual_even_direction
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:19:57.232802+00:00
-- url     : https://prove2.me/submissions/9a1bd639-719c-4b5b-abf7-dacd158e28d6

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
def v0 : Band := ⟨993405,1400000,5378978,6437028,8333285,11744051,10320805,7940297⟩
lemma b0ok : bandCheck v0=true := by decide +kernel
def t0x256 : Tree := .leaf ⟨true,8388608,524288,0,4061118,-8388608,-7340032⟩
lemma t0x256ok : treeCheck nodes v0 ⟨0,524288,-8388608,-7340032⟩ t0x256=true := by decide +kernel
def t0x514 : Tree := .leaf ⟨true,8388608,262144,4061117,5548543,-7340032,-6291456⟩
lemma t0x514ok : treeCheck nodes v0 ⟨0,262144,-7340032,-6291456⟩ t0x514=true := by decide +kernel
def t0x1030 : Tree := .leaf ⟨true,8384511,524288,4061117,4890233,-7340032,-6815744⟩
lemma t0x1030ok : treeCheck nodes v0 ⟨262144,524288,-7340032,-6815744⟩ t0x1030=true := by decide +kernel
def t0x1031 : Tree := .leaf ⟨true,8384511,524288,4890232,5548543,-6815744,-6291456⟩
lemma t0x1031ok : treeCheck nodes v0 ⟨262144,524288,-6815744,-6291456⟩ t0x1031=true := by decide +kernel
def t0x515 : Tree := .y (-6815744) t0x1030 t0x1031
lemma t0x515ok : treeCheck nodes v0 ⟨262144,524288,-7340032,-6291456⟩ t0x515=true := Bool.and_eq_true_iff.mpr ⟨t0x1030ok,t0x1031ok⟩
def t0x257 : Tree := .d (262144) t0x514 t0x515
lemma t0x257ok : treeCheck nodes v0 ⟨0,524288,-7340032,-6291456⟩ t0x257=true := Bool.and_eq_true_iff.mpr ⟨t0x514ok,t0x515ok⟩
def t0x128 : Tree := .y (-7340032) t0x256 t0x257
lemma t0x128ok : treeCheck nodes v0 ⟨0,524288,-8388608,-6291456⟩ t0x128=true := Bool.and_eq_true_iff.mpr ⟨t0x256ok,t0x257ok⟩
def t0x258 : Tree := .leaf ⟨true,8372208,1048576,0,4061118,-8388608,-7340032⟩
lemma t0x258ok : treeCheck nodes v0 ⟨524288,1048576,-8388608,-7340032⟩ t0x258=true := by decide +kernel
def t0x1036 : Tree := .leaf ⟨true,8372208,786432,4061117,4890233,-7340032,-6815744⟩
lemma t0x1036ok : treeCheck nodes v0 ⟨524288,786432,-7340032,-6815744⟩ t0x1036=true := by decide +kernel
def t0x1037 : Tree := .leaf ⟨true,8372208,786432,4890232,5548543,-6815744,-6291456⟩
lemma t0x1037ok : treeCheck nodes v0 ⟨524288,786432,-6815744,-6291456⟩ t0x1037=true := by decide +kernel
def t0x518 : Tree := .y (-6815744) t0x1036 t0x1037
lemma t0x518ok : treeCheck nodes v0 ⟨524288,786432,-7340032,-6291456⟩ t0x518=true := Bool.and_eq_true_iff.mpr ⟨t0x1036ok,t0x1037ok⟩
def t0x1038 : Tree := .leaf ⟨true,8351663,1048576,4061117,4890233,-7340032,-6815744⟩
lemma t0x1038ok : treeCheck nodes v0 ⟨786432,1048576,-7340032,-6815744⟩ t0x1038=true := by decide +kernel
def t0x1039 : Tree := .leaf ⟨true,8351663,1048576,4890232,5548543,-6815744,-6291456⟩
lemma t0x1039ok : treeCheck nodes v0 ⟨786432,1048576,-6815744,-6291456⟩ t0x1039=true := by decide +kernel
def t0x519 : Tree := .y (-6815744) t0x1038 t0x1039
lemma t0x519ok : treeCheck nodes v0 ⟨786432,1048576,-7340032,-6291456⟩ t0x519=true := Bool.and_eq_true_iff.mpr ⟨t0x1038ok,t0x1039ok⟩
def t0x259 : Tree := .d (786432) t0x518 t0x519
lemma t0x259ok : treeCheck nodes v0 ⟨524288,1048576,-7340032,-6291456⟩ t0x259=true := Bool.and_eq_true_iff.mpr ⟨t0x518ok,t0x519ok⟩
def t0x129 : Tree := .y (-7340032) t0x258 t0x259
lemma t0x129ok : treeCheck nodes v0 ⟨524288,1048576,-8388608,-6291456⟩ t0x129=true := Bool.and_eq_true_iff.mpr ⟨t0x258ok,t0x259ok⟩
def t0x64 : Tree := .d (524288) t0x128 t0x129
lemma t0x64ok : treeCheck nodes v0 ⟨0,1048576,-8388608,-6291456⟩ t0x64=true := Bool.and_eq_true_iff.mpr ⟨t0x128ok,t0x129ok⟩
def t0x1040 : Tree := .leaf ⟨true,8388608,262144,5548542,6091677,-6291456,-5767168⟩
lemma t0x1040ok : treeCheck nodes v0 ⟨0,262144,-6291456,-5767168⟩ t0x1040=true := by decide +kernel
def t0x1041 : Tree := .leaf ⟨true,8388608,262144,6091676,6548356,-5767168,-5242880⟩
lemma t0x1041ok : treeCheck nodes v0 ⟨0,262144,-5767168,-5242880⟩ t0x1041=true := by decide +kernel
def t0x520 : Tree := .y (-5767168) t0x1040 t0x1041
lemma t0x520ok : treeCheck nodes v0 ⟨0,262144,-6291456,-5242880⟩ t0x520=true := Bool.and_eq_true_iff.mpr ⟨t0x1040ok,t0x1041ok⟩
def t0x1042 : Tree := .leaf ⟨true,8384511,524288,5548542,6091677,-6291456,-5767168⟩
lemma t0x1042ok : treeCheck nodes v0 ⟨262144,524288,-6291456,-5767168⟩ t0x1042=true := by decide +kernel
def t0x1043 : Tree := .leaf ⟨true,8384511,524288,6091676,6548356,-5767168,-5242880⟩
lemma t0x1043ok : treeCheck nodes v0 ⟨262144,524288,-5767168,-5242880⟩ t0x1043=true := by decide +kernel
def t0x521 : Tree := .y (-5767168) t0x1042 t0x1043
lemma t0x521ok : treeCheck nodes v0 ⟨262144,524288,-6291456,-5242880⟩ t0x521=true := Bool.and_eq_true_iff.mpr ⟨t0x1042ok,t0x1043ok⟩
def t0x260 : Tree := .d (262144) t0x520 t0x521
lemma t0x260ok : treeCheck nodes v0 ⟨0,524288,-6291456,-5242880⟩ t0x260=true := Bool.and_eq_true_iff.mpr ⟨t0x520ok,t0x521ok⟩
def t0x4176 : Tree := .leaf ⟨true,8388608,131072,6548355,6749890,-5242880,-4980736⟩
lemma t0x4176ok : treeCheck nodes v0 ⟨0,131072,-5242880,-4980736⟩ t0x4176=true := by decide +kernel
def t0x4177 : Tree := .leaf ⟨true,8388608,131072,6749889,6935679,-4980736,-4718592⟩
lemma t0x4177ok : treeCheck nodes v0 ⟨0,131072,-4980736,-4718592⟩ t0x4177=true := by decide +kernel
def t0x2088 : Tree := .y (-4980736) t0x4176 t0x4177
lemma t0x2088ok : treeCheck nodes v0 ⟨0,131072,-5242880,-4718592⟩ t0x2088=true := Bool.and_eq_true_iff.mpr ⟨t0x4176ok,t0x4177ok⟩
def t0x4178 : Tree := .leaf ⟨true,8387584,262144,6548355,6749890,-5242880,-4980736⟩
lemma t0x4178ok : treeCheck nodes v0 ⟨131072,262144,-5242880,-4980736⟩ t0x4178=true := by decide +kernel
def t0x4179 : Tree := .leaf ⟨true,8387584,262144,6749889,6935679,-4980736,-4718592⟩
lemma t0x4179ok : treeCheck nodes v0 ⟨131072,262144,-4980736,-4718592⟩ t0x4179=true := by decide +kernel
def t0x2089 : Tree := .y (-4980736) t0x4178 t0x4179
lemma t0x2089ok : treeCheck nodes v0 ⟨131072,262144,-5242880,-4718592⟩ t0x2089=true := Bool.and_eq_true_iff.mpr ⟨t0x4178ok,t0x4179ok⟩
def t0x1044 : Tree := .d (131072) t0x2088 t0x2089
lemma t0x1044ok : treeCheck nodes v0 ⟨0,262144,-5242880,-4718592⟩ t0x1044=true := Bool.and_eq_true_iff.mpr ⟨t0x2088ok,t0x2089ok⟩
def t0x4180 : Tree := .leaf ⟨true,8388608,131072,6935678,7106956,-4718592,-4456448⟩
lemma t0x4180ok : treeCheck nodes v0 ⟨0,131072,-4718592,-4456448⟩ t0x4180=true := by decide +kernel
def t0x4181 : Tree := .leaf ⟨true,8388608,131072,7106955,7264748,-4456448,-4194304⟩
lemma t0x4181ok : treeCheck nodes v0 ⟨0,131072,-4456448,-4194304⟩ t0x4181=true := by decide +kernel
def t0x2090 : Tree := .y (-4456448) t0x4180 t0x4181
lemma t0x2090ok : treeCheck nodes v0 ⟨0,131072,-4718592,-4194304⟩ t0x2090=true := Bool.and_eq_true_iff.mpr ⟨t0x4180ok,t0x4181ok⟩
def t0x4182 : Tree := .leaf ⟨true,8387584,262144,6935678,7106956,-4718592,-4456448⟩
lemma t0x4182ok : treeCheck nodes v0 ⟨131072,262144,-4718592,-4456448⟩ t0x4182=true := by decide +kernel
def t0x4183 : Tree := .leaf ⟨true,8387584,262144,7106955,7264748,-4456448,-4194304⟩
lemma t0x4183ok : treeCheck nodes v0 ⟨131072,262144,-4456448,-4194304⟩ t0x4183=true := by decide +kernel
def t0x2091 : Tree := .y (-4456448) t0x4182 t0x4183
lemma t0x2091ok : treeCheck nodes v0 ⟨131072,262144,-4718592,-4194304⟩ t0x2091=true := Bool.and_eq_true_iff.mpr ⟨t0x4182ok,t0x4183ok⟩
def t0x1045 : Tree := .d (131072) t0x2090 t0x2091
lemma t0x1045ok : treeCheck nodes v0 ⟨0,262144,-4718592,-4194304⟩ t0x1045=true := Bool.and_eq_true_iff.mpr ⟨t0x2090ok,t0x2091ok⟩
def t0x522 : Tree := .y (-4718592) t0x1044 t0x1045
lemma t0x522ok : treeCheck nodes v0 ⟨0,262144,-5242880,-4194304⟩ t0x522=true := Bool.and_eq_true_iff.mpr ⟨t0x1044ok,t0x1045ok⟩
def t0x4184 : Tree := .leaf ⟨true,8384511,393216,6548355,6749890,-5242880,-4980736⟩
lemma t0x4184ok : treeCheck nodes v0 ⟨262144,393216,-5242880,-4980736⟩ t0x4184=true := by decide +kernel
def t0x4185 : Tree := .leaf ⟨true,8384511,393216,6749889,6935679,-4980736,-4718592⟩
lemma t0x4185ok : treeCheck nodes v0 ⟨262144,393216,-4980736,-4718592⟩ t0x4185=true := by decide +kernel
def t0x2092 : Tree := .y (-4980736) t0x4184 t0x4185
lemma t0x2092ok : treeCheck nodes v0 ⟨262144,393216,-5242880,-4718592⟩ t0x2092=true := Bool.and_eq_true_iff.mpr ⟨t0x4184ok,t0x4185ok⟩
def t0x4186 : Tree := .leaf ⟨true,8379387,524288,6548355,6749890,-5242880,-4980736⟩
lemma t0x4186ok : treeCheck nodes v0 ⟨393216,524288,-5242880,-4980736⟩ t0x4186=true := by decide +kernel
def t0x4187 : Tree := .leaf ⟨true,8379387,524288,6749889,6935679,-4980736,-4718592⟩
lemma t0x4187ok : treeCheck nodes v0 ⟨393216,524288,-4980736,-4718592⟩ t0x4187=true := by decide +kernel
def t0x2093 : Tree := .y (-4980736) t0x4186 t0x4187
lemma t0x2093ok : treeCheck nodes v0 ⟨393216,524288,-5242880,-4718592⟩ t0x2093=true := Bool.and_eq_true_iff.mpr ⟨t0x4186ok,t0x4187ok⟩
def t0x1046 : Tree := .d (393216) t0x2092 t0x2093
lemma t0x1046ok : treeCheck nodes v0 ⟨262144,524288,-5242880,-4718592⟩ t0x1046=true := Bool.and_eq_true_iff.mpr ⟨t0x2092ok,t0x2093ok⟩
def t0x4188 : Tree := .leaf ⟨true,8384511,393216,6935678,7106956,-4718592,-4456448⟩
lemma t0x4188ok : treeCheck nodes v0 ⟨262144,393216,-4718592,-4456448⟩ t0x4188=true := by decide +kernel
def t0x4189 : Tree := .leaf ⟨true,8384511,393216,7106955,7264748,-4456448,-4194304⟩
lemma t0x4189ok : treeCheck nodes v0 ⟨262144,393216,-4456448,-4194304⟩ t0x4189=true := by decide +kernel
def t0x2094 : Tree := .y (-4456448) t0x4188 t0x4189
lemma t0x2094ok : treeCheck nodes v0 ⟨262144,393216,-4718592,-4194304⟩ t0x2094=true := Bool.and_eq_true_iff.mpr ⟨t0x4188ok,t0x4189ok⟩
def t0x4190 : Tree := .leaf ⟨true,8379387,524288,6935678,7106956,-4718592,-4456448⟩
lemma t0x4190ok : treeCheck nodes v0 ⟨393216,524288,-4718592,-4456448⟩ t0x4190=true := by decide +kernel
def t0x4191 : Tree := .leaf ⟨true,8379387,524288,7106955,7264748,-4456448,-4194304⟩
lemma t0x4191ok : treeCheck nodes v0 ⟨393216,524288,-4456448,-4194304⟩ t0x4191=true := by decide +kernel
def t0x2095 : Tree := .y (-4456448) t0x4190 t0x4191
lemma t0x2095ok : treeCheck nodes v0 ⟨393216,524288,-4718592,-4194304⟩ t0x2095=true := Bool.and_eq_true_iff.mpr ⟨t0x4190ok,t0x4191ok⟩
def t0x1047 : Tree := .d (393216) t0x2094 t0x2095
lemma t0x1047ok : treeCheck nodes v0 ⟨262144,524288,-4718592,-4194304⟩ t0x1047=true := Bool.and_eq_true_iff.mpr ⟨t0x2094ok,t0x2095ok⟩
def t0x523 : Tree := .y (-4718592) t0x1046 t0x1047
lemma t0x523ok : treeCheck nodes v0 ⟨262144,524288,-5242880,-4194304⟩ t0x523=true := Bool.and_eq_true_iff.mpr ⟨t0x1046ok,t0x1047ok⟩
def t0x261 : Tree := .d (262144) t0x522 t0x523
lemma t0x261ok : treeCheck nodes v0 ⟨0,524288,-5242880,-4194304⟩ t0x261=true := Bool.and_eq_true_iff.mpr ⟨t0x522ok,t0x523ok⟩
def t0x130 : Tree := .y (-5242880) t0x260 t0x261
lemma t0x130ok : treeCheck nodes v0 ⟨0,524288,-6291456,-4194304⟩ t0x130=true := Bool.and_eq_true_iff.mpr ⟨t0x260ok,t0x261ok⟩
def t0x1048 : Tree := .leaf ⟨true,8372208,786432,5548542,6091677,-6291456,-5767168⟩
lemma t0x1048ok : treeCheck nodes v0 ⟨524288,786432,-6291456,-5767168⟩ t0x1048=true := by decide +kernel
def t0x2098 : Tree := .leaf ⟨true,8372208,655360,6091676,6548356,-5767168,-5242880⟩
lemma t0x2098ok : treeCheck nodes v0 ⟨524288,655360,-5767168,-5242880⟩ t0x2098=true := by decide +kernel
def t0x2099 : Tree := .leaf ⟨true,8362969,786432,6091676,6548356,-5767168,-5242880⟩
lemma t0x2099ok : treeCheck nodes v0 ⟨655360,786432,-5767168,-5242880⟩ t0x2099=true := by decide +kernel
def t0x1049 : Tree := .d (655360) t0x2098 t0x2099
lemma t0x1049ok : treeCheck nodes v0 ⟨524288,786432,-5767168,-5242880⟩ t0x1049=true := Bool.and_eq_true_iff.mpr ⟨t0x2098ok,t0x2099ok⟩
def t0x524 : Tree := .y (-5767168) t0x1048 t0x1049
lemma t0x524ok : treeCheck nodes v0 ⟨524288,786432,-6291456,-5242880⟩ t0x524=true := Bool.and_eq_true_iff.mpr ⟨t0x1048ok,t0x1049ok⟩
def t0x1050 : Tree := .leaf ⟨true,8351663,1048576,5548542,6091677,-6291456,-5767168⟩
lemma t0x1050ok : treeCheck nodes v0 ⟨786432,1048576,-6291456,-5767168⟩ t0x1050=true := by decide +kernel
def t0x2102 : Tree := .leaf ⟨true,8351663,917504,6091676,6548356,-5767168,-5242880⟩
lemma t0x2102ok : treeCheck nodes v0 ⟨786432,917504,-5767168,-5242880⟩ t0x2102=true := by decide +kernel
def t0x2103 : Tree := .leaf ⟨true,8338282,1048576,6091676,6548356,-5767168,-5242880⟩
lemma t0x2103ok : treeCheck nodes v0 ⟨917504,1048576,-5767168,-5242880⟩ t0x2103=true := by decide +kernel
def t0x1051 : Tree := .d (917504) t0x2102 t0x2103
lemma t0x1051ok : treeCheck nodes v0 ⟨786432,1048576,-5767168,-5242880⟩ t0x1051=true := Bool.and_eq_true_iff.mpr ⟨t0x2102ok,t0x2103ok⟩
def t0x525 : Tree := .y (-5767168) t0x1050 t0x1051
lemma t0x525ok : treeCheck nodes v0 ⟨786432,1048576,-6291456,-5242880⟩ t0x525=true := Bool.and_eq_true_iff.mpr ⟨t0x1050ok,t0x1051ok⟩
def t0x262 : Tree := .d (786432) t0x524 t0x525
lemma t0x262ok : treeCheck nodes v0 ⟨524288,1048576,-6291456,-5242880⟩ t0x262=true := Bool.and_eq_true_iff.mpr ⟨t0x524ok,t0x525ok⟩
def t0x4208 : Tree := .leaf ⟨true,8372208,655360,6548355,6749890,-5242880,-4980736⟩
lemma t0x4208ok : treeCheck nodes v0 ⟨524288,655360,-5242880,-4980736⟩ t0x4208=true := by decide +kernel
def t0x4209 : Tree := .leaf ⟨true,8372208,655360,6749889,6935679,-4980736,-4718592⟩
lemma t0x4209ok : treeCheck nodes v0 ⟨524288,655360,-4980736,-4718592⟩ t0x4209=true := by decide +kernel
def t0x2104 : Tree := .y (-4980736) t0x4208 t0x4209
lemma t0x2104ok : treeCheck nodes v0 ⟨524288,655360,-5242880,-4718592⟩ t0x2104=true := Bool.and_eq_true_iff.mpr ⟨t0x4208ok,t0x4209ok⟩
def t0x4210 : Tree := .leaf ⟨true,8362969,786432,6548355,6749890,-5242880,-4980736⟩
lemma t0x4210ok : treeCheck nodes v0 ⟨655360,786432,-5242880,-4980736⟩ t0x4210=true := by decide +kernel
def t0x4211 : Tree := .leaf ⟨true,8362969,786432,6749889,6935679,-4980736,-4718592⟩
lemma t0x4211ok : treeCheck nodes v0 ⟨655360,786432,-4980736,-4718592⟩ t0x4211=true := by decide +kernel
def t0x2105 : Tree := .y (-4980736) t0x4210 t0x4211
lemma t0x2105ok : treeCheck nodes v0 ⟨655360,786432,-5242880,-4718592⟩ t0x2105=true := Bool.and_eq_true_iff.mpr ⟨t0x4210ok,t0x4211ok⟩
def t0x1052 : Tree := .d (655360) t0x2104 t0x2105
lemma t0x1052ok : treeCheck nodes v0 ⟨524288,786432,-5242880,-4718592⟩ t0x1052=true := Bool.and_eq_true_iff.mpr ⟨t0x2104ok,t0x2105ok⟩
def t0x4212 : Tree := .leaf ⟨true,8372208,655360,6935678,7106956,-4718592,-4456448⟩
lemma t0x4212ok : treeCheck nodes v0 ⟨524288,655360,-4718592,-4456448⟩ t0x4212=true := by decide +kernel
def t0x4213 : Tree := .leaf ⟨true,8372208,655360,7106955,7264748,-4456448,-4194304⟩
lemma t0x4213ok : treeCheck nodes v0 ⟨524288,655360,-4456448,-4194304⟩ t0x4213=true := by decide +kernel
def t0x2106 : Tree := .y (-4456448) t0x4212 t0x4213
lemma t0x2106ok : treeCheck nodes v0 ⟨524288,655360,-4718592,-4194304⟩ t0x2106=true := Bool.and_eq_true_iff.mpr ⟨t0x4212ok,t0x4213ok⟩
def t0x4214 : Tree := .leaf ⟨true,8362969,786432,6935678,7106956,-4718592,-4456448⟩
lemma t0x4214ok : treeCheck nodes v0 ⟨655360,786432,-4718592,-4456448⟩ t0x4214=true := by decide +kernel
def t0x4215 : Tree := .leaf ⟨true,8362969,786432,7106955,7264748,-4456448,-4194304⟩
lemma t0x4215ok : treeCheck nodes v0 ⟨655360,786432,-4456448,-4194304⟩ t0x4215=true := by decide +kernel
def t0x2107 : Tree := .y (-4456448) t0x4214 t0x4215
lemma t0x2107ok : treeCheck nodes v0 ⟨655360,786432,-4718592,-4194304⟩ t0x2107=true := Bool.and_eq_true_iff.mpr ⟨t0x4214ok,t0x4215ok⟩
def t0x1053 : Tree := .d (655360) t0x2106 t0x2107
lemma t0x1053ok : treeCheck nodes v0 ⟨524288,786432,-4718592,-4194304⟩ t0x1053=true := Bool.and_eq_true_iff.mpr ⟨t0x2106ok,t0x2107ok⟩
def t0x526 : Tree := .y (-4718592) t0x1052 t0x1053
lemma t0x526ok : treeCheck nodes v0 ⟨524288,786432,-5242880,-4194304⟩ t0x526=true := Bool.and_eq_true_iff.mpr ⟨t0x1052ok,t0x1053ok⟩
def t0x4216 : Tree := .leaf ⟨true,8351663,917504,6548355,6749890,-5242880,-4980736⟩
lemma t0x4216ok : treeCheck nodes v0 ⟨786432,917504,-5242880,-4980736⟩ t0x4216=true := by decide +kernel
def t0x4217 : Tree := .leaf ⟨true,8351663,917504,6749889,6935679,-4980736,-4718592⟩
lemma t0x4217ok : treeCheck nodes v0 ⟨786432,917504,-4980736,-4718592⟩ t0x4217=true := by decide +kernel
def t0x2108 : Tree := .y (-4980736) t0x4216 t0x4217
lemma t0x2108ok : treeCheck nodes v0 ⟨786432,917504,-5242880,-4718592⟩ t0x2108=true := Bool.and_eq_true_iff.mpr ⟨t0x4216ok,t0x4217ok⟩
def t0x4218 : Tree := .leaf ⟨true,8338282,1048576,6548355,6749890,-5242880,-4980736⟩
lemma t0x4218ok : treeCheck nodes v0 ⟨917504,1048576,-5242880,-4980736⟩ t0x4218=true := by decide +kernel
def t0x4219 : Tree := .leaf ⟨true,8338282,1048576,6749889,6935679,-4980736,-4718592⟩
lemma t0x4219ok : treeCheck nodes v0 ⟨917504,1048576,-4980736,-4718592⟩ t0x4219=true := by decide +kernel
def t0x2109 : Tree := .y (-4980736) t0x4218 t0x4219
lemma t0x2109ok : treeCheck nodes v0 ⟨917504,1048576,-5242880,-4718592⟩ t0x2109=true := Bool.and_eq_true_iff.mpr ⟨t0x4218ok,t0x4219ok⟩
def t0x1054 : Tree := .d (917504) t0x2108 t0x2109
lemma t0x1054ok : treeCheck nodes v0 ⟨786432,1048576,-5242880,-4718592⟩ t0x1054=true := Bool.and_eq_true_iff.mpr ⟨t0x2108ok,t0x2109ok⟩
def t0x4220 : Tree := .leaf ⟨true,8351663,917504,6935678,7106956,-4718592,-4456448⟩
lemma t0x4220ok : treeCheck nodes v0 ⟨786432,917504,-4718592,-4456448⟩ t0x4220=true := by decide +kernel
def t0x4221 : Tree := .leaf ⟨true,8351663,917504,7106955,7264748,-4456448,-4194304⟩
lemma t0x4221ok : treeCheck nodes v0 ⟨786432,917504,-4456448,-4194304⟩ t0x4221=true := by decide +kernel
def t0x2110 : Tree := .y (-4456448) t0x4220 t0x4221
lemma t0x2110ok : treeCheck nodes v0 ⟨786432,917504,-4718592,-4194304⟩ t0x2110=true := Bool.and_eq_true_iff.mpr ⟨t0x4220ok,t0x4221ok⟩
def t0x4222 : Tree := .leaf ⟨true,8338282,1048576,6935678,7106956,-4718592,-4456448⟩
lemma t0x4222ok : treeCheck nodes v0 ⟨917504,1048576,-4718592,-4456448⟩ t0x4222=true := by decide +kernel
def t0x4223 : Tree := .leaf ⟨true,8338282,1048576,7106955,7264748,-4456448,-4194304⟩
lemma t0x4223ok : treeCheck nodes v0 ⟨917504,1048576,-4456448,-4194304⟩ t0x4223=true := by decide +kernel
def t0x2111 : Tree := .y (-4456448) t0x4222 t0x4223
lemma t0x2111ok : treeCheck nodes v0 ⟨917504,1048576,-4718592,-4194304⟩ t0x2111=true := Bool.and_eq_true_iff.mpr ⟨t0x4222ok,t0x4223ok⟩
def t0x1055 : Tree := .d (917504) t0x2110 t0x2111
lemma t0x1055ok : treeCheck nodes v0 ⟨786432,1048576,-4718592,-4194304⟩ t0x1055=true := Bool.and_eq_true_iff.mpr ⟨t0x2110ok,t0x2111ok⟩
def t0x527 : Tree := .y (-4718592) t0x1054 t0x1055
lemma t0x527ok : treeCheck nodes v0 ⟨786432,1048576,-5242880,-4194304⟩ t0x527=true := Bool.and_eq_true_iff.mpr ⟨t0x1054ok,t0x1055ok⟩
def t0x263 : Tree := .d (786432) t0x526 t0x527
lemma t0x263ok : treeCheck nodes v0 ⟨524288,1048576,-5242880,-4194304⟩ t0x263=true := Bool.and_eq_true_iff.mpr ⟨t0x526ok,t0x527ok⟩
def t0x131 : Tree := .y (-5242880) t0x262 t0x263
lemma t0x131ok : treeCheck nodes v0 ⟨524288,1048576,-6291456,-4194304⟩ t0x131=true := Bool.and_eq_true_iff.mpr ⟨t0x262ok,t0x263ok⟩
def t0x65 : Tree := .d (524288) t0x130 t0x131
lemma t0x65ok : treeCheck nodes v0 ⟨0,1048576,-6291456,-4194304⟩ t0x65=true := Bool.and_eq_true_iff.mpr ⟨t0x130ok,t0x131ok⟩
def t0x32 : Tree := .y (-6291456) t0x64 t0x65
lemma t0x32ok : treeCheck nodes v0 ⟨0,1048576,-8388608,-4194304⟩ t0x32=true := Bool.and_eq_true_iff.mpr ⟨t0x64ok,t0x65ok⟩
def t0x264 : Tree := .leaf ⟨true,8322814,1572864,0,4061118,-8388608,-7340032⟩
lemma t0x264ok : treeCheck nodes v0 ⟨1048576,1572864,-8388608,-7340032⟩ t0x264=true := by decide +kernel
def t0x1060 : Tree := .leaf ⟨true,8322814,1310720,4061117,4890233,-7340032,-6815744⟩
lemma t0x1060ok : treeCheck nodes v0 ⟨1048576,1310720,-7340032,-6815744⟩ t0x1060=true := by decide +kernel
def t0x1061 : Tree := .leaf ⟨true,8322814,1310720,4890232,5548543,-6815744,-6291456⟩
lemma t0x1061ok : treeCheck nodes v0 ⟨1048576,1310720,-6815744,-6291456⟩ t0x1061=true := by decide +kernel
def t0x530 : Tree := .y (-6815744) t0x1060 t0x1061
lemma t0x530ok : treeCheck nodes v0 ⟨1048576,1310720,-7340032,-6291456⟩ t0x530=true := Bool.and_eq_true_iff.mpr ⟨t0x1060ok,t0x1061ok⟩
def t0x1062 : Tree := .leaf ⟨true,8285576,1572864,4061117,4890233,-7340032,-6815744⟩
lemma t0x1062ok : treeCheck nodes v0 ⟨1310720,1572864,-7340032,-6815744⟩ t0x1062=true := by decide +kernel
def t0x1063 : Tree := .leaf ⟨true,8285576,1572864,4890232,5548543,-6815744,-6291456⟩
lemma t0x1063ok : treeCheck nodes v0 ⟨1310720,1572864,-6815744,-6291456⟩ t0x1063=true := by decide +kernel
def t0x531 : Tree := .y (-6815744) t0x1062 t0x1063
lemma t0x531ok : treeCheck nodes v0 ⟨1310720,1572864,-7340032,-6291456⟩ t0x531=true := Bool.and_eq_true_iff.mpr ⟨t0x1062ok,t0x1063ok⟩
def t0x265 : Tree := .d (1310720) t0x530 t0x531
lemma t0x265ok : treeCheck nodes v0 ⟨1048576,1572864,-7340032,-6291456⟩ t0x265=true := Bool.and_eq_true_iff.mpr ⟨t0x530ok,t0x531ok⟩
def t0x132 : Tree := .y (-7340032) t0x264 t0x265
lemma t0x132ok : treeCheck nodes v0 ⟨1048576,1572864,-8388608,-6291456⟩ t0x132=true := Bool.and_eq_true_iff.mpr ⟨t0x264ok,t0x265ok⟩
def t0x266 : Tree := .leaf ⟨true,8239833,2097152,0,4061118,-8388608,-7340032⟩
lemma t0x266ok : treeCheck nodes v0 ⟨1572864,2097152,-8388608,-7340032⟩ t0x266=true := by decide +kernel
def t0x1068 : Tree := .leaf ⟨true,8239833,1835008,4061117,4890233,-7340032,-6815744⟩
lemma t0x1068ok : treeCheck nodes v0 ⟨1572864,1835008,-7340032,-6815744⟩ t0x1068=true := by decide +kernel
def t0x1069 : Tree := .leaf ⟨true,8239833,1835008,4890232,5548543,-6815744,-6291456⟩
lemma t0x1069ok : treeCheck nodes v0 ⟨1572864,1835008,-6815744,-6291456⟩ t0x1069=true := by decide +kernel
def t0x534 : Tree := .y (-6815744) t0x1068 t0x1069
lemma t0x534ok : treeCheck nodes v0 ⟨1572864,1835008,-7340032,-6291456⟩ t0x534=true := Bool.and_eq_true_iff.mpr ⟨t0x1068ok,t0x1069ok⟩
def t0x1070 : Tree := .leaf ⟨true,8185444,2097152,4061117,4890233,-7340032,-6815744⟩
lemma t0x1070ok : treeCheck nodes v0 ⟨1835008,2097152,-7340032,-6815744⟩ t0x1070=true := by decide +kernel
def t0x1071 : Tree := .leaf ⟨true,8185444,2097152,4890232,5548543,-6815744,-6291456⟩
lemma t0x1071ok : treeCheck nodes v0 ⟨1835008,2097152,-6815744,-6291456⟩ t0x1071=true := by decide +kernel
def t0x535 : Tree := .y (-6815744) t0x1070 t0x1071
lemma t0x535ok : treeCheck nodes v0 ⟨1835008,2097152,-7340032,-6291456⟩ t0x535=true := Bool.and_eq_true_iff.mpr ⟨t0x1070ok,t0x1071ok⟩
def t0x267 : Tree := .d (1835008) t0x534 t0x535
lemma t0x267ok : treeCheck nodes v0 ⟨1572864,2097152,-7340032,-6291456⟩ t0x267=true := Bool.and_eq_true_iff.mpr ⟨t0x534ok,t0x535ok⟩
def t0x133 : Tree := .y (-7340032) t0x266 t0x267
lemma t0x133ok : treeCheck nodes v0 ⟨1572864,2097152,-8388608,-6291456⟩ t0x133=true := Bool.and_eq_true_iff.mpr ⟨t0x266ok,t0x267ok⟩
def t0x66 : Tree := .d (1572864) t0x132 t0x133
lemma t0x66ok : treeCheck nodes v0 ⟨1048576,2097152,-8388608,-6291456⟩ t0x66=true := Bool.and_eq_true_iff.mpr ⟨t0x132ok,t0x133ok⟩
def t0x1072 : Tree := .leaf ⟨true,8322814,1310720,5548542,6091677,-6291456,-5767168⟩
lemma t0x1072ok : treeCheck nodes v0 ⟨1048576,1310720,-6291456,-5767168⟩ t0x1072=true := by decide +kernel
def t0x2146 : Tree := .leaf ⟨true,8322814,1179648,6091676,6548356,-5767168,-5242880⟩
lemma t0x2146ok : treeCheck nodes v0 ⟨1048576,1179648,-5767168,-5242880⟩ t0x2146=true := by decide +kernel
def t0x2147 : Tree := .leaf ⟨true,8305250,1310720,6091676,6548356,-5767168,-5242880⟩
lemma t0x2147ok : treeCheck nodes v0 ⟨1179648,1310720,-5767168,-5242880⟩ t0x2147=true := by decide +kernel
def t0x1073 : Tree := .d (1179648) t0x2146 t0x2147
lemma t0x1073ok : treeCheck nodes v0 ⟨1048576,1310720,-5767168,-5242880⟩ t0x1073=true := Bool.and_eq_true_iff.mpr ⟨t0x2146ok,t0x2147ok⟩
def t0x536 : Tree := .y (-5767168) t0x1072 t0x1073
lemma t0x536ok : treeCheck nodes v0 ⟨1048576,1310720,-6291456,-5242880⟩ t0x536=true := Bool.and_eq_true_iff.mpr ⟨t0x1072ok,t0x1073ok⟩
def t0x1074 : Tree := .leaf ⟨true,8285576,1572864,5548542,6091677,-6291456,-5767168⟩
lemma t0x1074ok : treeCheck nodes v0 ⟨1310720,1572864,-6291456,-5767168⟩ t0x1074=true := by decide +kernel
def t0x1075 : Tree := .leaf ⟨true,8285576,1572864,6091676,6548356,-5767168,-5242880⟩
lemma t0x1075ok : treeCheck nodes v0 ⟨1310720,1572864,-5767168,-5242880⟩ t0x1075=true := by decide +kernel
def t0x537 : Tree := .y (-5767168) t0x1074 t0x1075
lemma t0x537ok : treeCheck nodes v0 ⟨1310720,1572864,-6291456,-5242880⟩ t0x537=true := Bool.and_eq_true_iff.mpr ⟨t0x1074ok,t0x1075ok⟩
def t0x268 : Tree := .d (1310720) t0x536 t0x537
lemma t0x268ok : treeCheck nodes v0 ⟨1048576,1572864,-6291456,-5242880⟩ t0x268=true := Bool.and_eq_true_iff.mpr ⟨t0x536ok,t0x537ok⟩
def t0x4304 : Tree := .leaf ⟨true,8322814,1179648,6548355,6749890,-5242880,-4980736⟩
lemma t0x4304ok : treeCheck nodes v0 ⟨1048576,1179648,-5242880,-4980736⟩ t0x4304=true := by decide +kernel
def t0x4305 : Tree := .leaf ⟨true,8322814,1179648,6749889,6935679,-4980736,-4718592⟩
lemma t0x4305ok : treeCheck nodes v0 ⟨1048576,1179648,-4980736,-4718592⟩ t0x4305=true := by decide +kernel
def t0x2152 : Tree := .y (-4980736) t0x4304 t0x4305
lemma t0x2152ok : treeCheck nodes v0 ⟨1048576,1179648,-5242880,-4718592⟩ t0x2152=true := Bool.and_eq_true_iff.mpr ⟨t0x4304ok,t0x4305ok⟩
def t0x4306 : Tree := .leaf ⟨true,8305250,1310720,6548355,6749890,-5242880,-4980736⟩
lemma t0x4306ok : treeCheck nodes v0 ⟨1179648,1310720,-5242880,-4980736⟩ t0x4306=true := by decide +kernel
def t0x4307 : Tree := .leaf ⟨true,8305250,1310720,6749889,6935679,-4980736,-4718592⟩
lemma t0x4307ok : treeCheck nodes v0 ⟨1179648,1310720,-4980736,-4718592⟩ t0x4307=true := by decide +kernel
def t0x2153 : Tree := .y (-4980736) t0x4306 t0x4307
lemma t0x2153ok : treeCheck nodes v0 ⟨1179648,1310720,-5242880,-4718592⟩ t0x2153=true := Bool.and_eq_true_iff.mpr ⟨t0x4306ok,t0x4307ok⟩
def t0x1076 : Tree := .d (1179648) t0x2152 t0x2153
lemma t0x1076ok : treeCheck nodes v0 ⟨1048576,1310720,-5242880,-4718592⟩ t0x1076=true := Bool.and_eq_true_iff.mpr ⟨t0x2152ok,t0x2153ok⟩
def t0x4308 : Tree := .leaf ⟨true,8322814,1179648,6935678,7106956,-4718592,-4456448⟩
lemma t0x4308ok : treeCheck nodes v0 ⟨1048576,1179648,-4718592,-4456448⟩ t0x4308=true := by decide +kernel
def t0x4309 : Tree := .leaf ⟨true,8322814,1179648,7106955,7264748,-4456448,-4194304⟩
lemma t0x4309ok : treeCheck nodes v0 ⟨1048576,1179648,-4456448,-4194304⟩ t0x4309=true := by decide +kernel
def t0x2154 : Tree := .y (-4456448) t0x4308 t0x4309
lemma t0x2154ok : treeCheck nodes v0 ⟨1048576,1179648,-4718592,-4194304⟩ t0x2154=true := Bool.and_eq_true_iff.mpr ⟨t0x4308ok,t0x4309ok⟩
def t0x4310 : Tree := .leaf ⟨true,8305250,1310720,6935678,7106956,-4718592,-4456448⟩
lemma t0x4310ok : treeCheck nodes v0 ⟨1179648,1310720,-4718592,-4456448⟩ t0x4310=true := by decide +kernel
def t0x4311 : Tree := .leaf ⟨true,8305250,1310720,7106955,7264748,-4456448,-4194304⟩
lemma t0x4311ok : treeCheck nodes v0 ⟨1179648,1310720,-4456448,-4194304⟩ t0x4311=true := by decide +kernel
def t0x2155 : Tree := .y (-4456448) t0x4310 t0x4311
lemma t0x2155ok : treeCheck nodes v0 ⟨1179648,1310720,-4718592,-4194304⟩ t0x2155=true := Bool.and_eq_true_iff.mpr ⟨t0x4310ok,t0x4311ok⟩
def t0x1077 : Tree := .d (1179648) t0x2154 t0x2155
lemma t0x1077ok : treeCheck nodes v0 ⟨1048576,1310720,-4718592,-4194304⟩ t0x1077=true := Bool.and_eq_true_iff.mpr ⟨t0x2154ok,t0x2155ok⟩
def t0x538 : Tree := .y (-4718592) t0x1076 t0x1077
lemma t0x538ok : treeCheck nodes v0 ⟨1048576,1310720,-5242880,-4194304⟩ t0x538=true := Bool.and_eq_true_iff.mpr ⟨t0x1076ok,t0x1077ok⟩
def t0x4312 : Tree := .leaf ⟨true,8285576,1441792,6548355,6749890,-5242880,-4980736⟩
lemma t0x4312ok : treeCheck nodes v0 ⟨1310720,1441792,-5242880,-4980736⟩ t0x4312=true := by decide +kernel
def t0x4313 : Tree := .leaf ⟨true,8285576,1441792,6749889,6935679,-4980736,-4718592⟩
lemma t0x4313ok : treeCheck nodes v0 ⟨1310720,1441792,-4980736,-4718592⟩ t0x4313=true := by decide +kernel
def t0x2156 : Tree := .y (-4980736) t0x4312 t0x4313
lemma t0x2156ok : treeCheck nodes v0 ⟨1310720,1441792,-5242880,-4718592⟩ t0x2156=true := Bool.and_eq_true_iff.mpr ⟨t0x4312ok,t0x4313ok⟩
def t0x4314 : Tree := .leaf ⟨true,8263776,1572864,6548355,6749890,-5242880,-4980736⟩
lemma t0x4314ok : treeCheck nodes v0 ⟨1441792,1572864,-5242880,-4980736⟩ t0x4314=true := by decide +kernel
def t0x4315 : Tree := .leaf ⟨true,8263776,1572864,6749889,6935679,-4980736,-4718592⟩
lemma t0x4315ok : treeCheck nodes v0 ⟨1441792,1572864,-4980736,-4718592⟩ t0x4315=true := by decide +kernel
def t0x2157 : Tree := .y (-4980736) t0x4314 t0x4315
lemma t0x2157ok : treeCheck nodes v0 ⟨1441792,1572864,-5242880,-4718592⟩ t0x2157=true := Bool.and_eq_true_iff.mpr ⟨t0x4314ok,t0x4315ok⟩
def t0x1078 : Tree := .d (1441792) t0x2156 t0x2157
lemma t0x1078ok : treeCheck nodes v0 ⟨1310720,1572864,-5242880,-4718592⟩ t0x1078=true := Bool.and_eq_true_iff.mpr ⟨t0x2156ok,t0x2157ok⟩
def t0x4316 : Tree := .leaf ⟨true,8285576,1441792,6935678,7106956,-4718592,-4456448⟩
lemma t0x4316ok : treeCheck nodes v0 ⟨1310720,1441792,-4718592,-4456448⟩ t0x4316=true := by decide +kernel
def t0x4317 : Tree := .leaf ⟨true,8285576,1441792,7106955,7264748,-4456448,-4194304⟩
lemma t0x4317ok : treeCheck nodes v0 ⟨1310720,1441792,-4456448,-4194304⟩ t0x4317=true := by decide +kernel
def t0x2158 : Tree := .y (-4456448) t0x4316 t0x4317
lemma t0x2158ok : treeCheck nodes v0 ⟨1310720,1441792,-4718592,-4194304⟩ t0x2158=true := Bool.and_eq_true_iff.mpr ⟨t0x4316ok,t0x4317ok⟩
def t0x4318 : Tree := .leaf ⟨true,8263776,1572864,6935678,7106956,-4718592,-4456448⟩
lemma t0x4318ok : treeCheck nodes v0 ⟨1441792,1572864,-4718592,-4456448⟩ t0x4318=true := by decide +kernel
def t0x4319 : Tree := .leaf ⟨true,8263776,1572864,7106955,7264748,-4456448,-4194304⟩
lemma t0x4319ok : treeCheck nodes v0 ⟨1441792,1572864,-4456448,-4194304⟩ t0x4319=true := by decide +kernel
def t0x2159 : Tree := .y (-4456448) t0x4318 t0x4319
lemma t0x2159ok : treeCheck nodes v0 ⟨1441792,1572864,-4718592,-4194304⟩ t0x2159=true := Bool.and_eq_true_iff.mpr ⟨t0x4318ok,t0x4319ok⟩
def t0x1079 : Tree := .d (1441792) t0x2158 t0x2159
lemma t0x1079ok : treeCheck nodes v0 ⟨1310720,1572864,-4718592,-4194304⟩ t0x1079=true := Bool.and_eq_true_iff.mpr ⟨t0x2158ok,t0x2159ok⟩
def t0x539 : Tree := .y (-4718592) t0x1078 t0x1079
lemma t0x539ok : treeCheck nodes v0 ⟨1310720,1572864,-5242880,-4194304⟩ t0x539=true := Bool.and_eq_true_iff.mpr ⟨t0x1078ok,t0x1079ok⟩
def t0x269 : Tree := .d (1310720) t0x538 t0x539
lemma t0x269ok : treeCheck nodes v0 ⟨1048576,1572864,-5242880,-4194304⟩ t0x269=true := Bool.and_eq_true_iff.mpr ⟨t0x538ok,t0x539ok⟩
def t0x134 : Tree := .y (-5242880) t0x268 t0x269
lemma t0x134ok : treeCheck nodes v0 ⟨1048576,1572864,-6291456,-4194304⟩ t0x134=true := Bool.and_eq_true_iff.mpr ⟨t0x268ok,t0x269ok⟩
def t0x1080 : Tree := .leaf ⟨true,8239833,1835008,5548542,6091677,-6291456,-5767168⟩
lemma t0x1080ok : treeCheck nodes v0 ⟨1572864,1835008,-6291456,-5767168⟩ t0x1080=true := by decide +kernel
def t0x1081 : Tree := .leaf ⟨true,8239833,1835008,6091676,6548356,-5767168,-5242880⟩
lemma t0x1081ok : treeCheck nodes v0 ⟨1572864,1835008,-5767168,-5242880⟩ t0x1081=true := by decide +kernel
def t0x540 : Tree := .y (-5767168) t0x1080 t0x1081
lemma t0x540ok : treeCheck nodes v0 ⟨1572864,1835008,-6291456,-5242880⟩ t0x540=true := Bool.and_eq_true_iff.mpr ⟨t0x1080ok,t0x1081ok⟩
def t0x1082 : Tree := .leaf ⟨true,8185444,2097152,5548542,6091677,-6291456,-5767168⟩
lemma t0x1082ok : treeCheck nodes v0 ⟨1835008,2097152,-6291456,-5767168⟩ t0x1082=true := by decide +kernel
def t0x1083 : Tree := .leaf ⟨true,8185444,2097152,6091676,6548356,-5767168,-5242880⟩
lemma t0x1083ok : treeCheck nodes v0 ⟨1835008,2097152,-5767168,-5242880⟩ t0x1083=true := by decide +kernel
def t0x541 : Tree := .y (-5767168) t0x1082 t0x1083
lemma t0x541ok : treeCheck nodes v0 ⟨1835008,2097152,-6291456,-5242880⟩ t0x541=true := Bool.and_eq_true_iff.mpr ⟨t0x1082ok,t0x1083ok⟩
def t0x270 : Tree := .d (1835008) t0x540 t0x541
lemma t0x270ok : treeCheck nodes v0 ⟨1572864,2097152,-6291456,-5242880⟩ t0x270=true := Bool.and_eq_true_iff.mpr ⟨t0x540ok,t0x541ok⟩
def t0x4336 : Tree := .leaf ⟨true,8239833,1703936,6548355,6749890,-5242880,-4980736⟩
lemma t0x4336ok : treeCheck nodes v0 ⟨1572864,1703936,-5242880,-4980736⟩ t0x4336=true := by decide +kernel
def t0x4337 : Tree := .leaf ⟨true,8239833,1703936,6749889,6935679,-4980736,-4718592⟩
lemma t0x4337ok : treeCheck nodes v0 ⟨1572864,1703936,-4980736,-4718592⟩ t0x4337=true := by decide +kernel
def t0x2168 : Tree := .y (-4980736) t0x4336 t0x4337
lemma t0x2168ok : treeCheck nodes v0 ⟨1572864,1703936,-5242880,-4718592⟩ t0x2168=true := Bool.and_eq_true_iff.mpr ⟨t0x4336ok,t0x4337ok⟩
def t0x4338 : Tree := .leaf ⟨true,8213730,1835008,6548355,6749890,-5242880,-4980736⟩
lemma t0x4338ok : treeCheck nodes v0 ⟨1703936,1835008,-5242880,-4980736⟩ t0x4338=true := by decide +kernel
def t0x4339 : Tree := .leaf ⟨true,8213730,1835008,6749889,6935679,-4980736,-4718592⟩
lemma t0x4339ok : treeCheck nodes v0 ⟨1703936,1835008,-4980736,-4718592⟩ t0x4339=true := by decide +kernel
def t0x2169 : Tree := .y (-4980736) t0x4338 t0x4339
lemma t0x2169ok : treeCheck nodes v0 ⟨1703936,1835008,-5242880,-4718592⟩ t0x2169=true := Bool.and_eq_true_iff.mpr ⟨t0x4338ok,t0x4339ok⟩
def t0x1084 : Tree := .d (1703936) t0x2168 t0x2169
lemma t0x1084ok : treeCheck nodes v0 ⟨1572864,1835008,-5242880,-4718592⟩ t0x1084=true := Bool.and_eq_true_iff.mpr ⟨t0x2168ok,t0x2169ok⟩
def t0x4340 : Tree := .leaf ⟨true,8239833,1703936,6935678,7106956,-4718592,-4456448⟩
lemma t0x4340ok : treeCheck nodes v0 ⟨1572864,1703936,-4718592,-4456448⟩ t0x4340=true := by decide +kernel
def t0x4341 : Tree := .leaf ⟨true,8239833,1703936,7106955,7264748,-4456448,-4194304⟩
lemma t0x4341ok : treeCheck nodes v0 ⟨1572864,1703936,-4456448,-4194304⟩ t0x4341=true := by decide +kernel
def t0x2170 : Tree := .y (-4456448) t0x4340 t0x4341
lemma t0x2170ok : treeCheck nodes v0 ⟨1572864,1703936,-4718592,-4194304⟩ t0x2170=true := Bool.and_eq_true_iff.mpr ⟨t0x4340ok,t0x4341ok⟩
def t0x4342 : Tree := .leaf ⟨true,8213730,1835008,6935678,7106956,-4718592,-4456448⟩
lemma t0x4342ok : treeCheck nodes v0 ⟨1703936,1835008,-4718592,-4456448⟩ t0x4342=true := by decide +kernel
def t0x4343 : Tree := .leaf ⟨true,8213730,1835008,7106955,7264748,-4456448,-4194304⟩
lemma t0x4343ok : treeCheck nodes v0 ⟨1703936,1835008,-4456448,-4194304⟩ t0x4343=true := by decide +kernel
def t0x2171 : Tree := .y (-4456448) t0x4342 t0x4343
lemma t0x2171ok : treeCheck nodes v0 ⟨1703936,1835008,-4718592,-4194304⟩ t0x2171=true := Bool.and_eq_true_iff.mpr ⟨t0x4342ok,t0x4343ok⟩
def t0x1085 : Tree := .d (1703936) t0x2170 t0x2171
lemma t0x1085ok : treeCheck nodes v0 ⟨1572864,1835008,-4718592,-4194304⟩ t0x1085=true := Bool.and_eq_true_iff.mpr ⟨t0x2170ok,t0x2171ok⟩
def t0x542 : Tree := .y (-4718592) t0x1084 t0x1085
lemma t0x542ok : treeCheck nodes v0 ⟨1572864,1835008,-5242880,-4194304⟩ t0x542=true := Bool.and_eq_true_iff.mpr ⟨t0x1084ok,t0x1085ok⟩
def t0x4344 : Tree := .leaf ⟨true,8185444,1966080,6548355,6749890,-5242880,-4980736⟩
lemma t0x4344ok : treeCheck nodes v0 ⟨1835008,1966080,-5242880,-4980736⟩ t0x4344=true := by decide +kernel
def t0x4345 : Tree := .leaf ⟨true,8185444,1966080,6749889,6935679,-4980736,-4718592⟩
lemma t0x4345ok : treeCheck nodes v0 ⟨1835008,1966080,-4980736,-4718592⟩ t0x4345=true := by decide +kernel
def t0x2172 : Tree := .y (-4980736) t0x4344 t0x4345
lemma t0x2172ok : treeCheck nodes v0 ⟨1835008,1966080,-5242880,-4718592⟩ t0x2172=true := Bool.and_eq_true_iff.mpr ⟨t0x4344ok,t0x4345ok⟩
def t0x2173 : Tree := .leaf ⟨true,8154954,2097152,6548355,6935679,-5242880,-4718592⟩
lemma t0x2173ok : treeCheck nodes v0 ⟨1966080,2097152,-5242880,-4718592⟩ t0x2173=true := by decide +kernel
def t0x1086 : Tree := .d (1966080) t0x2172 t0x2173
lemma t0x1086ok : treeCheck nodes v0 ⟨1835008,2097152,-5242880,-4718592⟩ t0x1086=true := Bool.and_eq_true_iff.mpr ⟨t0x2172ok,t0x2173ok⟩
def t0x4348 : Tree := .leaf ⟨true,8185444,1966080,6935678,7106956,-4718592,-4456448⟩
lemma t0x4348ok : treeCheck nodes v0 ⟨1835008,1966080,-4718592,-4456448⟩ t0x4348=true := by decide +kernel
def t0x4349 : Tree := .leaf ⟨true,8185444,1966080,7106955,7264748,-4456448,-4194304⟩
lemma t0x4349ok : treeCheck nodes v0 ⟨1835008,1966080,-4456448,-4194304⟩ t0x4349=true := by decide +kernel
def t0x2174 : Tree := .y (-4456448) t0x4348 t0x4349
lemma t0x2174ok : treeCheck nodes v0 ⟨1835008,1966080,-4718592,-4194304⟩ t0x2174=true := Bool.and_eq_true_iff.mpr ⟨t0x4348ok,t0x4349ok⟩
def t0x4350 : Tree := .leaf ⟨true,8154954,2097152,6935678,7106956,-4718592,-4456448⟩
lemma t0x4350ok : treeCheck nodes v0 ⟨1966080,2097152,-4718592,-4456448⟩ t0x4350=true := by decide +kernel
def t0x4351 : Tree := .leaf ⟨true,8154954,2097152,7106955,7264748,-4456448,-4194304⟩
lemma t0x4351ok : treeCheck nodes v0 ⟨1966080,2097152,-4456448,-4194304⟩ t0x4351=true := by decide +kernel
def t0x2175 : Tree := .y (-4456448) t0x4350 t0x4351
lemma t0x2175ok : treeCheck nodes v0 ⟨1966080,2097152,-4718592,-4194304⟩ t0x2175=true := Bool.and_eq_true_iff.mpr ⟨t0x4350ok,t0x4351ok⟩
def t0x1087 : Tree := .d (1966080) t0x2174 t0x2175
lemma t0x1087ok : treeCheck nodes v0 ⟨1835008,2097152,-4718592,-4194304⟩ t0x1087=true := Bool.and_eq_true_iff.mpr ⟨t0x2174ok,t0x2175ok⟩
def t0x543 : Tree := .y (-4718592) t0x1086 t0x1087
lemma t0x543ok : treeCheck nodes v0 ⟨1835008,2097152,-5242880,-4194304⟩ t0x543=true := Bool.and_eq_true_iff.mpr ⟨t0x1086ok,t0x1087ok⟩
def t0x271 : Tree := .d (1835008) t0x542 t0x543
lemma t0x271ok : treeCheck nodes v0 ⟨1572864,2097152,-5242880,-4194304⟩ t0x271=true := Bool.and_eq_true_iff.mpr ⟨t0x542ok,t0x543ok⟩
def t0x135 : Tree := .y (-5242880) t0x270 t0x271
lemma t0x135ok : treeCheck nodes v0 ⟨1572864,2097152,-6291456,-4194304⟩ t0x135=true := Bool.and_eq_true_iff.mpr ⟨t0x270ok,t0x271ok⟩
def t0x67 : Tree := .d (1572864) t0x134 t0x135
lemma t0x67ok : treeCheck nodes v0 ⟨1048576,2097152,-6291456,-4194304⟩ t0x67=true := Bool.and_eq_true_iff.mpr ⟨t0x134ok,t0x135ok⟩
def t0x33 : Tree := .y (-6291456) t0x66 t0x67
lemma t0x33ok : treeCheck nodes v0 ⟨1048576,2097152,-8388608,-4194304⟩ t0x33=true := Bool.and_eq_true_iff.mpr ⟨t0x66ok,t0x67ok⟩
def t0x16 : Tree := .d (1048576) t0x32 t0x33
lemma t0x16ok : treeCheck nodes v0 ⟨0,2097152,-8388608,-4194304⟩ t0x16=true := Bool.and_eq_true_iff.mpr ⟨t0x32ok,t0x33ok⟩
def t0x4352 : Tree := .leaf ⟨true,8388608,131072,7264747,7409917,-4194304,-3932160⟩
lemma t0x4352ok : treeCheck nodes v0 ⟨0,131072,-4194304,-3932160⟩ t0x4352=true := by decide +kernel
def t0x4353 : Tree := .leaf ⟨true,8388608,131072,7409916,7543191,-3932160,-3670016⟩
lemma t0x4353ok : treeCheck nodes v0 ⟨0,131072,-3932160,-3670016⟩ t0x4353=true := by decide +kernel
def t0x2176 : Tree := .y (-3932160) t0x4352 t0x4353
lemma t0x2176ok : treeCheck nodes v0 ⟨0,131072,-4194304,-3670016⟩ t0x2176=true := Bool.and_eq_true_iff.mpr ⟨t0x4352ok,t0x4353ok⟩
def t0x4354 : Tree := .leaf ⟨true,8387584,262144,7264747,7409917,-4194304,-3932160⟩
lemma t0x4354ok : treeCheck nodes v0 ⟨131072,262144,-4194304,-3932160⟩ t0x4354=true := by decide +kernel
def t0x4355 : Tree := .leaf ⟨true,8387584,262144,7409916,7543191,-3932160,-3670016⟩
lemma t0x4355ok : treeCheck nodes v0 ⟨131072,262144,-3932160,-3670016⟩ t0x4355=true := by decide +kernel
def t0x2177 : Tree := .y (-3932160) t0x4354 t0x4355
lemma t0x2177ok : treeCheck nodes v0 ⟨131072,262144,-4194304,-3670016⟩ t0x2177=true := Bool.and_eq_true_iff.mpr ⟨t0x4354ok,t0x4355ok⟩
def t0x1088 : Tree := .d (131072) t0x2176 t0x2177
lemma t0x1088ok : treeCheck nodes v0 ⟨0,262144,-4194304,-3670016⟩ t0x1088=true := Bool.and_eq_true_iff.mpr ⟨t0x2176ok,t0x2177ok⟩
def t0x1089 : Tree := .leaf ⟨true,8388608,262144,7543190,7776448,-3670016,-3145728⟩
lemma t0x1089ok : treeCheck nodes v0 ⟨0,262144,-3670016,-3145728⟩ t0x1089=true := by decide +kernel
def t0x544 : Tree := .y (-3670016) t0x1088 t0x1089
lemma t0x544ok : treeCheck nodes v0 ⟨0,262144,-4194304,-3145728⟩ t0x544=true := Bool.and_eq_true_iff.mpr ⟨t0x1088ok,t0x1089ok⟩
def t0x4360 : Tree := .leaf ⟨true,8384511,393216,7264747,7409917,-4194304,-3932160⟩
lemma t0x4360ok : treeCheck nodes v0 ⟨262144,393216,-4194304,-3932160⟩ t0x4360=true := by decide +kernel
def t0x4361 : Tree := .leaf ⟨true,8384511,393216,7409916,7543191,-3932160,-3670016⟩
lemma t0x4361ok : treeCheck nodes v0 ⟨262144,393216,-3932160,-3670016⟩ t0x4361=true := by decide +kernel
def t0x2180 : Tree := .y (-3932160) t0x4360 t0x4361
lemma t0x2180ok : treeCheck nodes v0 ⟨262144,393216,-4194304,-3670016⟩ t0x2180=true := Bool.and_eq_true_iff.mpr ⟨t0x4360ok,t0x4361ok⟩
def t0x4362 : Tree := .leaf ⟨true,8379387,524288,7264747,7409917,-4194304,-3932160⟩
lemma t0x4362ok : treeCheck nodes v0 ⟨393216,524288,-4194304,-3932160⟩ t0x4362=true := by decide +kernel
def t0x4363 : Tree := .leaf ⟨true,8379387,524288,7409916,7543191,-3932160,-3670016⟩
lemma t0x4363ok : treeCheck nodes v0 ⟨393216,524288,-3932160,-3670016⟩ t0x4363=true := by decide +kernel
def t0x2181 : Tree := .y (-3932160) t0x4362 t0x4363
lemma t0x2181ok : treeCheck nodes v0 ⟨393216,524288,-4194304,-3670016⟩ t0x2181=true := Bool.and_eq_true_iff.mpr ⟨t0x4362ok,t0x4363ok⟩
def t0x1090 : Tree := .d (393216) t0x2180 t0x2181
lemma t0x1090ok : treeCheck nodes v0 ⟨262144,524288,-4194304,-3670016⟩ t0x1090=true := Bool.and_eq_true_iff.mpr ⟨t0x2180ok,t0x2181ok⟩
def t0x1091 : Tree := .leaf ⟨true,8384511,524288,7543190,7776448,-3670016,-3145728⟩
lemma t0x1091ok : treeCheck nodes v0 ⟨262144,524288,-3670016,-3145728⟩ t0x1091=true := by decide +kernel
def t0x545 : Tree := .y (-3670016) t0x1090 t0x1091
lemma t0x545ok : treeCheck nodes v0 ⟨262144,524288,-4194304,-3145728⟩ t0x545=true := Bool.and_eq_true_iff.mpr ⟨t0x1090ok,t0x1091ok⟩
def t0x272 : Tree := .d (262144) t0x544 t0x545
lemma t0x272ok : treeCheck nodes v0 ⟨0,524288,-4194304,-3145728⟩ t0x272=true := Bool.and_eq_true_iff.mpr ⟨t0x544ok,t0x545ok⟩
def t0x1092 : Tree := .leaf ⟨true,8388608,262144,7776447,7968488,-3145728,-2621440⟩
lemma t0x1092ok : treeCheck nodes v0 ⟨0,262144,-3145728,-2621440⟩ t0x1092=true := by decide +kernel
def t0x1093 : Tree := .leaf ⟨true,8388608,262144,7968487,8122235,-2621440,-2097152⟩
lemma t0x1093ok : treeCheck nodes v0 ⟨0,262144,-2621440,-2097152⟩ t0x1093=true := by decide +kernel
def t0x546 : Tree := .y (-2621440) t0x1092 t0x1093
lemma t0x546ok : treeCheck nodes v0 ⟨0,262144,-3145728,-2097152⟩ t0x546=true := Bool.and_eq_true_iff.mpr ⟨t0x1092ok,t0x1093ok⟩
def t0x1094 : Tree := .leaf ⟨true,8384511,524288,7776447,7968488,-3145728,-2621440⟩
lemma t0x1094ok : treeCheck nodes v0 ⟨262144,524288,-3145728,-2621440⟩ t0x1094=true := by decide +kernel
def t0x1095 : Tree := .leaf ⟨true,8384511,524288,7968487,8122235,-2621440,-2097152⟩
lemma t0x1095ok : treeCheck nodes v0 ⟨262144,524288,-2621440,-2097152⟩ t0x1095=true := by decide +kernel
def t0x547 : Tree := .y (-2621440) t0x1094 t0x1095
lemma t0x547ok : treeCheck nodes v0 ⟨262144,524288,-3145728,-2097152⟩ t0x547=true := Bool.and_eq_true_iff.mpr ⟨t0x1094ok,t0x1095ok⟩
def t0x273 : Tree := .d (262144) t0x546 t0x547
lemma t0x273ok : treeCheck nodes v0 ⟨0,524288,-3145728,-2097152⟩ t0x273=true := Bool.and_eq_true_iff.mpr ⟨t0x546ok,t0x547ok⟩
def t0x136 : Tree := .y (-3145728) t0x272 t0x273
lemma t0x136ok : treeCheck nodes v0 ⟨0,524288,-4194304,-2097152⟩ t0x136=true := Bool.and_eq_true_iff.mpr ⟨t0x272ok,t0x273ok⟩
def t0x4384 : Tree := .leaf ⟨true,8372208,655360,7264747,7409917,-4194304,-3932160⟩
lemma t0x4384ok : treeCheck nodes v0 ⟨524288,655360,-4194304,-3932160⟩ t0x4384=true := by decide +kernel
def t0x4385 : Tree := .leaf ⟨true,8372208,655360,7409916,7543191,-3932160,-3670016⟩
lemma t0x4385ok : treeCheck nodes v0 ⟨524288,655360,-3932160,-3670016⟩ t0x4385=true := by decide +kernel
def t0x2192 : Tree := .y (-3932160) t0x4384 t0x4385
lemma t0x2192ok : treeCheck nodes v0 ⟨524288,655360,-4194304,-3670016⟩ t0x2192=true := Bool.and_eq_true_iff.mpr ⟨t0x4384ok,t0x4385ok⟩
def t0x4386 : Tree := .leaf ⟨true,8362969,786432,7264747,7409917,-4194304,-3932160⟩
lemma t0x4386ok : treeCheck nodes v0 ⟨655360,786432,-4194304,-3932160⟩ t0x4386=true := by decide +kernel
def t0x4387 : Tree := .leaf ⟨true,8362969,786432,7409916,7543191,-3932160,-3670016⟩
lemma t0x4387ok : treeCheck nodes v0 ⟨655360,786432,-3932160,-3670016⟩ t0x4387=true := by decide +kernel
def t0x2193 : Tree := .y (-3932160) t0x4386 t0x4387
lemma t0x2193ok : treeCheck nodes v0 ⟨655360,786432,-4194304,-3670016⟩ t0x2193=true := Bool.and_eq_true_iff.mpr ⟨t0x4386ok,t0x4387ok⟩
def t0x1096 : Tree := .d (655360) t0x2192 t0x2193
lemma t0x1096ok : treeCheck nodes v0 ⟨524288,786432,-4194304,-3670016⟩ t0x1096=true := Bool.and_eq_true_iff.mpr ⟨t0x2192ok,t0x2193ok⟩
def t0x1097 : Tree := .leaf ⟨true,8372208,786432,7543190,7776448,-3670016,-3145728⟩
lemma t0x1097ok : treeCheck nodes v0 ⟨524288,786432,-3670016,-3145728⟩ t0x1097=true := by decide +kernel
def t0x548 : Tree := .y (-3670016) t0x1096 t0x1097
lemma t0x548ok : treeCheck nodes v0 ⟨524288,786432,-4194304,-3145728⟩ t0x548=true := Bool.and_eq_true_iff.mpr ⟨t0x1096ok,t0x1097ok⟩
def t0x4392 : Tree := .leaf ⟨true,8351663,917504,7264747,7409917,-4194304,-3932160⟩
lemma t0x4392ok : treeCheck nodes v0 ⟨786432,917504,-4194304,-3932160⟩ t0x4392=true := by decide +kernel
def t0x4393 : Tree := .leaf ⟨true,8351663,917504,7409916,7543191,-3932160,-3670016⟩
lemma t0x4393ok : treeCheck nodes v0 ⟨786432,917504,-3932160,-3670016⟩ t0x4393=true := by decide +kernel
def t0x2196 : Tree := .y (-3932160) t0x4392 t0x4393
lemma t0x2196ok : treeCheck nodes v0 ⟨786432,917504,-4194304,-3670016⟩ t0x2196=true := Bool.and_eq_true_iff.mpr ⟨t0x4392ok,t0x4393ok⟩
def t0x4394 : Tree := .leaf ⟨true,8338282,1048576,7264747,7409917,-4194304,-3932160⟩
lemma t0x4394ok : treeCheck nodes v0 ⟨917504,1048576,-4194304,-3932160⟩ t0x4394=true := by decide +kernel
def t0x4395 : Tree := .leaf ⟨true,8338282,1048576,7409916,7543191,-3932160,-3670016⟩
lemma t0x4395ok : treeCheck nodes v0 ⟨917504,1048576,-3932160,-3670016⟩ t0x4395=true := by decide +kernel
def t0x2197 : Tree := .y (-3932160) t0x4394 t0x4395
lemma t0x2197ok : treeCheck nodes v0 ⟨917504,1048576,-4194304,-3670016⟩ t0x2197=true := Bool.and_eq_true_iff.mpr ⟨t0x4394ok,t0x4395ok⟩
def t0x1098 : Tree := .d (917504) t0x2196 t0x2197
lemma t0x1098ok : treeCheck nodes v0 ⟨786432,1048576,-4194304,-3670016⟩ t0x1098=true := Bool.and_eq_true_iff.mpr ⟨t0x2196ok,t0x2197ok⟩
def t0x1099 : Tree := .leaf ⟨true,8351663,1048576,7543190,7776448,-3670016,-3145728⟩
lemma t0x1099ok : treeCheck nodes v0 ⟨786432,1048576,-3670016,-3145728⟩ t0x1099=true := by decide +kernel
def t0x549 : Tree := .y (-3670016) t0x1098 t0x1099
lemma t0x549ok : treeCheck nodes v0 ⟨786432,1048576,-4194304,-3145728⟩ t0x549=true := Bool.and_eq_true_iff.mpr ⟨t0x1098ok,t0x1099ok⟩
def t0x274 : Tree := .d (786432) t0x548 t0x549
lemma t0x274ok : treeCheck nodes v0 ⟨524288,1048576,-4194304,-3145728⟩ t0x274=true := Bool.and_eq_true_iff.mpr ⟨t0x548ok,t0x549ok⟩
def t0x1100 : Tree := .leaf ⟨true,8372208,786432,7776447,7968488,-3145728,-2621440⟩
lemma t0x1100ok : treeCheck nodes v0 ⟨524288,786432,-3145728,-2621440⟩ t0x1100=true := by decide +kernel
def t0x1101 : Tree := .leaf ⟨true,8372208,786432,7968487,8122235,-2621440,-2097152⟩
lemma t0x1101ok : treeCheck nodes v0 ⟨524288,786432,-2621440,-2097152⟩ t0x1101=true := by decide +kernel
def t0x550 : Tree := .y (-2621440) t0x1100 t0x1101
lemma t0x550ok : treeCheck nodes v0 ⟨524288,786432,-3145728,-2097152⟩ t0x550=true := Bool.and_eq_true_iff.mpr ⟨t0x1100ok,t0x1101ok⟩
def t0x1102 : Tree := .leaf ⟨true,8351663,1048576,7776447,7968488,-3145728,-2621440⟩
lemma t0x1102ok : treeCheck nodes v0 ⟨786432,1048576,-3145728,-2621440⟩ t0x1102=true := by decide +kernel
def t0x1103 : Tree := .leaf ⟨true,8351663,1048576,7968487,8122235,-2621440,-2097152⟩
lemma t0x1103ok : treeCheck nodes v0 ⟨786432,1048576,-2621440,-2097152⟩ t0x1103=true := by decide +kernel
def t0x551 : Tree := .y (-2621440) t0x1102 t0x1103
lemma t0x551ok : treeCheck nodes v0 ⟨786432,1048576,-3145728,-2097152⟩ t0x551=true := Bool.and_eq_true_iff.mpr ⟨t0x1102ok,t0x1103ok⟩
def t0x275 : Tree := .d (786432) t0x550 t0x551
lemma t0x275ok : treeCheck nodes v0 ⟨524288,1048576,-3145728,-2097152⟩ t0x275=true := Bool.and_eq_true_iff.mpr ⟨t0x550ok,t0x551ok⟩
def t0x137 : Tree := .y (-3145728) t0x274 t0x275
lemma t0x137ok : treeCheck nodes v0 ⟨524288,1048576,-4194304,-2097152⟩ t0x137=true := Bool.and_eq_true_iff.mpr ⟨t0x274ok,t0x275ok⟩
def t0x68 : Tree := .d (524288) t0x136 t0x137
lemma t0x68ok : treeCheck nodes v0 ⟨0,1048576,-4194304,-2097152⟩ t0x68=true := Bool.and_eq_true_iff.mpr ⟨t0x136ok,t0x137ok⟩
def t0x69 : Tree := .leaf ⟨true,8388608,1048576,8122234,8388608,-2097152,0⟩
lemma t0x69ok : treeCheck nodes v0 ⟨0,1048576,-2097152,0⟩ t0x69=true := by decide +kernel
def t0x34 : Tree := .y (-2097152) t0x68 t0x69
lemma t0x34ok : treeCheck nodes v0 ⟨0,1048576,-4194304,0⟩ t0x34=true := Bool.and_eq_true_iff.mpr ⟨t0x68ok,t0x69ok⟩
def t0x4480 : Tree := .leaf ⟨true,8322814,1179648,7264747,7409917,-4194304,-3932160⟩
lemma t0x4480ok : treeCheck nodes v0 ⟨1048576,1179648,-4194304,-3932160⟩ t0x4480=true := by decide +kernel
def t0x4481 : Tree := .leaf ⟨true,8322814,1179648,7409916,7543191,-3932160,-3670016⟩
lemma t0x4481ok : treeCheck nodes v0 ⟨1048576,1179648,-3932160,-3670016⟩ t0x4481=true := by decide +kernel
def t0x2240 : Tree := .y (-3932160) t0x4480 t0x4481
lemma t0x2240ok : treeCheck nodes v0 ⟨1048576,1179648,-4194304,-3670016⟩ t0x2240=true := Bool.and_eq_true_iff.mpr ⟨t0x4480ok,t0x4481ok⟩
def t0x4482 : Tree := .leaf ⟨true,8305250,1310720,7264747,7409917,-4194304,-3932160⟩
lemma t0x4482ok : treeCheck nodes v0 ⟨1179648,1310720,-4194304,-3932160⟩ t0x4482=true := by decide +kernel
def t0x4483 : Tree := .leaf ⟨true,8305250,1310720,7409916,7543191,-3932160,-3670016⟩
lemma t0x4483ok : treeCheck nodes v0 ⟨1179648,1310720,-3932160,-3670016⟩ t0x4483=true := by decide +kernel
def t0x2241 : Tree := .y (-3932160) t0x4482 t0x4483
lemma t0x2241ok : treeCheck nodes v0 ⟨1179648,1310720,-4194304,-3670016⟩ t0x2241=true := Bool.and_eq_true_iff.mpr ⟨t0x4482ok,t0x4483ok⟩
def t0x1120 : Tree := .d (1179648) t0x2240 t0x2241
lemma t0x1120ok : treeCheck nodes v0 ⟨1048576,1310720,-4194304,-3670016⟩ t0x1120=true := Bool.and_eq_true_iff.mpr ⟨t0x2240ok,t0x2241ok⟩
def t0x1121 : Tree := .leaf ⟨true,8322814,1310720,7543190,7776448,-3670016,-3145728⟩
lemma t0x1121ok : treeCheck nodes v0 ⟨1048576,1310720,-3670016,-3145728⟩ t0x1121=true := by decide +kernel
def t0x560 : Tree := .y (-3670016) t0x1120 t0x1121
lemma t0x560ok : treeCheck nodes v0 ⟨1048576,1310720,-4194304,-3145728⟩ t0x560=true := Bool.and_eq_true_iff.mpr ⟨t0x1120ok,t0x1121ok⟩
def t0x4488 : Tree := .leaf ⟨true,8285576,1441792,7264747,7409917,-4194304,-3932160⟩
lemma t0x4488ok : treeCheck nodes v0 ⟨1310720,1441792,-4194304,-3932160⟩ t0x4488=true := by decide +kernel
def t0x4489 : Tree := .leaf ⟨true,8285576,1441792,7409916,7543191,-3932160,-3670016⟩
lemma t0x4489ok : treeCheck nodes v0 ⟨1310720,1441792,-3932160,-3670016⟩ t0x4489=true := by decide +kernel
def t0x2244 : Tree := .y (-3932160) t0x4488 t0x4489
lemma t0x2244ok : treeCheck nodes v0 ⟨1310720,1441792,-4194304,-3670016⟩ t0x2244=true := Bool.and_eq_true_iff.mpr ⟨t0x4488ok,t0x4489ok⟩
def t0x4490 : Tree := .leaf ⟨true,8263776,1572864,7264747,7409917,-4194304,-3932160⟩
lemma t0x4490ok : treeCheck nodes v0 ⟨1441792,1572864,-4194304,-3932160⟩ t0x4490=true := by decide +kernel
def t0x4491 : Tree := .leaf ⟨true,8263776,1572864,7409916,7543191,-3932160,-3670016⟩
lemma t0x4491ok : treeCheck nodes v0 ⟨1441792,1572864,-3932160,-3670016⟩ t0x4491=true := by decide +kernel
def t0x2245 : Tree := .y (-3932160) t0x4490 t0x4491
lemma t0x2245ok : treeCheck nodes v0 ⟨1441792,1572864,-4194304,-3670016⟩ t0x2245=true := Bool.and_eq_true_iff.mpr ⟨t0x4490ok,t0x4491ok⟩
def t0x1122 : Tree := .d (1441792) t0x2244 t0x2245
lemma t0x1122ok : treeCheck nodes v0 ⟨1310720,1572864,-4194304,-3670016⟩ t0x1122=true := Bool.and_eq_true_iff.mpr ⟨t0x2244ok,t0x2245ok⟩
def t0x1123 : Tree := .leaf ⟨true,8285576,1572864,7543190,7776448,-3670016,-3145728⟩
lemma t0x1123ok : treeCheck nodes v0 ⟨1310720,1572864,-3670016,-3145728⟩ t0x1123=true := by decide +kernel
def t0x561 : Tree := .y (-3670016) t0x1122 t0x1123
lemma t0x561ok : treeCheck nodes v0 ⟨1310720,1572864,-4194304,-3145728⟩ t0x561=true := Bool.and_eq_true_iff.mpr ⟨t0x1122ok,t0x1123ok⟩
def t0x280 : Tree := .d (1310720) t0x560 t0x561
lemma t0x280ok : treeCheck nodes v0 ⟨1048576,1572864,-4194304,-3145728⟩ t0x280=true := Bool.and_eq_true_iff.mpr ⟨t0x560ok,t0x561ok⟩
def t0x1124 : Tree := .leaf ⟨true,8322814,1310720,7776447,7968488,-3145728,-2621440⟩
lemma t0x1124ok : treeCheck nodes v0 ⟨1048576,1310720,-3145728,-2621440⟩ t0x1124=true := by decide +kernel
def t0x1125 : Tree := .leaf ⟨true,8322814,1310720,7968487,8122235,-2621440,-2097152⟩
lemma t0x1125ok : treeCheck nodes v0 ⟨1048576,1310720,-2621440,-2097152⟩ t0x1125=true := by decide +kernel
def t0x562 : Tree := .y (-2621440) t0x1124 t0x1125
lemma t0x562ok : treeCheck nodes v0 ⟨1048576,1310720,-3145728,-2097152⟩ t0x562=true := Bool.and_eq_true_iff.mpr ⟨t0x1124ok,t0x1125ok⟩
def t0x1126 : Tree := .leaf ⟨true,8285576,1572864,7776447,7968488,-3145728,-2621440⟩
lemma t0x1126ok : treeCheck nodes v0 ⟨1310720,1572864,-3145728,-2621440⟩ t0x1126=true := by decide +kernel
def t0x1127 : Tree := .leaf ⟨true,8285576,1572864,7968487,8122235,-2621440,-2097152⟩
lemma t0x1127ok : treeCheck nodes v0 ⟨1310720,1572864,-2621440,-2097152⟩ t0x1127=true := by decide +kernel
def t0x563 : Tree := .y (-2621440) t0x1126 t0x1127
lemma t0x563ok : treeCheck nodes v0 ⟨1310720,1572864,-3145728,-2097152⟩ t0x563=true := Bool.and_eq_true_iff.mpr ⟨t0x1126ok,t0x1127ok⟩
def t0x281 : Tree := .d (1310720) t0x562 t0x563
lemma t0x281ok : treeCheck nodes v0 ⟨1048576,1572864,-3145728,-2097152⟩ t0x281=true := Bool.and_eq_true_iff.mpr ⟨t0x562ok,t0x563ok⟩
def t0x140 : Tree := .y (-3145728) t0x280 t0x281
lemma t0x140ok : treeCheck nodes v0 ⟨1048576,1572864,-4194304,-2097152⟩ t0x140=true := Bool.and_eq_true_iff.mpr ⟨t0x280ok,t0x281ok⟩
def t0x4512 : Tree := .leaf ⟨true,8239833,1703936,7264747,7409917,-4194304,-3932160⟩
lemma t0x4512ok : treeCheck nodes v0 ⟨1572864,1703936,-4194304,-3932160⟩ t0x4512=true := by decide +kernel
def t0x4513 : Tree := .leaf ⟨true,8239833,1703936,7409916,7543191,-3932160,-3670016⟩
lemma t0x4513ok : treeCheck nodes v0 ⟨1572864,1703936,-3932160,-3670016⟩ t0x4513=true := by decide +kernel
def t0x2256 : Tree := .y (-3932160) t0x4512 t0x4513
lemma t0x2256ok : treeCheck nodes v0 ⟨1572864,1703936,-4194304,-3670016⟩ t0x2256=true := Bool.and_eq_true_iff.mpr ⟨t0x4512ok,t0x4513ok⟩
def t0x2257 : Tree := .leaf ⟨true,8213730,1835008,7264747,7543191,-4194304,-3670016⟩
lemma t0x2257ok : treeCheck nodes v0 ⟨1703936,1835008,-4194304,-3670016⟩ t0x2257=true := by decide +kernel
def t0x1128 : Tree := .d (1703936) t0x2256 t0x2257
lemma t0x1128ok : treeCheck nodes v0 ⟨1572864,1835008,-4194304,-3670016⟩ t0x1128=true := Bool.and_eq_true_iff.mpr ⟨t0x2256ok,t0x2257ok⟩
def t0x1129 : Tree := .leaf ⟨true,8239833,1835008,7543190,7776448,-3670016,-3145728⟩
lemma t0x1129ok : treeCheck nodes v0 ⟨1572864,1835008,-3670016,-3145728⟩ t0x1129=true := by decide +kernel
def t0x564 : Tree := .y (-3670016) t0x1128 t0x1129
lemma t0x564ok : treeCheck nodes v0 ⟨1572864,1835008,-4194304,-3145728⟩ t0x564=true := Bool.and_eq_true_iff.mpr ⟨t0x1128ok,t0x1129ok⟩
def t0x2260 : Tree := .leaf ⟨true,8185444,1966080,7264747,7543191,-4194304,-3670016⟩
lemma t0x2260ok : treeCheck nodes v0 ⟨1835008,1966080,-4194304,-3670016⟩ t0x2260=true := by decide +kernel
def t0x2261 : Tree := .leaf ⟨true,8154954,2097152,7264747,7543191,-4194304,-3670016⟩
lemma t0x2261ok : treeCheck nodes v0 ⟨1966080,2097152,-4194304,-3670016⟩ t0x2261=true := by decide +kernel
def t0x1130 : Tree := .d (1966080) t0x2260 t0x2261
lemma t0x1130ok : treeCheck nodes v0 ⟨1835008,2097152,-4194304,-3670016⟩ t0x1130=true := Bool.and_eq_true_iff.mpr ⟨t0x2260ok,t0x2261ok⟩
def t0x1131 : Tree := .leaf ⟨true,8185444,2097152,7543190,7776448,-3670016,-3145728⟩
lemma t0x1131ok : treeCheck nodes v0 ⟨1835008,2097152,-3670016,-3145728⟩ t0x1131=true := by decide +kernel
def t0x565 : Tree := .y (-3670016) t0x1130 t0x1131
lemma t0x565ok : treeCheck nodes v0 ⟨1835008,2097152,-4194304,-3145728⟩ t0x565=true := Bool.and_eq_true_iff.mpr ⟨t0x1130ok,t0x1131ok⟩
def t0x282 : Tree := .d (1835008) t0x564 t0x565
lemma t0x282ok : treeCheck nodes v0 ⟨1572864,2097152,-4194304,-3145728⟩ t0x282=true := Bool.and_eq_true_iff.mpr ⟨t0x564ok,t0x565ok⟩
def t0x566 : Tree := .leaf ⟨true,8239833,1835008,7776447,8122235,-3145728,-2097152⟩
lemma t0x566ok : treeCheck nodes v0 ⟨1572864,1835008,-3145728,-2097152⟩ t0x566=true := by decide +kernel
def t0x567 : Tree := .leaf ⟨true,8185444,2097152,7776447,8122235,-3145728,-2097152⟩
lemma t0x567ok : treeCheck nodes v0 ⟨1835008,2097152,-3145728,-2097152⟩ t0x567=true := by decide +kernel
def t0x283 : Tree := .d (1835008) t0x566 t0x567
lemma t0x283ok : treeCheck nodes v0 ⟨1572864,2097152,-3145728,-2097152⟩ t0x283=true := Bool.and_eq_true_iff.mpr ⟨t0x566ok,t0x567ok⟩
def t0x141 : Tree := .y (-3145728) t0x282 t0x283
lemma t0x141ok : treeCheck nodes v0 ⟨1572864,2097152,-4194304,-2097152⟩ t0x141=true := Bool.and_eq_true_iff.mpr ⟨t0x282ok,t0x283ok⟩
def t0x70 : Tree := .d (1572864) t0x140 t0x141
lemma t0x70ok : treeCheck nodes v0 ⟨1048576,2097152,-4194304,-2097152⟩ t0x70=true := Bool.and_eq_true_iff.mpr ⟨t0x140ok,t0x141ok⟩
def t0x71 : Tree := .leaf ⟨true,8322814,2097152,8122234,8388608,-2097152,0⟩
lemma t0x71ok : treeCheck nodes v0 ⟨1048576,2097152,-2097152,0⟩ t0x71=true := by decide +kernel
def t0x35 : Tree := .y (-2097152) t0x70 t0x71
lemma t0x35ok : treeCheck nodes v0 ⟨1048576,2097152,-4194304,0⟩ t0x35=true := Bool.and_eq_true_iff.mpr ⟨t0x70ok,t0x71ok⟩
def t0x17 : Tree := .d (1048576) t0x34 t0x35
lemma t0x17ok : treeCheck nodes v0 ⟨0,2097152,-4194304,0⟩ t0x17=true := Bool.and_eq_true_iff.mpr ⟨t0x34ok,t0x35ok⟩
def t0x8 : Tree := .y (-4194304) t0x16 t0x17
lemma t0x8ok : treeCheck nodes v0 ⟨0,2097152,-8388608,0⟩ t0x8=true := Bool.and_eq_true_iff.mpr ⟨t0x16ok,t0x17ok⟩
def t0x288 : Tree := .leaf ⟨true,8122235,2621440,0,4061118,-8388608,-7340032⟩
lemma t0x288ok : treeCheck nodes v0 ⟨2097152,2621440,-8388608,-7340032⟩ t0x288=true := by decide +kernel
def t0x1156 : Tree := .leaf ⟨true,8122235,2359296,4061117,4890233,-7340032,-6815744⟩
lemma t0x1156ok : treeCheck nodes v0 ⟨2097152,2359296,-7340032,-6815744⟩ t0x1156=true := by decide +kernel
def t0x1157 : Tree := .leaf ⟨true,8122235,2359296,4890232,5548543,-6815744,-6291456⟩
lemma t0x1157ok : treeCheck nodes v0 ⟨2097152,2359296,-6815744,-6291456⟩ t0x1157=true := by decide +kernel
def t0x578 : Tree := .y (-6815744) t0x1156 t0x1157
lemma t0x578ok : treeCheck nodes v0 ⟨2097152,2359296,-7340032,-6291456⟩ t0x578=true := Bool.and_eq_true_iff.mpr ⟨t0x1156ok,t0x1157ok⟩
def t0x579 : Tree := .leaf ⟨true,8049998,2621440,4061117,5548543,-7340032,-6291456⟩
lemma t0x579ok : treeCheck nodes v0 ⟨2359296,2621440,-7340032,-6291456⟩ t0x579=true := by decide +kernel
def t0x289 : Tree := .d (2359296) t0x578 t0x579
lemma t0x289ok : treeCheck nodes v0 ⟨2097152,2621440,-7340032,-6291456⟩ t0x289=true := Bool.and_eq_true_iff.mpr ⟨t0x578ok,t0x579ok⟩
def t0x144 : Tree := .y (-7340032) t0x288 t0x289
lemma t0x144ok : treeCheck nodes v0 ⟨2097152,2621440,-8388608,-6291456⟩ t0x144=true := Bool.and_eq_true_iff.mpr ⟨t0x288ok,t0x289ok⟩
def t0x290 : Tree := .leaf ⟨true,7968488,3145728,0,4061118,-8388608,-7340032⟩
lemma t0x290ok : treeCheck nodes v0 ⟨2621440,3145728,-8388608,-7340032⟩ t0x290=true := by decide +kernel
def t0x582 : Tree := .leaf ⟨true,7968488,2883584,4061117,5548543,-7340032,-6291456⟩
lemma t0x582ok : treeCheck nodes v0 ⟨2621440,2883584,-7340032,-6291456⟩ t0x582=true := by decide +kernel
def t0x583 : Tree := .leaf ⟨true,7877417,3145728,4061117,5548543,-7340032,-6291456⟩
lemma t0x583ok : treeCheck nodes v0 ⟨2883584,3145728,-7340032,-6291456⟩ t0x583=true := by decide +kernel
def t0x291 : Tree := .d (2883584) t0x582 t0x583
lemma t0x291ok : treeCheck nodes v0 ⟨2621440,3145728,-7340032,-6291456⟩ t0x291=true := Bool.and_eq_true_iff.mpr ⟨t0x582ok,t0x583ok⟩
def t0x145 : Tree := .y (-7340032) t0x290 t0x291
lemma t0x145ok : treeCheck nodes v0 ⟨2621440,3145728,-8388608,-6291456⟩ t0x145=true := Bool.and_eq_true_iff.mpr ⟨t0x290ok,t0x291ok⟩
def t0x72 : Tree := .d (2621440) t0x144 t0x145
lemma t0x72ok : treeCheck nodes v0 ⟨2097152,3145728,-8388608,-6291456⟩ t0x72=true := Bool.and_eq_true_iff.mpr ⟨t0x144ok,t0x145ok⟩
def t0x1168 : Tree := .leaf ⟨true,8122235,2359296,5548542,6091677,-6291456,-5767168⟩
lemma t0x1168ok : treeCheck nodes v0 ⟨2097152,2359296,-6291456,-5767168⟩ t0x1168=true := by decide +kernel
def t0x1169 : Tree := .leaf ⟨true,8122235,2359296,6091676,6548356,-5767168,-5242880⟩
lemma t0x1169ok : treeCheck nodes v0 ⟨2097152,2359296,-5767168,-5242880⟩ t0x1169=true := by decide +kernel
def t0x584 : Tree := .y (-5767168) t0x1168 t0x1169
lemma t0x584ok : treeCheck nodes v0 ⟨2097152,2359296,-6291456,-5242880⟩ t0x584=true := Bool.and_eq_true_iff.mpr ⟨t0x1168ok,t0x1169ok⟩
def t0x1170 : Tree := .leaf ⟨true,8049998,2621440,5548542,6091677,-6291456,-5767168⟩
lemma t0x1170ok : treeCheck nodes v0 ⟨2359296,2621440,-6291456,-5767168⟩ t0x1170=true := by decide +kernel
def t0x1171 : Tree := .leaf ⟨true,8049998,2621440,6091676,6548356,-5767168,-5242880⟩
lemma t0x1171ok : treeCheck nodes v0 ⟨2359296,2621440,-5767168,-5242880⟩ t0x1171=true := by decide +kernel
def t0x585 : Tree := .y (-5767168) t0x1170 t0x1171
lemma t0x585ok : treeCheck nodes v0 ⟨2359296,2621440,-6291456,-5242880⟩ t0x585=true := Bool.and_eq_true_iff.mpr ⟨t0x1170ok,t0x1171ok⟩
def t0x292 : Tree := .d (2359296) t0x584 t0x585
lemma t0x292ok : treeCheck nodes v0 ⟨2097152,2621440,-6291456,-5242880⟩ t0x292=true := Bool.and_eq_true_iff.mpr ⟨t0x584ok,t0x585ok⟩
def t0x2344 : Tree := .leaf ⟨true,8122235,2228224,6548355,6935679,-5242880,-4718592⟩
lemma t0x2344ok : treeCheck nodes v0 ⟨2097152,2228224,-5242880,-4718592⟩ t0x2344=true := by decide +kernel
def t0x2345 : Tree := .leaf ⟨true,8087260,2359296,6548355,6935679,-5242880,-4718592⟩
lemma t0x2345ok : treeCheck nodes v0 ⟨2228224,2359296,-5242880,-4718592⟩ t0x2345=true := by decide +kernel
def t0x1172 : Tree := .d (2228224) t0x2344 t0x2345
lemma t0x1172ok : treeCheck nodes v0 ⟨2097152,2359296,-5242880,-4718592⟩ t0x1172=true := Bool.and_eq_true_iff.mpr ⟨t0x2344ok,t0x2345ok⟩
def t0x2346 : Tree := .leaf ⟨true,8122235,2228224,6935678,7264748,-4718592,-4194304⟩
lemma t0x2346ok : treeCheck nodes v0 ⟨2097152,2228224,-4718592,-4194304⟩ t0x2346=true := by decide +kernel
def t0x2347 : Tree := .leaf ⟨true,8087260,2359296,6935678,7264748,-4718592,-4194304⟩
lemma t0x2347ok : treeCheck nodes v0 ⟨2228224,2359296,-4718592,-4194304⟩ t0x2347=true := by decide +kernel
def t0x1173 : Tree := .d (2228224) t0x2346 t0x2347
lemma t0x1173ok : treeCheck nodes v0 ⟨2097152,2359296,-4718592,-4194304⟩ t0x1173=true := Bool.and_eq_true_iff.mpr ⟨t0x2346ok,t0x2347ok⟩
def t0x586 : Tree := .y (-4718592) t0x1172 t0x1173
lemma t0x586ok : treeCheck nodes v0 ⟨2097152,2359296,-5242880,-4194304⟩ t0x586=true := Bool.and_eq_true_iff.mpr ⟨t0x1172ok,t0x1173ok⟩
def t0x1174 : Tree := .leaf ⟨true,8049998,2621440,6548355,6935679,-5242880,-4718592⟩
lemma t0x1174ok : treeCheck nodes v0 ⟨2359296,2621440,-5242880,-4718592⟩ t0x1174=true := by decide +kernel
def t0x1175 : Tree := .leaf ⟨true,8049998,2621440,6935678,7264748,-4718592,-4194304⟩
lemma t0x1175ok : treeCheck nodes v0 ⟨2359296,2621440,-4718592,-4194304⟩ t0x1175=true := by decide +kernel
def t0x587 : Tree := .y (-4718592) t0x1174 t0x1175
lemma t0x587ok : treeCheck nodes v0 ⟨2359296,2621440,-5242880,-4194304⟩ t0x587=true := Bool.and_eq_true_iff.mpr ⟨t0x1174ok,t0x1175ok⟩
def t0x293 : Tree := .d (2359296) t0x586 t0x587
lemma t0x293ok : treeCheck nodes v0 ⟨2097152,2621440,-5242880,-4194304⟩ t0x293=true := Bool.and_eq_true_iff.mpr ⟨t0x586ok,t0x587ok⟩
def t0x146 : Tree := .y (-5242880) t0x292 t0x293
lemma t0x146ok : treeCheck nodes v0 ⟨2097152,2621440,-6291456,-4194304⟩ t0x146=true := Bool.and_eq_true_iff.mpr ⟨t0x292ok,t0x293ok⟩
def t0x1176 : Tree := .leaf ⟨true,7968488,2883584,5548542,6091677,-6291456,-5767168⟩
lemma t0x1176ok : treeCheck nodes v0 ⟨2621440,2883584,-6291456,-5767168⟩ t0x1176=true := by decide +kernel
def t0x1177 : Tree := .leaf ⟨true,7968488,2883584,6091676,6548356,-5767168,-5242880⟩
lemma t0x1177ok : treeCheck nodes v0 ⟨2621440,2883584,-5767168,-5242880⟩ t0x1177=true := by decide +kernel
def t0x588 : Tree := .y (-5767168) t0x1176 t0x1177
lemma t0x588ok : treeCheck nodes v0 ⟨2621440,2883584,-6291456,-5242880⟩ t0x588=true := Bool.and_eq_true_iff.mpr ⟨t0x1176ok,t0x1177ok⟩
def t0x1178 : Tree := .leaf ⟨true,7877417,3145728,5548542,6091677,-6291456,-5767168⟩
lemma t0x1178ok : treeCheck nodes v0 ⟨2883584,3145728,-6291456,-5767168⟩ t0x1178=true := by decide +kernel
def t0x1179 : Tree := .leaf ⟨true,7877417,3145728,6091676,6548356,-5767168,-5242880⟩
lemma t0x1179ok : treeCheck nodes v0 ⟨2883584,3145728,-5767168,-5242880⟩ t0x1179=true := by decide +kernel
def t0x589 : Tree := .y (-5767168) t0x1178 t0x1179
lemma t0x589ok : treeCheck nodes v0 ⟨2883584,3145728,-6291456,-5242880⟩ t0x589=true := Bool.and_eq_true_iff.mpr ⟨t0x1178ok,t0x1179ok⟩
def t0x294 : Tree := .d (2883584) t0x588 t0x589
lemma t0x294ok : treeCheck nodes v0 ⟨2621440,3145728,-6291456,-5242880⟩ t0x294=true := Bool.and_eq_true_iff.mpr ⟨t0x588ok,t0x589ok⟩
def t0x1180 : Tree := .leaf ⟨true,7968488,2883584,6548355,6935679,-5242880,-4718592⟩
lemma t0x1180ok : treeCheck nodes v0 ⟨2621440,2883584,-5242880,-4718592⟩ t0x1180=true := by decide +kernel
def t0x1181 : Tree := .leaf ⟨true,7968488,2883584,6935678,7264748,-4718592,-4194304⟩
lemma t0x1181ok : treeCheck nodes v0 ⟨2621440,2883584,-4718592,-4194304⟩ t0x1181=true := by decide +kernel
def t0x590 : Tree := .y (-4718592) t0x1180 t0x1181
lemma t0x590ok : treeCheck nodes v0 ⟨2621440,2883584,-5242880,-4194304⟩ t0x590=true := Bool.and_eq_true_iff.mpr ⟨t0x1180ok,t0x1181ok⟩
def t0x1182 : Tree := .leaf ⟨true,7877417,3145728,6548355,6935679,-5242880,-4718592⟩
lemma t0x1182ok : treeCheck nodes v0 ⟨2883584,3145728,-5242880,-4718592⟩ t0x1182=true := by decide +kernel
def t0x1183 : Tree := .leaf ⟨true,7877417,3145728,6935678,7264748,-4718592,-4194304⟩
lemma t0x1183ok : treeCheck nodes v0 ⟨2883584,3145728,-4718592,-4194304⟩ t0x1183=true := by decide +kernel
def t0x591 : Tree := .y (-4718592) t0x1182 t0x1183
lemma t0x591ok : treeCheck nodes v0 ⟨2883584,3145728,-5242880,-4194304⟩ t0x591=true := Bool.and_eq_true_iff.mpr ⟨t0x1182ok,t0x1183ok⟩
def t0x295 : Tree := .d (2883584) t0x590 t0x591
lemma t0x295ok : treeCheck nodes v0 ⟨2621440,3145728,-5242880,-4194304⟩ t0x295=true := Bool.and_eq_true_iff.mpr ⟨t0x590ok,t0x591ok⟩
def t0x147 : Tree := .y (-5242880) t0x294 t0x295
lemma t0x147ok : treeCheck nodes v0 ⟨2621440,3145728,-6291456,-4194304⟩ t0x147=true := Bool.and_eq_true_iff.mpr ⟨t0x294ok,t0x295ok⟩
def t0x73 : Tree := .d (2621440) t0x146 t0x147
lemma t0x73ok : treeCheck nodes v0 ⟨2097152,3145728,-6291456,-4194304⟩ t0x73=true := Bool.and_eq_true_iff.mpr ⟨t0x146ok,t0x147ok⟩
def t0x36 : Tree := .y (-6291456) t0x72 t0x73
lemma t0x36ok : treeCheck nodes v0 ⟨2097152,3145728,-8388608,-4194304⟩ t0x36=true := Bool.and_eq_true_iff.mpr ⟨t0x72ok,t0x73ok⟩
def t0x296 : Tree := .leaf ⟨true,7776448,3670016,0,4061118,-8388608,-7340032⟩
lemma t0x296ok : treeCheck nodes v0 ⟨3145728,3670016,-8388608,-7340032⟩ t0x296=true := by decide +kernel
def t0x594 : Tree := .leaf ⟨true,7776448,3407872,4061117,5548543,-7340032,-6291456⟩
lemma t0x594ok : treeCheck nodes v0 ⟨3145728,3407872,-7340032,-6291456⟩ t0x594=true := by decide +kernel
def t0x595 : Tree := .leaf ⟨true,7665191,3670016,4061117,5548543,-7340032,-6291456⟩
lemma t0x595ok : treeCheck nodes v0 ⟨3407872,3670016,-7340032,-6291456⟩ t0x595=true := by decide +kernel
def t0x297 : Tree := .d (3407872) t0x594 t0x595
lemma t0x297ok : treeCheck nodes v0 ⟨3145728,3670016,-7340032,-6291456⟩ t0x297=true := Bool.and_eq_true_iff.mpr ⟨t0x594ok,t0x595ok⟩
def t0x148 : Tree := .y (-7340032) t0x296 t0x297
lemma t0x148ok : treeCheck nodes v0 ⟨3145728,3670016,-8388608,-6291456⟩ t0x148=true := Bool.and_eq_true_iff.mpr ⟨t0x296ok,t0x297ok⟩
def t0x298 : Tree := .leaf ⟨true,7543191,4194304,0,4061118,-8388608,-7340032⟩
lemma t0x298ok : treeCheck nodes v0 ⟨3670016,4194304,-8388608,-7340032⟩ t0x298=true := by decide +kernel
def t0x299 : Tree := .leaf ⟨true,7543191,4194304,4061117,5548543,-7340032,-6291456⟩
lemma t0x299ok : treeCheck nodes v0 ⟨3670016,4194304,-7340032,-6291456⟩ t0x299=true := by decide +kernel
def t0x149 : Tree := .y (-7340032) t0x298 t0x299
lemma t0x149ok : treeCheck nodes v0 ⟨3670016,4194304,-8388608,-6291456⟩ t0x149=true := Bool.and_eq_true_iff.mpr ⟨t0x298ok,t0x299ok⟩
def t0x74 : Tree := .d (3670016) t0x148 t0x149
lemma t0x74ok : treeCheck nodes v0 ⟨3145728,4194304,-8388608,-6291456⟩ t0x74=true := Bool.and_eq_true_iff.mpr ⟨t0x148ok,t0x149ok⟩
def t0x1200 : Tree := .leaf ⟨true,7776448,3407872,5548542,6091677,-6291456,-5767168⟩
lemma t0x1200ok : treeCheck nodes v0 ⟨3145728,3407872,-6291456,-5767168⟩ t0x1200=true := by decide +kernel
def t0x1201 : Tree := .leaf ⟨true,7776448,3407872,6091676,6548356,-5767168,-5242880⟩
lemma t0x1201ok : treeCheck nodes v0 ⟨3145728,3407872,-5767168,-5242880⟩ t0x1201=true := by decide +kernel
def t0x600 : Tree := .y (-5767168) t0x1200 t0x1201
lemma t0x600ok : treeCheck nodes v0 ⟨3145728,3407872,-6291456,-5242880⟩ t0x600=true := Bool.and_eq_true_iff.mpr ⟨t0x1200ok,t0x1201ok⟩
def t0x1202 : Tree := .leaf ⟨true,7665191,3670016,5548542,6091677,-6291456,-5767168⟩
lemma t0x1202ok : treeCheck nodes v0 ⟨3407872,3670016,-6291456,-5767168⟩ t0x1202=true := by decide +kernel
def t0x1203 : Tree := .leaf ⟨true,7665191,3670016,6091676,6548356,-5767168,-5242880⟩
lemma t0x1203ok : treeCheck nodes v0 ⟨3407872,3670016,-5767168,-5242880⟩ t0x1203=true := by decide +kernel
def t0x601 : Tree := .y (-5767168) t0x1202 t0x1203
lemma t0x601ok : treeCheck nodes v0 ⟨3407872,3670016,-6291456,-5242880⟩ t0x601=true := Bool.and_eq_true_iff.mpr ⟨t0x1202ok,t0x1203ok⟩
def t0x300 : Tree := .d (3407872) t0x600 t0x601
lemma t0x300ok : treeCheck nodes v0 ⟨3145728,3670016,-6291456,-5242880⟩ t0x300=true := Bool.and_eq_true_iff.mpr ⟨t0x600ok,t0x601ok⟩
def t0x1204 : Tree := .leaf ⟨true,7776448,3407872,6548355,6935679,-5242880,-4718592⟩
lemma t0x1204ok : treeCheck nodes v0 ⟨3145728,3407872,-5242880,-4718592⟩ t0x1204=true := by decide +kernel
def t0x1205 : Tree := .leaf ⟨true,7776448,3407872,6935678,7264748,-4718592,-4194304⟩
lemma t0x1205ok : treeCheck nodes v0 ⟨3145728,3407872,-4718592,-4194304⟩ t0x1205=true := by decide +kernel
def t0x602 : Tree := .y (-4718592) t0x1204 t0x1205
lemma t0x602ok : treeCheck nodes v0 ⟨3145728,3407872,-5242880,-4194304⟩ t0x602=true := Bool.and_eq_true_iff.mpr ⟨t0x1204ok,t0x1205ok⟩
def t0x1206 : Tree := .leaf ⟨true,7665191,3670016,6548355,6935679,-5242880,-4718592⟩
lemma t0x1206ok : treeCheck nodes v0 ⟨3407872,3670016,-5242880,-4718592⟩ t0x1206=true := by decide +kernel
def t0x1207 : Tree := .leaf ⟨true,7665191,3670016,6935678,7264748,-4718592,-4194304⟩
lemma t0x1207ok : treeCheck nodes v0 ⟨3407872,3670016,-4718592,-4194304⟩ t0x1207=true := by decide +kernel
def t0x603 : Tree := .y (-4718592) t0x1206 t0x1207
lemma t0x603ok : treeCheck nodes v0 ⟨3407872,3670016,-5242880,-4194304⟩ t0x603=true := Bool.and_eq_true_iff.mpr ⟨t0x1206ok,t0x1207ok⟩
def t0x301 : Tree := .d (3407872) t0x602 t0x603
lemma t0x301ok : treeCheck nodes v0 ⟨3145728,3670016,-5242880,-4194304⟩ t0x301=true := Bool.and_eq_true_iff.mpr ⟨t0x602ok,t0x603ok⟩
def t0x150 : Tree := .y (-5242880) t0x300 t0x301
lemma t0x150ok : treeCheck nodes v0 ⟨3145728,3670016,-6291456,-4194304⟩ t0x150=true := Bool.and_eq_true_iff.mpr ⟨t0x300ok,t0x301ok⟩
def t0x1208 : Tree := .leaf ⟨true,7543191,3932160,5548542,6091677,-6291456,-5767168⟩
lemma t0x1208ok : treeCheck nodes v0 ⟨3670016,3932160,-6291456,-5767168⟩ t0x1208=true := by decide +kernel
def t0x1209 : Tree := .leaf ⟨true,7543191,3932160,6091676,6548356,-5767168,-5242880⟩
lemma t0x1209ok : treeCheck nodes v0 ⟨3670016,3932160,-5767168,-5242880⟩ t0x1209=true := by decide +kernel
def t0x604 : Tree := .y (-5767168) t0x1208 t0x1209
lemma t0x604ok : treeCheck nodes v0 ⟨3670016,3932160,-6291456,-5242880⟩ t0x604=true := Bool.and_eq_true_iff.mpr ⟨t0x1208ok,t0x1209ok⟩
def t0x605 : Tree := .leaf ⟨true,7409917,4194304,5548542,6548356,-6291456,-5242880⟩
lemma t0x605ok : treeCheck nodes v0 ⟨3932160,4194304,-6291456,-5242880⟩ t0x605=true := by decide +kernel
def t0x302 : Tree := .d (3932160) t0x604 t0x605
lemma t0x302ok : treeCheck nodes v0 ⟨3670016,4194304,-6291456,-5242880⟩ t0x302=true := Bool.and_eq_true_iff.mpr ⟨t0x604ok,t0x605ok⟩
def t0x1212 : Tree := .leaf ⟨true,7543191,3932160,6548355,6935679,-5242880,-4718592⟩
lemma t0x1212ok : treeCheck nodes v0 ⟨3670016,3932160,-5242880,-4718592⟩ t0x1212=true := by decide +kernel
def t0x1213 : Tree := .leaf ⟨true,7543191,3932160,6935678,7264748,-4718592,-4194304⟩
lemma t0x1213ok : treeCheck nodes v0 ⟨3670016,3932160,-4718592,-4194304⟩ t0x1213=true := by decide +kernel
def t0x606 : Tree := .y (-4718592) t0x1212 t0x1213
lemma t0x606ok : treeCheck nodes v0 ⟨3670016,3932160,-5242880,-4194304⟩ t0x606=true := Bool.and_eq_true_iff.mpr ⟨t0x1212ok,t0x1213ok⟩
def t0x1214 : Tree := .leaf ⟨true,7409917,4194304,6548355,6935679,-5242880,-4718592⟩
lemma t0x1214ok : treeCheck nodes v0 ⟨3932160,4194304,-5242880,-4718592⟩ t0x1214=true := by decide +kernel
def t0x1215 : Tree := .leaf ⟨true,7409917,4194304,6935678,7264748,-4718592,-4194304⟩
lemma t0x1215ok : treeCheck nodes v0 ⟨3932160,4194304,-4718592,-4194304⟩ t0x1215=true := by decide +kernel
def t0x607 : Tree := .y (-4718592) t0x1214 t0x1215
lemma t0x607ok : treeCheck nodes v0 ⟨3932160,4194304,-5242880,-4194304⟩ t0x607=true := Bool.and_eq_true_iff.mpr ⟨t0x1214ok,t0x1215ok⟩
def t0x303 : Tree := .d (3932160) t0x606 t0x607
lemma t0x303ok : treeCheck nodes v0 ⟨3670016,4194304,-5242880,-4194304⟩ t0x303=true := Bool.and_eq_true_iff.mpr ⟨t0x606ok,t0x607ok⟩
def t0x151 : Tree := .y (-5242880) t0x302 t0x303
lemma t0x151ok : treeCheck nodes v0 ⟨3670016,4194304,-6291456,-4194304⟩ t0x151=true := Bool.and_eq_true_iff.mpr ⟨t0x302ok,t0x303ok⟩
def t0x75 : Tree := .d (3670016) t0x150 t0x151
lemma t0x75ok : treeCheck nodes v0 ⟨3145728,4194304,-6291456,-4194304⟩ t0x75=true := Bool.and_eq_true_iff.mpr ⟨t0x150ok,t0x151ok⟩
def t0x37 : Tree := .y (-6291456) t0x74 t0x75
lemma t0x37ok : treeCheck nodes v0 ⟨3145728,4194304,-8388608,-4194304⟩ t0x37=true := Bool.and_eq_true_iff.mpr ⟨t0x74ok,t0x75ok⟩
def t0x18 : Tree := .d (3145728) t0x36 t0x37
lemma t0x18ok : treeCheck nodes v0 ⟨2097152,4194304,-8388608,-4194304⟩ t0x18=true := Bool.and_eq_true_iff.mpr ⟨t0x36ok,t0x37ok⟩
def t0x1216 : Tree := .leaf ⟨true,8122235,2359296,7264747,7543191,-4194304,-3670016⟩
lemma t0x1216ok : treeCheck nodes v0 ⟨2097152,2359296,-4194304,-3670016⟩ t0x1216=true := by decide +kernel
def t0x1217 : Tree := .leaf ⟨true,8122235,2359296,7543190,7776448,-3670016,-3145728⟩
lemma t0x1217ok : treeCheck nodes v0 ⟨2097152,2359296,-3670016,-3145728⟩ t0x1217=true := by decide +kernel
def t0x608 : Tree := .y (-3670016) t0x1216 t0x1217
lemma t0x608ok : treeCheck nodes v0 ⟨2097152,2359296,-4194304,-3145728⟩ t0x608=true := Bool.and_eq_true_iff.mpr ⟨t0x1216ok,t0x1217ok⟩
def t0x1218 : Tree := .leaf ⟨true,8049998,2621440,7264747,7543191,-4194304,-3670016⟩
lemma t0x1218ok : treeCheck nodes v0 ⟨2359296,2621440,-4194304,-3670016⟩ t0x1218=true := by decide +kernel
def t0x1219 : Tree := .leaf ⟨true,8049998,2621440,7543190,7776448,-3670016,-3145728⟩
lemma t0x1219ok : treeCheck nodes v0 ⟨2359296,2621440,-3670016,-3145728⟩ t0x1219=true := by decide +kernel
def t0x609 : Tree := .y (-3670016) t0x1218 t0x1219
lemma t0x609ok : treeCheck nodes v0 ⟨2359296,2621440,-4194304,-3145728⟩ t0x609=true := Bool.and_eq_true_iff.mpr ⟨t0x1218ok,t0x1219ok⟩
def t0x304 : Tree := .d (2359296) t0x608 t0x609
lemma t0x304ok : treeCheck nodes v0 ⟨2097152,2621440,-4194304,-3145728⟩ t0x304=true := Bool.and_eq_true_iff.mpr ⟨t0x608ok,t0x609ok⟩
def t0x610 : Tree := .leaf ⟨true,8122235,2359296,7776447,8122235,-3145728,-2097152⟩
lemma t0x610ok : treeCheck nodes v0 ⟨2097152,2359296,-3145728,-2097152⟩ t0x610=true := by decide +kernel
def t0x611 : Tree := .leaf ⟨true,8049998,2621440,7776447,8122235,-3145728,-2097152⟩
lemma t0x611ok : treeCheck nodes v0 ⟨2359296,2621440,-3145728,-2097152⟩ t0x611=true := by decide +kernel
def t0x305 : Tree := .d (2359296) t0x610 t0x611
lemma t0x305ok : treeCheck nodes v0 ⟨2097152,2621440,-3145728,-2097152⟩ t0x305=true := Bool.and_eq_true_iff.mpr ⟨t0x610ok,t0x611ok⟩
def t0x152 : Tree := .y (-3145728) t0x304 t0x305
lemma t0x152ok : treeCheck nodes v0 ⟨2097152,2621440,-4194304,-2097152⟩ t0x152=true := Bool.and_eq_true_iff.mpr ⟨t0x304ok,t0x305ok⟩
def t0x1224 : Tree := .leaf ⟨true,7968488,2883584,7264747,7543191,-4194304,-3670016⟩
lemma t0x1224ok : treeCheck nodes v0 ⟨2621440,2883584,-4194304,-3670016⟩ t0x1224=true := by decide +kernel
def t0x1225 : Tree := .leaf ⟨true,7968488,2883584,7543190,7776448,-3670016,-3145728⟩
lemma t0x1225ok : treeCheck nodes v0 ⟨2621440,2883584,-3670016,-3145728⟩ t0x1225=true := by decide +kernel
def t0x612 : Tree := .y (-3670016) t0x1224 t0x1225
lemma t0x612ok : treeCheck nodes v0 ⟨2621440,2883584,-4194304,-3145728⟩ t0x612=true := Bool.and_eq_true_iff.mpr ⟨t0x1224ok,t0x1225ok⟩
def t0x1226 : Tree := .leaf ⟨true,7877417,3145728,7264747,7543191,-4194304,-3670016⟩
lemma t0x1226ok : treeCheck nodes v0 ⟨2883584,3145728,-4194304,-3670016⟩ t0x1226=true := by decide +kernel
def t0x1227 : Tree := .leaf ⟨true,7877417,3145728,7543190,7776448,-3670016,-3145728⟩
lemma t0x1227ok : treeCheck nodes v0 ⟨2883584,3145728,-3670016,-3145728⟩ t0x1227=true := by decide +kernel
def t0x613 : Tree := .y (-3670016) t0x1226 t0x1227
lemma t0x613ok : treeCheck nodes v0 ⟨2883584,3145728,-4194304,-3145728⟩ t0x613=true := Bool.and_eq_true_iff.mpr ⟨t0x1226ok,t0x1227ok⟩
def t0x306 : Tree := .d (2883584) t0x612 t0x613
lemma t0x306ok : treeCheck nodes v0 ⟨2621440,3145728,-4194304,-3145728⟩ t0x306=true := Bool.and_eq_true_iff.mpr ⟨t0x612ok,t0x613ok⟩
def t0x307 : Tree := .leaf ⟨true,7968488,3145728,7776447,8122235,-3145728,-2097152⟩
lemma t0x307ok : treeCheck nodes v0 ⟨2621440,3145728,-3145728,-2097152⟩ t0x307=true := by decide +kernel
def t0x153 : Tree := .y (-3145728) t0x306 t0x307
lemma t0x153ok : treeCheck nodes v0 ⟨2621440,3145728,-4194304,-2097152⟩ t0x153=true := Bool.and_eq_true_iff.mpr ⟨t0x306ok,t0x307ok⟩
def t0x76 : Tree := .d (2621440) t0x152 t0x153
lemma t0x76ok : treeCheck nodes v0 ⟨2097152,3145728,-4194304,-2097152⟩ t0x76=true := Bool.and_eq_true_iff.mpr ⟨t0x152ok,t0x153ok⟩
def t0x154 : Tree := .leaf ⟨true,8122235,2621440,8122234,8388608,-2097152,0⟩
lemma t0x154ok : treeCheck nodes v0 ⟨2097152,2621440,-2097152,0⟩ t0x154=true := by decide +kernel
def t0x155 : Tree := .leaf ⟨true,7968488,3145728,8122234,8388608,-2097152,0⟩
lemma t0x155ok : treeCheck nodes v0 ⟨2621440,3145728,-2097152,0⟩ t0x155=true := by decide +kernel
def t0x77 : Tree := .d (2621440) t0x154 t0x155
lemma t0x77ok : treeCheck nodes v0 ⟨2097152,3145728,-2097152,0⟩ t0x77=true := Bool.and_eq_true_iff.mpr ⟨t0x154ok,t0x155ok⟩
def t0x38 : Tree := .y (-2097152) t0x76 t0x77
lemma t0x38ok : treeCheck nodes v0 ⟨2097152,3145728,-4194304,0⟩ t0x38=true := Bool.and_eq_true_iff.mpr ⟨t0x76ok,t0x77ok⟩
def t0x1248 : Tree := .leaf ⟨true,7776448,3407872,7264747,7543191,-4194304,-3670016⟩
lemma t0x1248ok : treeCheck nodes v0 ⟨3145728,3407872,-4194304,-3670016⟩ t0x1248=true := by decide +kernel
def t0x1249 : Tree := .leaf ⟨true,7776448,3407872,7543190,7776448,-3670016,-3145728⟩
lemma t0x1249ok : treeCheck nodes v0 ⟨3145728,3407872,-3670016,-3145728⟩ t0x1249=true := by decide +kernel
def t0x624 : Tree := .y (-3670016) t0x1248 t0x1249
lemma t0x624ok : treeCheck nodes v0 ⟨3145728,3407872,-4194304,-3145728⟩ t0x624=true := Bool.and_eq_true_iff.mpr ⟨t0x1248ok,t0x1249ok⟩
def t0x1250 : Tree := .leaf ⟨true,7665191,3670016,7264747,7543191,-4194304,-3670016⟩
lemma t0x1250ok : treeCheck nodes v0 ⟨3407872,3670016,-4194304,-3670016⟩ t0x1250=true := by decide +kernel
def t0x1251 : Tree := .leaf ⟨true,7665191,3670016,7543190,7776448,-3670016,-3145728⟩
lemma t0x1251ok : treeCheck nodes v0 ⟨3407872,3670016,-3670016,-3145728⟩ t0x1251=true := by decide +kernel
def t0x625 : Tree := .y (-3670016) t0x1250 t0x1251
lemma t0x625ok : treeCheck nodes v0 ⟨3407872,3670016,-4194304,-3145728⟩ t0x625=true := Bool.and_eq_true_iff.mpr ⟨t0x1250ok,t0x1251ok⟩
def t0x312 : Tree := .d (3407872) t0x624 t0x625
lemma t0x312ok : treeCheck nodes v0 ⟨3145728,3670016,-4194304,-3145728⟩ t0x312=true := Bool.and_eq_true_iff.mpr ⟨t0x624ok,t0x625ok⟩
def t0x313 : Tree := .leaf ⟨true,7776448,3670016,7776447,8122235,-3145728,-2097152⟩
lemma t0x313ok : treeCheck nodes v0 ⟨3145728,3670016,-3145728,-2097152⟩ t0x313=true := by decide +kernel
def t0x156 : Tree := .y (-3145728) t0x312 t0x313
lemma t0x156ok : treeCheck nodes v0 ⟨3145728,3670016,-4194304,-2097152⟩ t0x156=true := Bool.and_eq_true_iff.mpr ⟨t0x312ok,t0x313ok⟩
def t0x1256 : Tree := .leaf ⟨true,7543191,3932160,7264747,7543191,-4194304,-3670016⟩
lemma t0x1256ok : treeCheck nodes v0 ⟨3670016,3932160,-4194304,-3670016⟩ t0x1256=true := by decide +kernel
def t0x1257 : Tree := .leaf ⟨true,7543191,3932160,7543190,7776448,-3670016,-3145728⟩
lemma t0x1257ok : treeCheck nodes v0 ⟨3670016,3932160,-3670016,-3145728⟩ t0x1257=true := by decide +kernel
def t0x628 : Tree := .y (-3670016) t0x1256 t0x1257
lemma t0x628ok : treeCheck nodes v0 ⟨3670016,3932160,-4194304,-3145728⟩ t0x628=true := Bool.and_eq_true_iff.mpr ⟨t0x1256ok,t0x1257ok⟩
def t0x629 : Tree := .leaf ⟨true,7409917,4194304,7264747,7776448,-4194304,-3145728⟩
lemma t0x629ok : treeCheck nodes v0 ⟨3932160,4194304,-4194304,-3145728⟩ t0x629=true := by decide +kernel
def t0x314 : Tree := .d (3932160) t0x628 t0x629
lemma t0x314ok : treeCheck nodes v0 ⟨3670016,4194304,-4194304,-3145728⟩ t0x314=true := Bool.and_eq_true_iff.mpr ⟨t0x628ok,t0x629ok⟩
def t0x315 : Tree := .leaf ⟨true,7543191,4194304,7776447,8122235,-3145728,-2097152⟩
lemma t0x315ok : treeCheck nodes v0 ⟨3670016,4194304,-3145728,-2097152⟩ t0x315=true := by decide +kernel
def t0x157 : Tree := .y (-3145728) t0x314 t0x315
lemma t0x157ok : treeCheck nodes v0 ⟨3670016,4194304,-4194304,-2097152⟩ t0x157=true := Bool.and_eq_true_iff.mpr ⟨t0x314ok,t0x315ok⟩
def t0x78 : Tree := .d (3670016) t0x156 t0x157
lemma t0x78ok : treeCheck nodes v0 ⟨3145728,4194304,-4194304,-2097152⟩ t0x78=true := Bool.and_eq_true_iff.mpr ⟨t0x156ok,t0x157ok⟩
def t0x158 : Tree := .leaf ⟨true,7776448,3670016,8122234,8388608,-2097152,0⟩
lemma t0x158ok : treeCheck nodes v0 ⟨3145728,3670016,-2097152,0⟩ t0x158=true := by decide +kernel
def t0x159 : Tree := .leaf ⟨true,7543191,4194304,8122234,8388608,-2097152,0⟩
lemma t0x159ok : treeCheck nodes v0 ⟨3670016,4194304,-2097152,0⟩ t0x159=true := by decide +kernel
def t0x79 : Tree := .d (3670016) t0x158 t0x159
lemma t0x79ok : treeCheck nodes v0 ⟨3145728,4194304,-2097152,0⟩ t0x79=true := Bool.and_eq_true_iff.mpr ⟨t0x158ok,t0x159ok⟩
def t0x39 : Tree := .y (-2097152) t0x78 t0x79
lemma t0x39ok : treeCheck nodes v0 ⟨3145728,4194304,-4194304,0⟩ t0x39=true := Bool.and_eq_true_iff.mpr ⟨t0x78ok,t0x79ok⟩
def t0x19 : Tree := .d (3145728) t0x38 t0x39
lemma t0x19ok : treeCheck nodes v0 ⟨2097152,4194304,-4194304,0⟩ t0x19=true := Bool.and_eq_true_iff.mpr ⟨t0x38ok,t0x39ok⟩
def t0x9 : Tree := .y (-4194304) t0x18 t0x19
lemma t0x9ok : treeCheck nodes v0 ⟨2097152,4194304,-8388608,0⟩ t0x9=true := Bool.and_eq_true_iff.mpr ⟨t0x18ok,t0x19ok⟩
def t0x4 : Tree := .d (2097152) t0x8 t0x9
lemma t0x4ok : treeCheck nodes v0 ⟨0,4194304,-8388608,0⟩ t0x4=true := Bool.and_eq_true_iff.mpr ⟨t0x8ok,t0x9ok⟩
def t0x20 : Tree := .leaf ⟨true,8388608,2097152,7264747,8388608,0,4194304⟩
lemma t0x20ok : treeCheck nodes v0 ⟨0,2097152,0,4194304⟩ t0x20=true := by decide +kernel
def t0x21 : Tree := .leaf ⟨true,8388608,2097152,0,7264748,4194304,8388608⟩
lemma t0x21ok : treeCheck nodes v0 ⟨0,2097152,4194304,8388608⟩ t0x21=true := by decide +kernel
def t0x10 : Tree := .y (4194304) t0x20 t0x21
lemma t0x10ok : treeCheck nodes v0 ⟨0,2097152,0,8388608⟩ t0x10=true := Bool.and_eq_true_iff.mpr ⟨t0x20ok,t0x21ok⟩
def t0x88 : Tree := .leaf ⟨true,8122235,3145728,8122234,8388608,0,2097152⟩
lemma t0x88ok : treeCheck nodes v0 ⟨2097152,3145728,0,2097152⟩ t0x88=true := by decide +kernel
def t0x89 : Tree := .leaf ⟨true,8122235,3145728,7264747,8122235,2097152,4194304⟩
lemma t0x89ok : treeCheck nodes v0 ⟨2097152,3145728,2097152,4194304⟩ t0x89=true := by decide +kernel
def t0x44 : Tree := .y (2097152) t0x88 t0x89
lemma t0x44ok : treeCheck nodes v0 ⟨2097152,3145728,0,4194304⟩ t0x44=true := Bool.and_eq_true_iff.mpr ⟨t0x88ok,t0x89ok⟩
def t0x90 : Tree := .leaf ⟨true,7776448,4194304,8122234,8388608,0,2097152⟩
lemma t0x90ok : treeCheck nodes v0 ⟨3145728,4194304,0,2097152⟩ t0x90=true := by decide +kernel
def t0x91 : Tree := .leaf ⟨true,7776448,4194304,7264747,8122235,2097152,4194304⟩
lemma t0x91ok : treeCheck nodes v0 ⟨3145728,4194304,2097152,4194304⟩ t0x91=true := by decide +kernel
def t0x45 : Tree := .y (2097152) t0x90 t0x91
lemma t0x45ok : treeCheck nodes v0 ⟨3145728,4194304,0,4194304⟩ t0x45=true := Bool.and_eq_true_iff.mpr ⟨t0x90ok,t0x91ok⟩
def t0x22 : Tree := .d (3145728) t0x44 t0x45
lemma t0x22ok : treeCheck nodes v0 ⟨2097152,4194304,0,4194304⟩ t0x22=true := Bool.and_eq_true_iff.mpr ⟨t0x44ok,t0x45ok⟩
def t0x23 : Tree := .leaf ⟨true,8122235,4194304,0,7264748,4194304,8388608⟩
lemma t0x23ok : treeCheck nodes v0 ⟨2097152,4194304,4194304,8388608⟩ t0x23=true := by decide +kernel
def t0x11 : Tree := .y (4194304) t0x22 t0x23
lemma t0x11ok : treeCheck nodes v0 ⟨2097152,4194304,0,8388608⟩ t0x11=true := Bool.and_eq_true_iff.mpr ⟨t0x22ok,t0x23ok⟩
def t0x5 : Tree := .d (2097152) t0x10 t0x11
lemma t0x5ok : treeCheck nodes v0 ⟨0,4194304,0,8388608⟩ t0x5=true := Bool.and_eq_true_iff.mpr ⟨t0x10ok,t0x11ok⟩
def t0x2 : Tree := .y (0) t0x4 t0x5
lemma t0x2ok : treeCheck nodes v0 ⟨0,4194304,-8388608,8388608⟩ t0x2=true := Bool.and_eq_true_iff.mpr ⟨t0x4ok,t0x5ok⟩
def t0x384 : Tree := .leaf ⟨true,7264748,4718592,0,4061118,-8388608,-7340032⟩
lemma t0x384ok : treeCheck nodes v0 ⟨4194304,4718592,-8388608,-7340032⟩ t0x384=true := by decide +kernel
def t0x385 : Tree := .leaf ⟨true,7264748,4718592,4061117,5548543,-7340032,-6291456⟩
lemma t0x385ok : treeCheck nodes v0 ⟨4194304,4718592,-7340032,-6291456⟩ t0x385=true := by decide +kernel
def t0x192 : Tree := .y (-7340032) t0x384 t0x385
lemma t0x192ok : treeCheck nodes v0 ⟨4194304,4718592,-8388608,-6291456⟩ t0x192=true := Bool.and_eq_true_iff.mpr ⟨t0x384ok,t0x385ok⟩
def t0x386 : Tree := .leaf ⟨true,6935679,5242880,0,4061118,-8388608,-7340032⟩
lemma t0x386ok : treeCheck nodes v0 ⟨4718592,5242880,-8388608,-7340032⟩ t0x386=true := by decide +kernel
def t0x387 : Tree := .leaf ⟨true,6935679,5242880,4061117,5548543,-7340032,-6291456⟩
lemma t0x387ok : treeCheck nodes v0 ⟨4718592,5242880,-7340032,-6291456⟩ t0x387=true := by decide +kernel
def t0x193 : Tree := .y (-7340032) t0x386 t0x387
lemma t0x193ok : treeCheck nodes v0 ⟨4718592,5242880,-8388608,-6291456⟩ t0x193=true := Bool.and_eq_true_iff.mpr ⟨t0x386ok,t0x387ok⟩
def t0x96 : Tree := .d (4718592) t0x192 t0x193
lemma t0x96ok : treeCheck nodes v0 ⟨4194304,5242880,-8388608,-6291456⟩ t0x96=true := Bool.and_eq_true_iff.mpr ⟨t0x192ok,t0x193ok⟩
def t0x776 : Tree := .leaf ⟨true,7264748,4456448,5548542,6548356,-6291456,-5242880⟩
lemma t0x776ok : treeCheck nodes v0 ⟨4194304,4456448,-6291456,-5242880⟩ t0x776=true := by decide +kernel
def t0x777 : Tree := .leaf ⟨true,7106956,4718592,5548542,6548356,-6291456,-5242880⟩
lemma t0x777ok : treeCheck nodes v0 ⟨4456448,4718592,-6291456,-5242880⟩ t0x777=true := by decide +kernel
def t0x388 : Tree := .d (4456448) t0x776 t0x777
lemma t0x388ok : treeCheck nodes v0 ⟨4194304,4718592,-6291456,-5242880⟩ t0x388=true := Bool.and_eq_true_iff.mpr ⟨t0x776ok,t0x777ok⟩
def t0x778 : Tree := .leaf ⟨true,7264748,4456448,6548355,7264748,-5242880,-4194304⟩
lemma t0x778ok : treeCheck nodes v0 ⟨4194304,4456448,-5242880,-4194304⟩ t0x778=true := by decide +kernel
def t0x779 : Tree := .leaf ⟨true,7106956,4718592,6548355,7264748,-5242880,-4194304⟩
lemma t0x779ok : treeCheck nodes v0 ⟨4456448,4718592,-5242880,-4194304⟩ t0x779=true := by decide +kernel
def t0x389 : Tree := .d (4456448) t0x778 t0x779
lemma t0x389ok : treeCheck nodes v0 ⟨4194304,4718592,-5242880,-4194304⟩ t0x389=true := Bool.and_eq_true_iff.mpr ⟨t0x778ok,t0x779ok⟩
def t0x194 : Tree := .y (-5242880) t0x388 t0x389
lemma t0x194ok : treeCheck nodes v0 ⟨4194304,4718592,-6291456,-4194304⟩ t0x194=true := Bool.and_eq_true_iff.mpr ⟨t0x388ok,t0x389ok⟩
def t0x390 : Tree := .leaf ⟨true,6935679,5242880,5548542,6548356,-6291456,-5242880⟩
lemma t0x390ok : treeCheck nodes v0 ⟨4718592,5242880,-6291456,-5242880⟩ t0x390=true := by decide +kernel
def t0x782 : Tree := .leaf ⟨true,6935679,4980736,6548355,7264748,-5242880,-4194304⟩
lemma t0x782ok : treeCheck nodes v0 ⟨4718592,4980736,-5242880,-4194304⟩ t0x782=true := by decide +kernel
def t0x783 : Tree := .leaf ⟨true,6749890,5242880,6548355,7264748,-5242880,-4194304⟩
lemma t0x783ok : treeCheck nodes v0 ⟨4980736,5242880,-5242880,-4194304⟩ t0x783=true := by decide +kernel
def t0x391 : Tree := .d (4980736) t0x782 t0x783
lemma t0x391ok : treeCheck nodes v0 ⟨4718592,5242880,-5242880,-4194304⟩ t0x391=true := Bool.and_eq_true_iff.mpr ⟨t0x782ok,t0x783ok⟩
def t0x195 : Tree := .y (-5242880) t0x390 t0x391
lemma t0x195ok : treeCheck nodes v0 ⟨4718592,5242880,-6291456,-4194304⟩ t0x195=true := Bool.and_eq_true_iff.mpr ⟨t0x390ok,t0x391ok⟩
def t0x97 : Tree := .d (4718592) t0x194 t0x195
lemma t0x97ok : treeCheck nodes v0 ⟨4194304,5242880,-6291456,-4194304⟩ t0x97=true := Bool.and_eq_true_iff.mpr ⟨t0x194ok,t0x195ok⟩
def t0x48 : Tree := .y (-6291456) t0x96 t0x97
lemma t0x48ok : treeCheck nodes v0 ⟨4194304,5242880,-8388608,-4194304⟩ t0x48=true := Bool.and_eq_true_iff.mpr ⟨t0x96ok,t0x97ok⟩
def t0x392 : Tree := .leaf ⟨true,6548356,5767168,0,4061118,-8388608,-7340032⟩
lemma t0x392ok : treeCheck nodes v0 ⟨5242880,5767168,-8388608,-7340032⟩ t0x392=true := by decide +kernel
def t0x393 : Tree := .leaf ⟨true,6548356,5767168,4061117,5548543,-7340032,-6291456⟩
lemma t0x393ok : treeCheck nodes v0 ⟨5242880,5767168,-7340032,-6291456⟩ t0x393=true := by decide +kernel
def t0x196 : Tree := .y (-7340032) t0x392 t0x393
lemma t0x196ok : treeCheck nodes v0 ⟨5242880,5767168,-8388608,-6291456⟩ t0x196=true := Bool.and_eq_true_iff.mpr ⟨t0x392ok,t0x393ok⟩
def t0x394 : Tree := .leaf ⟨true,6091677,6291456,0,4061118,-8388608,-7340032⟩
lemma t0x394ok : treeCheck nodes v0 ⟨5767168,6291456,-8388608,-7340032⟩ t0x394=true := by decide +kernel
def t0x395 : Tree := .leaf ⟨true,6091677,6291456,4061117,5548543,-7340032,-6291456⟩
lemma t0x395ok : treeCheck nodes v0 ⟨5767168,6291456,-7340032,-6291456⟩ t0x395=true := by decide +kernel
def t0x197 : Tree := .y (-7340032) t0x394 t0x395
lemma t0x197ok : treeCheck nodes v0 ⟨5767168,6291456,-8388608,-6291456⟩ t0x197=true := Bool.and_eq_true_iff.mpr ⟨t0x394ok,t0x395ok⟩
def t0x98 : Tree := .d (5767168) t0x196 t0x197
lemma t0x98ok : treeCheck nodes v0 ⟨5242880,6291456,-8388608,-6291456⟩ t0x98=true := Bool.and_eq_true_iff.mpr ⟨t0x196ok,t0x197ok⟩
def t0x396 : Tree := .leaf ⟨true,6548356,5767168,5548542,6548356,-6291456,-5242880⟩
lemma t0x396ok : treeCheck nodes v0 ⟨5242880,5767168,-6291456,-5242880⟩ t0x396=true := by decide +kernel
def t0x397 : Tree := .leaf ⟨true,6548356,5767168,6548355,7264748,-5242880,-4194304⟩
lemma t0x397ok : treeCheck nodes v0 ⟨5242880,5767168,-5242880,-4194304⟩ t0x397=true := by decide +kernel
def t0x198 : Tree := .y (-5242880) t0x396 t0x397
lemma t0x198ok : treeCheck nodes v0 ⟨5242880,5767168,-6291456,-4194304⟩ t0x198=true := Bool.and_eq_true_iff.mpr ⟨t0x396ok,t0x397ok⟩
def t0x398 : Tree := .leaf ⟨true,6091677,6291456,5548542,6548356,-6291456,-5242880⟩
lemma t0x398ok : treeCheck nodes v0 ⟨5767168,6291456,-6291456,-5242880⟩ t0x398=true := by decide +kernel
def t0x399 : Tree := .leaf ⟨true,6091677,6291456,6548355,7264748,-5242880,-4194304⟩
lemma t0x399ok : treeCheck nodes v0 ⟨5767168,6291456,-5242880,-4194304⟩ t0x399=true := by decide +kernel
def t0x199 : Tree := .y (-5242880) t0x398 t0x399
lemma t0x199ok : treeCheck nodes v0 ⟨5767168,6291456,-6291456,-4194304⟩ t0x199=true := Bool.and_eq_true_iff.mpr ⟨t0x398ok,t0x399ok⟩
def t0x99 : Tree := .d (5767168) t0x198 t0x199
lemma t0x99ok : treeCheck nodes v0 ⟨5242880,6291456,-6291456,-4194304⟩ t0x99=true := Bool.and_eq_true_iff.mpr ⟨t0x198ok,t0x199ok⟩
def t0x49 : Tree := .y (-6291456) t0x98 t0x99
lemma t0x49ok : treeCheck nodes v0 ⟨5242880,6291456,-8388608,-4194304⟩ t0x49=true := Bool.and_eq_true_iff.mpr ⟨t0x98ok,t0x99ok⟩
def t0x24 : Tree := .d (5242880) t0x48 t0x49
lemma t0x24ok : treeCheck nodes v0 ⟨4194304,6291456,-8388608,-4194304⟩ t0x24=true := Bool.and_eq_true_iff.mpr ⟨t0x48ok,t0x49ok⟩
def t0x800 : Tree := .leaf ⟨true,7264748,4456448,7264747,7776448,-4194304,-3145728⟩
lemma t0x800ok : treeCheck nodes v0 ⟨4194304,4456448,-4194304,-3145728⟩ t0x800=true := by decide +kernel
def t0x801 : Tree := .leaf ⟨true,7106956,4718592,7264747,7776448,-4194304,-3145728⟩
lemma t0x801ok : treeCheck nodes v0 ⟨4456448,4718592,-4194304,-3145728⟩ t0x801=true := by decide +kernel
def t0x400 : Tree := .d (4456448) t0x800 t0x801
lemma t0x400ok : treeCheck nodes v0 ⟨4194304,4718592,-4194304,-3145728⟩ t0x400=true := Bool.and_eq_true_iff.mpr ⟨t0x800ok,t0x801ok⟩
def t0x401 : Tree := .leaf ⟨true,7264748,4718592,7776447,8122235,-3145728,-2097152⟩
lemma t0x401ok : treeCheck nodes v0 ⟨4194304,4718592,-3145728,-2097152⟩ t0x401=true := by decide +kernel
def t0x200 : Tree := .y (-3145728) t0x400 t0x401
lemma t0x200ok : treeCheck nodes v0 ⟨4194304,4718592,-4194304,-2097152⟩ t0x200=true := Bool.and_eq_true_iff.mpr ⟨t0x400ok,t0x401ok⟩
def t0x402 : Tree := .leaf ⟨true,6935679,5242880,7264747,7776448,-4194304,-3145728⟩
lemma t0x402ok : treeCheck nodes v0 ⟨4718592,5242880,-4194304,-3145728⟩ t0x402=true := by decide +kernel
def t0x403 : Tree := .leaf ⟨true,6935679,5242880,7776447,8122235,-3145728,-2097152⟩
lemma t0x403ok : treeCheck nodes v0 ⟨4718592,5242880,-3145728,-2097152⟩ t0x403=true := by decide +kernel
def t0x201 : Tree := .y (-3145728) t0x402 t0x403
lemma t0x201ok : treeCheck nodes v0 ⟨4718592,5242880,-4194304,-2097152⟩ t0x201=true := Bool.and_eq_true_iff.mpr ⟨t0x402ok,t0x403ok⟩
def t0x100 : Tree := .d (4718592) t0x200 t0x201
lemma t0x100ok : treeCheck nodes v0 ⟨4194304,5242880,-4194304,-2097152⟩ t0x100=true := Bool.and_eq_true_iff.mpr ⟨t0x200ok,t0x201ok⟩
def t0x404 : Tree := .leaf ⟨true,7264748,4718592,8122234,8322814,-2097152,-1048576⟩
lemma t0x404ok : treeCheck nodes v0 ⟨4194304,4718592,-2097152,-1048576⟩ t0x404=true := by decide +kernel
def t0x405 : Tree := .leaf ⟨true,7264748,4718592,8322813,8388608,-1048576,0⟩
lemma t0x405ok : treeCheck nodes v0 ⟨4194304,4718592,-1048576,0⟩ t0x405=true := by decide +kernel
def t0x202 : Tree := .y (-1048576) t0x404 t0x405
lemma t0x202ok : treeCheck nodes v0 ⟨4194304,4718592,-2097152,0⟩ t0x202=true := Bool.and_eq_true_iff.mpr ⟨t0x404ok,t0x405ok⟩
def t0x406 : Tree := .leaf ⟨true,6935679,5242880,8122234,8322814,-2097152,-1048576⟩
lemma t0x406ok : treeCheck nodes v0 ⟨4718592,5242880,-2097152,-1048576⟩ t0x406=true := by decide +kernel
def t0x407 : Tree := .leaf ⟨true,6935679,5242880,8322813,8388608,-1048576,0⟩
lemma t0x407ok : treeCheck nodes v0 ⟨4718592,5242880,-1048576,0⟩ t0x407=true := by decide +kernel
def t0x203 : Tree := .y (-1048576) t0x406 t0x407
lemma t0x203ok : treeCheck nodes v0 ⟨4718592,5242880,-2097152,0⟩ t0x203=true := Bool.and_eq_true_iff.mpr ⟨t0x406ok,t0x407ok⟩
def t0x101 : Tree := .d (4718592) t0x202 t0x203
lemma t0x101ok : treeCheck nodes v0 ⟨4194304,5242880,-2097152,0⟩ t0x101=true := Bool.and_eq_true_iff.mpr ⟨t0x202ok,t0x203ok⟩
def t0x50 : Tree := .y (-2097152) t0x100 t0x101
lemma t0x50ok : treeCheck nodes v0 ⟨4194304,5242880,-4194304,0⟩ t0x50=true := Bool.and_eq_true_iff.mpr ⟨t0x100ok,t0x101ok⟩
def t0x408 : Tree := .leaf ⟨true,6548356,5767168,7264747,7776448,-4194304,-3145728⟩
lemma t0x408ok : treeCheck nodes v0 ⟨5242880,5767168,-4194304,-3145728⟩ t0x408=true := by decide +kernel
def t0x409 : Tree := .leaf ⟨true,6548356,5767168,7776447,8122235,-3145728,-2097152⟩
lemma t0x409ok : treeCheck nodes v0 ⟨5242880,5767168,-3145728,-2097152⟩ t0x409=true := by decide +kernel
def t0x204 : Tree := .y (-3145728) t0x408 t0x409
lemma t0x204ok : treeCheck nodes v0 ⟨5242880,5767168,-4194304,-2097152⟩ t0x204=true := Bool.and_eq_true_iff.mpr ⟨t0x408ok,t0x409ok⟩
def t0x410 : Tree := .leaf ⟨true,6091677,6291456,7264747,7776448,-4194304,-3145728⟩
lemma t0x410ok : treeCheck nodes v0 ⟨5767168,6291456,-4194304,-3145728⟩ t0x410=true := by decide +kernel
def t0x411 : Tree := .leaf ⟨true,6091677,6291456,7776447,8122235,-3145728,-2097152⟩
lemma t0x411ok : treeCheck nodes v0 ⟨5767168,6291456,-3145728,-2097152⟩ t0x411=true := by decide +kernel
def t0x205 : Tree := .y (-3145728) t0x410 t0x411
lemma t0x205ok : treeCheck nodes v0 ⟨5767168,6291456,-4194304,-2097152⟩ t0x205=true := Bool.and_eq_true_iff.mpr ⟨t0x410ok,t0x411ok⟩
def t0x102 : Tree := .d (5767168) t0x204 t0x205
lemma t0x102ok : treeCheck nodes v0 ⟨5242880,6291456,-4194304,-2097152⟩ t0x102=true := Bool.and_eq_true_iff.mpr ⟨t0x204ok,t0x205ok⟩
def t0x412 : Tree := .leaf ⟨true,6548356,5767168,8122234,8322814,-2097152,-1048576⟩
lemma t0x412ok : treeCheck nodes v0 ⟨5242880,5767168,-2097152,-1048576⟩ t0x412=true := by decide +kernel
def t0x413 : Tree := .leaf ⟨true,6548356,5767168,8322813,8388608,-1048576,0⟩
lemma t0x413ok : treeCheck nodes v0 ⟨5242880,5767168,-1048576,0⟩ t0x413=true := by decide +kernel
def t0x206 : Tree := .y (-1048576) t0x412 t0x413
lemma t0x206ok : treeCheck nodes v0 ⟨5242880,5767168,-2097152,0⟩ t0x206=true := Bool.and_eq_true_iff.mpr ⟨t0x412ok,t0x413ok⟩
def t0x207 : Tree := .leaf ⟨true,6091677,6291456,8122234,8388608,-2097152,0⟩
lemma t0x207ok : treeCheck nodes v0 ⟨5767168,6291456,-2097152,0⟩ t0x207=true := by decide +kernel
def t0x103 : Tree := .d (5767168) t0x206 t0x207
lemma t0x103ok : treeCheck nodes v0 ⟨5242880,6291456,-2097152,0⟩ t0x103=true := Bool.and_eq_true_iff.mpr ⟨t0x206ok,t0x207ok⟩
def t0x51 : Tree := .y (-2097152) t0x102 t0x103
lemma t0x51ok : treeCheck nodes v0 ⟨5242880,6291456,-4194304,0⟩ t0x51=true := Bool.and_eq_true_iff.mpr ⟨t0x102ok,t0x103ok⟩
def t0x25 : Tree := .d (5242880) t0x50 t0x51
lemma t0x25ok : treeCheck nodes v0 ⟨4194304,6291456,-4194304,0⟩ t0x25=true := Bool.and_eq_true_iff.mpr ⟨t0x50ok,t0x51ok⟩
def t0x12 : Tree := .y (-4194304) t0x24 t0x25
lemma t0x12ok : treeCheck nodes v0 ⟨4194304,6291456,-8388608,0⟩ t0x12=true := Bool.and_eq_true_iff.mpr ⟨t0x24ok,t0x25ok⟩
def t0x416 : Tree := .leaf ⟨true,5548543,6815744,0,4061118,-8388608,-7340032⟩
lemma t0x416ok : treeCheck nodes v0 ⟨6291456,6815744,-8388608,-7340032⟩ t0x416=true := by decide +kernel
def t0x417 : Tree := .leaf ⟨true,5548543,6815744,4061117,5548543,-7340032,-6291456⟩
lemma t0x417ok : treeCheck nodes v0 ⟨6291456,6815744,-7340032,-6291456⟩ t0x417=true := by decide +kernel
def t0x208 : Tree := .y (-7340032) t0x416 t0x417
lemma t0x208ok : treeCheck nodes v0 ⟨6291456,6815744,-8388608,-6291456⟩ t0x208=true := Bool.and_eq_true_iff.mpr ⟨t0x416ok,t0x417ok⟩
def t0x209 : Tree := .leaf ⟨true,4890233,7340032,0,5548543,-8388608,-6291456⟩
lemma t0x209ok : treeCheck nodes v0 ⟨6815744,7340032,-8388608,-6291456⟩ t0x209=true := by decide +kernel
def t0x104 : Tree := .d (6815744) t0x208 t0x209
lemma t0x104ok : treeCheck nodes v0 ⟨6291456,7340032,-8388608,-6291456⟩ t0x104=true := Bool.and_eq_true_iff.mpr ⟨t0x208ok,t0x209ok⟩
def t0x210 : Tree := .leaf ⟨true,5548543,6815744,5548542,7264748,-6291456,-4194304⟩
lemma t0x210ok : treeCheck nodes v0 ⟨6291456,6815744,-6291456,-4194304⟩ t0x210=true := by decide +kernel
def t0x211 : Tree := .leaf ⟨true,4890233,7340032,5548542,7264748,-6291456,-4194304⟩
lemma t0x211ok : treeCheck nodes v0 ⟨6815744,7340032,-6291456,-4194304⟩ t0x211=true := by decide +kernel
def t0x105 : Tree := .d (6815744) t0x210 t0x211
lemma t0x105ok : treeCheck nodes v0 ⟨6291456,7340032,-6291456,-4194304⟩ t0x105=true := Bool.and_eq_true_iff.mpr ⟨t0x210ok,t0x211ok⟩
def t0x52 : Tree := .y (-6291456) t0x104 t0x105
lemma t0x52ok : treeCheck nodes v0 ⟨6291456,7340032,-8388608,-4194304⟩ t0x52=true := Bool.and_eq_true_iff.mpr ⟨t0x104ok,t0x105ok⟩
def t0x106 : Tree := .leaf ⟨true,4061118,8388608,0,5548543,-8388608,-6291456⟩
lemma t0x106ok : treeCheck nodes v0 ⟨7340032,8388608,-8388608,-6291456⟩ t0x106=true := by decide +kernel
def t0x107 : Tree := .leaf ⟨true,4061118,8388608,5548542,7264748,-6291456,-4194304⟩
lemma t0x107ok : treeCheck nodes v0 ⟨7340032,8388608,-6291456,-4194304⟩ t0x107=true := by decide +kernel
def t0x53 : Tree := .y (-6291456) t0x106 t0x107
lemma t0x53ok : treeCheck nodes v0 ⟨7340032,8388608,-8388608,-4194304⟩ t0x53=true := Bool.and_eq_true_iff.mpr ⟨t0x106ok,t0x107ok⟩
def t0x26 : Tree := .d (7340032) t0x52 t0x53
lemma t0x26ok : treeCheck nodes v0 ⟨6291456,8388608,-8388608,-4194304⟩ t0x26=true := Bool.and_eq_true_iff.mpr ⟨t0x52ok,t0x53ok⟩
def t0x216 : Tree := .leaf ⟨true,5548543,6815744,7264747,8122235,-4194304,-2097152⟩
lemma t0x216ok : treeCheck nodes v0 ⟨6291456,6815744,-4194304,-2097152⟩ t0x216=true := by decide +kernel
def t0x217 : Tree := .leaf ⟨true,4890233,7340032,7264747,8122235,-4194304,-2097152⟩
lemma t0x217ok : treeCheck nodes v0 ⟨6815744,7340032,-4194304,-2097152⟩ t0x217=true := by decide +kernel
def t0x108 : Tree := .d (6815744) t0x216 t0x217
lemma t0x108ok : treeCheck nodes v0 ⟨6291456,7340032,-4194304,-2097152⟩ t0x108=true := Bool.and_eq_true_iff.mpr ⟨t0x216ok,t0x217ok⟩
def t0x218 : Tree := .leaf ⟨true,5548543,6815744,8122234,8388608,-2097152,0⟩
lemma t0x218ok : treeCheck nodes v0 ⟨6291456,6815744,-2097152,0⟩ t0x218=true := by decide +kernel
def t0x219 : Tree := .leaf ⟨true,4890233,7340032,8122234,8388608,-2097152,0⟩
lemma t0x219ok : treeCheck nodes v0 ⟨6815744,7340032,-2097152,0⟩ t0x219=true := by decide +kernel
def t0x109 : Tree := .d (6815744) t0x218 t0x219
lemma t0x109ok : treeCheck nodes v0 ⟨6291456,7340032,-2097152,0⟩ t0x109=true := Bool.and_eq_true_iff.mpr ⟨t0x218ok,t0x219ok⟩
def t0x54 : Tree := .y (-2097152) t0x108 t0x109
lemma t0x54ok : treeCheck nodes v0 ⟨6291456,7340032,-4194304,0⟩ t0x54=true := Bool.and_eq_true_iff.mpr ⟨t0x108ok,t0x109ok⟩
def t0x110 : Tree := .leaf ⟨true,4061118,8388608,7264747,8122235,-4194304,-2097152⟩
lemma t0x110ok : treeCheck nodes v0 ⟨7340032,8388608,-4194304,-2097152⟩ t0x110=true := by decide +kernel
def t0x111 : Tree := .leaf ⟨true,4061118,8388608,8122234,8388608,-2097152,0⟩
lemma t0x111ok : treeCheck nodes v0 ⟨7340032,8388608,-2097152,0⟩ t0x111=true := by decide +kernel
def t0x55 : Tree := .y (-2097152) t0x110 t0x111
lemma t0x55ok : treeCheck nodes v0 ⟨7340032,8388608,-4194304,0⟩ t0x55=true := Bool.and_eq_true_iff.mpr ⟨t0x110ok,t0x111ok⟩
def t0x27 : Tree := .d (7340032) t0x54 t0x55
lemma t0x27ok : treeCheck nodes v0 ⟨6291456,8388608,-4194304,0⟩ t0x27=true := Bool.and_eq_true_iff.mpr ⟨t0x54ok,t0x55ok⟩
def t0x13 : Tree := .y (-4194304) t0x26 t0x27
lemma t0x13ok : treeCheck nodes v0 ⟨6291456,8388608,-8388608,0⟩ t0x13=true := Bool.and_eq_true_iff.mpr ⟨t0x26ok,t0x27ok⟩
def t0x6 : Tree := .d (6291456) t0x12 t0x13
lemma t0x6ok : treeCheck nodes v0 ⟨4194304,8388608,-8388608,0⟩ t0x6=true := Bool.and_eq_true_iff.mpr ⟨t0x12ok,t0x13ok⟩
def t0x224 : Tree := .leaf ⟨true,7264748,4718592,8122234,8388608,0,2097152⟩
lemma t0x224ok : treeCheck nodes v0 ⟨4194304,4718592,0,2097152⟩ t0x224=true := by decide +kernel
def t0x225 : Tree := .leaf ⟨true,6935679,5242880,8122234,8388608,0,2097152⟩
lemma t0x225ok : treeCheck nodes v0 ⟨4718592,5242880,0,2097152⟩ t0x225=true := by decide +kernel
def t0x112 : Tree := .d (4718592) t0x224 t0x225
lemma t0x112ok : treeCheck nodes v0 ⟨4194304,5242880,0,2097152⟩ t0x112=true := Bool.and_eq_true_iff.mpr ⟨t0x224ok,t0x225ok⟩
def t0x113 : Tree := .leaf ⟨true,7264748,5242880,7264747,8122235,2097152,4194304⟩
lemma t0x113ok : treeCheck nodes v0 ⟨4194304,5242880,2097152,4194304⟩ t0x113=true := by decide +kernel
def t0x56 : Tree := .y (2097152) t0x112 t0x113
lemma t0x56ok : treeCheck nodes v0 ⟨4194304,5242880,0,4194304⟩ t0x56=true := Bool.and_eq_true_iff.mpr ⟨t0x112ok,t0x113ok⟩
def t0x228 : Tree := .leaf ⟨true,6548356,5767168,8122234,8388608,0,2097152⟩
lemma t0x228ok : treeCheck nodes v0 ⟨5242880,5767168,0,2097152⟩ t0x228=true := by decide +kernel
def t0x229 : Tree := .leaf ⟨true,6091677,6291456,8122234,8388608,0,2097152⟩
lemma t0x229ok : treeCheck nodes v0 ⟨5767168,6291456,0,2097152⟩ t0x229=true := by decide +kernel
def t0x114 : Tree := .d (5767168) t0x228 t0x229
lemma t0x114ok : treeCheck nodes v0 ⟨5242880,6291456,0,2097152⟩ t0x114=true := Bool.and_eq_true_iff.mpr ⟨t0x228ok,t0x229ok⟩
def t0x115 : Tree := .leaf ⟨true,6548356,6291456,7264747,8122235,2097152,4194304⟩
lemma t0x115ok : treeCheck nodes v0 ⟨5242880,6291456,2097152,4194304⟩ t0x115=true := by decide +kernel
def t0x57 : Tree := .y (2097152) t0x114 t0x115
lemma t0x57ok : treeCheck nodes v0 ⟨5242880,6291456,0,4194304⟩ t0x57=true := Bool.and_eq_true_iff.mpr ⟨t0x114ok,t0x115ok⟩
def t0x28 : Tree := .d (5242880) t0x56 t0x57
lemma t0x28ok : treeCheck nodes v0 ⟨4194304,6291456,0,4194304⟩ t0x28=true := Bool.and_eq_true_iff.mpr ⟨t0x56ok,t0x57ok⟩
def t0x58 : Tree := .leaf ⟨true,7264748,5242880,0,7264748,4194304,8388608⟩
lemma t0x58ok : treeCheck nodes v0 ⟨4194304,5242880,4194304,8388608⟩ t0x58=true := by decide +kernel
def t0x59 : Tree := .leaf ⟨true,6548356,6291456,0,7264748,4194304,8388608⟩
lemma t0x59ok : treeCheck nodes v0 ⟨5242880,6291456,4194304,8388608⟩ t0x59=true := by decide +kernel
def t0x29 : Tree := .d (5242880) t0x58 t0x59
lemma t0x29ok : treeCheck nodes v0 ⟨4194304,6291456,4194304,8388608⟩ t0x29=true := Bool.and_eq_true_iff.mpr ⟨t0x58ok,t0x59ok⟩
def t0x14 : Tree := .y (4194304) t0x28 t0x29
lemma t0x14ok : treeCheck nodes v0 ⟨4194304,6291456,0,8388608⟩ t0x14=true := Bool.and_eq_true_iff.mpr ⟨t0x28ok,t0x29ok⟩
def t0x240 : Tree := .leaf ⟨true,5548543,6815744,8122234,8388608,0,2097152⟩
lemma t0x240ok : treeCheck nodes v0 ⟨6291456,6815744,0,2097152⟩ t0x240=true := by decide +kernel
def t0x241 : Tree := .leaf ⟨true,4890233,7340032,8122234,8388608,0,2097152⟩
lemma t0x241ok : treeCheck nodes v0 ⟨6815744,7340032,0,2097152⟩ t0x241=true := by decide +kernel
def t0x120 : Tree := .d (6815744) t0x240 t0x241
lemma t0x120ok : treeCheck nodes v0 ⟨6291456,7340032,0,2097152⟩ t0x120=true := Bool.and_eq_true_iff.mpr ⟨t0x240ok,t0x241ok⟩
def t0x121 : Tree := .leaf ⟨true,5548543,7340032,7264747,8122235,2097152,4194304⟩
lemma t0x121ok : treeCheck nodes v0 ⟨6291456,7340032,2097152,4194304⟩ t0x121=true := by decide +kernel
def t0x60 : Tree := .y (2097152) t0x120 t0x121
lemma t0x60ok : treeCheck nodes v0 ⟨6291456,7340032,0,4194304⟩ t0x60=true := Bool.and_eq_true_iff.mpr ⟨t0x120ok,t0x121ok⟩
def t0x61 : Tree := .leaf ⟨true,4061118,8388608,7264747,8388608,0,4194304⟩
lemma t0x61ok : treeCheck nodes v0 ⟨7340032,8388608,0,4194304⟩ t0x61=true := by decide +kernel
def t0x30 : Tree := .d (7340032) t0x60 t0x61
lemma t0x30ok : treeCheck nodes v0 ⟨6291456,8388608,0,4194304⟩ t0x30=true := Bool.and_eq_true_iff.mpr ⟨t0x60ok,t0x61ok⟩
def t0x62 : Tree := .leaf ⟨true,5548543,7340032,0,7264748,4194304,8388608⟩
lemma t0x62ok : treeCheck nodes v0 ⟨6291456,7340032,4194304,8388608⟩ t0x62=true := by decide +kernel
def t0x63 : Tree := .leaf ⟨true,4061118,8388608,0,7264748,4194304,8388608⟩
lemma t0x63ok : treeCheck nodes v0 ⟨7340032,8388608,4194304,8388608⟩ t0x63=true := by decide +kernel
def t0x31 : Tree := .d (7340032) t0x62 t0x63
lemma t0x31ok : treeCheck nodes v0 ⟨6291456,8388608,4194304,8388608⟩ t0x31=true := Bool.and_eq_true_iff.mpr ⟨t0x62ok,t0x63ok⟩
def t0x15 : Tree := .y (4194304) t0x30 t0x31
lemma t0x15ok : treeCheck nodes v0 ⟨6291456,8388608,0,8388608⟩ t0x15=true := Bool.and_eq_true_iff.mpr ⟨t0x30ok,t0x31ok⟩
def t0x7 : Tree := .d (6291456) t0x14 t0x15
lemma t0x7ok : treeCheck nodes v0 ⟨4194304,8388608,0,8388608⟩ t0x7=true := Bool.and_eq_true_iff.mpr ⟨t0x14ok,t0x15ok⟩
def t0x3 : Tree := .y (0) t0x6 t0x7
lemma t0x3ok : treeCheck nodes v0 ⟨4194304,8388608,-8388608,8388608⟩ t0x3=true := Bool.and_eq_true_iff.mpr ⟨t0x6ok,t0x7ok⟩
def t0x1 : Tree := .d (4194304) t0x2 t0x3
lemma t0x1ok : treeCheck nodes v0 ⟨0,8388608,-8388608,8388608⟩ t0x1=true := Bool.and_eq_true_iff.mpr ⟨t0x2ok,t0x3ok⟩
end GateChecker.M0

end

section

open GrothendieckLB FiberDual GateChecker PanelAudit PanelBand PanelChain

theorem solution (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ)
    (hlo : (993405 : ℝ) / 1000000 ≤ c) (hhi : c ≤ 7/5) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c):= by
  have l0 : price M0.v0.lo ≤ c := by convert hlo using 1 <;> norm_num [price,M0.v0]
  exact band ha M0.starts M0.ok0 M0.v0 M0.t0x1 M0.b0ok M0.t0x1ok l0 (by convert hhi using 1 <;> norm_num [price,M0.v0])

end
