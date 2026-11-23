-- Prove2me | solution 1 for GrothendieckLB.fiber_dual_tail
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:51:42.48982+00:00
-- url     : https://prove2.me/submissions/c388f7a8-2336-4acb-b977-8038f7552e5b

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

lemma central_even {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) (s : ℝ) (hs : 0 ≤ s)
    (hs' : s ≤ 1/8) : |evenP a s| ≤ amp a * (1 - (33/100)*s^2) := by
  let u := (s^2-1)/Real.sqrt 2
  have hu : u^2 = (s^2-1)^2/2 := by simp [u, div_pow, Real.sq_sqrt]
  have cs : (evenP a s)^2 ≤ (1-oddSq a) * (1+u^2) := by
    rw [← (odd_range ha).2.2]
    change (a 0 + a 2 * u)^2 ≤ _
    nlinarith only [sq_nonneg (a 0 * u - a 2)]
  have hs2 : s^2 ≤ (1/8:ℝ)^2 := pow_le_pow_left₀ hs hs' 2
  have hs4 := mul_le_mul_of_nonneg_left hs2 (sq_nonneg s)
  have hn : 1 + u^2 ≤ 3/2 * (1-(33/100)*s^2)^2 := by
    rw [hu]
    nlinarith only [hs4, sq_nonneg s]
  have hpos : 0 ≤ 1-(33/100)*s^2 := by linarith only [hs2]
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (mul_nonneg (show 0 ≤ amp a from Real.sqrt_nonneg _) hpos)
  rw [sq_abs,mul_pow,amp_sq ha]
  have hprod := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (odd_range ha).2.1)
  nlinarith only [cs,hprod]

lemma central_odd (a : Fin 4 → ℝ) (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1/8) :
    |oddP a s| ≤ slope a * s := by
  let u := (s^2-3)/Real.sqrt 6
  have hu : u^2 = (s^2-3)^2/6 := by simp [u, div_pow, Real.sq_sqrt]
  have hid : oddP a s = s * (a 1 + a 3*u) := by dsimp [oddP, u]; ring
  rw [hid, abs_mul, abs_of_nonneg hs, mul_comm (slope a)]
  apply mul_le_mul_of_nonneg_left _ hs
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (show 0 ≤ slope a from Real.sqrt_nonneg _)
  rw [sq_abs,slope_sq]
  have cs : (a 1 + a 3*u)^2 ≤ oddSq a * (1+u^2) := by
    unfold oddSq; nlinarith only [sq_nonneg (a 1 * u-a 3)]
  have hs2 : s^2 ≤ 6 := (pow_le_pow_left₀ hs hs' 2).trans (by norm_num)
  have hpoly := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) (sub_nonpos.mpr hs2)
  have hsm : 1 + u^2 ≤ 5/2 := by rw [hu]; nlinarith only [hpoly]
  have hh := mul_le_mul_of_nonneg_left hsm (show 0 ≤ oddSq a by unfold oddSq; positivity)
  exact cs.trans (by linarith only [hh])

lemma middle_small (c s : ℝ) (hc : 12 ≤ c) (hl : 3/2 ≤ c*s) (hs : 0 ≤ s) (hu : s ≤ 1) :
    3/2 + 3/2*s^2 - s^4/2 + s^6/6 ≤ (c*s)^2 := by
  have cs : (3/2:ℝ)^2 ≤ (c*s)^2 := pow_le_pow_left₀ (by norm_num) hl 2
  have h2 : s^2 ≤ 1 := by simpa using pow_le_pow_left₀ hs hu 2
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (s^2))
  have hc2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 12) hc 2) (sq_nonneg s)
  nlinarith only [cs,h4,hc2,sq_nonneg (s^2)]

lemma middle_large (c s : ℝ) (hc : 12 ≤ c) (hs : 1 ≤ s)
    (hu : s^2 ≤ (31/20:ℝ)^2*c) :
    3/2 + 3/2*s^2 - s^4/2 + s^6/6 ≤ (c*s)^2 := by
  have h1 : (1:ℝ) ≤ s^2 := by simpa using pow_le_pow_left₀ (by norm_num) hs 2
  have h4 := pow_le_pow_left₀ (sq_nonneg s) hu 2
  have h6 := mul_le_mul_of_nonneg_right h4 (sq_nonneg s)
  have hc2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 12) hc 2) (sq_nonneg s)
  nlinarith only [h1,h6,hc2,sq_nonneg (s^2)]

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

noncomputable def tailStart (c : ℝ) := (31/20)*Real.sqrt c
lemma start_sq {c : ℝ} (hc : 0 ≤ c) : tailStart c ^ 2 = (31/20:ℝ)^2*c := by
  rw [tailStart,mul_pow,Real.sq_sqrt hc]
lemma start_ge {c : ℝ} (hc : 12 ≤ c) : 2 ≤ tailStart c := by
  have hh : (3:ℝ) ≤ Real.sqrt c := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  unfold tailStart; linarith

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

lemma remote_bound (c : ℝ) (hc : 12 ≤ c) :
    ABPOnline.cG * (tailStart c ^ 2 + 2) * E (tailStart c) ≤ (3/100) / c^3 := by
  let t : ℝ := (31/20:ℝ)^2
  let H := fun z : ℝ => z^3*(t*z+2)*Real.exp (-(t*z/2))
  have dt (z : ℝ) : HasDerivAt H
      (z^2*Real.exp (-(t*z/2))*(6+4*t*z - (t*z/2)*(t*z+2))) z := by
    convert! ((((hasDerivAt_pow 3 z).mul (((hasDerivAt_id z).const_mul t).add_const 2)).mul
      ((((hasDerivAt_id z).const_mul t).div_const 2).neg.exp))) using 1 <;> dsimp [H] <;> ring
  have hanti : AntitoneOn H (Ici 12) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) (fun z _ => (dt z).continuousAt.continuousWithinAt)
      (fun z _ => (dt z).differentiableAt.differentiableWithinAt)
    intro z hz
    have h12 : 12 ≤ z := interior_subset hz
    rw [(dt z).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    have ht : 28 ≤ t*z := by dsimp [t]; linarith only [h12]
    rw [mul_assoc (4:ℝ) t z]
    generalize t*z = x at ht ⊢
    nlinarith only [ht, mul_nonneg (sub_nonneg.mpr ht) (by linarith only [ht] : 0 ≤ x)]
  have hν : ν ≤ 4/5 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · apply (div_le_iff₀ Real.pi_pos).mpr
      linarith only [Real.pi_gt_d2]
  have initial : (4/5:ℝ)*H 12 ≤ 3/100 := by
    change 4/5 * (12^3*(t*12+2)*Real.exp (-(t*12/2))) ≤ _
    rw [Real.exp_neg]
    have he := Real.sum_le_exp_of_nonneg (x := t*12/2) (by dsimp [t]; norm_num) 24
    norm_num [t, Finset.sum_range_succ, Nat.factorial] at he ⊢
    field_simp
    linarith only [he]
  have hh := hanti (mem_Ici.mpr (le_refl 12)) (mem_Ici.mpr hc) hc
  have hp : 0 ≤ H c := by dsimp [H, t]; positivity
  have h := mul_le_mul hν hh hp (by norm_num)
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < c) 3)).mpr
  rw [E,start_sq (by linarith)]
  change ν * (t*c+2) * Real.exp (-(t*c/2)) * c^3 ≤ _
  calc _ = ν * H c := by dsimp [H]; ring
    _ ≤ _ := h.trans initial

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

open MeasureTheory ProbabilityTheory Real Filter Set
namespace CubicTriangle

noncomputable abbrev θ : ℝ := 99/100
noncomputable abbrev curv : ℝ := 33/100
noncomputable def line (A t s : ℝ) := max (A-t*s) 0
noncomputable def corr (A t s : ℝ) := (Iic (θ*A/t)).indicator (fun z => A*curv*z^2) s
noncomputable def major (A t s : ℝ) := line A t s - corr A t s

lemma basic {A t c : ℝ} (hA : 0 ≤ A) (ha : A ≤ 123/100) (hc : 12 ≤ c)
    (ht : (43/50)*c ≤ t) :
    0 < t ∧ 0 ≤ θ*A/t ∧ θ*A/t ≤ 3/(2*c) ∧ (3/(2*c) : ℝ) ≤ 1/8 := by
  have cpos : 0 < c := by linarith
  have tpos : 0 < t := by linarith
  refine ⟨tpos, div_nonneg (mul_nonneg (by norm_num) hA) tpos.le, ?_, ?_⟩
  · rw [div_le_div_iff₀ tpos (by positivity)]
    have hh := mul_le_mul_of_nonneg_right ha cpos.le
    dsimp [θ]
    nlinarith only [hh,ht,cpos]
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hc]

lemma central_branch {A t c s : ℝ} (hA : 0 ≤ A) (ha : A ≤ 123/100) (hc : 12 ≤ c)
    (ht : (43/50)*c ≤ t) (hs : 0 ≤ s) (hs' : s ≤ 3/(2*c)) :
    max (A*(1-curv*s^2)-t*s) 0 ≤ major A t s := by
  have h := basic hA ha hc ht
  have h1 : s ≤ 1/8 := hs'.trans h.2.2.2
  have h2 : s^2 ≤ (1/8:ℝ)^2 := pow_le_pow_left₀ hs h1 2
  unfold major line corr
  by_cases hz : s ≤ θ*A/t
  · rw [Set.indicator_of_mem (show s ∈ Iic (θ*A/t) from hz)]
    have hts := (le_div_iff₀ h.1).mp hz
    have hc' := mul_le_mul_of_nonneg_left (show curv*s^2 ≤ 1-θ by dsimp [curv,θ]; linarith only [h2]) hA
    have hp : 0 ≤ A-t*s := by dsimp [θ] at hts; linarith only [hts, hA]
    rw [max_eq_left hp, max_eq_left (by nlinarith only [hts,hc'] : 0 ≤ A*(1-curv*s^2)-t*s)]
    linarith
  · rw [Set.indicator_of_notMem (show s ∉ Iic (θ*A/t) from hz),sub_zero]
    apply max_le_max_right
    dsimp [curv]
    nlinarith only [mul_nonneg hA (sq_nonneg s)]

lemma major_nonneg {A t c s : ℝ} (hA : 0 ≤ A) (ha : A ≤ 123/100) (hc : 12 ≤ c)
    (ht : (43/50)*c ≤ t) (hs : 0 ≤ s) : 0 ≤ major A t s := by
  by_cases h : s ≤ 3/(2*c)
  · exact (le_max_right _ _).trans (central_branch hA ha hc ht hs h)
  · have hz := (basic hA ha hc ht).2.2.1.trans_lt (lt_of_not_ge h)
    simp only [major,corr,Set.indicator_of_notMem (show s ∉ Iic (θ*A/t) from not_le.mpr hz),sub_zero,line,le_max_iff]
    exact Or.inr le_rfl

lemma line_formula {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    IntegrableOn (line A t) (Ioi 0) ∧ (∫ s in Ioi 0, line A t s) = A^2/(2*t) := by
  let r := A/t
  have hr : 0 ≤ r := div_nonneg hA ht.le
  have eqf : line A t = (Iic r).indicator (fun s => A-t*s) := by
    funext s
    by_cases hs : s ≤ r
    · rw [Set.indicator_of_mem (show s ∈ Iic r from hs), line, max_eq_left]
      linarith only [(le_div_iff₀ ht).mp hs]
    · rw [Set.indicator_of_notMem (show s ∉ Iic r from hs), line, max_eq_right]
      linarith only [(div_lt_iff₀ ht).mp (lt_of_not_ge hs)]
  rw [eqf]
  have hcont : Continuous (fun s : ℝ => A-t*s) := by fun_prop
  have hint := hcont.intervalIntegrable (μ := volume) 0 r
  constructor
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, Set.Ioi_inter_Iic]
    exact hint.1
  · rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.inter_comm, Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hr,
      intervalIntegral.integral_sub (f := fun _ : ℝ => A) (g := fun x : ℝ => t*x) intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, smul_eq_mul, zero_pow (by decide : 2 ≠ 0),r]
    field_simp
    ring

lemma major_formula {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) :
    IntegrableOn (major A t) (Ioi 0) ∧
    (∫ s in Ioi 0, major A t s) = A^2/(2*t) - (A*curv)/3*(θ*A/t)^3 := by
  have hline := line_formula hA ht
  let r := θ*A/t
  have hr : 0 ≤ r := div_nonneg (mul_nonneg (by norm_num) hA) ht.le
  have hi := (show Continuous (fun s : ℝ => A*curv*s^2) by fun_prop).intervalIntegrable (μ := volume) 0 r
  have hcorr : IntegrableOn (corr A t) (Ioi 0) := by
    unfold corr IntegrableOn
    rw [integrable_indicator_iff measurableSet_Iic, IntegrableOn, Measure.restrict_restrict measurableSet_Iic,
      Set.inter_comm, Set.Ioi_inter_Iic]
    exact hi.1
  refine ⟨hline.1.sub hcorr, ?_⟩
  change (∫ s in Ioi 0, line A t s - corr A t s) = _
  rw [integral_sub hline.1 hcorr, hline.2]
  unfold corr
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, Set.inter_comm,
    Set.Ioi_inter_Iic, ← intervalIntegral.integral_of_le hr, intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

end CubicTriangle

end

section

open Real Filter Set MeasureTheory ProbabilityTheory GrothendieckLB FiberDual
open CubicEnvelope CubicTriangle GaussianRemote HighBudget

namespace CubicLargePrice

lemma dimensions {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) {c : ℝ} (hc : 12 ≤ c) :
    amp a ≤ 123/100 ∧ slope a ≤ 8/5 ∧ (43/50)*c ≤ c - slope a ∧ (43/50)*c ≤ c + slope a := by
  have h0 := (odd_range ha).1
  have h1 := (odd_range ha).2.1
  have hA : amp a ≤ 123/100 := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num)
    (by rw [amp_sq ha]; linarith only [h0])
  have hB : slope a ≤ 8/5 := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num)
    (by rw [slope_sq]; linarith only [h1])
  have hB0 : 0 ≤ slope a := Real.sqrt_nonneg _
  exact ⟨hA,hB,by linarith only [hB,hc],by linarith only [hc,hB0]⟩

noncomputable def remote (c s : ℝ) :=
  (Ioi (tailStart c)).indicator (fun t : ℝ => 2*(t^3*E t)) s

lemma pointwise {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) {c s : ℝ} (hc : 12 ≤ c) (hs : 0 ≤ s) :
    fold a c s * E s ≤ major (amp a) (c-slope a) s + major (amp a) (c+slope a) s + remote c s := by
  let A := amp a
  let B := slope a
  have d := dimensions ha hc
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have cpos : 0 < c := by linarith
  have E0 : 0 ≤ E s := (Real.exp_pos _).le
  have m1 := major_nonneg hA d.1 hc d.2.2.1 hs
  have m2 := major_nonneg hA d.1 hc d.2.2.2 hs
  have f0 : 0 ≤ fold a c s := add_nonneg (le_max_right _ _) (le_max_right _ _)
  by_cases small : s ≤ 3/(2*c)
  · have sm := small.trans (basic hA d.1 hc d.2.2.1).2.2.2
    have hsr : s ≤ tailStart c := sm.trans ((by norm_num : (1/8:ℝ) ≤ 2).trans (start_ge hc))
    rw [remote, Set.indicator_of_notMem (show s ∉ Ioi (tailStart c) from not_lt.mpr hsr),add_zero]
    let X := A*(1-curv*s^2)
    let Y := B*s
    have hp := folded_mono (evenP a s) (oddP a s) X Y (c*s)
      (central_even ha s hs sm) (central_odd a s hs sm)
    have ybound : Y ≤ c*s := mul_le_mul_of_nonneg_right (d.2.1.trans (by linarith)) hs
    have hX : 0 ≤ X := (abs_nonneg _).trans (central_even ha s hs sm)
    have heq : max (|X-Y|-c*s) 0 = max (X-Y-c*s) 0 := by
      by_cases H : 0 ≤ X-Y
      · rw [abs_of_nonneg H]
      · rw [abs_of_neg (lt_of_not_ge H), max_eq_right (by linarith only [ybound,hX] : -(X-Y)-c*s ≤ 0),
          max_eq_right (by linarith only [H,mul_nonneg cpos.le hs] : X-Y-c*s ≤ 0)]
    rw [heq, show X+Y-c*s = A*(1-curv*s^2)-(c-B)*s by dsimp [X,Y];ring,
      show X-Y-c*s = A*(1-curv*s^2)-(c+B)*s by dsimp [X,Y];ring] at hp
    have sc := central_branch hA d.1 hc d.2.2.1 hs small
    have sc' := central_branch hA d.1 hc d.2.2.2 hs small
    have hfold : fold a c s ≤ major A (c-B) s + major A (c+B) s := by
      rw [fold,poly_split,poly_neg];exact hp.trans (add_le_add sc sc')
    have E1 : E s ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg s])
    exact (mul_le_of_le_one_right f0 E1).trans hfold
  · have hsum := add_nonneg m1 m2
    by_cases mid : s ≤ tailStart c
    · rw [remote,Set.indicator_of_notMem (show s ∉ Ioi (tailStart c) from not_lt.mpr mid),add_zero]
      have h3 : 3/2 ≤ c*s := by
        have H := (div_lt_iff₀ (show 0 < 2*c by positivity)).mp (lt_of_not_ge small)
        linarith only [H]
      have h2 : s^2 ≤ (31/20:ℝ)^2*c := (pow_le_pow_left₀ hs mid 2).trans_eq (start_sq cpos.le)
      have hk := (le_total s 1).elim (middle_small c s hc h3 hs) (fun h => middle_large c s hc h h2)
      have ppos : |poly a s| ≤ c*s := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (mul_nonneg cpos.le hs)
        (by rw [sq_abs]; exact (poly_sq ha s).trans hk)
      have pn : |poly a (-s)| ≤ c*s := le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (mul_nonneg cpos.le hs)
        (by rw [sq_abs]; have hh := poly_sq ha (-s); nlinarith only [hh,hk])
      simp only [fold,max_eq_right (sub_nonpos.mpr ppos),max_eq_right (sub_nonpos.mpr pn),add_zero,zero_mul]
      exact hsum
    · have hsr := lt_of_not_ge mid
      rw [remote, Set.indicator_of_mem (show s ∈ Ioi (tailStart c) from hsr)]
      have H := far_poly ha ((start_ge hc).trans hsr.le)
      have hcS := mul_nonneg cpos.le hs
      have hs3 : 0 ≤ s^3 := pow_nonneg hs _
      have hF : fold a c s ≤ 2*s^3 := by
        unfold fold
        have h1 : max (|poly a s|-c*s) 0 ≤ s^3 := max_le (by linarith only [H.1,hcS]) hs3
        have h2 : max (|poly a (-s)|-c*s) 0 ≤ s^3 := max_le (by linarith only [H.2,hcS]) hs3
        linarith only [h1,h2]
      have hmul := mul_le_mul_of_nonneg_right hF E0
      change _ ≤ _ + 2*(s^3*E s)
      linarith only [hmul,hsum]

lemma integrated {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) {c : ℝ} (hc : 12 ≤ c) :
    let A := amp a
    let B := slope a
    J a c ≤ (ABPOnline.cG/2) *
      ((A^2/(2*(c-B))-(A*curv)/3*(θ*A/(c-B))^3) +
       (A^2/(2*(c+B))-(A*curv)/3*(θ*A/(c+B))^3)) + (3/100)/c^3 := by
  intro A B
  have d := dimensions ha hc
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have h1 := major_formula hA (basic hA d.1 hc d.2.2.1).1
  have h2 := major_formula hA (basic hA d.1 hc d.2.2.2).1
  have hr : 0 ≤ tailStart c := (by norm_num : (0:ℝ) ≤ 2).trans (start_ge hc)
  have hR := gauss_tail (tailStart c) hr
  have hRi : IntegrableOn (remote c) (Ioi 0) := by
    unfold remote IntegrableOn
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left hr]
    exact hR.1.const_mul 2
  have hRint : (∫ s in Ioi 0, remote c s) = 2*((tailStart c)^2+2)*E (tailStart c) := by
    unfold remote
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,Ioi_inter_Ioi,
      max_eq_left hr,integral_const_mul,hR.2]; ring
  have H := integral_mono_of_nonneg (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun s => fold a c s * E s)
    (Eventually.of_forall fun s => mul_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _)) (Real.exp_pos _).le)
    ((h1.1.add h2.1).add hRi)
    ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => pointwise ha hc (le_of_lt hs))
  simp only [Pi.add_apply] at H
  rw [integral_add (f := fun s => major A (c-B) s + major A (c+B) s) (g := remote c)
    (h1.1.add h2.1) hRi, integral_add h1.1 h2.1,h1.2,h2.2,hRint] at H
  rw [folded_integral]
  have H' := mul_le_mul_of_nonneg_left H (div_nonneg ν_pos.le (by norm_num : (0:ℝ) ≤ 2))
  have hremote := remote_bound c hc
  linarith only [H',hremote]

end CubicLargePrice

end

section

open Real MeasureTheory ProbabilityTheory GrothendieckLB FiberDual CubicEnvelope CubicTriangle CubicLargePrice HighBudget

private lemma recip_cubes (c B : ℝ) (hB : 0 ≤ B) (hl : 0 < c-B) :
    2/c^3 ≤ 1/(c-B)^3 + 1/(c+B)^3 := by
  have hc : 0 < c := by linarith
  have hp : 0 < c+B := by linarith
  have h2 : B^2 ≤ c^2 := pow_le_pow_left₀ hB (by linarith) 2
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
  have hpos : 0 ≤ B^4 - 3*B^2*c^2 + 6*c^4 := by
    nlinarith only [h4,sq_nonneg (B^2),sq_nonneg (c^2)]
  have hh := mul_nonneg (sq_nonneg B) hpos
  field_simp
  nlinarith only [hh]

private lemma scalar_margin (u c : ℝ) (hu : 0 ≤ u) (hc : 12 ≤ c) :
    31/100 ≤ (49/50)*u*c^2 + curv*θ^3*(1-u)^2 := by
  have hc2 : (12:ℝ)^2 ≤ c^2 := pow_le_pow_left₀ (by norm_num) hc 2
  by_cases h : 1/100 ≤ u
  · have hh := mul_le_mul h hc2 (by norm_num) hu
    dsimp [curv,θ]
    nlinarith only [hh,sq_nonneg (1-u)]
  · have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 99/100)
      (by linarith only [h] : 99/100 ≤ 1-u) 2
    have hpos := mul_nonneg hu (sq_nonneg c)
    dsimp [curv,θ]
    nlinarith only [hh,hpos]

private lemma sqrt_minor (c : ℝ) (hc : 0 < c) :
    (1/(2*c))*(1-1/(4*c^2)) ≤ Real.sqrt (1+c^2) - c := by
  let S := Real.sqrt (1+c^2)
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hs : S^2 = 1+c^2 := Real.sq_sqrt (by positivity)
  have hA : S ≤ c + 1/(2*c) := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
    rw [hs]
    field_simp
    nlinarith only [sq_nonneg c]
  have hid : S - c = 1/(S+c) := by
    apply (eq_div_iff (by linarith : S+c ≠ 0)).mpr
    nlinarith only [hs]
  change _ ≤ S - c
  rw [hid]
  calc _ ≤ 1/(2*c+1/(2*c)) := by
              apply (le_div_iff₀ (by positivity)).mpr
              calc _ = 1 - 1/(16*c^4) := by field_simp; ring
                _ ≤ _ := sub_le_self _ (by positivity)
    _ ≤ 1/(S+c) := by apply one_div_le_one_div_of_le (by positivity); linarith only [hA]

private lemma algebra {a : Fin 4 → ℝ} (ha : ∑ j, a j ^ 2 = 1) (c : ℝ) (hc : 12 ≤ c) :
    J a c ≤ R * (Real.sqrt (1+c^2)-c) := by
  let A := amp a
  let B := slope a
  let u := oddSq a
  let K := 3*ν/(4*c)
  let D := c^2-B^2
  let T := curv*θ^3
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hA2 : A^2 = 3/2*(1-u) := amp_sq ha
  have hB2 : B^2 = (5/2)*u := slope_sq
  have hu : 0 ≤ u := (odd_range ha).1
  have hu1 : u ≤ 1 := (odd_range ha).2.1
  have cp : 0 < c := by linarith
  have cm : 0 < c-B := (basic hA (dimensions ha hc).1 hc (dimensions ha hc).2.2.1).1
  have ca : 0 < c+B := by linarith
  have hD : 0 < D := by
    change 0 < c^2-B^2
    rw [sq_sub_sq]; positivity
  have hK : 0 ≤ K := by dsimp [K]; exact div_nonneg (by linarith only [ν_pos]) (by positivity)
  have H := integrated ha hc
  change J a c ≤ ν/2 * ((A^2/(2*(c-B)) - (A*curv)/3*(θ*A/(c-B))^3) +
      (A^2/(2*(c+B)) - (A*curv)/3*(θ*A/(c+B))^3)) + (3/100)/c^3 at H
  have hlead : ν/2 * (A^2/(2*(c-B)) + A^2/(2*(c+B))) = K*((1-u)*c^2/D) := by
    rw [hA2]; dsimp [K,D]
    field_simp [(show c^2-B^2 ≠ 0 from hD.ne')]; ring
  have hloss : K * (T*(1-u)^2/c^2) ≤ ν/2 *
      ((A*curv)/3*(θ*A/(c-B))^3 + (A*curv)/3*(θ*A/(c+B))^3) := by
    let k := ν/2 * (A*curv)/3*(θ*A)^3
    have kn : 0 ≤ k := by dsimp [k,curv,θ]; have := ν_pos; positivity
    have hrec := mul_le_mul_of_nonneg_left (recip_cubes c B hB cm) kn
    have hx : K * (T*(1-u)^2/c^2) = k*(2/c^3) := by
      have hA4 := congrArg (fun z : ℝ => z^2) hA2
      dsimp [K,k,T,curv,θ]
      field_simp
      nlinarith only [congrArg (fun z : ℝ => ν*z) hA4]
    rw [hx]
    exact hrec.trans_eq (by dsimp [k]; field_simp [cm.ne',ca.ne'])
  have hZ : (1-u)*c^2/D ≤ 1-49/50*u := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D]; rw [hB2]
    have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 12) hc 2) hu
    nlinarith only [hh,hu,sq_nonneg u]
  have hz := mul_le_mul_of_nonneg_left hZ hK
  have hmar := scalar_margin u c hu hc
  change _ ≤ 49/50*u*c^2 + T*(1-u)^2 at hmar
  have hstep : K*(1-49/50*u) - K*(T*(1-u)^2/c^2) ≤ K*(1-(31/100)/c^2) := by
    rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ hK
    have hh := div_le_div_of_nonneg_right hmar (sq_nonneg c)
    have hEq : (49/50*u*c^2+T*(1-u)^2)/c^2 = 49/50*u + T*(1-u)^2/c^2 := by
      rw [add_div,mul_div_cancel_right₀ _ (pow_ne_zero _ cp.ne')]
    rw [hEq] at hh
    linarith only [hh]
  have hbnd : J a c ≤ K*(1-(31/100)/c^2) + (3/100)/c^3 := by
    linarith only [H,hlead,hloss,hz,hstep]
  have hnear : K*(1-(31/100)/c^2)+(3/100)/c^3 ≤ K*(1-(1/4)/c^2) := by
    dsimp [K]; field_simp; nlinarith only [ν_low]
  have hm := mul_le_mul_of_nonneg_left (sqrt_minor c cp) (show 0 ≤ R by dsimp [R]; linarith only [ν_pos])
  apply hbnd.trans (hnear.trans _)
  convert hm using 1
  dsimp [R,K]; ring

theorem solution (a : Fin 4 → ℝ) (ha : ∑ j, a j ^ 2 = 1) (c : ℝ) (hlo : (12 : ℝ) ≤ c) :
    stdExp (fun s => max (|∑ j, a j * he j s| - c * |s|) 0) ≤
      (3 * ABPOnline.cG / 2) * (Real.sqrt (1 + c ^ 2) - c) :=
  algebra ha c hlo

end
