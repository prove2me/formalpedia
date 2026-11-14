-- Prove2me | solution 1 for OAI.AtomicTriangular.gaussianPair_poisson_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:39:35.429467+00:00
-- url     : https://prove2.me/submissions/4584d321-3a30-4059-ad85-e89aece083c4

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E026
import Definitions.Def_OAIQ334E033

section
-- module Solutions.OAIQ334_EU.Triangular_Certificate_WaveIntervals
attribute [-instance] _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex Polynomial

lemma hasDerivAt_P (s : ℂ) : HasDerivAt P (waveDerivative 1 s) s := by
  simpa only [waveDerivative_zero] using hasDerivAt_waveDerivative 0 s

lemma fourier_node_cancel (n : Node) : waveDerivative 0 n.val = 0 := by
  rw [waveDerivative_zero, P_node]

lemma fourier_node_deriv_cancel (n : Node) : waveDerivative 1 n.val = 0 := by
  rw [← (hasDerivAt_P n.val).deriv, deriv_P_node]

end AtomicTriangular.Construction

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators Topology
open Finset Filter

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators

noncomputable section

noncomputable section
open scoped BigOperators FourierTransform
namespace AtomicTriangular.Construction
open Complex

lemma spectralParameter_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < (spectralParameter k t).re := by
  simpa [spectralParameter] using mul_pos b_pos hk
lemma spectralParameter_inv {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (spectralParameter k t)⁻¹ = lambda k t := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  apply inv_eq_of_mul_eq_one_right
  unfold lambda spectralParameter
  push_cast
  field_simp
  simp only [waveDen]
  push_cast
  ring_nf
  simp [I_sq]

lemma spectral_exponent {k : ℝ} (hk : 0 < k) (v t : ℝ) (x : Plane) :
    -(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter k t =
      -(Real.pi:ℂ)*v*(radial x:ℂ)+I*Real.pi*zeta k v t*(radial x:ℂ) := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast b_pos.ne'
  have hd : (waveDen k t:ℂ) ≠ 0 := by exact_mod_cast (waveDen_pos hk t).ne'
  have hbs := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hbs
  rw [div_eq_mul_inv,spectralParameter_inv hk]
  unfold lambda zeta Xwave radial
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  rw [hbs]
  ring

lemma transformed_spectral_wave {k : ℝ} (hk : 0 < k) (v t : ℝ) (w : Plane) :
    𝓕 (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedWave k v t (radial w) := by
  have hfun : (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*t*(radial x:ℂ))) =
      (fun x : Plane => exp (-(Real.pi:ℂ)*spectralParameter k t*‖x‖^2)) := by
    funext x
    rw [← exp_add]
    congr 1
    unfold spectralParameter radial
    push_cast
    ring
  rw [hfun,complex_gaussian_transform _ (spectralParameter_pos hk t),
    spectralParameter_inv hk,spectral_exponent hk,exp_add]
  unfold transformedWave
  ring

end AtomicTriangular.Construction

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TriangularUniversal.Theta

lemma intGaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.exp (-a * (n : ℝ)^2)) := by
  have h := (isLittleO_exp_neg_mul_sq_cocompact
    (show 0 < (a : ℂ).re from ha) (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  have H : Summable (fun n : ℤ => Complex.exp (-(a : ℂ) * (n : ℂ)^2)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      (by simpa only [Function.comp_def, Complex.ofReal_intCast] using h)
  simpa [Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im] using H.norm

lemma real_Q_ge (m n : ℝ) : (m^2+n^2)/2 ≤ m^2+m*n+n^2 := by nlinarith [sq_nonneg (m+n)]

lemma triangular_summable {c : ℂ} (hc : 0 < c.re) :
    Summable (fun p : ℤ × ℤ => Complex.exp (-Real.pi*c*
      ((p.1:ℂ)^2+(p.1:ℂ)*p.2+(p.2:ℂ)^2))) := by
  have hg := intGaussian_summable (div_pos (mul_pos Real.pi_pos hc) (by norm_num : (0:ℝ)<2))
  apply Summable.of_norm
  refine (hg.mul_of_nonneg hg (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨m,n⟩
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.add_im,
    pow_two, Complex.mul_re, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith [mul_le_mul_of_nonneg_left (real_Q_ge (m:ℝ) (n:ℝ)) (mul_pos Real.pi_pos hc).le]

lemma inv_re_pos {c : ℂ} (hc : 0 < c.re) : 0 < (c⁻¹).re := by
  rw [Complex.inv_re]
  exact div_pos hc (Complex.normSq_pos.mpr (by intro h; simp [h] at hc))


lemma middle_summable {c : ℂ} (hc : 0 < c.re) :
    Summable (fun p : ℤ × ℤ => Complex.exp
      (-3*Real.pi*c*(p.2:ℂ)^2/4 + Real.pi*Complex.I*p.1*p.2 - Real.pi/c*(p.1:ℂ)^2)) := by
  have ha := intGaussian_summable (mul_pos Real.pi_pos (inv_re_pos hc))
  have hb := intGaussian_summable (show 0 < 3*Real.pi*c.re/4 by positivity)
  apply Summable.of_norm
  refine (ha.mul_of_nonneg hb (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)).of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨j,n⟩
  rw [Complex.norm_exp, ← Real.exp_add]
  apply le_of_eq
  congr 1
  simp only [div_eq_mul_inv, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.intCast_re, Complex.intCast_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im,
    Complex.inv_re, Complex.inv_im]
  norm_num
  ring

lemma first_step {c : ℂ} (hc : 0 < c.re) (n : ℤ) :
    (∑' m : ℤ, Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2))) =
      1 / c^(1/2:ℂ) * ∑' j : ℤ, Complex.exp
        (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have h := Complex.tsum_exp_neg_quadratic hc (-c*n/2)
  have hsplit (m : ℤ) :
      Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2)) =
        Complex.exp (-Real.pi*c*(n:ℂ)^2) *
        Complex.exp (-Real.pi*c*(m:ℂ)^2+2*Real.pi*(-c*n/2)*m) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hsplit]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro j
  rw [← Complex.exp_add]
  congr 1
  field_simp [hc0]
  ring_nf
  norm_num [show Complex.I^4 = 1 by norm_num [pow_succ, Complex.I_sq], Complex.I_sq]
  ring


lemma second_step {c : ℂ} (hc : 0 < c.re) (j : ℤ) :
    (∑' n : ℤ, Complex.exp
      (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2)) =
      1 / (3*c/4)^(1/2:ℂ) * ∑' k : ℤ,
        Complex.exp (-Real.pi*(4/(3*c))*((j:ℂ)^2-(j:ℂ)*k+(k:ℂ)^2)) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hpos : 0 < (3*c/4).re := by simp <;> linarith
  have h := Complex.tsum_exp_neg_quadratic hpos (Complex.I*j/2)
  have hsplit (n : ℤ) : Complex.exp
      (-3*Real.pi*c*(n:ℂ)^2/4 + Real.pi*Complex.I*j*n - Real.pi/c*(j:ℂ)^2) =
      Complex.exp (-Real.pi/c*(j:ℂ)^2) *
      Complex.exp (-Real.pi*(3*c/4)*(n:ℂ)^2+2*Real.pi*(Complex.I*j/2)*n) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp_rw [hsplit]
  rw [tsum_mul_left, h, ← mul_assoc, mul_comm (Complex.exp _) _, mul_assoc,
    ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  rw [← Complex.exp_add]
  congr 1
  field_simp [hc0]
  ring_nf
  norm_num [show Complex.I^4 = 1 by norm_num [pow_succ, Complex.I_sq], Complex.I_sq]
  ring


lemma dual_re_pos {c : ℂ} (hc : 0 < c.re) : 0 < (4/(3*c)).re := by
  have : (4/(3*c):ℂ) = (4/3:ℝ) * c⁻¹ := by push_cast <;> ring
  rw [this, Complex.re_ofReal_mul]
  exact mul_pos (by norm_num) (inv_re_pos hc)

lemma theta_raw {c : ℂ} (hc : 0 < c.re) :
    theta c = (1/c^(1/2:ℂ)) * (1/(3*c/4)^(1/2:ℂ)) * theta (4/(3*c)) := by
  have hstart : theta c = ∑' n : ℤ, ∑' m : ℤ,
      Complex.exp (-Real.pi*c*((m:ℂ)^2+(m:ℂ)*n+(n:ℂ)^2)) := by
    rw [theta, (triangular_summable hc).tsum_prod]
    apply tsum_congr; intro n
    apply tsum_congr; intro m
    congr 1; ring
  rw [hstart]
  simp_rw [first_step hc]
  rw [tsum_mul_left, (middle_summable hc).tsum_comm]
  simp_rw [second_step hc]
  rw [tsum_mul_left, ← mul_assoc]
  congr 1
  rw [theta, (triangular_summable (dual_re_pos hc)).tsum_prod]
  calc
    _ = (∑' j : ℤ, ∑' k : ℤ, Complex.exp
        (-Real.pi*(4/(3*c))*(((-j:ℤ):ℂ)^2+((-j:ℤ):ℂ)*k+(k:ℂ)^2))) := by
      apply tsum_congr; intro j
      apply tsum_congr; intro k
      congr 1; push_cast <;> ring
    _ = _ := by
      simpa only using! (Equiv.neg ℤ).tsum_eq (fun j => ∑' k : ℤ, Complex.exp
        (-Real.pi*(4/(3*c))*((j:ℂ)^2+(j:ℂ)*k+(k:ℂ)^2)))

lemma cpow_scale {c : ℂ} (hc0 : c ≠ 0) :
    (3*c/4)^(1/2:ℂ) = ((Real.sqrt 3 / 2 : ℝ):ℂ) * c^(1/2:ℂ) := by
  have hscale : (3*c/4:ℂ) = ((3/4:ℝ):ℂ)*c := by push_cast <;> ring
  rw [hscale, Complex.cpow_def_of_ne_zero (mul_ne_zero (by norm_num) hc0),
    Complex.log_ofReal_mul (by norm_num) hc0, add_mul, Complex.exp_add,
    ← Complex.cpow_def_of_ne_zero hc0]
  congr 1
  have hpow : ((3/4:ℝ):ℂ)^(1/2:ℂ) = ((Real.sqrt 3/2:ℝ):ℂ) := by
    calc
      _ = Complex.ofReal ((3/4:ℝ)^(1/2:ℝ)) := by
        convert (Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 3/4) (1/2)).symm using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast; try rfl)
      _ = _ := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num)]
        rw [show Real.sqrt (4 : ℝ) = 2 from
          (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]
  rw [Complex.cpow_def_of_ne_zero (by norm_num), ← Complex.ofReal_log (by norm_num)] at hpow
  exact hpow


lemma theta_transform {c : ℂ} (hc : 0 < c.re) :
    theta c = 2/((Real.sqrt 3:ℂ)*c) * theta (4/(3*c)) := by
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  rw [theta_raw hc]
  congr 1
  rw [div_mul_div_comm, one_mul, cpow_scale hc0]
  have h : c^(1/2:ℂ) * (((Real.sqrt 3/2:ℝ):ℂ) * c^(1/2:ℂ)) =
      ((Real.sqrt 3/2:ℝ):ℂ)*c := by
    rw [mul_left_comm, ← Complex.cpow_add _ _ hc0]
    norm_num
  rw [h]
  push_cast
  ring

end TriangularUniversal.Theta

end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Envelope_Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma Xwave_pos {k : ℝ} (hk : 0<k) (t : ℝ) : 0<Xwave k t := by
  unfold Xwave
  exact div_pos (by norm_num) (waveDen_pos hk t)
lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
lemma damping_Xwave_lower (q : Fin 2) {t : ℝ} (ht0 : 0≤t) (ht : t≤5/6) :
    1≤Real.pi*damping q*Xwave (damping q) t := by
  have hx := Xwave_antitone (damping_pos q) ht0 ht
  have hl : 1<3*damping q*Xwave (damping q) (5/6) := by
    fin_cases q <;> (first | (simp [damping,h,H,Xwave,waveDen]; all_goals first | (norm_num [damping,h,H,Xwave,waveDen]; done) | rfl | decide) | (norm_num [damping,h,H,Xwave,waveDen]; done) | norm_num [damping,h,H,Xwave,waveDen])
  have hp := Real.pi_gt_three
  have hq := damping_pos q
  have hxpos := Xwave_pos hq t
  calc
    1 ≤ 3*damping q*Xwave (damping q) (5/6) := hl.le
    _ ≤ 3*damping q*Xwave (damping q) t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Real.pi*damping q*Xwave (damping q) t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.le hq.le) hxpos.le

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Mixtures
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal

lemma triangularPoint_norm_sq (j k : ℤ) :
    b * ‖triangularPoint (j, k)‖ ^ 2 = (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one, Real.norm_eq_abs,
    sq_abs, mul_pow]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 / Real.sqrt (3 : ℝ))) ^ 2 = 2 / Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  rw [hc]
  dsimp [b]
  field_simp
  nlinarith [hs]

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Lattice_LatticeGeometry
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AtomicTriangular
lemma triangular_scale_eq : (Real.sqrt b)⁻¹=Real.sqrt (2/Real.sqrt 3) := by
  rw [←Real.sqrt_inv]
  congr 1
  simp [b,inv_div]
lemma triangularPoint_eq_support (v : ℤ × ℤ) : triangularPoint v=TriangularUniversal.triangularPoint v := by
  unfold triangularPoint TriangularUniversal.triangularPoint
  rw [triangular_scale_eq]
  congr 2
  unfold b
  ring_nf
lemma b_pos : 0 < b := by unfold b; positivity
lemma b_sq : b^2=3/4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
lemma triangularPoint_norm_sq (j k : ℤ) :
    b*‖triangularPoint (j,k)‖^2=(j:ℝ)^2+(j:ℝ)*k+(k:ℝ)^2 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_norm_sq j k
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_TailSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set
namespace AtomicTriangular.Construction
open MeasureTheory

lemma continuous_intervalIntegral_complex {f : ℂ → ℝ → ℂ}
    (hf : Continuous f.uncurry) (a b : ℝ) :
    Continuous (fun s => ∫ t in a..b, f s t) := by
  have h₁ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := a) (b := b))
  have h₂ := continuous_parametric_integral_of_continuous (μ := volume) hf (isCompact_Icc (a := b) (b := a))
  simpa only [intervalIntegral, integral_Icc_eq_integral_Ioc] using! h₁.sub h₂

lemma exponential_first_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    I*Real.pi * (∫ r in (0:ℝ)..t, exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1)/u := by
  have hc : I*(Real.pi:ℂ)*u ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  have hi := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, exp_zero] at hi
  simp_rw [show ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = (I*Real.pi*u)*(r:ℂ) by intro r; ring]
  rw [hi]
  field_simp

lemma exponential_second_integral (u : ℂ) (hu : u ≠ 0) (t : ℝ) :
    -(Real.pi:ℂ)^2 * (∫ r in (0:ℝ)..t, ((t:ℂ)-r)*exp (I*Real.pi*(r:ℂ)*u)) =
      (exp (I*Real.pi*(t:ℂ)*u)-1-I*Real.pi*(t:ℂ)*u)/u^2 := by
  let c : ℂ := I*Real.pi*u
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (by exact_mod_cast Real.pi_ne_zero)) hu
  let F : ℝ → ℂ := fun r => (((t:ℂ)-(r:ℂ))/c+1/c^2)*exp (c*(r:ℂ))
  have hd (x : ℝ) : HasDerivAt F (((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) x := by
    have hx : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := x))
    have hf := ((hx.const_sub (t:ℂ)).div_const c).add_const (1/c^2)
    have hh := hf.mul ((hx.const_mul c).cexp)
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (show IntervalIntegrable (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ))) volume 0 t from
      (by fun_prop : Continuous (fun x : ℝ => ((t:ℂ)-(x:ℂ))*exp (c*(x:ℂ)))).intervalIntegrable 0 t)
  have he : ∀ r : ℝ, I*(Real.pi:ℂ)*(r:ℂ)*u = c*(r:ℂ) := by intro r; dsimp [c] <;> ring
  simp_rw [he]
  rw [hi]
  dsimp [F]
  simp only [sub_self, zero_div, zero_add, mul_zero, exp_zero,
    mul_one, sub_zero]
  dsimp [c]
  field_simp
  simp [Complex.I_sq]
  ring

lemma continuous_integralDBasis (n : Node) : Continuous (integralDBasis n) := by
  unfold integralDBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma continuous_integralCBasis (n : Node) : Continuous (integralCBasis n) := by
  unfold integralCBasis
  refine continuous_finsetSum _ fun l _ => ?_
  exact continuous_const.mul <| continuous_const.mul
    (continuous_intervalIntegral_complex (by fun_prop) 0 (frequency l))

lemma exp_frequency_sub (s n : ℂ) (l : Fin 31) :
    exp (I*Real.pi*frequency l*n) * exp (I*Real.pi*frequency l*(s-n)) =
      exp (I*Real.pi*frequency l*s) := by
  rw [← exp_add]
  congr 1
  ring

lemma integralDBasis_eq (n : Node) : integralDBasis n = dBasis n := by
  apply (continuous_integralDBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_dBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [dBasis_eq n hsn]
  unfold integralDBasis
  simp_rw [exponential_first_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        ∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_one, mul_assoc, exp_frequency_sub]
    _ = P s := by
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hz, sub_zero, P_fourier]

lemma integralCBasis_eq (n : Node) : integralCBasis n = cBasis n := by
  apply (continuous_integralCBasis n).ext_on (dense_compl_singleton (n.val:ℂ))
    (differentiable_cBasis n).continuous
  intro s hs
  have hsn : s ≠ (n.val:ℂ) := hs
  rw [cBasis_eq n hsn]
  unfold integralCBasis
  simp_rw [exponential_second_integral (s-n.val) (sub_ne_zero.mpr hsn), ← mul_div_assoc,
    ← Finset.sum_div]
  congr 1
  calc
    _ = (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*s)) -
        (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) -
        (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) * (s-n.val) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [mul_sub, mul_sub, mul_one, mul_assoc, exp_frequency_sub]
      ring
    _ = P s := by
      have hd : (∑ l : Fin 31, fourierCoeff l * (I*Real.pi*frequency l) *
          exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_deriv_cancel n
      have hz : (∑ l : Fin 31, fourierCoeff l * exp (I*Real.pi*frequency l*n.val)) = 0 := by
        simpa [waveDerivative] using fourier_node_cancel n
      rw [hd, hz, zero_mul, sub_zero, sub_zero, P_fourier]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_SpectralCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma spectralCCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralCCLM n f = spectralC n f :=
  spectralCLinear_apply n f
lemma spectralDCLM_apply (n : Node) (f : C(Spectrum,ℂ)) : spectralDCLM n f = spectralD n f :=
  spectralDLinear_apply n f
lemma spectralPCLM_apply (f : C(Spectrum,ℂ)) : spectralPCLM f = spectralP f := by
  simp [spectralPCLM,spectralP]

lemma spectralCCLM_norm (n : Node) : ‖spectralCCLM n‖ ≤ cVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [cVariation, coeffAbs] <;> positivity) _
lemma spectralDCLM_norm (n : Node) : ‖spectralDCLM n‖ ≤ dVariation :=
  LinearMap.mkContinuous_norm_le _ (by simp only [dVariation, coeffAbs] <;> positivity) _

lemma extend_on (f : C(Spectrum,ℂ)) (t : ℝ) (ht : t ∈ Spectrum) :
    extend f t = f ⟨t,ht⟩ := by
  simp only [extend,Set.projIcc_of_mem _ ht]

lemma interval_frequency_subset (l : Fin 31) : Set.uIcc 0 (frequency l) ⊆ Spectrum := by
  have h := Set.uIcc_subset_uIcc (show (0:ℝ) ∈ Set.uIcc (-(5/6)) (5/6) by norm_num)
    (show frequency l ∈ Set.uIcc (-(5/6)) (5/6) by simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using frequency_mem l)
  simpa [Set.uIcc_of_le (by norm_num : (-(5/6):ℝ) ≤ 5/6)] using h

lemma spectralD_phase (n : Node) (s : ℂ) : spectralD n (phaseFunction s) = dBasis n s := by
  rw [← integralDBasis_eq]
  unfold spectralD integralDBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [← exp_add]
  congr 1
  ring

lemma spectralC_phase (n : Node) (s : ℂ) : spectralC n (phaseFunction s) = cBasis n s := by
  rw [← integralCBasis_eq]
  unfold spectralC integralCBasis
  apply Finset.sum_congr rfl
  intro l hl
  congr 2
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [extend_on _ t (interval_frequency_subset l ht)]
  change ((frequency l:ℂ)-t)*exp (-I*Real.pi*(t:ℂ)*n.val)*exp (I*Real.pi*(t:ℂ)*s) = _
  rw [mul_assoc,← exp_add]
  congr 2
  ring

lemma spectralP_phase (s : ℂ) : spectralP (phaseFunction s) = P s := by
  exact (P_fourier s).symm

lemma exponential_apply (f : C(Spectrum,ℂ)) (t : Spectrum) :
    (NormedSpace.exp f) t = exp (f t) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ t)
    (ContinuousMap.evalCLM ℂ t).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Complex.exp_eq_exp_ℂ] using h

lemma phaseFunction_exp (s : ℂ) : phaseFunction s = NormedSpace.exp (s • frequencyFunction) := by
  ext t
  rw [exponential_apply]
  change exp (I*Real.pi*(t.val:ℂ)*s) = exp (s*(I*Real.pi*(t.val:ℂ)))
  congr 1
  ring

lemma differentiable_phaseFunction : Differentiable ℂ phaseFunction := by
  have he : phaseFunction = fun s => NormedSpace.exp (s • frequencyFunction) := funext phaseFunction_exp
  rw [he]
  exact differentiable_exp_smul_const ℂ frequencyFunction

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierCLM
attribute [-instance] _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform RealInnerProductSpace
open Complex Filter Set MeasureTheory GaussianFourier
namespace AtomicTriangular.Construction

lemma transformedFunction_apply (k v : ℝ) (hk : 0 < k) (s : ℂ) (t : Spectrum) :
    transformedFunction k v hk s t = transformedWave k v t.val s := by
  simp only [transformedFunction,ContinuousMap.mul_apply,exponential_apply]
  change lambda k t.val * exp (s*(I*Real.pi*zeta k v t.val)) = _
  unfold transformedWave
  congr 2
  ring
lemma atomFunction_apply (k : ℝ) (x : Plane) (t : Spectrum) :
    atomFunction k x t = exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
      exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ)) := rfl
lemma continuous_atomFunction (k : ℝ) : Continuous (atomFunction k) := by
  have hs : Continuous (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))) := by
    unfold radial; fun_prop
  have ht : Continuous (fun x : Plane => phaseFunction (radial x:ℂ)) := by
    apply differentiable_phaseFunction.continuous.comp
    unfold radial; fun_prop
  simpa only [atomFunction] using! hs.smul ht
lemma atomFunction_bound (k : ℝ) (x : Plane) : ‖atomFunction k x‖ ≤ gaussian k x := by
  apply (ContinuousMap.norm_le _ (by unfold gaussian; positivity)).mpr
  intro t
  rw [atomFunction_apply,norm_mul]
  have hp : ‖exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp,mul_one,Complex.norm_exp]
  simp [gaussian]
lemma integrable_gaussian {k : ℝ} (hk : 0 < k) : Integrable (gaussian k) := by
  have hc : 0 < ((Real.pi*k*b:ℝ):ℂ).re := by
    simpa only [Complex.ofReal_re] using mul_pos (mul_pos Real.pi_pos hk) b_pos
  have hi := (integrable_cexp_neg_mul_sq_norm_add hc 0 (0:Plane)).norm
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp [gaussian,radial,Complex.norm_exp,mul_assoc,pow_two]
lemma integrable_atomFunction {k : ℝ} (hk : 0 < k) : Integrable (atomFunction k) :=
  (integrable_gaussian hk).mono' (continuous_atomFunction k).aestronglyMeasurable
    (ae_of_all _ (atomFunction_bound k))
lemma clm_fourier {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (f : Plane → E) (hf : Integrable f) (w : Plane) :
    𝓕 (fun x => L (f x)) w = L (𝓕 f w) := by
  simp only [Real.fourier_eq]
  have hh := L.integral_comp_comm ((Real.fourierIntegral_convergent_iff w).mpr hf)
  simpa only [Circle.smul_def,map_smul] using hh
lemma fourier_atomFunction {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (atomFunction k) w = exp (-(Real.pi:ℂ)*v*(radial w:ℂ)) •
      transformedFunction k v hk (radial w:ℂ) := by
  ext t
  have hh := clm_fourier (ContinuousMap.evalCLM ℂ t) (atomFunction k) (integrable_atomFunction hk) w
  have ha := transformed_spectral_wave hk v t.val w
  change 𝓕 (fun x => atomFunction k x t) w = (𝓕 (atomFunction k) w) t at hh
  rw [← hh]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*
    exp (I*Real.pi*(t.val:ℂ)*(radial x:ℂ))) w =
    exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*transformedFunction k v hk (radial w:ℂ) t
  rw [transformedFunction_apply]
  exact ha
lemma fourier_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) (v : ℝ) (w : Plane) :
    𝓕 (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) w =
      exp (-(Real.pi:ℂ)*v*(radial w:ℂ))*S (transformedFunction k v hk (radial w:ℂ)) := by
  have hh := clm_fourier S (atomFunction k) (integrable_atomFunction hk) w
  have he : (fun x => S (atomFunction k x)) =
      (fun x => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
    ext x
    simp only [atomFunction,map_smul,smul_eq_mul]
  rw [he,fourier_atomFunction hk v,map_smul] at hh
  exact hh
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_InputCLM
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Complex Filter Set MeasureTheory
namespace AtomicTriangular.Construction

lemma tailSpectral_term_bound (a : InputCoefficients) (n : TailNode) :
    ‖(a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val‖ ≤
      (|a.tailC n|+|a.tailD n|)*tailVariation := by
  have hc : cVariation ≤ tailVariation := by
    exact le_add_of_nonneg_right (by unfold dVariation coeffAbs; positivity)
  have hd : dVariation ≤ tailVariation := by
    exact le_add_of_nonneg_left (by unfold cVariation coeffAbs; positivity)
  calc
    _ ≤ ‖(a.tailC n:ℂ) • spectralCCLM n.val‖ + ‖(a.tailD n:ℂ) • spectralDCLM n.val‖ := by
      convert! norm_add_le ((a.tailC n:ℂ) • spectralCCLM n.val) ((a.tailD n:ℂ) • spectralDCLM n.val) using 1
      all_goals try with_reducible_and_instances rfl
    _ ≤ |a.tailC n| * ‖spectralCCLM n.val‖ + |a.tailD n| * ‖spectralDCLM n.val‖ := by
      have hn (r : ℝ) (T : C(Spectrum,ℂ) →L[ℂ] ℂ) : ‖(r:ℂ) • T‖ ≤ |r| * ‖T‖ := by
        apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg r) (norm_nonneg T))
        intro f
        change ‖(r:ℂ) * T f‖ ≤ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul_of_nonneg_left (T.le_opNorm f) (abs_nonneg r)
      exact add_le_add (hn _ _) (hn _ _)
    _ ≤ |a.tailC n| *tailVariation+|a.tailD n| *tailVariation :=
      add_le_add (mul_le_mul_of_nonneg_left ((spectralCCLM_norm n.val).trans hc) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ((spectralDCLM_norm n.val).trans hd) (abs_nonneg _))
    _ = _ := by ring

lemma summable_tailSpectral (a : InputCoefficients) :
    Summable (fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val) :=
  Summable.of_norm_bounded (E := C(Spectrum,ℂ) →L[ℂ] ℂ)
    (f := fun n => (a.tailC n:ℂ) • spectralCCLM n.val + (a.tailD n:ℂ) • spectralDCLM n.val)
    (a.summable.mul_right tailVariation) (tailSpectral_term_bound a)

lemma tailSpectral_apply (a : InputCoefficients) (f : C(Spectrum,ℂ)) :
    tailSpectral a f = (a.C:ℂ)*spectralP f +
      ∑' n : TailNode, ((a.tailC n:ℂ)*spectralC n.val f + (a.tailD n:ℂ)*spectralD n.val f) := by
  have ht := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_tailSpectral a)
  simpa only [tailSpectral,add_apply, smul_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul,spectralPCLM_apply,
    spectralCCLM_apply,spectralDCLM_apply] using congrArg (fun x => (a.C:ℂ)*spectralP f+x) ht

lemma tailSpectral_phase (a : InputCoefficients) (s : ℂ) :
    tailSpectral a (phaseFunction s) = tailInput a s := by
  simp only [tailSpectral_apply,spectralP_phase,spectralC_phase,spectralD_phase,tailInput]

lemma atomSpectral_apply (S : Fin 31 → ℂ) (f : C(Spectrum,ℂ)) :
    atomSpectral S f = ∑ j : Fin 31, S j*f ⟨frequency j,frequency_mem j⟩ := by
  simp [atomSpectral]

lemma atomSpectral_finiteC_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.cCoefficient j) (phaseFunction s) = finiteC j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteC_fourier]
  rfl
lemma atomSpectral_finiteD_phase (j : Fin 15) (s : ℂ) :
    atomSpectral (FiniteCertificate.dCoefficient j) (phaseFunction s) = finiteD j s := by
  rw [atomSpectral_apply,FiniteCertificate.finiteD_fourier]
  rfl

lemma finiteSpectral_phase (a : InputCoefficients) (s : ℂ) :
    finiteSpectral a (phaseFunction s) = finiteInput a s := by
  simp only [finiteSpectral,sum_apply,add_apply,
    smul_apply,smul_eq_mul,atomSpectral_finiteC_phase,atomSpectral_finiteD_phase,finiteInput]

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace AtomicTriangular.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedDeriv_real_of_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => (f x).re) = fun x : ℝ => (iteratedDeriv n f x).re := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hf.contDiff (n := ⊤)).differentiable_iteratedDeriv n (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x : ℂ)).hasDerivAt.real_of_complex.deriv

lemma entire_real_temperate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) :
    Function.HasTemperateGrowth (fun x : ℝ => (f x).re) := by
  obtain ⟨M,hM⟩ := hstrip
  refine ⟨hf.contDiff.real_of_complex, fun n => ⟨0,(n.factorial:ℝ)*M,?_⟩⟩
  intro x
  rw [pow_zero,mul_one,norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_real_of_complex hf]
  apply (Complex.abs_re_le_norm _).trans
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl (c := (x:ℂ)) (C := M) (fun z hz => hM z (by
      have hi := Complex.abs_im_le_norm (z-(x:ℂ))
      have he := Metric.mem_sphere.mp hz
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,← dist_eq_norm,he] using hi))
  simpa using hh

lemma dampedEntireSchwartz_apply (c : ℝ) (hc : 0 < c) (b : ℝ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hstrip : ∃ M : ℝ, ∀ z : ℂ, |z.im| ≤ 1 → ‖f z‖ ≤ M) (x : E) :
    dampedEntireSchwartz c hc b f hf hstrip x = Real.exp (-c*‖x‖^2)*(f (b*‖x‖^2)).re := by
  have ht := entire_real_temperate hf hstrip
  have hg : Function.HasTemperateGrowth (fun x : E => (f (b*‖x‖^2)).re) := by
    convert ht.comp (by fun_prop : Function.HasTemperateGrowth (fun x : E => b*‖x‖^2)) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp
  rw [dampedEntireSchwartz,SchwartzMap.smulLeftCLM_apply_apply hg,gaussianSchwartz_apply]
  simp [mul_comm]

end AtomicTriangular.Analysis
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology SchwartzMap
open Complex Filter Set
namespace AtomicTriangular.Construction

lemma inputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    inputSchwartz a x = Real.exp (-Real.pi*h*radial x)*(tailInput a (radial x)).re +
      Real.exp (-Real.pi*H*radial x)*(finiteInput a (radial x)).re := by
  simp only [inputSchwartz,add_apply,Analysis.dampedEntireSchwartz_apply,radial]
  push_cast
  congr 3 <;> ring

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_Realness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma P_conj (s : ℂ) : conj (P s) = P (conj s) := by
  simp only [P,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]

lemma dslope_conj_real {f : ℂ → ℂ} (hf : ∀ s, conj (f s) = f (conj s))
    (r : ℝ) (s : ℂ) : conj (dslope f (r:ℂ) s) = dslope f (r:ℂ) (conj s) := by
  have he : conj ∘ f ∘ conj = f := by
    ext z
    simp only [Function.comp_apply,hf,RCLike.conj_conj]
  have hd := congrFun (deriv_conj_conj (f := f)) (r:ℂ)
  rw [he] at hd
  simp only [Function.comp_apply,Complex.conj_ofReal] at hd
  by_cases hs : s = (r:ℂ)
  · subst s
    simpa only [Complex.conj_ofReal,dslope_same] using hd.symm
  · have hc : conj s ≠ (r:ℂ) := by
      intro h; apply hs
      have hh := congrArg conj h
      simpa using hh
    rw [dslope_of_ne _ hs,dslope_of_ne _ hc]
    simp only [slope_def_field,map_div₀,map_sub,hf,Complex.conj_ofReal]

lemma dBasis_conj (n : Node) (s : ℂ) : conj (dBasis n s) = dBasis n (conj s) := by
  simpa only [dBasis,Complex.ofReal_intCast] using dslope_conj_real P_conj (n.val:ℝ) s
lemma cBasis_conj (n : Node) (s : ℂ) : conj (cBasis n s) = cBasis n (conj s) := by
  simpa only [cBasis,Complex.ofReal_intCast] using dslope_conj_real (dBasis_conj n) (n.val:ℝ) s
lemma finiteC_conj (j : Fin 15) (s : ℂ) : conj (finiteC j s) = finiteC j (conj s) := by
  simp only [finiteC,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma finiteD_conj (j : Fin 15) (s : ℂ) : conj (finiteD j s) = finiteD j (conj s) := by
  simp only [finiteD,sineFactor,map_prod,map_pow,map_mul,← Complex.sin_conj,← Complex.cos_conj,map_sub,
    Complex.conj_ofReal,map_ofNat,map_intCast]
lemma tailInput_conj (a : InputCoefficients) (s : ℂ) : conj (tailInput a s) = tailInput a (conj s) := by
  simp only [tailInput,map_add,map_mul,Complex.conj_ofReal,P_conj,Complex.conj_tsum,cBasis_conj,dBasis_conj]
lemma finiteInput_conj (a : InputCoefficients) (s : ℂ) : conj (finiteInput a s) = finiteInput a (conj s) := by
  simp only [finiteInput,map_sum,map_add,map_mul,Complex.conj_ofReal,finiteC_conj,finiteD_conj]

lemma inputComplex_real (a : InputCoefficients) (x : Plane) : conj (inputComplex a x) = inputComplex a x := by
  simp only [inputComplex,map_add,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal,tailInput_conj,finiteInput_conj]
lemma inputComplex_re (a : InputCoefficients) (x : Plane) : (inputComplex a x).re = inputSchwartz a x := by
  rw [inputSchwartz_apply]
  simp [inputComplex,Complex.mul_re,← Complex.ofReal_mul,← Complex.ofReal_neg,Complex.exp_ofReal_re]
lemma inputComplex_eq (a : InputCoefficients) (x : Plane) : inputComplex a x = (inputSchwartz a x:ℂ) := by
  rw [← inputComplex_re]
  exact (Complex.conj_eq_iff_re.mp (inputComplex_real a x)).symm

lemma complexInputSchwartz_apply (a : InputCoefficients) (x : Plane) :
    complexInputSchwartz a x = inputComplex a x := by
  exact (inputComplex_eq a x).symm

end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Schwartz_FourierPair
attribute [-instance] _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology FourierTransform ComplexConjugate SchwartzMap
open Complex MeasureTheory
namespace AtomicTriangular.Construction

lemma integrable_spectral (S : C(Spectrum,ℂ) →L[ℂ] ℂ) {k : ℝ} (hk : 0 < k) :
    Integrable (fun x : Plane => exp (-(Real.pi:ℂ)*k*(radial x:ℂ))*S (phaseFunction (radial x:ℂ))) := by
  have hh := S.integrable_comp (integrable_atomFunction hk)
  simpa only [atomFunction,map_smul,smul_eq_mul,Function.comp_def] using hh
lemma inputComplex_spectral (a : InputCoefficients) (x : Plane) : inputComplex a x =
    exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ)) +
    exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ)) := by
  rw [tailSpectral_phase,finiteSpectral_phase]
  rfl
lemma fourier_inputComplex (a : InputCoefficients) : 𝓕 (inputComplex a) = outputComplex a := by
  ext w
  simp only [Real.fourier_eq,inputComplex_spectral,smul_add]
  rw [integral_add ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (tailSpectral a) h_pos))
    ((Real.fourierIntegral_convergent_iff w).mpr (integrable_spectral (finiteSpectral a) H_pos))]
  change 𝓕 (fun x => exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*tailSpectral a (phaseFunction (radial x:ℂ))) w +
    𝓕 (fun x => exp (-(Real.pi:ℂ)*H*(radial x:ℂ))*finiteSpectral a (phaseFunction (radial x:ℂ))) w = _
  rw [fourier_spectral _ h_pos h,fourier_spectral _ H_pos h]
  simp only [outputComplex,transformedInput,mul_add]

lemma coe_complexInputSchwartz (a : InputCoefficients) :
    (complexInputSchwartz a : Plane → ℂ) = inputComplex a := funext (complexInputSchwartz_apply a)
lemma coe_fourier_input (a : InputCoefficients) :
    ((𝓕 (complexInputSchwartz a) : 𝓢(Plane,ℂ)) : Plane → ℂ) = outputComplex a := by
  rw [SchwartzMap.fourier_coe,coe_complexInputSchwartz,fourier_inputComplex]
lemma pairSchwartz_apply (a₁ a₂ : InputCoefficients) (x : Plane) :
    pairSchwartz a₁ a₂ x = (pairComplex a₁ a₂ x).re := by
  simp only [pairSchwartz,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,add_apply,
    coe_fourier_input,complexInputSchwartz_apply,pairComplex,Pi.add_apply]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma radial_triangularPoint (v : ℤ × ℤ) :
    radial (AtomicTriangular.triangularPoint v)=(v.1:ℝ)^2+(v.1:ℝ)*v.2+(v.2:ℝ)^2 :=
  AtomicTriangular.triangularPoint_norm_sq v.1 v.2
lemma lattice_gaussian_summable {k : ℝ} (hk : 0<k) :
    Summable (fun v : ℤ × ℤ => gaussian k (AtomicTriangular.triangularPoint v)) := by
  have H := (TriangularUniversal.Theta.triangular_summable (show 0<(k:ℂ).re from hk)).norm
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  rw [gaussian,radial_triangularPoint,Complex.norm_exp]
  congr 1
  simp [pow_two,mul_re,mul_im]
lemma atom_lattice_summable {k : ℝ} (hk : 0<k) :
    Summable (fun v : ℤ × ℤ => atomFunction k (AtomicTriangular.triangularPoint v)) := by
  exact Summable.of_norm ((lattice_gaussian_summable hk).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => atomFunction_bound k _))
lemma dualAtomFunction_apply (q : Fin 2) (x : Plane) (t : Spectrum) :
    dualAtomFunction q x t=exp (-(Real.pi:ℂ)*h*(radial x:ℂ))*transformedWave (damping q) h t.val (radial x:ℂ) := by
  simp only [dualAtomFunction,ContinuousMap.smul_apply,smul_eq_mul,transformedFunction_apply]
lemma dualAtomFunction_bound (q : Fin 2) (x : Plane) :
    ‖dualAtomFunction q x‖ ≤ ‖lambdaFunction (damping q) (damping_pos q)‖*Real.exp (-radial x) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have ht : |t.val|≤5/6 := abs_le.mpr t.property
  have hx := damping_Xwave_lower q (abs_nonneg t.val) ht
  have he : Xwave (damping q) |t.val|=Xwave (damping q) t.val := by simp [Xwave,waveDen]
  rw [he] at hx
  have hl : ‖lambda (damping q) t.val‖ ≤ ‖lambdaFunction (damping q) (damping_pos q)‖ :=
    (lambdaFunction (damping q) (damping_pos q)).norm_coe_le_norm t
  rw [dualAtomFunction_apply,transformedWave,norm_mul,norm_mul,norm_exp,norm_exp]
  have h1 : (-(Real.pi:ℂ)*h*(radial x:ℂ)).re=-Real.pi*h*radial x := by simp
  have h2 : (I*Real.pi*zeta (damping q) h t.val*(radial x:ℂ)).re=
      -Real.pi*(damping q*Xwave (damping q) t.val-h)*radial x := by
    rw [mul_re]
    simp only [ofReal_re,ofReal_im,mul_zero,sub_zero,wavePhase_re]
  rw [h1,h2]
  calc
    _ = ‖lambda (damping q) t.val‖*Real.exp (-(Real.pi*damping q*Xwave (damping q) t.val)*radial x) := by
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul hl (Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ radial x from mul_nonneg b_pos.le (sq_nonneg ‖x‖)])) (Real.exp_pos _).le (norm_nonneg _)
lemma dualAtom_lattice_summable (q : Fin 2) :
    Summable (fun v : ℤ × ℤ => dualAtomFunction q (AtomicTriangular.triangularPoint v)) := by
  have hs := lattice_gaussian_summable (inv_pos.mpr Real.pi_pos)
  have he (v : ℤ × ℤ) : gaussian Real.pi⁻¹ (AtomicTriangular.triangularPoint v)=
      Real.exp (-radial (AtomicTriangular.triangularPoint v)) := by
    unfold gaussian
    congr 1
    field_simp
  simp_rw [he] at hs
  exact Summable.of_norm ((hs.mul_left ‖lambdaFunction (damping q) (damping_pos q)‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun v => dualAtomFunction_bound q _))
lemma dualAtom_gaussian (q : Fin 2) (x : Plane) (t : Spectrum) :
    dualAtomFunction q x t=(spectralParameter (damping q) t.val)⁻¹*
      exp (-(Real.pi:ℂ)*(‖x‖:ℂ)^2/spectralParameter (damping q) t.val) := by
  rw [spectralParameter_inv (damping_pos q),spectral_exponent (damping_pos q) h]
  rw [dualAtomFunction_apply,transformedWave,exp_add]
  ring
lemma scalar_lattice_poisson (q : Fin 2) (t : Spectrum) :
    (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v) t)=
      ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) t := by
  let c : ℂ := (damping q:ℂ)-I*(t.val:ℂ)
  have hc : 0 < c.re := by simpa [c] using damping_pos q
  have hc0 : c≠0 := by intro he; simp [he] at hc
  have hb : (b:ℂ)≠0 := by exact_mod_cast b_pos.ne'
  have hr := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hr
  have hatom (v : ℤ × ℤ) : atomFunction (damping q) (AtomicTriangular.triangularPoint v) t=
      exp (-Real.pi*c*((v.1:ℂ)^2+(v.1:ℂ)*v.2+(v.2:ℂ)^2)) := by
    rw [atomFunction_apply,←exp_add,radial_triangularPoint]
    congr 1
    dsimp [c]
    push_cast
    ring
  have hlam : (spectralParameter (damping q) t.val)⁻¹=2/((Real.sqrt 3:ℂ)*c) := by
    change ((b:ℂ)*c)⁻¹=_
    unfold b
    push_cast
    ring_nf
  have hdual (v : ℤ × ℤ) : dualAtomFunction q (AtomicTriangular.triangularPoint v) t=
      (2/((Real.sqrt 3:ℂ)*c))*exp (-Real.pi*(4/(3*c))*((v.1:ℂ)^2+(v.1:ℂ)*v.2+(v.2:ℂ)^2)) := by
    rw [dualAtom_gaussian,hlam]
    congr 1
    congr 1
    have hv := congrArg (fun r : ℝ => (r:ℂ)) (radial_triangularPoint v)
    dsimp [radial] at hv
    push_cast at hv
    change -(Real.pi:ℂ)*(‖AtomicTriangular.triangularPoint v‖:ℂ)^2/((b:ℂ)*c)=_
    field_simp [hb,hc0]
    linear_combination -(4:ℂ)*(b:ℂ)*hv + (4:ℂ)*(‖AtomicTriangular.triangularPoint v‖:ℂ)^2*hr
  simp_rw [hatom,hdual]
  rw [tsum_mul_left]
  exact TriangularUniversal.Theta.theta_transform hc
lemma atom_lattice_poisson (q : Fin 2) :
    (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) := by
  ext t
  have h1 := (ContinuousMap.evalCLM ℂ t).map_tsum (atom_lattice_summable (damping_pos q))
  have h2 := (ContinuousMap.evalCLM ℂ t).map_tsum (dualAtom_lattice_summable q)
  change (∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v)) t=
    ∑' v : ℤ × ℤ, atomFunction (damping q) (AtomicTriangular.triangularPoint v) t at h1
  change (∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v)) t=
    ∑' v : ℤ × ℤ, dualAtomFunction q (AtomicTriangular.triangularPoint v) t at h2
  rw [h1,h2,scalar_lattice_poisson]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_PairPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma inputComplex_spectral_atoms (a : InputCoefficients) (x : Plane) :
    inputComplex a x=tailSpectral a (atomFunction h x)+finiteSpectral a (atomFunction H x) := by
  simp only [inputComplex_spectral,atomFunction,map_smul,smul_eq_mul]
lemma outputComplex_spectral_atoms (a : InputCoefficients) (x : Plane) :
    outputComplex a x=tailSpectral a (dualAtomFunction 0 x)+finiteSpectral a (dualAtomFunction 1 x) := by
  simp only [dualAtomFunction,map_smul,smul_eq_mul,outputComplex,transformedInput,mul_add]
  rfl
lemma inputComplex_lattice_summable (a : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => inputComplex a (AtomicTriangular.triangularPoint v)) := by
  simp_rw [inputComplex_spectral_atoms]
  exact ((tailSpectral a).summable (atom_lattice_summable h_pos)).add
    ((finiteSpectral a).summable (atom_lattice_summable H_pos))
lemma outputComplex_lattice_summable (a : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => outputComplex a (AtomicTriangular.triangularPoint v)) := by
  simp_rw [outputComplex_spectral_atoms]
  exact ((tailSpectral a).summable (dualAtom_lattice_summable 0)).add
    ((finiteSpectral a).summable (dualAtom_lattice_summable 1))
lemma input_output_lattice_poisson (a : InputCoefficients) :
    (∑' v : ℤ × ℤ, inputComplex a (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, outputComplex a (AtomicTriangular.triangularPoint v) := by
  simp_rw [inputComplex_spectral_atoms,outputComplex_spectral_atoms]
  rw [((tailSpectral a).summable (atom_lattice_summable h_pos)).tsum_add
    ((finiteSpectral a).summable (atom_lattice_summable H_pos)),
    ((tailSpectral a).summable (dualAtom_lattice_summable 0)).tsum_add
    ((finiteSpectral a).summable (dualAtom_lattice_summable 1)),
    ←(tailSpectral a).map_tsum (atom_lattice_summable h_pos),
    ←(finiteSpectral a).map_tsum (atom_lattice_summable H_pos),
    ←(tailSpectral a).map_tsum (dualAtom_lattice_summable 0),
    ←(finiteSpectral a).map_tsum (dualAtom_lattice_summable 1)]
  change tailSpectral a (∑' v : ℤ × ℤ, atomFunction (damping 0) (AtomicTriangular.triangularPoint v))+
    finiteSpectral a (∑' v : ℤ × ℤ, atomFunction (damping 1) (AtomicTriangular.triangularPoint v))=_
  rw [atom_lattice_poisson,atom_lattice_poisson]
lemma pairComplex_lattice_summable (a₁ a₂ : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v)) :=
  (inputComplex_lattice_summable a₁).add (outputComplex_lattice_summable a₂)
lemma pairComplex_lattice_poisson (a₁ a₂ : InputCoefficients) :
    (∑' v : ℤ × ℤ, pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, pairComplex a₂ a₁ (AtomicTriangular.triangularPoint v) := by
  simp only [pairComplex,Pi.add_apply]
  rw [(inputComplex_lattice_summable a₁).tsum_add (outputComplex_lattice_summable a₂),
    (inputComplex_lattice_summable a₂).tsum_add (outputComplex_lattice_summable a₁),
    input_output_lattice_poisson,input_output_lattice_poisson,add_comm]
lemma pairSchwartz_lattice_summable (a₁ a₂ : InputCoefficients) :
    Summable (fun v : ℤ × ℤ => pairSchwartz a₁ a₂ (AtomicTriangular.triangularPoint v)) := by
  simpa only [pairSchwartz_apply,Complex.reCLM_apply] using Complex.reCLM.summable (pairComplex_lattice_summable a₁ a₂)
lemma pairSchwartz_lattice_poisson (a₁ a₂ : InputCoefficients) :
    (∑' v : ℤ × ℤ, pairSchwartz a₁ a₂ (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, pairSchwartz a₂ a₁ (AtomicTriangular.triangularPoint v) := by
  simp only [pairSchwartz_apply]
  change (∑' v : ℤ × ℤ, Complex.reCLM (pairComplex a₁ a₂ (AtomicTriangular.triangularPoint v)))=
    ∑' v : ℤ × ℤ, Complex.reCLM (pairComplex a₂ a₁ (AtomicTriangular.triangularPoint v))
  rw [←Complex.reCLM.map_tsum (pairComplex_lattice_summable a₁ a₂),
    ←Complex.reCLM.map_tsum (pairComplex_lattice_summable a₂ a₁),pairComplex_lattice_poisson]
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_GaussianPoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_lattice_summable (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    Summable (fun v : ℤ × ℤ => actualSchwartz side z hz hzB (AtomicTriangular.triangularPoint v)) := by
  exact (pairSchwartz_lattice_summable _ _).const_smul (normalizingDen z)⁻¹
lemma actualSchwartz_lattice_poisson {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) :
    (∑' v : ℤ × ℤ, actualSchwartz 0 z hz hzB (AtomicTriangular.triangularPoint v))=
      ∑' v : ℤ × ℤ, actualSchwartz 1 z hz hzB (AtomicTriangular.triangularPoint v) := by
  simp only [actualSchwartz,smul_apply,smul_eq_mul,tsum_mul_left]
  rw [pairSchwartz_lattice_poisson]
  rfl
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators SchwartzMap
open Complex
namespace AtomicTriangular
lemma gaussian_eq_radial (α : ℝ) (x : Plane) :
    gaussian α x=Construction.gaussian (α/b) x := by
  unfold gaussian Construction.gaussian Construction.radial
  congr 1
  field_simp [b_pos.ne']
  rfl
lemma gaussian_lattice_summable {α : ℝ} (hα : 0<α) :
    Summable (fun v : ℤ × ℤ => gaussian α (triangularPoint v)) := by
  simp_rw [gaussian_eq_radial]
  exact Construction.lattice_gaussian_summable (div_pos hα b_pos)
lemma complex_gaussian_lattice (α : ℝ) :
    (∑' v : ℤ × ℤ, (gaussian α (triangularPoint v):ℂ))=
      TriangularUniversal.Theta.theta ((α/b:ℝ):ℂ) := by
  apply tsum_congr
  intro v
  rw [gaussian_eq_radial,Construction.gaussian,Construction.radial_triangularPoint,ofReal_exp]
  congr 1
  push_cast
  ring
lemma gaussian_lattice_theta {α : ℝ} (hα : 0<α) :
    (∑' v : ℤ × ℤ, gaussian α (triangularPoint v))=
      α⁻¹*∑' v : ℤ × ℤ, gaussian α⁻¹ (triangularPoint v) := by
  have ha0 : (α:ℂ)≠0 := by exact_mod_cast hα.ne'
  have hb0 : (b:ℂ)≠0 := by exact_mod_cast b_pos.ne'
  have hr := congrArg (fun r : ℝ => (r:ℂ)) b_sq
  push_cast at hr
  have he1 : (2:ℂ)/((Real.sqrt 3:ℂ)*((α/b:ℝ):ℂ))=((α⁻¹:ℝ):ℂ) := by
    unfold b
    push_cast
    field_simp
  have he2 : (4:ℂ)/(3*((α/b:ℝ):ℂ))=((α⁻¹/b:ℝ):ℂ) := by
    push_cast
    field_simp [ha0,hb0]
    linear_combination 4*hr
  have ht := TriangularUniversal.Theta.theta_transform (show 0<((α/b:ℝ):ℂ).re from div_pos hα b_pos)
  rw [he1,he2,←complex_gaussian_lattice,←complex_gaussian_lattice] at ht
  have hfirst := Complex.ofRealCLM.map_tsum (gaussian_lattice_summable hα)
  have hsecond := Complex.ofRealCLM.map_tsum (gaussian_lattice_summable (inv_pos.mpr hα))
  simp only [Complex.ofRealCLM_apply] at hfirst hsecond
  rw [←hfirst,←hsecond,←ofReal_mul] at ht
  exact_mod_cast ht

lemma largeGaussianPair_poisson {α : ℝ} (hα : 1 ≤ α) :
    GaussianLatticePoisson (largeGaussianPair hα) where
  first_summable := Construction.actualSchwartz_lattice_summable 0 _ _
  second_summable := Construction.actualSchwartz_lattice_summable 1 _ _
  poisson := Construction.actualSchwartz_lattice_poisson _ _
lemma reciprocalGaussianPair_poisson {α : ℝ} (hα : 0<α) (p : GaussianPair α⁻¹)
    (hp : GaussianLatticePoisson p) : GaussianLatticePoisson (reciprocalGaussianPair hα p) where
  first_summable := by
    change Summable (fun v => gaussianSchwartz α hα (triangularPoint v)-α⁻¹*p.second (triangularPoint v))
    simp_rw [gaussianSchwartz_apply]
    exact (gaussian_lattice_summable hα).sub (hp.second_summable.mul_left _)
  second_summable := by
    change Summable (fun v => α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) (triangularPoint v)-p.first (triangularPoint v)))
    simp_rw [gaussianSchwartz_apply]
    exact ((gaussian_lattice_summable (inv_pos.mpr hα)).sub hp.first_summable).mul_left _
  poisson := by
    change (∑' v, (gaussianSchwartz α hα (triangularPoint v)-α⁻¹*p.second (triangularPoint v)))=
      ∑' v, α⁻¹*(gaussianSchwartz α⁻¹ (inv_pos.mpr hα) (triangularPoint v)-p.first (triangularPoint v))
    simp_rw [gaussianSchwartz_apply]
    rw [(gaussian_lattice_summable hα).tsum_sub (hp.second_summable.mul_left _),
      tsum_mul_left,tsum_mul_left,(gaussian_lattice_summable (inv_pos.mpr hα)).tsum_sub hp.first_summable,
      gaussian_lattice_theta hα,hp.poisson,mul_sub]
lemma gaussianPair_poisson_eu_oai (α : ℝ) (hα : 0<α) : GaussianLatticePoisson (gaussianPair α hα) := by
  unfold gaussianPair
  split_ifs with h
  · exact largeGaussianPair_poisson h
  · exact reciprocalGaussianPair_poisson hα _ (largeGaussianPair_poisson _)
end AtomicTriangular
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.gaussianPair_poisson_eu_oai := @OAI.AtomicTriangular.gaussianPair_poisson_eu_oai
