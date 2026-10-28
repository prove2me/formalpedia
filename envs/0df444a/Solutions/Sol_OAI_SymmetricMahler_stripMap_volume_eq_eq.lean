-- Prove2me | solution 1 for OAI.SymmetricMahler.stripMap_volume_eq_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:35:37.761196+00:00
-- url     : https://prove2.me/submissions/d5688a0c-3f07-4646-bdf0-bc9190eef370

import Mathlib
import Definitions.Def_OAIQ2Ma000

section
-- module Solutions.OAIQ2_Mah.Compat
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiniteStrips
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-dimensional algebra for the finite-strip construction.
The image estimate and algebraic injectivity step do not require
the analytic mass inequality. -/

namespace SymmetricMahler

open Finset

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The transpose identity in the image bound. -/
theorem transpose_pairing (A : J → I → ℝ) (p : J → ℝ) (v : I → ℝ) :
    (∑ i, push A p i * v i) = ∑ j, p j * measurement A v j := by
  simp only [push, measurement, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

end SymmetricMahler

namespace SymmetricMahler

open Finset
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The relevant vertical fibers need only support strict monotonicity on
an interval, rather than on all of the real line. -/
theorem vertical_map_injOn (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (S : J → Set ℝ) (f : J → ℝ → ℝ)
    (hf : ∀ j, StrictMonoOn (f j) (S j)) :
    Set.InjOn (fun y : I → ℝ => push A (fun j => f j (measurement A y j)))
      {y | ∀ j, measurement A y j ∈ S j} := by
  classical
  intro y hy y' hy' hout
  by_contra hne
  have hnonneg : ∀ j, 0 ≤ (f j (measurement A y j) - f j (measurement A y' j)) *
      (measurement A y j - measurement A y' j) := by
    intro j
    rcases le_total (measurement A y j) (measurement A y' j) with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((hf j).monotoneOn (hy j) (hy' j) h)) (sub_nonpos.mpr h)
    · exact mul_nonneg
        (sub_nonneg.mpr ((hf j).monotoneOn (hy' j) (hy j) h)) (sub_nonneg.mpr h)
  have hdiff : measurement A y ≠ measurement A y' := fun h => hne (hA h)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hdiff
  have hpos : 0 < (f j (measurement A y j) - f j (measurement A y' j)) *
      (measurement A y j - measurement A y' j) := by
    rcases lt_or_gt_of_ne hj with h | h
    · exact mul_pos_of_neg_of_neg
        (sub_neg.mpr (hf j (hy j) (hy' j) h)) (sub_neg.mpr h)
    · exact mul_pos (sub_pos.mpr (hf j (hy' j) (hy j) h)) (sub_pos.mpr h)
  have hp : 0 < ∑ k, (f k (measurement A y k) - f k (measurement A y' k)) *
      (measurement A y k - measurement A y' k) :=
    sum_pos' (fun k _ => hnonneg k) ⟨j, mem_univ j, hpos⟩
  have hz : (∑ i, push A (fun k => f k (measurement A y k) -
      f k (measurement A y' k)) i * (y i - y' i)) = 0 := by
    apply sum_eq_zero
    intro i _
    have hi := congrFun hout i
    simp only [push] at hi ⊢
    simp only [mul_sub, sum_sub_distrib, hi, sub_self, zero_mul]
  rw [transpose_pairing] at hz
  have hmeasurement : ∀ k, measurement A (fun i => y i - y' i) k =
      measurement A y k - measurement A y' k := by
    intro k
    simp only [measurement, mul_sub, sum_sub_distrib]
  simp only [hmeasurement] at hz
  linarith

/-- The full real map is injective when each vertical slice satisfies the
hypotheses proved above. This also permits the fiber interval to depend on x. -/
theorem full_map_injOn (A : J → I → ℝ)
    (hA : Function.Injective (measurement A))
    (S : (I → ℝ) → J → Set ℝ) (f : (I → ℝ) → J → ℝ → ℝ)
    (hf : ∀ x j, StrictMonoOn (f x j) (S x j)) :
    Set.InjOn
      (fun z : (I → ℝ) × (I → ℝ) =>
        (z.1, push A (fun j => f z.1 j (measurement A z.2 j))))
      {z | ∀ j, measurement A z.2 j ∈ S z.1 j} := by
  intro z hz w hw h
  have hx : z.1 = w.1 := by
    simpa only using congrArg (fun q : (I → ℝ) × (I → ℝ) => q.1) h
  change ∀ j, measurement A z.2 j ∈ S z.1 j at hz
  change ∀ j, measurement A w.2 j ∈ S w.1 j at hw
  have hv : push A (fun j => f z.1 j (measurement A z.2 j)) =
      push A (fun j => f z.1 j (measurement A w.2 j)) := by
    simpa only [hx] using congrArg Prod.snd h
  have hy := vertical_map_injOn A hA (S z.1) (f z.1) (hf z.1) hz
    (by simpa only [Set.mem_ofPred_eq, hx] using hw) hv
  exact Prod.ext hx hy

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalSeries
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conformal series and its logarithmic derivative. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma D_zero : D 0 = 1 := by
  unfold D
  rw [tsum_eq_single 0]
  · norm_num
  · intro k hk
    have hp : 2*k ≠ 0 := by omega
    simp [zero_pow hp]

lemma pi_cast_ne : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- Holomorphicity on the open unit disk. -/
theorem differentiableOn_F : DifferentiableOn ℂ F (ball 0 1) := by
  intro w hw
  exact (hasDerivAt_F_series (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem F_zero : F 0 = 0 := by simp [F, series_zero]

/-- The removable value of the derivative at zero. -/
theorem hasDerivAt_F_zero : HasDerivAt F (8/(Real.pi : ℂ)^2) 0 := by
  simpa [D_zero] using hasDerivAt_F_series (w := 0) (by norm_num)

lemma log_cayley_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    Complex.log (cayley w) ≠ 0 := by
  intro h
  have hq0 : cayley w ≠ 0 := div_ne_zero (one_add_ne hw) (one_sub_ne hw)
  have he : cayley w = 1 := by rw [← Complex.exp_log hq0, h, Complex.exp_zero]
  have hl : 1+w = 1-w := (div_eq_one_iff_eq (one_sub_ne hw)).mp he
  apply hw0
  linear_combination (1/2 : ℂ) * hl

/-- Nonvanishing of the derivative. -/
theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ pi_cast_ne)
  · rw [(hasDerivAt_F_log hw hw0).deriv]
    exact mul_ne_zero
      (div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw0))
      (log_cayley_ne_zero hw hw0)

/-- Conjugation symmetry of the conformal map. -/
theorem F_conj (w : ℂ) : F (starRingEnd ℂ w) = starRingEnd ℂ (F w) := by
  simp only [F, series, term, map_mul, map_div₀, map_pow, map_ofNat,
    map_natCast, Complex.conj_ofReal, Complex.conj_tsum]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular geometry of the conformal series. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma polar_re (r θ : ℝ) : (polar r θ).re = r * Real.cos θ := by
  simp [polar]

theorem B_lt_two_div_pi (r θ : ℝ) : B r θ < 2 / Real.pi := by
  have h := mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two (2*r*Real.sin θ/(1-r^2)))
    (show 0 < 4 / Real.pi^2 by positivity)
  have he : 4 / Real.pi^2 * (Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he] using h

lemma polar_pi_sub (r θ : ℝ) : polar r (Real.pi-θ) = -starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_pi_sub, Real.sin_pi_sub]

lemma F_real_im (r : ℝ) : (F (r : ℂ)).im = 0 := by
  have h := congrArg Complex.im (F_conj (r : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

theorem Q_pi_sub (r θ : ℝ) : Q r (Real.pi-θ) = -Q r θ := by
  simp only [Q, polar_pi_sub, F_odd, F_conj, Complex.neg_re, Complex.conj_re]

theorem S_zero (r : ℝ) : S r 0 = 0 := by rw [S, polar_zero, F_real_im]

theorem S_pi (r : ℝ) : S r Real.pi = 0 := by
  rw [S, polar_pi, F_odd, Complex.neg_im, F_real_im, neg_zero]

theorem Q_mem_Ioo {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Q r θ ∈ Ioo (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := Q_strictAntiOn hr hr1
  constructor
  · simpa only [Q_pi] using ha ⟨hθ.le, hθπ.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hθπ
  · simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.le, hθπ.le⟩ hθ

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ErrorBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real

lemma radial_log_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r ≤ log ((1+r)/(1-r)) := by
  have hd : 0 < 1-r := by linarith
  have hfrac : 1/(1-r) ≤ (1+r)/(1-r) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have hlog := log_le_log (one_div_pos.mpr hd) hfrac
  rw [one_div, log_inv] at hlog
  have hlin := log_le_sub_one_of_pos hd
  linarith

/-- A concrete global positive lower bound for the radial derivative. -/
theorem radial_derivative_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    4/Real.pi^2 ≤ radialDerivative r := by
  have hratio : 1 ≤ log ((1+r)/(1-r))/r :=
    (le_div_iff₀ hr).2 (by simpa using radial_log_lower hr hr1)
  have h := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4/Real.pi^2 by positivity)
  calc
    4/Real.pi^2 = (4/Real.pi^2)*1 := (mul_one _).symm
    _ ≤ (4/Real.pi^2)*(log ((1+r)/(1-r))/r) := h
    _ = radialDerivative r := by dsimp [radialDerivative]; field_simp

end SymmetricMahler

namespace SymmetricMahler
open Real Set

/-- The global M-increment estimate obtained from the actual radial derivative,
with only open-interval derivatives required, including when the left endpoint is 0. -/
theorem radial_increment_lower {M : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hcont : ContinuousOn M (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt M (radialDerivative x) x) :
    (4/Real.pi^2)*(b-a) ≤ M b-M a := by
  rcases hab.eq_or_lt with heq | hlt
  · subst b
    simp
  · obtain ⟨x, hx, heq⟩ := exists_hasDerivAt_eq_slope M radialDerivative hlt hcont hderiv
    have hlow := radial_derivative_lower (show 0 < x by linarith [hx.1])
      (show x < 1 by linarith [hx.2])
    rw [heq] at hlow
    exact (le_div_iff₀ (sub_pos.mpr hlt)).1 hlow

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_RadialBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex MeasureTheory Set

lemma continuousOn_radialMap : ContinuousOn radialMap (Ico 0 1) := by
  intro r hr
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_nonneg hr.1] using hr.2
  have h := (MahlerConformal.hasDerivAt_F_series hw).real_of_complex
  exact h.continuousAt.continuousWithinAt

theorem hasDerivAt_radialMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt radialMap (radialDerivative r) r := by
  have hw : ‖(r : ℂ)‖ < 1 := by simpa [Complex.norm_real, abs_of_pos hr] using hr1
  have hw0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := (MahlerConformal.hasDerivAt_F_log hw hw0).real_of_complex
  have hq : 0 ≤ (1+r)/(1-r) := by positivity
  have hcast : (1+(r : ℂ))/(1-(r : ℂ)) = (((1+r)/(1-r) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hd : 4/((Real.pi : ℂ)^2*(r : ℂ))*Complex.log ((1+(r : ℂ))/(1-(r : ℂ))) =
      (radialDerivative r : ℂ) := by
    rw [hcast, ← Complex.ofReal_log hq]
    dsimp [radialDerivative]
    push_cast
    rfl
  rw [hd, Complex.ofReal_re] at h
  exact h

/-- The actual series obeys the quantitative radial increment estimate. -/
theorem conformal_radial_increment {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (4/Real.pi^2)*(b-a) ≤ radialMap b-radialMap a := by
  apply radial_increment_lower ha hab hb
  · exact continuousOn_radialMap.mono (fun x hx => ⟨ha.trans hx.1, hx.2.trans_lt hb⟩)
  · intro x hx
    exact hasDerivAt_radialMap (by linarith [hx.1]) (hx.2.trans hb)

/-- Strict radial monotonicity is proved on the entire positive real radius. -/
theorem strictMonoOn_radialMap : StrictMonoOn radialMap (Ico 0 1) := by
  intro a ha b hb hab
  have h := conformal_radial_increment ha.1 hab.le hb.2
  have hpos : 0 < (4/Real.pi^2)*(b-a) := by positivity
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_VerticalSpeed
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology

/-- The Cauchy--Riemann algebra on a real-level curve. -/
theorem vertical_speed_algebra {z : ℂ} {t : ℝ}
    (hreal : (z*(1+Complex.I*(t : ℂ))).re = 0) (him : 0 < z.im) :
    (z*(1+Complex.I*(t : ℂ))).im = Complex.normSq z/z.im := by
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.I_re,
    Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.one_im] at hreal ⊢
  have hmul := congrArg (fun x : ℝ => z.re*x) hreal
  rw [Complex.normSq_apply]
  field_simp
  nlinarith

/-- The derivative of a polar curve with differentiable angle. -/
theorem hasDerivAt_polarCurve {θ : ℝ → ℝ} {r t : ℝ} (hθ : HasDerivAt θ t r) :
    HasDerivAt (polarCurve θ)
      (Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have hc := (Complex.hasDerivAt_exp ((θ r : ℂ)*Complex.I)).comp r
    (hθ.ofReal_comp.mul_const Complex.I)
  have h := (Complex.ofRealCLM.hasDerivAt (x := r)).mul hc
  have heq : Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ)) =
      Complex.ofRealCLM 1 * (Complex.exp ∘ fun y => (θ y : ℂ)*Complex.I) r +
      Complex.ofRealCLM r * (Complex.exp ((θ r : ℂ)*Complex.I)*((t : ℂ)*Complex.I)) := by
    dsimp only [Complex.ofRealCLM_apply, Function.comp_def]
    push_cast
    ring
  rw [← heq] at h
  exact h

/-- The image curve's derivative is obtained by the actual complex chain rule. -/
theorem hasDerivAt_image_polarCurve {F : ℂ → ℂ} {θ : ℝ → ℝ} {r t : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r) :
    HasDerivAt (fun s => F (polarCurve θ s))
      ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have h := hF.comp r (hasDerivAt_polarCurve hθ)
  rw [mul_assoc]
  exact h

/-- Constancy of the real part forces the image curve to move upward
under the angular derivative sign condition. -/
theorem image_polarCurve_vertical_derivative {F : ℂ → ℂ} {θ : ℝ → ℝ}
    {r t q : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r)
    (hlevel : ∀ᶠ s in 𝓝 r, (F (polarCurve θ s)).re = q)
    (him : 0 < (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) :
    HasDerivAt (fun s => (F (polarCurve θ s)).im)
      (Complex.normSq (g*Complex.exp ((θ r : ℂ)*Complex.I)) /
        (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) r := by
  have h := hasDerivAt_image_polarCurve hF hθ
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have hconst : HasDerivAt (fun s => (F (polarCurve θ s)).re) 0 r :=
    (hasDerivAt_const r q).congr_of_eventuallyEq hlevel
  have hzero := hre.unique hconst
  have hreal : ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))).re = 0 := hzero
  have himder := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  simpa only [Complex.imCLM_apply, Function.comp_def, vertical_speed_algebra hreal him] using! himder

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ImplicitAngle
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The scalar implicit function theorem with the angular nonzero derivative
as its explicit hypothesis. -/
theorem exists_local_real_level {f : ℝ × ℝ → ℝ} {a b c : ℝ}
    (hC : ContDiffAt ℝ ∞ f (a,b))
    (hD : HasDerivAt (fun y => f (a,y)) c b) (hc : c ≠ 0) :
    ∃ θ : ℝ → ℝ, θ a = b ∧ ContDiffAt ℝ ∞ θ a ∧
      ∀ᶠ r in 𝓝 a, f (r,θ r) = f (a,b) := by
  let D := fderiv ℝ f (a,b) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hfd : HasFDerivAt (fun y => f (a,y)) D b :=
    (hC.differentiableAt (by norm_num)).hasFDerivAt.comp b (hasFDerivAt_prodMk_right a b)
  have heq := hfd.unique hD.hasFDerivAt
  have hval (x : ℝ) : D x = x*c := by
    rw [heq]
    simp
  have hinj : Function.Injective D := by
    intro x y h
    rw [hval, hval] at h
    exact mul_right_cancel₀ hc h
  have hsurj : Function.Surjective D := by
    intro x
    refine ⟨x/c, ?_⟩
    rw [hval]
    field_simp
  have hInv : D.IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
      (LinearMap.range_eq_top.mpr hsurj), ?_⟩
    rfl
  refine ⟨hC.implicitFunction (by norm_num) hInv, ?_, ?_, ?_⟩
  · exact hC.implicitFunction_apply_self (by norm_num) hInv
  · exact hC.contDiffAt_implicitFunction (by norm_num) hInv
  · exact hC.eventually_apply_implicitFunction (by norm_num) hInv

lemma contDiffAt_Q_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.Q p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.reCLM.contDiff.contDiffAt.comp (r,θ) hcomp

lemma contDiffAt_S_uncurry {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.S p.1 p.2) (r,θ) := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by
    rwa [MahlerConformal.norm_polar hr.le]
  have hF : ContDiffAt ℂ ∞ MahlerConformal.F (MahlerConformal.polar r θ) :=
    (MahlerConformal.differentiableOn_F.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))).contDiffAt
  have hFR := hF.restrict_scalars ℝ
  have hp : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => MahlerConformal.polar p.1 p.2) (r,θ) := by
    have hfst : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_fst
    have hsnd : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (p.2 : ℂ)) (r,θ) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp (r,θ) contDiffAt_snd
    exact hfst.mul ((hsnd.mul contDiffAt_const).cexp)
  have hcomp := hFR.comp (r,θ) hp
  exact Complex.imCLM.contDiff.contDiffAt.comp (r,θ) hcomp

/-- A smooth local angular fiber exists at every point of the upper half-disk.
This instantiates the implicit theorem with the actual power-series real part. -/
theorem exists_local_angle {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ∃ ψ : ℝ → ℝ, ψ r = θ ∧ ContDiffAt ℝ ∞ ψ r ∧
      ∀ᶠ s in 𝓝 r, MahlerConformal.Q s (ψ s) = MahlerConformal.Q r θ := by
  apply exists_local_real_level (contDiffAt_Q_uncurry hr hr1)
    (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  exact neg_ne_zero.mpr (MahlerConformal.B_pos hr hr1 hθ hθπ).ne'

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularFibers
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

lemma fiberDomain_isOpen (q : ℝ) : IsOpen (fiberDomain q) := by
  apply isOpen_iff_mem_nhds.mpr
  intro r hr
  have hc := (hasDerivAt_radialMap hr.1 hr.2.1).continuousAt
  have hm := hc (Ioi_mem_nhds hr.2.2)
  filter_upwards [Ioo_mem_nhds hr.1 hr.2.1, hm] with s hs hms
  exact ⟨hs.1,hs.2,hms⟩

lemma fiberAngle_spec {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle q r ∈ Ioo 0 Real.pi ∧ MahlerConformal.Q r (fiberAngle q r) = q := by
  unfold fiberAngle
  rw [dite_eq_left hr]
  exact Classical.choose_spec (exists_fiberAngle hr)

/-- Local implicit angles agree with the globally chosen fiber by uniqueness.
Thus the global choice is smooth at every point of its open domain. -/
theorem contDiffAt_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ContDiffAt ℝ ∞ (fiberAngle q) r := by
  have hs := fiberAngle_spec hr
  obtain ⟨ψ,hψr,hψC,hψQ⟩ := exists_local_angle hr.1 hr.2.1 hs.1.1 hs.1.2
  have hψcont := hψC.continuousAt
  have hψrange : ∀ᶠ s in 𝓝 r, ψ s ∈ Ioo (0 : ℝ) Real.pi := by
    apply hψcont
    rw [hψr]
    exact Ioo_mem_nhds hs.1.1 hs.1.2
  apply hψC.congr_of_eventuallyEq
  filter_upwards [(fiberDomain_isOpen q).mem_nhds hr, hψrange, hψQ] with s hsd hsp hsQ
  have hg := fiberAngle_spec hsd
  have heq : MahlerConformal.Q s (fiberAngle q s) = MahlerConformal.Q s (ψ s) := by
    rw [hg.2, hsQ, hs.2]
  exact (MahlerConformal.Q_strictAntiOn hsd.1 hsd.2.1).injOn
    ⟨hg.1.1.le,hg.1.2.le⟩ ⟨hsp.1.le,hsp.2.le⟩ heq

/-- Every radius after r0 has a unique fiber angle when M(r0)=|q|. -/
theorem mem_fiberDomain_of_basepoint {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) : r ∈ fiberDomain q := by
  have hrpos : 0 < r := hr₀.trans_lt hr.1
  refine ⟨hrpos,hr.2,?_⟩
  rw [← hq]
  exact strictMonoOn_radialMap ⟨hr₀,hr.1.trans hr.2⟩ ⟨hrpos.le,hr.2⟩ hr.1

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiberHeight
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The angular function B gives the imaginary part of the rotated complex derivative. -/
theorem rotated_derivative_im {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
      Complex.exp ((θ : ℂ)*Complex.I)).im = MahlerConformal.B r θ := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by rwa [MahlerConformal.norm_polar hr.le]
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hQ := (hF.comp (θ : ℂ) (MahlerConformal.hasDerivAt_polar_complex r θ)).real_of_complex
  have hq : HasDerivAt (MahlerConformal.Q r)
      ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re θ := hQ
  have heq := hq.unique (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  have halg : ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re =
      -r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        Complex.exp ((θ : ℂ)*Complex.I)).im := by
    simp only [MahlerConformal.polar, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [halg] at heq
  linarith

/-- The actual chosen fiber has positive vertical derivative on its open domain. -/
theorem hasDerivAt_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    HasDerivAt (fiberHeight q)
      (r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r)) r := by
  have hs := fiberAngle_spec hr
  have hθ := (contDiffAt_fiberAngle hr).differentiableAt (by norm_num) |>.hasDerivAt
  have hw : ‖MahlerConformal.polar r (fiberAngle q r)‖ < 1 := by
    simpa only [MahlerConformal.norm_polar hr.1.le] using hr.2.1
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hlevel : ∀ᶠ s in 𝓝 r,
      (MahlerConformal.F (polarCurve (fiberAngle q) s)).re = q := by
    filter_upwards [(fiberDomain_isOpen q).mem_nhds hr] with s hs
    exact (fiberAngle_spec hs).2
  have hB := MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2
  have hrot := rotated_derivative_im hr.1 hr.2.1 (θ := fiberAngle q r)
  have him : 0 < ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im := by nlinarith [hr.1]
  have hv := image_polarCurve_vertical_derivative hF hθ hlevel him
  have hn : Complex.normSq ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)) =
      ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
    rw [Complex.normSq_eq_norm_sq, norm_mul]
    simp [Complex.norm_exp]
  rw [hn] at hv
  have hquot : ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
      ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
        Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im =
      r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r) := by
    rw [← hrot]
    field_simp [hr.1.ne']
  rw [hquot] at hv
  exact hv

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularIntegrals
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular integral and sine estimate. -/

noncomputable section
open Complex Set MeasureTheory
open scoped Topology
namespace MahlerConformal

lemma continuous_B (r : ℝ) : Continuous (B r) := by
  unfold B
  fun_prop

/-- Fundamental theorem of calculus for the actual angular derivative. -/
theorem integral_B {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (a b : ℝ) :
    (∫ θ in a..b, B r θ) = Q r a - Q r b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => -Q r θ) (f' := B r)
    (fun θ (_ : θ ∈ uIcc a b) => by
      convert (hasDerivAt_Q hr hr1 θ).neg using 1
      all_goals first | rfl | simp only [neg_neg])
    (show IntervalIntegrable (B r) volume a b from (continuous_B r).intervalIntegrable a b)
  simpa only [neg_neg, neg_sub_neg] using h

/-- The normalization identity for the angular integral. -/
theorem integral_B_semicircle {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, B r θ) = 2*(F (r : ℂ)).re := by
  rw [integral_B hr hr1, Q_zero, Q_pi]
  ring

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularEndpoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded-convergence normalization M(r) → 1. -/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
namespace MahlerConformal

lemma eventually_radius : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one

lemma B_nonneg {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) : 0 ≤ B r θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hd : 0 < 1-r^2 := by nlinarith
  unfold B
  apply mul_nonneg (by positivity)
  apply Real.arctan_nonneg.mpr
  positivity

/-- Pointwise interior-angle limit; the endpoint angles are intentionally excluded. -/
theorem B_tendsto_one {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun r => B r θ) (𝓝[<] 1) (𝓝 (2/Real.pi)) := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hd0 : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hid.pow 2)
  have hd : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd0, ?_⟩
    filter_upwards [eventually_radius] with r hr
    change 0 < 1-r^2
    nlinarith [hr.1, hr.2]
  have hn : Tendsto (fun r : ℝ => 2*r*Real.sin θ) (𝓝[<] 1) (𝓝 (2*Real.sin θ)) := by
    simpa using (tendsto_const_nhds.mul hid).mul_const (Real.sin θ)
  have hv : Tendsto (fun r : ℝ => 2*r*Real.sin θ/(1-r^2)) (𝓝[<] 1) atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hn.pos_mul_atTop
      (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
      hd.inv_tendsto_nhdsGT_zero
  have ha := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hv).const_mul
    (4/Real.pi^2)
  have he : 4/Real.pi^2*(Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he, Function.comp_apply] using ha

/-- Bounded convergence applied to the actual angular speed of F. -/
theorem integral_B_tendsto_one :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..Real.pi, B r θ) (𝓝[<] 1) (𝓝 2) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := Real.pi) (F := B) (f := fun _ => 2/Real.pi)
    (fun _ => 2/Real.pi)
    (Filter.Eventually.of_forall fun r => (continuous_B r).aestronglyMeasurable)
    (by
      filter_upwards [eventually_radius] with r hr
      exact Filter.Eventually.of_forall fun θ hθ => by
        rw [uIoc_of_le Real.pi_pos.le] at hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (B_nonneg hr.1 hr.2 ⟨hθ.1.le, hθ.2⟩)]
        exact (B_lt_two_div_pi r θ).le)
    (intervalIntegrable_const)
    (by
      filter_upwards [(Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := Real.pi))] with θ heq
      intro hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hi : θ ∈ Ioo (0 : ℝ) Real.pi := heq.mpr hθ
      exact B_tendsto_one hi.1 hi.2)
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rwa [he] at ht

/-- The real part of M(r)=F(r) tends to 1.
No radial derivative or assumed endpoint normalization is used. -/
theorem F_real_tendsto_one :
    Tendsto (fun r : ℝ => (F (r : ℂ)).re) (𝓝[<] 1) (𝓝 1) := by
  have ht := integral_B_tendsto_one.div_const 2
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (∫ θ in (0 : ℝ)..Real.pi, B r θ)/2 = (F (r : ℂ)).re := by
    filter_upwards [eventually_radius] with r hr
    rw [integral_B_semicircle hr.1 hr.2]
    ring
  simpa using ht.congr' he

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_AngularStrip
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-part image and real preimages of the conformal map. -/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
namespace MahlerConformal

lemma F_real_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : (F (r : ℂ)).re < 1 := by
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := B r) (g := fun _ => 2/Real.pi) Real.pi_pos (continuous_B r).continuousOn
    continuous_const.continuousOn (fun θ _ => (B_lt_two_div_pi r θ).le)
    ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, B_lt_two_div_pi r 0⟩
  rw [integral_B_semicircle hr hr1] at hi
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rw [he] at hi
  linarith

lemma polar_neg_angle (r θ : ℝ) : polar r (-θ) = starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_neg, Real.sin_neg]

lemma Q_neg_angle (r θ : ℝ) : Q r (-θ) = Q r θ := by
  simp only [Q, polar_neg_angle, F_conj, Complex.conj_re]

lemma Q_mem_Icc {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Q r θ ∈ Icc (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := (Q_strictAntiOn hr hr1).antitoneOn
  exact ⟨by simpa only [Q_pi] using ha hθ ⟨Real.pi_pos.le, le_rfl⟩ hθ.2,
    by simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ hθ hθ.1⟩

/-- Every image point has real part in the strip. -/
theorem F_re_mem_strip {w : ℂ} (hw : ‖w‖ < 1) : (F w).re ∈ Ioo (-1 : ℝ) 1 := by
  by_cases hw0 : w = 0
  · simp [hw0, F_zero]
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hp : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
  have hθ : |w.arg| ∈ Icc (0 : ℝ) Real.pi := by
    refine ⟨abs_nonneg _, abs_le.mpr ⟨?_, Complex.arg_le_pi w⟩⟩
    exact (Complex.neg_pi_lt_arg w).le
  have he : Q ‖w‖ |w.arg| = (F w).re := by
    rcases le_total 0 w.arg with h | h
    · rw [abs_of_nonneg h, Q, hp]
    · rw [abs_of_nonpos h, Q_neg_angle, Q, hp]
  have hb := Q_mem_Icc hr hw hθ
  rw [he] at hb
  have hm := F_real_lt_one hr hw
  constructor <;> linarith [hb.1, hb.2]

lemma continuousOn_F_real {r : ℝ} (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn (fun t : ℝ => (F (t : ℂ)).re) (Icc 0 r) := by
  intro t ht
  have hw : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  exact (hasDerivAt_F_series hw).real_of_complex.continuousAt.continuousWithinAt

/-- Every point on the real interval (-1,1) is the actual value F(t) at a real
point t in the disk. This is existence only; it does not assert univalence. -/
theorem exists_real_preimage {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ t : ℝ, t ∈ Ioo (-1 : ℝ) 1 ∧ F (t : ℂ) = (q : ℂ) := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1], hq.2⟩
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 ∧ |q| < (F (r : ℂ)).re :=
    eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r, hr, hqr⟩ := he.exists
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  have hF : F (t : ℂ) = ((|q| : ℝ) : ℂ) := by
    apply Complex.ext
    · exact hte
    · simpa using F_real_im t
  by_cases hq0 : 0 ≤ q
  · refine ⟨t, ⟨by linarith [ht.1], ht.2.trans_lt hr.2⟩, ?_⟩
    simpa only [abs_of_nonneg hq0] using hF
  · refine ⟨-t, ⟨by linarith [ht.2, hr.2], by linarith [ht.1]⟩, ?_⟩
    rw [Complex.ofReal_neg, F_odd, hF, abs_of_neg (lt_of_not_ge hq0)]
    simp

/-- The set of real parts of the image is exactly (-1,1).
This does not assert that each vertical fiber is an interval. -/
theorem image_re_F_disk : Complex.re '' (F '' ball (0 : ℂ) 1) = Ioo (-1 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact F_re_mem_strip (by simpa using hw)
  · intro hq
    obtain ⟨t, ht, hF⟩ := exists_real_preimage hq
    refine ⟨(q : ℂ), ⟨(t : ℂ), ?_, hF⟩, by simp⟩
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInjectivity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

lemma norm_add_sub_sq (w : ℂ) : ‖1+w‖^2 - ‖1-w‖^2 = 4*w.re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

lemma re_mul_log_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hx : w.re ≠ 0) :
    0 < w.re * (Complex.log (cayley w)).re := by
  have hnum : 0 < ‖1+w‖ := norm_pos_iff.mpr (one_add_ne hw)
  have hden : 0 < ‖1-w‖ := norm_pos_iff.mpr (one_sub_ne hw)
  have hn := norm_add_sub_sq w
  rw [Complex.log_re, cayley, norm_div]
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hc : ‖1+w‖/‖1-w‖ < 1 := (div_lt_one hden).mpr (by nlinarith)
    exact mul_pos_of_neg_of_neg hx (Real.log_neg (div_pos hnum hden) hc)
  · have hc : 1 < ‖1+w‖/‖1-w‖ := (one_lt_div hden).mpr (by nlinarith)
    exact mul_pos hx (Real.log_pos hc)

lemma re_mul_log_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.re * (Complex.log (cayley w)).re := by
  by_cases hx : w.re = 0
  · simp [hx]
  · exact (re_mul_log_cayley_pos hw hx).le

lemma im_mul_arg_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) (hy : w.im ≠ 0) :
    0 < w.im * (cayley w).arg := by
  have hd : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rw [arg_eq_arctan_of_re_pos (cayley_re_pos hw), cayley_im_div_re hw]
  rcases lt_or_gt_of_ne hy with hy | hy
  · exact mul_pos_of_neg_of_neg hy
      (Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hd))
  · exact mul_pos hy (Real.arctan_pos.mpr (div_pos (by linarith) hd))

lemma im_mul_arg_cayley_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ w.im * (cayley w).arg := by
  by_cases hy : w.im = 0
  · simp [hy]
  · exact (im_mul_arg_cayley_pos hw hy).le

/-- A consequence of the derivative formula on the full disk, used for injectivity.
This is not a formula for M'(r), nor does it assume univalence. -/
theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  have hc : (4/(Real.pi : ℂ)^2) = ((4/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
  by_cases hw0 : w = 0
  · subst w
    rw [hasDerivAt_F_zero.deriv]
    have he : (8/(Real.pi : ℂ)^2) = ((8/Real.pi^2 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.ofReal_re]
    positivity
  have he : deriv F w = (4/(Real.pi : ℂ)^2)*(Complex.log (cayley w)/w) := by
    rw [(hasDerivAt_F_log hw hw0).deriv]
    dsimp [cayley]
    field_simp
  rw [he, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_pos (by positivity)
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hx := re_mul_log_cayley_nonneg hw
  have hy := im_mul_arg_cayley_nonneg hw
  rw [Complex.log_im]
  by_cases hx0 : w.re = 0
  · have hy0 : w.im ≠ 0 := by
      intro hy0
      apply hw0
      apply Complex.ext <;> simp [hx0, hy0]
    have hp := im_mul_arg_cayley_pos hw hy0
    nlinarith
  · have hp := re_mul_log_cayley_pos hw hx0
    nlinarith

lemma segment_mem_disk {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ‖a+(t : ℂ)*(b-a)‖ < 1 := by
  have hc := (convex_ball (0 : ℂ) (1 : ℝ)) (by simpa using ha) (by simpa using hb)
    (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
  have he : (1-t) • a + t • b = a+(t : ℂ)*(b-a) := by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he] at hc
  simpa using hc

/-- Injectivity on the exact open unit disk, with no assumed inverse or central
univalence theorem. Positive real derivative makes the segment projection strict. -/
theorem F_injOn_disk : Set.InjOn F (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  by_contra hne
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hb' : ‖b‖ < 1 := by simpa using hb
  have hd : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let g : ℝ → ℝ := fun t => (F (a+(t : ℂ)*(b-a))/(b-a)).re
  have hg : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt g (deriv F (a+(t : ℂ)*(b-a))).re t := by
    intro t ht
    have hw := segment_mem_disk ha' hb' ht
    have hf := (hasDerivAt_F_series hw).differentiableAt.hasDerivAt
    have hline : HasDerivAt (fun z : ℂ => a+z*(b-a)) (b-a) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (b-a)).const_add a
    have hs := ((hf.comp (t : ℂ) hline).div_const (b-a)).real_of_complex
    have he : (deriv F (a+(t : ℂ)*(b-a))*(b-a))/(b-a) =
        deriv F (a+(t : ℂ)*(b-a)) := mul_div_cancel_right₀ _ hd
    change HasDerivAt g _ t at hs
    rwa [he] at hs
  have hm : StrictMonoOn g (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hg t ht').deriv]
    exact deriv_F_re_pos (segment_mem_disk ha' hb' ht')
  have hlt := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_lt_one
  dsimp [g] at hlt
  simp only [zero_mul, add_zero, one_mul, add_sub_cancel] at hlt
  rw [hab] at hlt
  exact lt_irrefl _ hlt

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ConformalInverse
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The biholomorphic map and its inverse.
The vertical interval property and P_m estimates are not asserted here. -/

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace MahlerConformal

lemma inverseF_mem {u : ℂ} (hu : u ∈ Omega) : inverseF u ∈ ball (0 : ℂ) 1 :=
  Function.invFunOn_mem hu

lemma inverseF_right {u : ℂ} (hu : u ∈ Omega) : F (inverseF u) = u :=
  Function.invFunOn_eq hu

lemma inverseF_left {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : inverseF (F w) = w :=
  F_injOn_disk.leftInvOn_invFunOn hw

lemma hasStrictDerivAt_F {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    HasStrictDerivAt F (deriv F w) w :=
  ((differentiableOn_F.analyticAt (isOpen_ball.mem_nhds hw)).contDiffAt (n := 1)).hasStrictDerivAt
    (by norm_num)

theorem isOpen_Omega : IsOpen Omega := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨w, hw, rfl⟩
  rw [← (hasStrictDerivAt_F hw).map_nhds_eq (deriv_F_ne_zero (by simpa using hw))]
  change F ⁻¹' Omega ∈ 𝓝 w
  apply Filter.mem_of_superset (isOpen_ball.mem_nhds hw)
  intro z hz
  exact ⟨z, hz, rfl⟩

/-- The selected inverse is holomorphic on its exact image domain, with the
reciprocal derivative. Its local inverse hypotheses follow from proved injectivity. -/
theorem hasDerivAt_inverseF {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt inverseF (deriv F (inverseF u))⁻¹ u := by
  have hw := inverseF_mem hu
  have hl : ∀ᶠ w in 𝓝 (inverseF u), inverseF (F w) = w := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w hw
    exact inverseF_left hw
  have hd := (hasStrictDerivAt_F hw).to_local_left_inverse
    (deriv_F_ne_zero (by simpa using hw)) hl
  rw [inverseF_right hu] at hd
  exact hd.hasDerivAt

theorem differentiableOn_inverseF : DifferentiableOn ℂ inverseF Omega :=
  fun _ hu => (hasDerivAt_inverseF hu).differentiableAt.differentiableWithinAt

theorem inverseF_deriv_ne_zero {u : ℂ} (hu : u ∈ Omega) : deriv inverseF u ≠ 0 := by
  rw [(hasDerivAt_inverseF hu).deriv]
  exact inv_ne_zero (deriv_F_ne_zero (by simpa using inverseF_mem hu))

theorem Omega_conj {u : ℂ} (hu : u ∈ Omega) : starRingEnd ℂ u ∈ Omega := by
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa using hw

theorem inverseF_zero : inverseF 0 = 0 := by
  simpa only [F_zero] using inverseF_left (w := 0) (by simp)

theorem inverseF_eq_zero_iff {u : ℂ} (hu : u ∈ Omega) : inverseF u = 0 ↔ u = 0 := by
  constructor
  · intro h
    rw [← inverseF_right hu, h, F_zero]
  · intro h
    rw [h, inverseF_zero]

end MahlerConformal

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PlanarDensity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

lemma contDiffAt_normSq_comp {f : ℂ → ℂ} {u : ℂ}
    (hf : ContDiffAt ℝ ∞ f u) : ContDiffAt ℝ ∞ (fun z => Complex.normSq (f z)) u := by
  have hre := Complex.reCLM.contDiff.contDiffAt.comp u hf
  have him := Complex.imCLM.contDiff.contDiffAt.comp u hf
  convert (hre.mul hre).add (him.mul him) using 1 <;> rfl

/-- Smoothness of the actual vertical density, including at the origin. -/
theorem contDiffAt_planarDensity (m : ℕ) {u : ℂ} (hu : u ∈ MahlerConformal.Omega) :
    ContDiffAt ℝ ∞ (planarDensity m) u := by
  have hA := MahlerConformal.differentiableOn_inverseF.analyticAt
    (MahlerConformal.isOpen_Omega.mem_nhds hu)
  have hh : ContDiffAt ℝ ∞ MahlerConformal.inverseF u := hA.contDiffAt.restrict_scalars ℝ
  have hhd : ContDiffAt ℝ ∞ (deriv MahlerConformal.inverseF) u := hA.deriv.contDiffAt.restrict_scalars ℝ
  exact (contDiffAt_const.mul ((contDiffAt_normSq_comp hh).pow (m-1))).mul
    (contDiffAt_normSq_comp hhd)

lemma planarDensity_nonneg (m : ℕ) (u : ℂ) : 0 ≤ planarDensity m u := by
  have hh := Complex.normSq_nonneg (MahlerConformal.inverseF u)
  have hd := Complex.normSq_nonneg (deriv MahlerConformal.inverseF u)
  unfold planarDensity
  positivity

lemma planarDensity_pos {m : ℕ} (hm : 0 < m) {u : ℂ}
    (hu : u ∈ MahlerConformal.Omega) (hu0 : u ≠ 0) : 0 < planarDensity m u := by
  have hh : 0 < Complex.normSq (MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (fun h => hu0 ((MahlerConformal.inverseF_eq_zero_iff hu).mp h))
  have hhd : 0 < Complex.normSq (deriv MahlerConformal.inverseF u) :=
    Complex.normSq_pos.mpr (MahlerConformal.inverseF_deriv_ne_zero hu)
  unfold planarDensity
  positivity

lemma continuousAt_planarDensity_vertical (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    ContinuousAt (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) t := by
  have hl : ContinuousAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) t := by fun_prop
  have hd := (contDiffAt_planarDensity m hu).continuousAt
  have hc := hd.comp (f := fun s : ℝ => (q : ℂ)+(s : ℂ)*Complex.I) hl
  exact hc

/-- The fundamental theorem yields the vertical derivative whenever
the segment from zero lies in Omega.
Segment containment is an explicit geometric premise. -/
theorem hasDerivAt_planarPrimitive (m : ℕ) {q t : ℝ}
    (hseg : ∀ s ∈ uIcc (0 : ℝ) t, (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega) :
    HasDerivAt (planarPrimitive m q) (planarDensity m ((q : ℂ)+(t : ℂ)*Complex.I)) t := by
  have hi : IntervalIntegrable (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    exact (continuousAt_planarDensity_vertical m (hseg s hs)).continuousWithinAt
  have hopen : IsOpen {s : ℝ | (q : ℂ)+(s : ℂ)*Complex.I ∈ MahlerConformal.Omega} :=
    MahlerConformal.isOpen_Omega.preimage
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  have hmeas := ContinuousAt.stronglyMeasurableAtFilter (μ := volume) hopen
    (fun s hs => continuousAt_planarDensity_vertical m hs) t (hseg t (right_mem_uIcc))
  exact intervalIntegral.integral_hasDerivAt_right hi hmeas
    (continuousAt_planarDensity_vertical m (hseg t (right_mem_uIcc)))

/-- The polynomial expression equals the norm-power density. -/
theorem planarDensity_eq (m : ℕ) (hm : 1 ≤ m) (u : ℂ) :
    planarDensity m u = (4*(m : ℝ)/Real.pi)*
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ)*
      ‖deriv MahlerConformal.inverseF u‖^2 := by
  have he : ((2*(m-1) : ℕ) : ℝ) = 2*(m : ℝ)-2 := by
    rw [Nat.cast_mul, Nat.cast_sub hm]
    norm_num
    ; ring
  have hp : ‖MahlerConformal.inverseF u‖^(2*(m-1) : ℕ) =
      ‖MahlerConformal.inverseF u‖^(2*(m : ℝ)-2 : ℝ) := by
    rw [← Real.rpow_natCast, he]
  unfold planarDensity
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← pow_mul, hp]

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FiberEndpoint
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoints of the selected global angular fibers. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma eventually_fiberDomain {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ∀ᶠ r in 𝓝[>] r₀, r ∈ fiberDomain q := by
  filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hr₁).filter_mono nhdsWithin_le_nhds]
    with r hr hr1
  exact mem_fiberDomain_of_basepoint hr₀ hq ⟨hr,hr1⟩

lemma fiberAngle_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle (-q) r = Real.pi - fiberAngle q r := by
  have hn : r ∈ fiberDomain (-q) := by simpa [fiberDomain, abs_neg] using hr
  have hs := fiberAngle_spec hr
  have ht := fiberAngle_spec hn
  apply (Q_strictAntiOn hr.1 hr.2.1).injOn ⟨ht.1.1.le,ht.1.2.le⟩
    ⟨by linarith [hs.1.2],by linarith [hs.1.1]⟩
  rw [ht.2, Q_pi_sub, hs.2]

lemma fiberHeight_neg {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight (-q) r = fiberHeight q r := by
  rw [fiberHeight, fiberAngle_neg hr]
  simp only [S, polar_pi_sub, F_odd, F_conj, Complex.neg_im, Complex.conj_im, neg_neg,
    fiberHeight]

/-- On the actual selected angle, the positive real basepoint has angle limit zero. -/
theorem fiberAngle_tendsto_zero {q r₀ : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hq0 : 0 ≤ q) (hq : radialMap r₀ = |q|) :
    Tendsto (fiberAngle q) (𝓝[>] r₀) (𝓝 0) := by
  have hd := eventually_fiberDomain hr₀.le hr₁ hq
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hd] with r hr
    exact ha.trans (fiberAngle_spec hr).1.1
  · intro b hb
    let t := min (b/2) (Real.pi/2)
    have ht : 0 < t := lt_min (by linarith) Real.pi_div_two_pos
    have htπ : t < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
    have htb : t < b := (min_le_left _ _).trans_lt (by linarith)
    have hQ : Q r₀ t < q := by
      have h := Q_strictAntiOn hr₀ hr₁
        (show 0 ∈ Icc (0 : ℝ) Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ⟨ht.le,htπ.le⟩ ht
      rw [Q_zero] at h
      change Q r₀ t < radialMap r₀ at h
      simpa only [hq, abs_of_nonneg hq0] using h
    have hc : ContinuousAt (fun r : ℝ => Q r t) r₀ := by
      have hp : ContinuousAt (fun r : ℝ => polar r t) r₀ := by
        unfold polar
        fun_prop
      have hf := (hasDerivAt_F_series (w := polar r₀ t)
        (by rwa [norm_polar hr₀.le])).continuousAt
      exact Complex.continuous_re.continuousAt.comp (hf.comp (f := fun r : ℝ => polar r t) hp)
    have he : ∀ᶠ r in 𝓝[>] r₀, Q r t < q := (hc.tendsto.eventually (eventually_lt_nhds hQ)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hd, he] with r hr hQr
    have hs := fiberAngle_spec hr
    have hθ : fiberAngle q r < t := by
      by_contra h
      have hh := (Q_strictAntiOn hr.1 hr.2.1).antitoneOn
        ⟨ht.le,htπ.le⟩ ⟨hs.1.1.le,hs.1.2.le⟩ (le_of_not_gt h)
      rw [hs.2] at hh
      linarith
    exact hθ.trans htb

/-- Zero radius is handled by the norm of the actual polar preimage; no
angle at the origin is imposed. -/
theorem fiberHeight_tendsto_at_zero (q : ℝ) :
    Tendsto (fiberHeight q) (𝓝 0) (𝓝 0) := by
  have hn : Tendsto (fun r : ℝ => ‖polar r (fiberAngle q r)‖) (𝓝 0) (𝓝 0) := by
    simpa [polar, Complex.norm_exp] using (continuous_abs.tendsto (0 : ℝ))
  have hp : Tendsto (fun r : ℝ => polar r (fiberAngle q r)) (𝓝 0) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hF := (hasDerivAt_F_series (w := 0) (by simp)).continuousAt.tendsto.comp hp
  change Tendsto (fun r => (F (polar r (fiberAngle q r))).im) (𝓝 0) (𝓝 0)
  simpa only [F_zero, Complex.zero_im, Function.comp_def] using Complex.continuous_im.continuousAt.tendsto.comp hF

/-- The endpoint of the selected fiber, including q=0. -/
theorem fiberHeight_tendsto_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) :
    Tendsto (fiberHeight q) (𝓝[>] r₀) (𝓝 0) := by
  rcases hr₀.eq_or_lt with hzero | hpos
  · subst r₀
    exact (fiberHeight_tendsto_at_zero q).mono_left nhdsWithin_le_nhds
  have hnonneg (p : ℝ) (hp : 0 ≤ p) (he : radialMap r₀ = |p|) :
      Tendsto (fiberHeight p) (𝓝[>] r₀) (𝓝 0) := by
    have ht := fiberAngle_tendsto_zero hpos hr₁ hp he
    have hc := (contDiffAt_S_uncurry (θ := 0) hpos hr₁).continuousAt.tendsto
    have hp : Tendsto (fun r : ℝ => (r, fiberAngle p r)) (𝓝[>] r₀) (𝓝 (r₀,0)) :=
      (show Tendsto (fun r : ℝ => r) (𝓝[>] r₀) (𝓝 r₀) from nhdsWithin_le_nhds).prodMk_nhds ht
    change Tendsto (fun r => S r (fiberAngle p r)) (𝓝[>] r₀) (𝓝 0)
    simpa only [Function.comp_def, S_zero] using hc.comp hp
  by_cases hp : 0 ≤ q
  · exact hnonneg q hp hq
  · have hn := hnonneg (-q) (by linarith) (by simpa using hq)
    apply hn.congr'
    filter_upwards [eventually_fiberDomain hr₀ hr₁ hq] with r hr
    exact fiberHeight_neg hr

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_GlobalVerticalGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global vertical intervals of the conformal image. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

lemma exists_radial_basepoint {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ r₀ ∈ Ico (0 : ℝ) 1, radialMap r₀ = |q| := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1],hq.2⟩
  have he := eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r,hr,hqr⟩ := he.exists
  obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by
      simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  exact ⟨t,⟨ht.1,ht.2.trans_lt hr.2⟩,hte⟩

lemma fiberHeight_basepoint {q r₀ : ℝ} (hq : radialMap r₀ = |q|) :
    fiberHeight q r₀ = 0 := by
  have hn : r₀ ∉ fiberDomain q := by simp [fiberDomain, hq]
  simp [fiberHeight, fiberAngle, hn, S_zero]

lemma continuousOn_fiberHeight_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ContinuousOn (fiberHeight q) (Ico r₀ 1) := by
  intro r hr
  rcases hr.1.eq_or_lt with he | hlt
  · subst r
    have hc : ContinuousWithinAt (fiberHeight q) (Ioi r₀) r₀ := by
      rw [ContinuousWithinAt, fiberHeight_basepoint hq]
      exact fiberHeight_tendsto_basepoint hr₀ hr₁ hq
    exact (continuousWithinAt_Ioi_iff_Ici.mp hc).mono (fun _ h => h.1)
  · exact (hasDerivAt_fiberHeight (mem_fiberDomain_of_basepoint hr₀ hq ⟨hlt,hr.2⟩)).continuousAt.continuousWithinAt

lemma zero_mem_verticalFiber {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : 0 ∈ verticalFiber q := by
  obtain ⟨t,ht,hF⟩ := exists_real_preimage hq
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [Complex.norm_real, abs_lt] using ht
  simpa [verticalFiber] using (show (q : ℂ) ∈ Omega from ⟨t,hw,hF⟩)

lemma fiberHeight_mem_verticalFiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight q r ∈ verticalFiber q := by
  refine ⟨polar r (fiberAngle q r), ?_, ?_⟩
  · simpa [norm_polar hr.1.le] using hr.2.1
  · apply Complex.ext
    · simpa [Q] using (fiberAngle_spec hr).2
    · simp [fiberHeight, S]

lemma verticalFiber_neg {q y : ℝ} (hy : y ∈ verticalFiber q) : -y ∈ verticalFiber q := by
  have h := Omega_conj hy
  simpa [verticalFiber, map_add, map_mul] using h

lemma angular_height_mem_image {q r₀ r θ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) (hQ : Q r θ = q) :
    S r θ ∈ fiberHeight q '' Ico r₀ 1 := by
  by_cases hz : θ = 0
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hz,S_zero,fiberHeight_basepoint hq]⟩
  by_cases hp : θ = Real.pi
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hp,S_pi,fiberHeight_basepoint hq]⟩
  have hi : θ ∈ Ioo 0 Real.pi := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hz),lt_of_le_of_ne hθ.2 hp⟩
  have hm := Q_mem_Ioo hr hr1 hi.1 hi.2
  rw [hQ] at hm
  have habs : |q| < radialMap r := abs_lt.mpr hm
  have hrr : r₀ < r := by
    by_contra h
    have hb := strictMonoOn_radialMap.monotoneOn ⟨hr.le,hr1⟩ ⟨hr₀,hr₁⟩ (le_of_not_gt h)
    rw [hq] at hb
    linarith
  have hd : r ∈ fiberDomain q := ⟨hr,hr1,habs⟩
  have hs := fiberAngle_spec hd
  have he := (Q_strictAntiOn hr hr1).injOn ⟨hs.1.1.le,hs.1.2.le⟩ hθ (hs.2.trans hQ.symm)
  exact ⟨r,⟨hrr.le,hr1⟩,by simp only [fiberHeight,he]⟩

/-- Every image height belongs to the global increasing upper fiber or its reflection. -/
theorem verticalFiber_eq_images {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    verticalFiber q = fiberHeight q '' Ico r₀ 1 ∪
      (fun r => -fiberHeight q r) '' Ico r₀ 1 := by
  ext y
  constructor
  · rintro ⟨w,hw,hF⟩
    have hn : ‖w‖ < 1 := by simpa using hw
    have hQw : (F w).re = q := by rw [hF]; simp
    have hSw : (F w).im = y := by rw [hF]; simp
    by_cases hw0 : w = 0
    · have hy : y = 0 := by simpa [hw0,F_zero] using hSw.symm
      exact Or.inl ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hy,fiberHeight_basepoint hq]⟩
    have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have he : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    by_cases ha : 0 ≤ w.arg
    · have h := angular_height_mem_image hr₀ hr₁ hq hr hn ⟨ha,Complex.arg_le_pi w⟩
        (show Q ‖w‖ w.arg = q by simpa [Q,he] using hQw)
      exact Or.inl (by simpa [S,he,hSw] using h)
    · have har : -w.arg ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith,by linarith [Complex.neg_pi_lt_arg w]⟩
      have hep : polar ‖w‖ (-w.arg) = starRingEnd ℂ w := by rw [polar_neg_angle,he]
      have h := angular_height_mem_image hr₀ hr₁ hq hr hn har
        (show Q ‖w‖ (-w.arg) = q by simpa [Q,hep,F_conj] using hQw)
      obtain ⟨r,hrt,heq⟩ := h
      refine Or.inr ⟨r,hrt,?_⟩
      simpa [S,hep,F_conj,hSw] using congrArg Neg.neg heq
  · intro hy
    have hmem {r : ℝ} (hr : r ∈ Ico r₀ 1) : fiberHeight q r ∈ verticalFiber q := by
      rcases hr.1.eq_or_lt with he | ht
      · subst r; rw [fiberHeight_basepoint hq]; exact zero_mem_verticalFiber hqstrip
      · exact fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq ⟨ht,hr.2⟩)
    rcases hy with ⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩
    · exact hmem hr
    · exact verticalFiber_neg (hmem hr)

/-- The actual global vertical section is an open interval containing zero. -/
theorem verticalFiber_interval {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    IsOpen (verticalFiber q) ∧ OrdConnected (verticalFiber q) ∧ 0 ∈ verticalFiber q := by
  obtain ⟨r₀,hr₀,hbase⟩ := exists_radial_basepoint hq
  have hc := continuousOn_fiberHeight_basepoint hr₀.1 hr₀.2 hbase
  have hp := isPreconnected_Ico.image (fiberHeight q) hc
  have hn := isPreconnected_Ico.image (fun r => -fiberHeight q r) hc.neg
  have hz : (0 : ℝ) ∈ fiberHeight q '' Ico r₀ 1 ∩ (fun r => -fiberHeight q r) '' Ico r₀ 1 :=
    ⟨⟨r₀,⟨le_rfl,hr₀.2⟩,fiberHeight_basepoint hbase⟩,
     ⟨r₀,⟨le_rfl,hr₀.2⟩,by dsimp only; rw [fiberHeight_basepoint hbase,neg_zero]⟩⟩
  refine ⟨isOpen_Omega.preimage (by fun_prop),?_,zero_mem_verticalFiber hq⟩
  rw [verticalFiber_eq_images hq hr₀.1 hr₀.2 hbase]
  exact (IsPreconnected.union' ⟨0,hz⟩ hp hn).ordConnected

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_GlobalFiberParametrization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

/-- The whole integration segment for the vertical primitive belongs to Omega. -/
theorem vertical_segment_mem_Omega {u : ℂ} (hu : u ∈ Omega) {t : ℝ}
    (ht : t ∈ uIcc 0 u.im) : (u.re : ℂ) + (t : ℂ)*I ∈ Omega := by
  have hq : u.re ∈ Ioo (-1 : ℝ) 1 := by
    rw [← image_re_F_disk]
    exact ⟨u,hu,rfl⟩
  have hv := verticalFiber_interval hq
  have hy : u.im ∈ verticalFiber u.re := by
    simpa only [verticalFiber, mem_ofPred_eq, Complex.re_add_im] using hu
  exact hv.2.1.uIcc_subset hv.2.2 hy ht

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_GlobalPlanarBound
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology
open MahlerConformal

/-- The FTC applies at every point of Omega, including the real axis. -/
theorem hasDerivAt_planarPrimitive_global (m : ℕ) {q t : ℝ}
    (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    HasDerivAt (planarPrimitive m q) (planarDensity m ((q : ℂ)+(t : ℂ)*I)) t := by
  apply hasDerivAt_planarPrimitive
  intro s hs
  simpa using vertical_segment_mem_Omega hu (t := s) (by simpa using hs)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_GlobalPlanarMonotonicity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology

/-- The original primitive is strictly increasing on every entire actual
vertical section, including across its possible zero derivative at the origin. -/
theorem strictMonoOn_planarPrimitive_global {m : ℕ} (hm : 0 < m) {q : ℝ}
    (hq : q ∈ Ioo (-1 : ℝ) 1) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  have hv := verticalFiber_interval hq
  have hcont : ∀ a b : ℝ, a ∈ verticalFiber q → b ∈ verticalFiber q →
      ContinuousOn (fun s : ℝ => planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) (uIcc a b) := by
    intro a b ha hb s hs
    have hmem : s ∈ verticalFiber q := hv.2.1.uIcc_subset ha hb hs
    exact (continuousAt_planarDensity_vertical m hmem).continuousWithinAt
  intro a ha b hb hab
  have h0 : (0 : ℝ) ∈ verticalFiber q := hv.2.2
  have hia := (hcont 0 a h0 ha).intervalIntegrable (μ := volume)
  have hiab := (hcont a b ha hb).intervalIntegrable (μ := volume)
  have heq := intervalIntegral.integral_add_adjacent_intervals hia hiab
  have hpos : 0 < ∫ s in a..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I) := by
    apply intervalIntegral.integral_pos hab
    · simpa only [uIcc_of_le hab.le] using hcont a b ha hb
    · intro s _
      exact planarDensity_nonneg m _
    · by_cases ha0 : a = 0
      · refine ⟨b,⟨hab.le,le_rfl⟩,planarDensity_pos hm hb ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        linarith
      · refine ⟨a,⟨le_rfl,hab.le⟩,planarDensity_pos hm ha ?_⟩
        intro hz
        have him := congrArg Complex.im hz
        simp at him
        exact ha0 him
  change (∫ s in (0 : ℝ)..a, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)) <
    ∫ s in (0 : ℝ)..b, planarDensity m ((q : ℂ)+(s : ℂ)*Complex.I)
  linarith

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ActualFiniteStrips
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open MahlerConformal
variable {I J : Type*} [Fintype I] [fintypeJ : Fintype J]

lemma verticalFiber_realPart {q t : ℝ} (ht : t ∈ verticalFiber q) : q ∈ Ioo (-1 : ℝ) 1 := by
  have hu : (q : ℂ)+(t : ℂ)*Complex.I ∈ Omega := ht
  have h := F_re_mem_strip (w := inverseF ((q : ℂ)+(t : ℂ)*Complex.I))
    (by simpa using inverseF_mem hu)
  rw [inverseF_right hu] at h
  simpa using h

lemma strictMonoOn_planarPrimitive_any {m : ℕ} (hm : 0 < m) (q : ℝ) :
    StrictMonoOn (planarPrimitive m q) (verticalFiber q) := by
  intro a ha b hb hab
  exact strictMonoOn_planarPrimitive_global hm (verticalFiber_realPart ha) ha hb hab

/-- The finite-strip map is injective on its entire complex strip domain. -/
theorem stripMap_injOn (A : J → I → ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 0 < m) : InjOn (stripMap A m) (stripDomain A) := by
  exact full_map_injOn A hA (fun x j => verticalFiber (measurement A x j))
    (fun x j => planarPrimitive m (measurement A x j))
    (fun x j => strictMonoOn_planarPrimitive_any hm _)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_CompactIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace CompactIntegral

lemma isOpen_tube {U : Set (ℂ × ℝ)} (hU : IsOpen U) : IsOpen (tube U) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨V,W,hV,hW,hzV,hKW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact {z}) isCompact_Icc hU (by
      rintro ⟨x,t⟩ ⟨hx,ht⟩
      rcases mem_singleton_iff.mp hx with rfl
      exact hz t ht)
  apply Filter.mem_of_superset (hV.mem_nhds (hzV (mem_singleton z)))
  intro x hx t ht
  exact hVW ⟨hx,hKW ht⟩

variable {E : Type*} [NormedAddCommGroup E] [normedSpaceRealE : NormedSpace ℝ E]

omit normedSpaceRealE in
lemma local_bound [NormedSpace ℝ E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContinuousOn F U) {z : ℂ} (hz : z ∈ tube U) :
    ∃ V ∈ 𝓝 z, V ⊆ tube U ∧ ∃ C : ℝ, ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, ‖F (x,t)‖ ≤ C := by
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp ((isOpen_tube hU).mem_nhds hz)
  have hsub : closedBall z (r/2) ×ˢ Icc (0 : ℝ) 1 ⊆ U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    exact hrV (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt (by linarith))) t ht
  obtain ⟨C,hC⟩ := ((isCompact_closedBall z (r/2)).prod isCompact_Icc).bddAbove_image
    ((hF.mono hsub).norm)
  refine ⟨ball z (r/2),ball_mem_nhds z (by linarith),?_,C,?_⟩
  · intro x hx
    exact hrV (mem_ball.mpr ((mem_ball.mp hx).trans (by linarith)))
  · intro x hx t ht
    exact hC (mem_image_of_mem _ ⟨mem_closedBall.mpr (mem_ball.mp hx).le,ht⟩)

omit normedSpaceRealE in
lemma integrable_slice [NormedSpace ℝ E] {U : Set (ℂ × ℝ)} {F : ℂ × ℝ → E}
    (hF : ContinuousOn F U) {x : ℂ} (hx : x ∈ tube U) :
    IntegrableOn (fun t => F (x,t)) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.integrableOn_Icc
  exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => hx t ht)

lemma continuousOn_integral {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContinuousOn F U) :
    ContinuousOn (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  intro x hx
  obtain ⟨V,hV,hVU,C,hC⟩ := local_bound hU hF hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [hV] with y hy
    exact (integrable_slice hF (hVU hy)).aestronglyMeasurable
  · filter_upwards [hV] with y hy
    exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC y hy t ht)
  · exact integrableOn_const (isCompact_Icc.measure_ne_top)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hF.continuousAt (hU.mem_nhds (hx t ht))).comp
      (f := fun y : ℂ => (y,t)) (continuousAt_id.prodMk continuousAt_const)

variable [completeSpaceE : CompleteSpace E]

omit completeSpaceE in
lemma hasFDerivAt_integral [CompleteSpace E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} {G : ℂ × ℝ → ℂ →L[ℝ] E}
    (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (hd : ∀ p ∈ U, HasFDerivAt (fun x => F (x,p.2)) (G p) p.1)
    {x : ℂ} (hx : x ∈ tube U) :
    HasFDerivAt (fun y => ∫ t in Icc (0 : ℝ) 1, F (y,t))
      (∫ t in Icc (0 : ℝ) 1, G (x,t)) x := by
  obtain ⟨V,hV,hVU,C,hC⟩ := local_bound hU hG hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := V)
    (bound := fun _ => C) hV
  · filter_upwards [hV] with y hy
    exact (integrable_slice hF (hVU hy)).aestronglyMeasurable
  · exact integrable_slice hF hx
  · exact (integrable_slice hG hx).aestronglyMeasurable
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht y hy => hC y hy t ht)
  · exact integrableOn_const (isCompact_Icc.measure_ne_top)
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht y hy => hd (y,t) (hVU hy t ht))

/-- Integration over a fixed compact interval preserves every finite smoothness order.
The domain consists of the parameters whose whole compact fiber is in U. -/
theorem contDiffOn_integral_nat (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContDiffOn ℝ n F U) :
    ContDiffOn ℝ n (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  induction n generalizing E with
  | zero => exact contDiffOn_zero.mpr (continuousOn_integral hU hF.continuousOn)
  | succ n ih =>
    let G : ℂ × ℝ → ℂ →L[ℝ] E := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ ℂ ℝ)
    have hG : ContDiffOn ℝ n G U :=
      (hF.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const
    have hd : ∀ p ∈ U, HasFDerivAt (fun x => F (x,p.2)) (G p) p.1 := by
      intro p hp
      have hf := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)
      exact hf.hasFDerivAt.comp p.1 ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1))
    have hI := fun x hx => hasFDerivAt_integral hU hF.continuousOn hG.continuousOn hd (x := x) hx
    rw [show ((n+1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω)+1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_tube hU)]
    refine ⟨fun x hx => (hI x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · exact (ih hG).congr (fun x hx => (hI x hx).fderiv)

/-- Full joint C∞ regularity, with no domination assumption. -/
theorem contDiffOn_integral {U : Set (ℂ × ℝ)} (hU : IsOpen U)
    {F : ℂ × ℝ → E} (hF : ContDiffOn ℝ ∞ F U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in Icc (0 : ℝ) 1, F (x,t)) (tube U) := by
  rw [contDiffOn_infty]
  intro n
  exact contDiffOn_integral_nat n hU (hF.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))

end CompactIntegral

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Jacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Matrix Real

lemma weightedGram_posSemidef {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    {c : Fin N → ℝ} (hc : ∀ j, 0 ≤ c j) : (weightedGram A c).PosSemidef := by
  have h := (Matrix.posSemidef_diagonal_iff.mpr hc).conjTranspose_mul_mul_same A
  simpa only [weightedGram, Matrix.conjTranspose_eq_transpose_of_trivial] using h

lemma weightedGram_det_nonneg {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    {c : Fin N → ℝ} (hc : ∀ j, 0 ≤ c j) : 0 ≤ (weightedGram A c).det :=
  (weightedGram_posSemidef A hc).det_nonneg

lemma weightedGram_apply {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (c : Fin N → ℝ) (i k : Fin n) :
    weightedGram A c i k = ∑ j : Fin N, A j i*c j*A j k := by
  unfold weightedGram
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

lemma weightedGram_smul {n N : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (c : Fin N → ℝ) (a : ℝ) : weightedGram A (fun j => a*c j) = a • weightedGram A c := by
  ext i k
  simp only [weightedGram_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hessianWeight_nonneg (m : ℝ) (f d : ℂ) : 0 ≤ hessianWeight m f d := by
  unfold hessianWeight
  positivity

lemma verticalWeight_eq_scaled_hessianWeight {m : ℝ} (hm : m ≠ 0) (f d : ℂ) :
    verticalWeight m f d = (4/(Real.pi*m))*hessianWeight m f d := by
  unfold verticalWeight hessianWeight
  field_simp

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PlanarIntegralRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff

lemma contDiff_segmentPoint : ContDiff ℝ ∞ segmentPoint := by
  exact (Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp contDiff_fst)).add
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_snd.mul (Complex.imCLM.contDiff.comp contDiff_fst))).mul contDiff_const)

lemma isOpen_segmentParameterDomain : IsOpen segmentParameterDomain :=
  MahlerConformal.isOpen_Omega.preimage contDiff_segmentPoint.continuous

/-- The exact original integral under t=s*xi; the equality also holds at xi=0
and for negative xi, using oriented interval integration. -/
theorem planarPrimitive_eq_fixedIntegral (m : ℕ) (u : ℂ) :
    planarPrimitive m u.re u.im =
      u.im * ∫ s in Icc (0 : ℝ) 1, planarDensity m (segmentPoint (u,s)) := by
  have h := intervalIntegral.smul_integral_comp_mul_right
    (fun t : ℝ => planarDensity m ((u.re : ℂ)+(t : ℂ)*I)) (a := 0) (b := 1) u.im
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at h
  simpa [planarPrimitive,segmentPoint,smul_eq_mul] using h.symm

/-- The density on the fixed interval is jointly smooth on its actual open domain. -/
lemma contDiffOn_segmentDensity (m : ℕ) :
    ContDiffOn ℝ ∞ (fun p => planarDensity m (segmentPoint p)) segmentParameterDomain := by
  intro p hp
  exact ((contDiffAt_planarDensity m hp).comp p contDiff_segmentPoint.contDiffAt).contDiffWithinAt

/-- Joint C∞ regularity of the primitive on the open
segment-containment domain, including its real diameter. -/
theorem contDiffOn_planarPrimitive_segment (m : ℕ) :
    ContDiffOn ℝ ∞ (fun u : ℂ => planarPrimitive m u.re u.im) planarSegmentDomain := by
  have hi := CompactIntegral.contDiffOn_integral isOpen_segmentParameterDomain
    (contDiffOn_segmentDensity m)
  have him : ContDiffOn ℝ ∞ (fun u : ℂ => u.im) planarSegmentDomain :=
    Complex.imCLM.contDiff.contDiffOn
  exact (him.mul hi).congr (fun u _ => planarPrimitive_eq_fixedIntegral m u)

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_PlanarRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter MeasureTheory
open scoped Topology ContDiff
open MahlerConformal

lemma vertical_segment_mem_Omega_regularity {u : ℂ} (hu : u ∈ Omega) {t : ℝ}
    (ht : t ∈ uIcc 0 u.im) : (u.re : ℂ) + (t : ℂ)*I ∈ Omega := by
  have hq : u.re ∈ Ioo (-1 : ℝ) 1 := by
    rw [← image_re_F_disk]
    exact ⟨u,hu,rfl⟩
  have hv := verticalFiber_interval hq
  have hy : u.im ∈ verticalFiber u.re := by
    simpa only [verticalFiber, mem_ofPred_eq, Complex.re_add_im] using hu
  exact hv.2.1.uIcc_subset hv.2.2 hy ht

/-- The open domain used for parameter integration is exactly Omega. -/
theorem planarSegmentDomain_eq_Omega : planarSegmentDomain = Omega := by
  ext u
  constructor
  · intro hu
    have h := hu 1 (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    simpa [segmentParameterDomain,segmentPoint] using h
  · intro hu s hs
    apply vertical_segment_mem_Omega_regularity hu
    have h : s*u.im ∈ (fun x : ℝ => x*u.im) '' uIcc (0 : ℝ) 1 :=
      ⟨s,by simpa using hs,rfl⟩
    simpa only [image_mul_const_uIcc,zero_mul,one_mul] using h

/-- Full joint real C∞ regularity of P_m on
all of Omega. In particular, no exclusion of the zero or xi=0 is needed. -/
theorem contDiffOn_planarPrimitive (m : ℕ) :
    ContDiffOn ℝ ∞ (fun u : ℂ => planarPrimitive m u.re u.im) Omega := by
  rw [← planarSegmentDomain_eq_Omega]
  exact contDiffOn_planarPrimitive_segment m

theorem contDiffOn_one_planarPrimitive (m : ℕ) :
    ContDiffOn ℝ 1 (fun u : ℂ => planarPrimitive m u.re u.im) Omega :=
  (contDiffOn_planarPrimitive m).of_le (by norm_num)

theorem differentiableOn_planarPrimitive (m : ℕ) :
    DifferentiableOn ℝ (fun u : ℂ => planarPrimitive m u.re u.im) Omega :=
  (contDiffOn_one_planarPrimitive m).differentiableOn (by norm_num)

theorem hasFDerivAt_planarPrimitive (m : ℕ) {u : ℂ} (hu : u ∈ Omega) :
    HasFDerivAt (fun z : ℂ => planarPrimitive m z.re z.im)
      (fderiv ℝ (fun z : ℂ => planarPrimitive m z.re z.im) u) u :=
  ((differentiableOn_planarPrimitive m).differentiableAt (isOpen_Omega.mem_nhds hu)).hasFDerivAt

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripDifferential
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset
open scoped Topology ContDiff
open MahlerConformal

variable {n N : ℕ}

lemma rowCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N) (x : Fin n → ℝ) :
    rowCLM A j x = measurement A x j := by
  simp [rowCLM,measurement]

lemma stripCoordinateCLM_apply (A : Matrix (Fin N) (Fin n) ℝ) (j : Fin N)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : stripCoordinateCLM A j z = stripCoordinate A z j := by
  simp [stripCoordinateCLM,stripCoordinate,rowCLM_apply,mul_comm]

lemma planarDifferential_I (m : ℕ) {q t : ℝ} (hu : (q : ℂ)+(t : ℂ)*I ∈ Omega) :
    planarDifferential m ((q : ℂ)+(t : ℂ)*I) I = planarDensity m ((q : ℂ)+(t : ℂ)*I) := by
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
  have hl : HasDerivAt (fun s : ℝ => (q : ℂ)+(s : ℂ)*I) I t := by
    simpa using (hid.mul_const I).const_add (q : ℂ)
  have hp := (hasFDerivAt_planarPrimitive m hu).comp_hasDerivAt t hl
  have he : HasDerivAt (planarPrimitive m q) (planarDifferential m ((q : ℂ)+(t : ℂ)*I) I) t := by
    simpa [Function.comp_def,planarDifferential] using hp
  exact he.unique (hasDerivAt_planarPrimitive_global m hu)

/-- The full actual real derivative; its mixed x-derivative is retained. -/
theorem hasFDerivAt_stripMap (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) :
    HasFDerivAt (stripMap A m) (stripDerivative A m z) z := by
  have hp : ∀ j, HasFDerivAt
      (fun w => planarPrimitive m (measurement A w.1 j) (measurement A w.2 j))
      ((planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j)) z := by
    intro j
    have hc : HasFDerivAt (fun w => stripCoordinate A w j) (stripCoordinateCLM A j) z := by
      apply (stripCoordinateCLM A j).hasFDerivAt.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun w => (stripCoordinateCLM_apply A j w).symm)
    have h := (hasFDerivAt_planarPrimitive m (hz j)).comp z hc
    simpa [Function.comp_def,stripCoordinateCLM_apply,stripCoordinate,planarDifferential] using h
  have hb : HasFDerivAt
      (fun w => push A (fun j => planarPrimitive m (measurement A w.1 j) (measurement A w.2 j)))
      (ContinuousLinearMap.pi fun i =>
        ∑ j, A j i • (planarDifferential m (stripCoordinate A z j)).comp (stripCoordinateCLM A j)) z := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact HasFDerivAt.fun_sum (fun j _ => (hp j).const_mul (A j i))
  exact (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.prodMk hb

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Matrix
open MahlerConformal
variable {n N : ℕ}

/-- Determinant of a real linear map that fixes its first coordinate and has
vertical block G; arbitrary mixed derivatives do not affect the determinant. -/
lemma det_eq_vertical_block
    (L : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)))
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hfst : ∀ z, (L z).1 = z.1)
    (hvertical : ∀ y, (L (0,y)).2 = G.mulVec y) : L.det = G.det := by
  let b := (Pi.basisFun ℝ (Fin n)).prod (Pi.basisFun ℝ (Fin n))
  let C : Matrix (Fin n) (Fin n) ℝ := fun i j => (L (Pi.single j 1,0)).2 i
  have he : LinearMap.toMatrix b b L = Matrix.fromBlocks 1 0 C G := by
    ext (i | i) (j | j) <;>
      simp [b,C,LinearMap.toMatrix_apply,Module.Basis.prod_apply,Pi.basisFun_apply,hfst,hvertical,
        Matrix.fromBlocks,Matrix.one_apply,Pi.single_apply]
  rw [← LinearMap.det_toMatrix b,he,Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,one_mul]

lemma stripDerivative_fst (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    (z w : (Fin n → ℝ) × (Fin n → ℝ)) : (stripDerivative A m z w).1 = w.1 := rfl

lemma stripDerivative_vertical (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) (y : Fin n → ℝ) :
    (stripDerivative A m z (0,y)).2 =
      (weightedGram A (fun j => planarDensity m (stripCoordinate A z j))).mulVec y := by
  funext i
  have hcoord : ∀ j, stripCoordinateCLM A j (0,y) = measurement A y j • (I : ℂ) := by
    intro j
    simp [stripCoordinateCLM_apply,stripCoordinate,measurement,Complex.real_smul]
  have hP : ∀ j, planarDifferential m (stripCoordinate A z j) I =
      planarDensity m (stripCoordinate A z j) := fun j => planarDifferential_I m (hz j)
  simp only [stripDerivative,ContinuousLinearMap.prod_apply,ContinuousLinearMap.pi_apply,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    hcoord,map_smul,hP,smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, weightedGram_apply,measurement,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact Jacobian identity for the actual derivative of the actual map. -/
theorem abs_det_stripDerivative (A : Matrix (Fin N) (Fin n) ℝ) {m : ℕ} (hm : 2 ≤ m)
    {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripDomain A) :
    |(stripDerivative A m z).det| = (4/(Real.pi*(m : ℝ)))^n*
      (weightedGram A (fun j => hessianWeight m (inverseF (stripCoordinate A z j))
        (deriv inverseF (stripCoordinate A z j)))).det := by
  have hdet := det_eq_vertical_block (stripDerivative A m z).toLinearMap
    (weightedGram A (fun j => planarDensity m (stripCoordinate A z j)))
    (stripDerivative_fst A m z) (stripDerivative_vertical A m hz)
  change |(stripDerivative A m z).toLinearMap.det| = _
  rw [hdet]
  have hw : (fun j => planarDensity m (stripCoordinate A z j)) =
      fun j => (4/(Real.pi*(m : ℝ)))*hessianWeight m (inverseF (stripCoordinate A z j))
        (deriv inverseF (stripCoordinate A z j)) := by
    funext j
    rw [planarDensity_eq m (by omega)]
    exact verticalWeight_eq_scaled_hessianWeight (by exact_mod_cast (show m ≠ 0 by omega)) _ _
  rw [hw,weightedGram_smul,Matrix.det_smul,Fintype.card_fin]
  apply abs_of_nonneg
  exact mul_nonneg (pow_nonneg (by positivity) _) (weightedGram_det_nonneg A
    (fun j => hessianWeight_nonneg _ _ _))

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_StripVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

lemma isOpen_stripDomain (A : Matrix (Fin N) (Fin n) ℝ) : IsOpen (stripDomain A) := by
  have he : stripDomain A = ⋂ j, (stripCoordinateCLM A j) ⁻¹' Omega := by
    ext z
    simp only [stripDomain, mem_ofPred_eq, mem_iInter, Set.mem_preimage,stripCoordinateCLM_apply]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => isOpen_Omega.preimage (stripCoordinateCLM A j).continuous)

lemma continuousOn_stripTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    ContinuousOn (stripTau A m) (stripDomain A) := by
  have hc : ∀ j, ContinuousOn (fun z => ‖inverseF (stripCoordinate A z j)‖^(2*m : ℕ)) (stripDomain A) := by
    intro j
    have hi : ContinuousOn (fun z => inverseF (stripCoordinate A z j)) (stripDomain A) := by
      apply differentiableOn_inverseF.continuousOn.comp
      · have h : ContinuousOn (stripCoordinateCLM A j) (stripDomain A) := (stripCoordinateCLM A j).continuous.continuousOn
        exact h.congr (fun z _ => (stripCoordinateCLM_apply A j z).symm)
      · intro z hz
        exact hz j
    exact hi.norm.pow _
  have h := continuousOn_finsetSum (univ : Finset (Fin N)) (fun j _ => hc j)
  convert h using 1
  funext z
  unfold stripTau
  apply sum_congr rfl
  intro j _
  rw [show 2*(m : ℝ) = ((2*m : ℕ) : ℝ) by norm_cast,Real.rpow_natCast]

lemma isOpen_stripSublevel (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) :
    IsOpen (stripSublevel A m) :=
  (continuousOn_stripTau A m).isOpen_inter_preimage (isOpen_stripDomain A) isOpen_Iio

/-- Change of variables for the literal finite-strip map, allowing vanishing
Jacobian values. Neither local invertibility nor a change-of-variables premise
is assumed. -/
theorem stripMap_volume_eq_eq_oai (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) =
      ∫⁻ z in stripSublevel A m,
        ENNReal.ofReal ((4/(Real.pi*(m : ℝ)))^n*stripHessianDet A m z) := by
  let : (volume : Measure ((Fin n → ℝ) × (Fin n → ℝ))).IsAddHaarMeasure := by
    simpa only [Measure.volume_eq_prod] using!
      (Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ)))
  have hder : ∀ z ∈ stripSublevel A m,
      HasFDerivWithinAt (stripMap A m) (stripDerivative A m z) (stripSublevel A m) z :=
    fun z hz => (hasFDerivAt_stripMap A m hz.1).hasFDerivWithinAt
  have hinj : InjOn (stripMap A m) (stripSublevel A m) :=
    (stripMap_injOn A hA (show 0 < m by omega)).mono inter_subset_left
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume (isOpen_stripSublevel A m).measurableSet hder hinj]
  apply setLIntegral_congr_fun (isOpen_stripSublevel A m).measurableSet
  intro z hz
  dsimp only
  rw [abs_det_stripDerivative A hm hz.1]
  rfl

end SymmetricMahler

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.stripMap_volume_eq_eq_oai := @OAI.SymmetricMahler.stripMap_volume_eq_eq_oai
