-- Prove2me | solution 1 for OAI.SharpPlanar.exact_sign_tail_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:58:44.151648+00:00
-- url     : https://prove2.me/submissions/eb28428a-2170-4b34-ac6f-5656432d9c60

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G1652
import Definitions.Def_OAIQ098G1685
import Theorems.Thm_OAI_SharpPlanar_D_0_g
import Theorems.Thm_OAI_SharpPlanar_D_1_g
import Theorems.Thm_OAI_SharpPlanar_D_3_g
import Theorems.Thm_OAI_SharpPlanar_D_4_g
import Theorems.Thm_OAI_SharpPlanar_D_7_g
import Theorems.Thm_OAI_SharpPlanar_D_9_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_interpolation_exists_unique_g
import Theorems.Thm_OAI_SharpPlanar_Q_0_g
import Theorems.Thm_OAI_SharpPlanar_Q_1_g
import Theorems.Thm_OAI_SharpPlanar_Q_3_g
import Theorems.Thm_OAI_SharpPlanar_Q_4_g
import Theorems.Thm_OAI_SharpPlanar_Q_7_g
import Theorems.Thm_OAI_SharpPlanar_Q_9_g
import Theorems.Thm_OAI_SharpPlanar_X_norm_g
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
import Theorems.Thm_OAI_SharpPlanar_exact_head_lower_g
import Theorems.Thm_OAI_SharpPlanar_h_pos_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_realSpectral_norm_g
import Theorems.Thm_OAI_SharpPlanar_summand_bound_g
import Theorems.Thm_OAI_SharpPlanar_tail_second_bound_g
import Theorems.Thm_OAI_SharpPlanar_trig_table_g
import Theorems.Thm_OAI_SharpPlanar_u_bound_g
import Theorems.Thm_OAI_SharpPlanar_v_bound_g

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound_g n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound_g p.x n j ht)
    exact (X_summable_pairs_g p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound_g p.x n j ht)
          ((X_summable_pairs_g p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm_g]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound_g _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos_g) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos_g.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density_g p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval_g hj ht) |>.intervalIntegrable


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BarrierProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Set Filter
open scoped Topology
open scoped BigOperators
lemma logSin_hasDeriv (a r x : ℝ) (hx : Real.sin (a*(x-r)) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log (Real.sin (a*(u-r))))
      (a*Real.cos (a*(x-r))/Real.sin (a*(x-r))) x := by
  have hd := (((hasDerivAt_id x).sub_const r).const_mul a).sin.log hx
  simpa only [id_eq, mul_one, mul_comm] using hd

lemma cot_scaled_hasDeriv (a r x : ℝ) (hx : Real.sin (a*(x-r)) ≠ 0) :
    HasDerivAt (fun u : ℝ => a*Real.cos (a*(u-r))/Real.sin (a*(u-r)))
      (-a^2/(Real.sin (a*(x-r)))^2) x := by
  have hp := ((hasDerivAt_id x).sub_const r).const_mul a
  have hd := (hp.cos.const_mul a).div hp.sin hx
  simp only [id_eq, mul_one] at hd
  apply hd.congr_deriv
  congr 1
  nlinarith [sq_nonneg a, Real.sin_sq_add_cos_sq (a*(x-r)),
    congrArg (fun t : ℝ => a^2*t) (Real.sin_sq_add_cos_sq (a*(x-r)))]

lemma logSin_concaveOn {D : Set ℝ} (hD : Convex ℝ D) (a r : ℝ)
    (hs : ∀ x ∈ D, Real.sin (a*(x-r)) ≠ 0) :
    ConcaveOn ℝ D (fun x : ℝ => Real.log (Real.sin (a*(x-r)))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (f' := fun x => a*Real.cos (a*(x-r))/Real.sin (a*(x-r)))
    (f'' := fun x => -a^2/Real.sin (a*(x-r))^2)
  · exact (by fun_prop : Continuous fun x : ℝ => Real.sin (a*(x-r))).continuousOn.log hs
  · intro x hx
    exact (logSin_hasDeriv a r x (hs _ (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (cot_scaled_hasDeriv a r x (hs _ (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

lemma sinc_ne_zero {a x : ℝ} (ha : a ≠ 0)
    (hs : x ≠ 0 → Real.sin (a*x) ≠ 0) : Real.sinc (a*x) ≠ 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero ha hx)]
    exact div_ne_zero (hs hx) (mul_ne_zero ha hx)

lemma logSinc_hasDeriv (a x : ℝ) (ha : a ≠ 0) (hx : x ≠ 0)
    (hs : Real.sin (a*x) ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log (Real.sinc (a*u)))
      (a*Real.cos (a*x)/Real.sin (a*x) - 1/x) x := by
  have hp := (hasDerivAt_id x).const_mul a
  have hd := (hp.sin.div hp (mul_ne_zero ha hx)).log (div_ne_zero hs (mul_ne_zero ha hx))
  have he : (fun u : ℝ => Real.log (Real.sinc (a*u))) =ᶠ[𝓝 x]
      (fun u : ℝ => Real.log (Real.sin (a*u)/(a*u))) := by
    filter_upwards [eventually_ne_nhds hx] with u hu
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha hu)]
  apply HasDerivAt.congr_of_eventuallyEq (f := fun u : ℝ => Real.log (Real.sin (a*u)/(a*u))) _ he
  simp only [Pi.div_apply, id_eq, mul_one] at hd
  apply hd.congr_deriv
  field_simp

lemma logSinc_deriv_hasDeriv (a x : ℝ) (hx : x ≠ 0)
    (hs : Real.sin (a*x) ≠ 0) :
    HasDerivAt (fun u : ℝ => a*Real.cos (a*u)/Real.sin (a*u) - 1/u)
      (1/x^2 - a^2/Real.sin (a*x)^2) x := by
  have hd := (cot_scaled_hasDeriv a 0 x (by simpa using hs)).sub
    ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx)
  simp only [id_eq, sub_zero, zero_mul, one_mul, zero_sub] at hd
  apply hd.congr_deriv
  ring


lemma logSinc_concaveOn {D : Set ℝ} (hD : Convex ℝ D) (a : ℝ) (ha : a ≠ 0)
    (h0 : (0 : ℝ) ∉ interior D)
    (hs : ∀ x ∈ D, x ≠ 0 → Real.sin (a*x) ≠ 0) :
    ConcaveOn ℝ D (fun x : ℝ => Real.log (Real.sinc (a*x))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos hD
    (f' := fun x => a*Real.cos (a*x)/Real.sin (a*x) - 1/x)
    (f'' := fun x => 1/x^2 - a^2/Real.sin (a*x)^2)
  · apply (Real.continuous_sinc.comp (by fun_prop)).continuousOn.log
    exact fun x hx => sinc_ne_zero ha (hs x hx)
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    exact (logSinc_hasDeriv a x ha hx0 (hs x (interior_subset hx) hx0)).hasDerivWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    exact (logSinc_deriv_hasDeriv a x hx0 (hs x (interior_subset hx) hx0)).hasDerivWithinAt
  · intro x hx
    have hx0 : x ≠ 0 := fun he => h0 (he ▸ hx)
    have hsin : Real.sin (a*x) ≠ 0 := hs x (interior_subset hx) hx0
    apply sub_nonpos.mpr
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero hx0) (sq_pos_of_ne_zero hsin)).mpr
    have hh : Real.sin (a*x)^2 ≤ (a*x)^2 := by
      exact sq_le_sq.mpr Real.abs_sin_le_abs
    nlinarith

end SharpPlanar


namespace SharpPlanar
open Set Filter
open scoped Topology

lemma dividedP_zero (a : ℕ) (ha : a < 12) : dividedP a 0 = Q a := by
  simp [dividedP,Q,Nat.mod_eq_of_lt ha]

lemma dividedP_factor (a : ℕ) (ha : a ∈ residues) (u : ℝ) :
    u^2 * dividedP a u = P (a+u) := by
  rw [P,← Finset.mul_prod_erase residues (fun r : ℕ => (2*Real.sin (Real.pi*(a+u-r)/12))^2) ha]
  unfold dividedP
  rw [show ((a:ℝ)+u-a)=u by ring]
  have hs : (Real.pi*u/12)*Real.sinc (Real.pi*u/12) = Real.sin (Real.pi*u/12) := by
    by_cases hz : Real.pi*u/12 = 0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz,mul_div_cancel₀ _ hz]
  rw [← hs]
  ring

lemma sine_twelfth_ne {v : ℝ} (hl : -12 < v) (hr : v < 12) (hv : v ≠ 0) :
    Real.sin (Real.pi*v/12) ≠ 0 := by
  rw [ne_eq,Real.sin_eq_zero_iff_of_lt_of_lt
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (show 0 < v+12 by linarith)])
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (show 0 < 12-v by linarith)])]
  exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv) (by norm_num)

lemma half_pos (a : ℕ) (ha : a ∈ residues) : 0 < leftHalf a ∧ 0 < rightHalf a := by
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [leftHalf,rightHalf]
lemma half_bounds (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : -12 < u ∧ u < 12 := by
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [leftHalf,rightHalf,mem_Icc] at hu <;>
    constructor <;> linarith
lemma other_sine_ne (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) (r : ℕ) (hr : r ∈ residues.erase a) :
    Real.sin (Real.pi*(a+u-r)/12) ≠ 0 := by
  apply sine_twelfth_ne
  all_goals
    have hra := (Finset.mem_erase.mp hr).1
    have hrr := (Finset.mem_erase.mp hr).2
    simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha hrr
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases hrr with rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | contradiction | (norm_num [leftHalf,rightHalf,mem_Icc] at hu ⊢; grind)

lemma dividedP_pos (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : 0 < dividedP a u := by
  apply mul_pos
  · apply mul_pos (sq_pos_of_pos (by positivity))
    apply sq_pos_of_ne_zero
    rw [show Real.pi*u/12=(Real.pi/12)*u by ring]
    apply sinc_ne_zero (a := Real.pi/12) (by positivity)
    intro hu0
    have hb := half_bounds a ha hu
    convert sine_twelfth_ne hb.1 hb.2 hu0 using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  · exact Finset.prod_pos (fun r hr => sq_pos_of_ne_zero (mul_ne_zero (by norm_num) (other_sine_ne a ha hu r hr)))

lemma dividedP_log (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) :
    Real.log (dividedP a u) = 2*Real.log (Real.pi/6) +
      2*Real.log (Real.sinc (Real.pi*u/12)) +
      ∑ r ∈ residues.erase a, (2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
  have hn (r : ℕ) (hr : r ∈ residues.erase a) : 2*Real.sin (Real.pi*(a+u-r)/12) ≠ 0 :=
    mul_ne_zero (by norm_num) (other_sine_ne a ha hu r hr)
  have hb := half_bounds a ha hu
  have hsi : Real.sinc (Real.pi*u/12) ≠ 0 := by
    convert sinc_ne_zero (a := Real.pi/12) (by positivity)
      (fun hu0 => by convert sine_twelfth_ne hb.1 hb.2 hu0 using 1; congr 1; ring) using 1; congr 1; ring
  unfold dividedP
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hsi)) (Finset.prod_ne_zero_iff.mpr (fun r hr => pow_ne_zero 2 (hn r hr))),
    Real.log_mul (pow_ne_zero 2 (by positivity)) (pow_ne_zero 2 hsi),Real.log_pow,Real.log_pow,Real.log_prod (fun r hr => pow_ne_zero 2 (hn r hr))]
  simp only [Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Real.log_pow,Real.log_mul (by norm_num) (other_sine_ne a ha hu r hr)]
  push_cast
  ring

end SharpPlanar


namespace SharpPlanar
open Set Filter
open scoped Topology

lemma concaveOn_finset_sum {ι : Type*} (s : Finset ι) {D : Set ℝ}
    (hD : Convex ℝ D) (g : ι → ℝ → ℝ) (hg : ∀ r ∈ s, ConcaveOn ℝ D (g r)) :
    ConcaveOn ℝ D (fun u => ∑ r ∈ s, g r u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using concaveOn_const (0:ℝ) hD
  | @insert r s hrs ih =>
    have hh : ConcaveOn ℝ D (fun u => g r u + ∑ r ∈ s, g r u) := (hg r (Finset.mem_insert_self ..)).add (ih (fun v hv => hg v (Finset.mem_insert_of_mem hv)))
    simpa only [Finset.sum_insert hrs, Pi.add_apply] using hh

lemma dividedP_log_concave (a : ℕ) (ha : a ∈ residues) {D : Set ℝ}
    (hD : Convex ℝ D) (hsub : D ⊆ Icc (-leftHalf a) (rightHalf a))
    (h0 : (0:ℝ) ∉ interior D) : ConcaveOn ℝ D (fun u => Real.log (dividedP a u)) := by
  have hsinc0 := logSinc_concaveOn hD (Real.pi/12) (by positivity) h0 (fun u hu hu0 => by
    have hb := half_bounds a ha (hsub hu)
    rw [show (Real.pi/12)*u = Real.pi*u/12 by ring]
    exact sine_twelfth_ne hb.1 hb.2 hu0)
  have hsinc : ConcaveOn ℝ D (fun u => Real.log (Real.sinc (Real.pi*u/12))) := by
    apply hsinc0.congr
    intro u hu
    dsimp only
    rw [show (Real.pi/12)*u = Real.pi*u/12 by ring]
  have hother (r : ℕ) (hr : r ∈ residues.erase a) :
      ConcaveOn ℝ D (fun u => 2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
    have hh0 := logSin_concaveOn hD (Real.pi/12) ((r:ℝ)-a) (fun u hu => by
      rw [show (Real.pi/12)*(u-((r:ℝ)-a)) = Real.pi*(a+u-r)/12 by ring]
      exact other_sine_ne a ha (hsub hu) r hr)
    have hh : ConcaveOn ℝ D (fun u => Real.log (Real.sin (Real.pi*(a+u-r)/12))) := by
      apply hh0.congr
      intro u hu
      dsimp only
      rw [show (Real.pi/12)*(u-((r:ℝ)-a)) = Real.pi*(a+u-r)/12 by ring]
    exact (concaveOn_const (2*Real.log 2) hD).add (ConcaveOn.smul (by norm_num : 0 ≤ (2:ℝ)) hh)
  have hh : ConcaveOn ℝ D (fun u => 2*Real.log (Real.pi/6) + 2*Real.log (Real.sinc (Real.pi*u/12)) + ∑ r ∈ residues.erase a, (2*Real.log 2 + 2*Real.log (Real.sin (Real.pi*(a+u-r)/12)))) := ((concaveOn_const (2*Real.log (Real.pi/6)) hD).add
    (ConcaveOn.smul (by norm_num : 0 ≤ (2:ℝ)) hsinc)).add
      (concaveOn_finset_sum (residues.erase a) hD _ hother)
  apply hh.congr
  intro u hu
  exact (dividedP_log a ha (hsub hu)).symm

lemma lower_of_log_concave {f : ℝ → ℝ} {v w l : ℝ} (hl : 0 < l)
    (hp : ∀ u ∈ uIcc v w, 0 < f u)
    (hc : ConcaveOn ℝ (uIcc v w) (fun u => Real.log (f u)))
    (hv : l ≤ f v) (hw : l ≤ f w) {u : ℝ} (hu : u ∈ uIcc v w) : l ≤ f u := by
  have hs := hc.ge_on_segment (left_mem_uIcc) (right_mem_uIcc)
    (show u ∈ segment ℝ v w by simpa only [segment_eq_uIcc] using hu)
  have hj : Real.log l ≤ Real.log (f u) := le_trans (le_min
    (Real.log_le_log hl hv) (Real.log_le_log hl hw)) hs
  exact (Real.log_le_log_iff hl (hp u hu)).mp hj

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq_g]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1
lemma b_pow_4 : b^4 = (3/4 : ℝ)^2 := b_pow_even 2
lemma b_pow_5 : b^5 = (3/4 : ℝ)^2 * b := b_pow_odd 2
lemma b_pow_6 : b^6 = (3/4 : ℝ)^3 := b_pow_even 3

lemma b_lt_thirteen_fifteenths : b < 13/15 := by nlinarith [b_sq_g, b_pos_g]
lemma pi_lower : (157/50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]

lemma Q_small_lower : (7/4 : ℝ) < (2*Real.pi^2/3)*(2-2*b) := by
  have hpi2 : (157/50 : ℝ)^2 < Real.pi^2 := by nlinarith [pi_lower, Real.pi_pos]
  have hf : (4/15 : ℝ) < 2-2*b := by linarith [b_lt_thirteen_fifteenths]
  have hx : (2*(157/50 : ℝ)^2/3)*(4/15) < (2*Real.pi^2/3)*(2-2*b) := by
    gcongr
  norm_num at hx
  linarith


theorem Q_lower (n : ℕ) (hn : n%12 ∈ residues) : (7/4 : ℝ) < Q n := by
  rw [← Q_mod]
  have hb := b_pos_g
  have hp := Real.pi_pos
  have hp2 : (157/50 : ℝ)^2 < Real.pi^2 := by nlinarith [pi_lower]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    rw [hn] <;> first | rw [Q_0_g] | rw [Q_1_g] | rw [Q_3_g] | rw [Q_4_g] | rw [Q_7_g] | rw [Q_9_g]
  · nlinarith
  · exact Q_small_lower
  · exact Q_small_lower
  · nlinarith
  · nlinarith [mul_pos (sq_pos_of_pos hp) hb]
  · nlinarith [mul_pos (sq_pos_of_pos hp) hb]


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate

namespace SharpPlanar

lemma weighted_exp_integral (c : ℂ) (hc : c ≠ 0) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((T : ℂ)-t)*Complex.exp (c*t)) =
      (Complex.exp (c*T)-1-c*T)/c^2 := by
  let F : ℝ → ℂ := fun t => (((T : ℂ)-t)*Complex.exp (c*t))/c +
      Complex.exp (c*t)/c^2
  have hd (t : ℝ) : HasDerivAt F (((T : ℂ)-t)*Complex.exp (c*t)) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (c*t))
        (Complex.exp (c*t)*c) t := by
      convert (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal).cexp using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    have ht : HasDerivAt (fun t : ℝ => (T : ℂ)-t) (-1) t := by
      convert ((hasDerivAt_id (t : ℂ)).const_sub (T : ℂ)).comp_ofReal using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
    convert ((ht.mul he).div_const c).add (he.div_const (c^2)) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (field_simp [hc]; ring)
  have hi : IntervalIntegrable (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (c*t)) volume 0 T :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  simp only [F, Complex.ofReal_zero, sub_self, zero_mul, mul_zero, Complex.exp_zero,
    sub_zero, zero_div]
  field_simp
  ring

lemma exponential_division_one (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1)/(U : ℂ) =
      Complex.I*Real.pi * ∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 1; ring
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

lemma exponential_division_two (U T : ℝ) (hu : U ≠ 0) :
    (Complex.exp (Complex.I*Real.pi*T*U)-1-Complex.I*Real.pi*T*U)/(U : ℂ)^2 =
      -(Real.pi : ℂ)^2 * ∫ t in (0 : ℝ)..T,
        ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U) := by
  have hc : Complex.I*(Real.pi : ℂ)*(U : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      (by exact_mod_cast hu)
  have he : (fun t : ℝ => ((T : ℂ)-t)*Complex.exp (Complex.I*Real.pi*t*U)) =
      (fun t : ℝ => ((T : ℂ)-t)*Complex.exp ((Complex.I*Real.pi*(U : ℂ))*t)) := by
    funext t; congr 2; ring
  rw [he, weighted_exp_integral _ hc]
  have hh : Complex.I*Real.pi*(U : ℂ)*T = Complex.I*Real.pi*T*U := by ring
  rw [hh]
  field_simp
  simp [Complex.I_sq]
  ring

end SharpPlanar

namespace SharpPlanar

lemma triangular_piece_integrals (N : ℕ) (a : ℕ → ℝ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ l, Continuous (f l)) :
    (∑ j ∈ Finset.range N, ∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc 1 N, ∫ t in a 0..a l, f l t := by
  have ht (j : ℕ) : (∫ t in a j..a (j+1),
      ∑ l ∈ Finset.Icc (j+1) N, f l t) =
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    exact intervalIntegral.integral_finsetSum fun l _ => (hf l).intervalIntegrable _ _
  simp_rw [ht]
  have hswap := Finset.sum_Ico_Ico_comm' 0 (N+1)
    (fun j l => ∫ t in a j..a (j+1), f l t)
  have hi (j : ℕ) : Finset.Ico (j+1) (N+1) = Finset.Icc (j+1) N := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [Nat.Ico_zero_eq_range, hi] at hswap
  have hleft : (∑ j ∈ Finset.range (N+1),
      ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t) =
      ∑ j ∈ Finset.range N,
        ∑ l ∈ Finset.Icc (j+1) N, ∫ t in a j..a (j+1), f l t := by
    rw [Finset.sum_range_succ]
    simp
  rw [hleft] at hswap
  rw [hswap]
  have hadj (l : ℕ) : (∑ j ∈ Finset.range l, ∫ t in a j..a (j+1), f l t) =
      ∫ t in a 0..a l, f l t := by
    exact intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ => (hf l).intervalIntegrable _ _)
  simp_rw [hadj]
  symm
  apply Finset.sum_subset
  · intro l hl
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    omega
  · intro l hl hn
    have : l = 0 := by
      simp only [Finset.mem_Icc, Finset.mem_range, not_and, not_le] at *
      omega
    simp [this]

lemma u_integrand (n j : ℕ) (s t : ℝ) :
    u n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold u
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

lemma v_integrand (n j : ℕ) (s t : ℝ) :
    v n j t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
    ∑ l ∈ Finset.Icc (j+1) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))) := by
  unfold v
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have he : Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n) *
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*s) =
      Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  push_cast
  rw [show Complex.I*Real.pi*(l:ℂ)/6*n = Complex.I*Real.pi*((l:ℂ)/6)*n by ring]
  calc
    _ = 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℂ)/6)*n)*
      (Complex.I*Real.pi*
        (Complex.exp (-Complex.I*Real.pi*(t:ℂ)*n)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))) := by ring
    _ = _ := by rw [he]

end SharpPlanar

namespace SharpPlanar

lemma P_as_table (s : ℝ) : P s =
    ∏ a ∈ residues,
      (2 - 2*(Real.cos (Real.pi*s/6)*cosTable a + Real.sin (Real.pi*s/6)*sinTable a)) := by
  unfold P
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2*(Real.pi*(s-a)/12) = Real.pi*s/6-Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table_g a (by have := residue_lt ha; omega)).1,
    (trig_table_g a (by have := residue_lt ha; omega)).2]

lemma polynomial_reduce (c d : ℝ) (hcd : c^2+d^2=1) :
    (2-2*c)*(2-2*(c*b+d/2))*(2-2*d)*(2+c-2*b*d)*(2+2*(c*b+d/2))*(2+2*d) =
      (4*(c/2+b*d)^2-3)^2*(1-2*(c/2+b*d))^2 := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  ring_nf
  simp only [b_sq_g, b_pow_3, b_pow_4, b_pow_5, b_pow_6, hd2, hd3, hd4, hd5, hd6]
  ring

lemma P_cos_factor (s : ℝ) : P s =
    (4*Real.cos (Real.pi*(s-2)/6)^2-3)^2 *
      (1-2*Real.cos (Real.pi*(s-2)/6))^2 := by
  rw [P_as_table]
  norm_num [residues, cosTable, sinTable]
  rw [show Real.pi*(s-2)/6=Real.pi*s/6-Real.pi/3 by ring,
    Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  change _ = (4*(Real.cos (Real.pi*s/6)*(1/2)+Real.sin (Real.pi*s/6)*b)^2-3)^2 *
    (1-2*(Real.cos (Real.pi*s/6)*(1/2)+Real.sin (Real.pi*s/6)*b))^2
  convert polynomial_reduce (Real.cos (Real.pi*s/6)) (Real.sin (Real.pi*s/6))
    (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)]) using 1 <;> first | (with_reducible_and_instances rfl) | ring

end SharpPlanar

namespace SharpPlanar

lemma phase_nat (j : ℕ) (s : ℝ) :
    Complex.exp (Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s) =
      ((Real.cos (Real.pi*s/6) : ℂ) + Real.sin (Real.pi*s/6)*Complex.I)^j := by
  rw [show Complex.I * Real.pi * ((j : ℝ)/6 : ℝ) * s =
      (j : ℂ) * ((Real.pi*s/6 : ℝ) * Complex.I) by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_ofReal_mul_I]

lemma polynomial_fourier_algebra (c d : ℝ) (hcd : c^2+d^2=1) :
    (∏ a ∈ residues, (2-2*(c*cosTable a+d*sinTable a))) =
    (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*((c : ℂ)+(d : ℂ)*Complex.I)^j).re := by
  have hd2 : d^2 = 1-c^2 := by linarith
  have hd3 : d^3 = (1-c^2)*d := by rw [pow_succ, hd2]
  have hd4 : d^4 = (1-c^2)^2 := by rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hd2]
  have hd5 : d^5 = (1-c^2)^2*d := by rw [pow_succ, hd4]
  have hd6 : d^6 = (1-c^2)^3 := by rw [show (6 : ℕ) = 2*3 by norm_num, pow_mul, hd2]
  norm_num [residues, cosTable, sinTable, Finset.sum_Icc_succ_top, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  ring_nf
  simp only [b_sq_g, b_pow_3, hd2, hd3, hd4, hd5, hd6]
  ring


theorem P_fourier (s : ℝ) :
    P s = (Pcoeff 0 + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)).re := by
  simp_rw [phase_nat]
  rw [P_as_table]
  exact polynomial_fourier_algebra _ _ (by nlinarith [Real.sin_sq_add_cos_sq (Real.pi*s/6)])

end SharpPlanar

namespace SharpPlanar

lemma Pmoment_zero (s : ℝ) : Pmoment 0 s = P s := by
  rw [P_fourier]
  simp [Pmoment]

lemma Pmoment_hasDerivAt (ell : ℕ) (s : ℝ) :
    HasDerivAt (Pmoment ell) (Pmoment (ell+1) s) s := by
  have hh (j : ℕ) : HasDerivAt (fun s : ℝ =>
      2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s))
      (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^(ell+1) *
        Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*s)) s := by
    have he := (((hasDerivAt_id (s : ℂ)).const_mul
      (Complex.I*Real.pi*((j : ℝ)/6 : ℝ))).comp_ofReal).cexp.const_mul
        (2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell)
    convert he using 1 <;> first | rfl | (simp only [mul_one, pow_succ, id_eq]; ring)
  have hd := ((hasDerivAt_const s (Pcoeff 0*(0 : ℂ)^ell)).add
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.Icc (1 : ℕ) 6) => hh j)))
  have hdr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hd
  convert hdr using 1 <;> first | rfl | simp [Pmoment]

lemma trig_nat_mod12 (n : ℕ) :
    Real.sin (Real.pi*n/6) = sinTable (n%12) ∧
    Real.cos (Real.pi*n/6) = cosTable (n%12) := by
  have hn : (n : ℝ) = (n%12 : ℕ) + 12*(n/12 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 12).symm
  have ha : Real.pi*n/6 = Real.pi*(n%12 : ℕ)/6 + (n/12 : ℕ)*(2*Real.pi) := by
    conv_lhs => rw [hn]
    ring
  rw [ha, Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  exact trig_table_g (n%12) (by omega)

lemma Pmoment_mod (ell n : ℕ) : Pmoment ell n = Pmoment ell (n%12 : ℕ) := by
  unfold Pmoment
  simp only [phase_nat]
  rw [(trig_nat_mod12 n).1, (trig_nat_mod12 n).2,
    (trig_table_g (n%12) (by omega)).1, (trig_table_g (n%12) (by omega)).2]


lemma phase_node (j n : ℕ) :
    Complex.exp (Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ)) =
      (cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I := by
  rw [show Complex.I*Real.pi*((j : ℝ)/6 : ℝ)*(n : ℝ) =
      ((Real.pi*(j*n : ℕ)/6 : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, (trig_nat_mod12 (j*n)).1, (trig_nat_mod12 (j*n)).2]

lemma Pmoment_node_formula (ell n : ℕ) :
    Pmoment ell n =
      (Pcoeff 0*(0 : ℂ)^ell + ∑ j ∈ Finset.Icc (1 : ℕ) 6,
        2*Pcoeff j*(Complex.I*Real.pi*((j : ℝ)/6 : ℝ))^ell *
          ((cosTable ((j*n)%12) : ℂ) + sinTable ((j*n)%12)*Complex.I)).re := by
  unfold Pmoment
  simp_rw [phase_node]

lemma Pmoment_node_0 :
    Pmoment 0 (0 : ℕ) = 0 ∧ Pmoment 1 (0 : ℕ) = 0 ∧
      Pmoment 2 (0 : ℕ) = 2*Q 0 ∧ Pmoment 3 (0 : ℕ) = 6*Q 0*D 0 := by
  rw [Q_0_g, D_0_g, Pmoment_node_formula 0 0, Pmoment_node_formula 1 0,
    Pmoment_node_formula 2 0, Pmoment_node_formula 3 0]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf

lemma Pmoment_node_1 :
    Pmoment 0 (1 : ℕ) = 0 ∧ Pmoment 1 (1 : ℕ) = 0 ∧
      Pmoment 2 (1 : ℕ) = 2*Q 1 ∧ Pmoment 3 (1 : ℕ) = 6*Q 1*D 1 := by
  rw [Q_1_g, D_1_g, Pmoment_node_formula 0 1, Pmoment_node_formula 1 1,
    Pmoment_node_formula 2 1, Pmoment_node_formula 3 1]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_3 :
    Pmoment 0 (3 : ℕ) = 0 ∧ Pmoment 1 (3 : ℕ) = 0 ∧
      Pmoment 2 (3 : ℕ) = 2*Q 3 ∧ Pmoment 3 (3 : ℕ) = 6*Q 3*D 3 := by
  rw [Q_3_g, D_3_g, Pmoment_node_formula 0 3, Pmoment_node_formula 1 3,
    Pmoment_node_formula 2 3, Pmoment_node_formula 3 3]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_4 :
    Pmoment 0 (4 : ℕ) = 0 ∧ Pmoment 1 (4 : ℕ) = 0 ∧
      Pmoment 2 (4 : ℕ) = 2*Q 4 ∧ Pmoment 3 (4 : ℕ) = 6*Q 4*D 4 := by
  rw [Q_4_g, D_4_g, Pmoment_node_formula 0 4, Pmoment_node_formula 1 4,
    Pmoment_node_formula 2 4, Pmoment_node_formula 3 4]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_7 :
    Pmoment 0 (7 : ℕ) = 0 ∧ Pmoment 1 (7 : ℕ) = 0 ∧
      Pmoment 2 (7 : ℕ) = 2*Q 7 ∧ Pmoment 3 (7 : ℕ) = 6*Q 7*D 7 := by
  rw [Q_7_g, D_7_g, Pmoment_node_formula 0 7, Pmoment_node_formula 1 7,
    Pmoment_node_formula 2 7, Pmoment_node_formula 3 7]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring

lemma Pmoment_node_9 :
    Pmoment 0 (9 : ℕ) = 0 ∧ Pmoment 1 (9 : ℕ) = 0 ∧
      Pmoment 2 (9 : ℕ) = 2*Q 9 ∧ Pmoment 3 (9 : ℕ) = 6*Q 9*D 9 := by
  rw [Q_9_g, D_9_g, Pmoment_node_formula 0 9, Pmoment_node_formula 1 9,
    Pmoment_node_formula 2 9, Pmoment_node_formula 3 9]
  norm_num [Finset.sum_Icc_succ_top, cosTable, sinTable, Pcoeff,
    pow_succ, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  all_goals repeat' constructor
  all_goals try ring_nf
  all_goals simp only [b_sq_g]
  all_goals first | trivial | ring


theorem Pmoment_node_data (n : ℕ) (hn : n%12 ∈ residues) :
    Pmoment 0 n = 0 ∧ Pmoment 1 n = 0 ∧
      Pmoment 2 n = 2*Q n ∧ Pmoment 3 n = 6*Q n*D n := by
  rw [Pmoment_mod 0 n, Pmoment_mod 1 n, Pmoment_mod 2 n, Pmoment_mod 3 n,
    ← Q_mod n, ← D_mod n]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;> rw [hn]
  · exact Pmoment_node_0
  · exact Pmoment_node_1
  · exact Pmoment_node_3
  · exact Pmoment_node_4
  · exact Pmoment_node_7
  · exact Pmoment_node_9

end SharpPlanar

namespace SharpPlanar

lemma foldedU_unfold (n : ℕ) (s : ℝ) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedU
  simp_rw [u_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (-(Real.pi:ℂ)^2*((l:ℂ)/6-t)*
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))) (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedV_unfold (n : ℕ) (s : ℝ) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6, ∫ t in (0 : ℝ)..((l : ℝ)/6),
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n)))).re := by
  unfold foldedV
  simp_rw [v_integrand]
  congr 1
  convert triangular_piece_integrals 6 (fun j => (j : ℝ)/6)
    (fun l t => 2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        (Complex.I*Real.pi*Complex.exp (Complex.I*Real.pi*(t:ℂ)*(s-n))))
      (fun l => by fun_prop) using 1 <;>
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div]

lemma foldedU_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedU n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2)).re := by
  rw [foldedU_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_two (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

lemma foldedV_divided (n : ℕ) (s : ℝ) (hs : s ≠ n) : foldedV n s =
    (∑ l ∈ Finset.Icc (1 : ℕ) 6,
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ))).re := by
  rw [foldedV_unfold]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [intervalIntegral.integral_const_mul]
  congr 1
  have he := exponential_division_one (s-n) (l/6) (sub_ne_zero.mpr hs)
  push_cast at he ⊢
  rw [he, intervalIntegral.integral_const_mul]


lemma exp_phase_split (T s v : ℝ) :
    Complex.exp (Complex.I*Real.pi*T*v)*
      Complex.exp (Complex.I*Real.pi*T*(s-v)) =
        Complex.exp (Complex.I*Real.pi*T*s) := by
  rw [← Complex.exp_add]
  congr 1
  ring

lemma foldedU_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = (P s-P n-Pmoment 1 n*(s-n))/(s-n)^2 := by
  rw [foldedU_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1-
          Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))/(s-n : ℝ)^2) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)-
        (2*Pcoeff l*(Complex.I*Real.pi*((l:ℝ)/6:ℝ))*
          Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))*(s-n : ℝ))/(s-n : ℝ)^2 := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)-
          (2*Pcoeff l*(Complex.I*Real.pi*(l/6 : ℝ))*
            Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n))*(s-n : ℝ) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div]
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [P_fourier s, P_fourier n]
  simp [Pmoment, Complex.mul_re]

lemma foldedV_quotient (n : ℕ) (s : ℝ) (hs : s ≠ n) :
    foldedV n s = (P s-P n)/(s-n) := by
  rw [foldedV_divided n s hs]
  have ht (l : ℕ) :
      2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n)*
        ((Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*(s-n))-1)/(s-n : ℝ)) =
      (2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*s)-
        2*Pcoeff l*Complex.exp (Complex.I*Real.pi*((l:ℝ)/6:ℝ)*n))/(s-n : ℝ) := by
    rw [← mul_div_assoc]
    congr 1
    have he := exp_phase_split ((l:ℝ)/6) s n
    push_cast at he ⊢
    calc
      _ = 2*Pcoeff l*(Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n)*
          Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*(s-n)))-
          2*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l/6 : ℝ)*n) := by push_cast <;> ring
      _ = _ := by push_cast; rw [he]
  simp_rw [ht]
  rw [← Finset.sum_div, Complex.div_ofReal_re]
  congr 1
  rw [Finset.sum_sub_distrib, P_fourier s, P_fourier n]
  simp [Complex.mul_re]

lemma folded_basis_quotients (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) (hs : s ≠ n) :
    foldedU n s = P s/(s-n)^2 ∧ foldedV n s = P s/(s-n) := by
  obtain ⟨h0,h1,-,-⟩ := Pmoment_node_data n hn
  rw [Pmoment_zero] at h0
  rw [foldedU_quotient n s hs, foldedV_quotient n s hs, h0, h1]
  simp

end SharpPlanar



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

lemma integrable_moment_Icc {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Icc a b)) (n : ℕ) :
    Integrable (fun t => ‖t‖^n * ‖f t‖) (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn (fun t : ℝ => ‖t‖^n) (Icc a b) := by fun_prop
  exact IntegrableOn.continuousOn_mul hc hf.norm isCompact_Icc

end SharpPlanar

namespace SharpPlanar

lemma spectral_integrable {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (s : ℝ) :
    Integrable (fun t => Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I)*f t) μ := by
  refine (hf.norm).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ =>
        Complex.exp (((Real.pi*t*s : ℝ):ℂ)*Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards with t
    simp [Complex.norm_exp]

lemma spectral_hasDerivAt {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) (hm : Integrable (fun t => ‖t‖*‖f t‖) μ) (s : ℝ) :
    HasDerivAt (spectral μ f)
      (spectral μ (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) s) s := by
  have hf' : Integrable (fun t => ((Real.pi*t : ℝ):ℂ)*Complex.I*f t) μ := by
    refine (hm.const_mul Real.pi).mono' ?_ ?_
    · exact (((by fun_prop : Continuous (fun t : ℝ =>
          ((Real.pi*t : ℝ):ℂ)*Complex.I))).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · filter_upwards with t
      simp [abs_of_pos Real.pi_pos, mul_assoc]
  have he (t x : ℝ) : HasDerivAt (fun x : ℝ =>
      Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
      (Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
        (((Real.pi*t : ℝ):ℂ)*Complex.I*f t)) x := by
    convert ((((hasDerivAt_id x).const_mul (Real.pi*t)).ofReal_comp.mul_const
      Complex.I).cexp.mul_const (f t)) using 1 <;> first | rfl | (simp only [mul_one, id_eq]; ring)
  have hr := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun t => Real.pi*(‖t‖*‖f t‖))
    (F := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*f t)
    (F' := fun x t => Complex.exp (((Real.pi*t*x : ℝ):ℂ)*Complex.I)*
      (((Real.pi*t : ℝ):ℂ)*Complex.I*f t))
    (Filter.univ_mem) (Filter.Eventually.of_forall fun x => (spectral_integrable hf x).aestronglyMeasurable)
    (spectral_integrable hf s) (spectral_integrable hf' s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t x _ => by
      simp [Complex.norm_exp, abs_of_pos Real.pi_pos, mul_assoc])
    (hm.const_mul Real.pi) (Filter.Eventually.of_forall fun t x _ => he t x)
  exact hr.2

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma interval_spectral_eq (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) (s : ℝ) :
    (∫ t in a..b, f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f s := by
  unfold spectral
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [mul_comm (f t)]
  congr 1
  congr 1
  push_cast
  ring

lemma interval_exponential_hasDerivAt {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in a..b,
      f t * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in a..b, f t * (Complex.I*Real.pi*(t:ℂ)) *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
  have hfi : IntegrableOn f (Icc a b) volume := hf.integrableOn_Icc
  have hder := spectral_hasDerivAt hfi (by
    simpa only [pow_one] using integrable_moment_Icc hfi 1) s
  have hfun : (fun s : ℝ => ∫ t in a..b, f t*Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) =
      spectral (volume.restrict (Icc a b)) f :=
    funext (interval_spectral_eq f hab)
  rw [hfun]
  convert hder using 1
  all_goals try with_reducible_and_instances rfl
  rw [interval_spectral_eq _ hab]
  congr 1
  funext t
  push_cast
  ring

lemma basisMoment_zero (sec : Bool) (n : ℕ) : basisMoment sec n 0 =
    if sec then foldedV n else foldedU n := by
  cases sec <;> funext s <;> simp [basisMoment,foldedU,foldedV]

lemma basisMoment_hasDerivAt (sec : Bool) (n ell : ℕ) (s : ℝ) :
    HasDerivAt (basisMoment sec n ell) (basisMoment sec n (ell+1) s) s := by
  have hd (j : ℕ) : HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^(ell+1) *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)) s := by
    convert interval_exponential_hasDerivAt (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
      (f:=fun t => (if sec then v n j t else u n j t)*(Complex.I*Real.pi*(t:ℂ))^ell)
      (by cases sec <;> apply Continuous.continuousOn <;>
        apply Continuous.mul <;> first | exact continuous_u n j | exact continuous_v n j | fun_prop) s using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext t
    rw [pow_succ]
    ring
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.range 6) => hd j))

lemma basisU_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)^2*basisMoment false n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [Bool.false_eq_true,ite_false, if_false]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).1]
    field_simp

lemma basisV_factor (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    (s-n)*basisMoment true n 0 s = P s := by
  have hz := (Pmoment_node_data n hn).1
  rw [Pmoment_zero] at hz
  rw [basisMoment_zero]
  simp only [ite_true, if_true]
  by_cases hs : s = n
  · simp [hs,hz]
  · rw [(folded_basis_quotients n hn s hs).2]
    field_simp


lemma P_hasDerivAt (s : ℝ) : HasDerivAt P (Pmoment 1 s) s := by
  simpa only [show Pmoment 0 = P from funext Pmoment_zero] using Pmoment_hasDerivAt 0 s

lemma basisU_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*(s-n)*basisMoment false n 0 s + (s-n)^2*basisMoment false n 1 s = Pmoment 1 s := by
  have hd := (((hasDerivAt_id s).sub_const (n:ℝ)).pow 2).mul
    (basisMoment_hasDerivAt false n 0 s)
  have heq : (fun s : ℝ => (s-n)^2*basisMoment false n 0 s) = P :=
    funext (basisU_factor n hn)
  simp only [Pi.mul_def, Pi.pow_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisU_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment false n 0 s + 4*(s-n)*basisMoment false n 1 s +
      (s-n)^2*basisMoment false n 2 s = Pmoment 2 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := ((hl.const_mul 2).mul (basisMoment_hasDerivAt false n 0 s)).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 1 s))
  have heq : (fun s : ℝ => 2*(s-n)*basisMoment false n 0 s +
      (s-n)^2*basisMoment false n 1 s) = Pmoment 1 := funext (basisU_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisU_factor_deriv3 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    6*basisMoment false n 1 s + 6*(s-n)*basisMoment false n 2 s +
      (s-n)^2*basisMoment false n 3 s = Pmoment 3 s := by
  have hl := (hasDerivAt_id s).sub_const (n:ℝ)
  have hd := (((basisMoment_hasDerivAt false n 0 s).const_mul 2).add
    ((hl.const_mul 4).mul (basisMoment_hasDerivAt false n 1 s))).add
    ((hl.pow 2).mul (basisMoment_hasDerivAt false n 2 s))
  have heq : (fun s : ℝ => 2*basisMoment false n 0 s +
      4*(s-n)*basisMoment false n 1 s+(s-n)^2*basisMoment false n 2 s) = Pmoment 2 :=
    funext (basisU_factor_deriv2 n hn)
  simp only [Pi.mul_def, Pi.pow_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 2 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)

lemma basisV_factor_deriv1 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    basisMoment true n 0 s + (s-n)*basisMoment true n 1 s = Pmoment 1 s := by
  have hd := ((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 0 s)
  have heq : (fun s : ℝ => (s-n)*basisMoment true n 0 s) = P :=
    funext (basisV_factor n hn)
  simp only [Pi.mul_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (P_hasDerivAt s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp)

lemma basisV_factor_deriv2 (n : ℕ) (hn : n%12 ∈ residues) (s : ℝ) :
    2*basisMoment true n 1 s + (s-n)*basisMoment true n 2 s = Pmoment 2 s := by
  have hd := (basisMoment_hasDerivAt true n 0 s).add
    (((hasDerivAt_id s).sub_const (n:ℝ)).mul (basisMoment_hasDerivAt true n 1 s))
  have heq : (fun s : ℝ => basisMoment true n 0 s +
      (s-n)*basisMoment true n 1 s) = Pmoment 1 := funext (basisV_factor_deriv1 n hn)
  simp only [Pi.mul_def, Pi.add_def, id_eq] at hd
  rw [heq] at hd
  convert hd.unique (Pmoment_hasDerivAt 1 s) using 1 <;> first | (with_reducible_and_instances rfl) | (simp <;> ring)


theorem basis_diagonal_jets (n : ℕ) (hn : n%12 ∈ residues) :
    basisMoment false n 0 n = Q n ∧ basisMoment false n 1 n = Q n*D n ∧
    basisMoment true n 0 n = 0 ∧ basisMoment true n 1 n = Q n := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data n hn
  have hu0 := basisU_factor_deriv2 n hn n
  have hu1 := basisU_factor_deriv3 n hn n
  have hv0 := basisV_factor_deriv1 n hn n
  have hv1 := basisV_factor_deriv2 n hn n
  simp only [sub_self,zero_mul,zero_pow (by omega : 2 ≠ 0),add_zero] at hu0 hu1 hv0 hv1
  rw [h1] at hv0
  exact ⟨by linarith,by linarith,hv0,by linarith⟩


theorem basis_off_diagonal_jets (n m : ℕ) (hn : n%12 ∈ residues)
    (hm : m%12 ∈ residues) (hnm : m ≠ n) :
    basisMoment false n 0 m = 0 ∧ basisMoment false n 1 m = 0 ∧
    basisMoment true n 0 m = 0 ∧ basisMoment true n 1 m = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := Pmoment_node_data m hm
  rw [Pmoment_zero] at h0
  have hsub : (m:ℝ)-(n:ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hu0 := basisU_factor n hn m
  have hv0 := basisV_factor n hn m
  rw [h0] at hu0 hv0
  have hu : basisMoment false n 0 m = 0 := (mul_eq_zero.mp hu0).resolve_left (pow_ne_zero 2 hsub)
  have hv : basisMoment true n 0 m = 0 := (mul_eq_zero.mp hv0).resolve_left hsub
  have hu1 := basisU_factor_deriv1 n hn m
  have hv1 := basisV_factor_deriv1 n hn m
  rw [hu,h1,mul_zero,zero_add] at hu1
  rw [hv,h1,zero_add] at hv1
  exact ⟨hu,(mul_eq_zero.mp hu1).resolve_left (pow_ne_zero 2 hsub),
    hv,(mul_eq_zero.mp hv1).resolve_left hsub⟩

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma basisMoment_bound (sec : Bool) (n ell : ℕ) (s : ℝ) :
    |basisMoment sec n ell s| ≤ densityBound * Real.pi^ell := by
  have hj (j : ℕ) (hj : j < 6) :
      ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ ≤ densityBound*Real.pi^ell/6 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun t => (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
        Complex.exp (Complex.I*Real.pi*(t:ℂ)*s))
      (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6) (C:=densityBound*Real.pi^ell) (fun t ht => ?_)
    · convert hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
      ring
    · rw [mul_assoc,norm_mul]
      apply mul_le_mul _ (realSpectral_norm_g ell (piece_interval_g hj (uIoc_subset_uIcc ht)) s)
        (norm_nonneg _) densityBound_nonneg
      cases sec
      · exact u_bound_g n j (piece_interval_g hj (uIoc_subset_uIcc ht))
      · exact v_bound' n j (piece_interval_g hj (uIoc_subset_uIcc ht))
  unfold basisMoment
  calc
    _ ≤ ‖∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j ∈ Finset.range 6, ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        (if sec then v n j t else u n j t) * (Complex.I*Real.pi*(t:ℂ))^ell *
          Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range 6, densityBound*Real.pi^ell/6 := by
      exact Finset.sum_le_sum (fun j hj' => hj j (Finset.mem_range.mp hj'))
    _ = _ := by simp <;> ring

lemma cardinalSeries_summand_bound (p : CardinalData) (ell : ℕ) (s : ℝ) (n : Node) :
    ‖p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s‖ ≤
      (densityBound*Real.pi^ell)*(|p.x (n,false)|+|p.x (n,true)|) := by
  calc
    _ ≤ ‖p.x (n,false)*basisMoment false n.val ell s‖ +
        ‖p.x (n,true)*basisMoment true n.val ell s‖ := norm_add_le _ _
    _ = |p.x (n,false)| * |basisMoment false n.val ell s| +
        |p.x (n,true)| * |basisMoment true n.val ell s| := by simp [norm_mul,Real.norm_eq_abs]
    _ ≤ |p.x (n,false)| * (densityBound*Real.pi^ell)+
        |p.x (n,true)| * (densityBound*Real.pi^ell) := by
      gcongr <;> apply basisMoment_bound
    _ = _ := by ring

lemma cardinalSeries_summable (p : CardinalData) (ell : ℕ) (s : ℝ) :
    Summable (fun n : Node => p.x (n,false)*basisMoment false n.val ell s +
      p.x (n,true)*basisMoment true n.val ell s) :=
  ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^ell)).of_norm_bounded
    (cardinalSeries_summand_bound p ell s)

lemma cardinalSeries_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (cardinalSeries p ell) (cardinalSeries p (ell+1) s) s := by
  have hsum := hasDerivAt_tsum
    ((X_summable_pairs_g p.x).mul_left (densityBound*Real.pi^(ell+1)))
    (fun n y => ((basisMoment_hasDerivAt false n.val ell y).const_mul (p.x (n,false))).add
      ((basisMoment_hasDerivAt true n.val ell y).const_mul (p.x (n,true))))
    (fun n y => cardinalSeries_summand_bound p (ell+1) y n)
    (cardinalSeries_summable p ell 0) s
  exact ((((Pmoment_hasDerivAt ell s).const_mul p.C).add
    ((basisMoment_hasDerivAt false 0 ell s).const_mul p.c₀)).add
    ((basisMoment_hasDerivAt true 0 ell s).const_mul p.d₀)).add hsum


lemma cardinalSeries_jets (p : CardinalData) (m : Node) :
    cardinalSeries p 0 m.val = Q m.val * p.x (m,false) ∧
    cardinalSeries p 1 m.val = Q m.val * (D m.val*p.x (m,false)+p.x (m,true)) := by
  obtain ⟨hP0,hP1,-,-⟩ := Pmoment_node_data m.val m.property.2
  obtain ⟨hU0,hU1,hV0,hV1⟩ := basis_diagonal_jets m.val m.property.2
  have hm : m.val ≠ 0 := Nat.ne_of_gt m.property.1
  have hz : 0%12 ∈ residues := by norm_num [residues]
  obtain ⟨hc0,hc1,hd0,hd1⟩ := basis_off_diagonal_jets 0 m.val hz m.property.2 hm
  have hother (n : Node) (hn : n ≠ m) :
      basisMoment false n.val 0 m.val = 0 ∧ basisMoment false n.val 1 m.val = 0 ∧
      basisMoment true n.val 0 m.val = 0 ∧ basisMoment true n.val 1 m.val = 0 := by
    apply basis_off_diagonal_jets n.val m.val n.property.2 m.property.2
    intro he
    exact hn (Subtype.ext he.symm)
  have hs0 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 0 m.val +
      p.x (n,true)*basisMoment true n.val 0 m.val)) = p.x (m,false)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU0,hV0]; ring
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h0,h2]
  have hs1 : (∑' n : Node, (p.x (n,false)*basisMoment false n.val 1 m.val +
      p.x (n,true)*basisMoment true n.val 1 m.val)) =
      p.x (m,false)*(Q m.val*D m.val)+p.x (m,true)*Q m.val := by
    rw [tsum_eq_single m]
    · rw [hU1,hV1]
    · intro n hn
      obtain ⟨h0,h1,h2,h3⟩ := hother n hn
      simp [h1,h3]
  constructor
  · simp only [cardinalSeries,hP0,hc0,hd0,hs0,mul_zero,zero_add]
    ring
  · simp only [cardinalSeries,hP1,hc1,hd1,hs1,mul_zero,zero_add]
    ring

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

namespace SharpPlanar

lemma spectral_dirac_eq (t : ℝ) (c : ℂ) (s : ℝ) :
    spectral (Measure.dirac t) (fun _ => c) s =
      Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * c := by
  simp [spectral]

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma spectral_interval_direct (p : CardinalData) (j : ℕ) (s : ℝ) :
    spectral (volume.restrict (Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j) s =
    ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel 0 s t := by
  rw [spectral,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
    (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [directKernel,pow_zero,one_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

lemma cardinal_eq_cardinalSeries (p : CardinalData) (s : ℝ) :
    cardinal p s = cardinalSeries p 0 s := by
  unfold cardinal
  simp_rw [spectral_dirac_eq,spectral_interval_direct]
  have hat : (Complex.exp (((Real.pi*0*s:ℝ):ℂ)*Complex.I)*((p.C:ℂ)*Pcoeff 0) +
      ∑ j ∈ Finset.Icc (1:ℕ) 6,
        Complex.exp (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I)*(2*(p.C:ℂ)*Pcoeff j)) =
      (p.C:ℂ)*(Pcoeff 0 + ∑ j ∈ Finset.Icc (1:ℕ) 6,
        2*Pcoeff j*Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*s)) := by
    simp only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have he : (((Real.pi*((j:ℝ)/6)*s:ℝ):ℂ)*Complex.I) =
        Complex.I*Real.pi*((j:ℝ)/6)*s := by push_cast <;> ring
    rw [he]
    ring
  rw [hat,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series_g]
  simp only [cardinalSeries,Pmoment,pow_zero,mul_one]
  push_cast
  ring

lemma cardinal_hasDerivAt (p : CardinalData) (s : ℝ) :
    HasDerivAt (cardinal p) (cardinalSeries p 1 s) s := by
  simpa only [funext (cardinal_eq_cardinalSeries p)] using cardinalSeries_hasDerivAt p 0 s

lemma cardinal_jets (p : CardinalData) (m : Node) :
    cardinal p m.val = Q m.val*p.x (m,false) ∧
      deriv (cardinal p) m.val = Q m.val*(p.x (m,true)+D m.val*p.x (m,false)) := by
  rcases cardinalSeries_jets p m with ⟨h0,h1⟩
  rw [cardinal_eq_cardinalSeries,h0,(cardinal_hasDerivAt p m.val).deriv]
  exact ⟨rfl,by simpa only [add_comm] using h1⟩

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BarrierEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Set
lemma P_period (s : ℝ) : P (s+12) = P s := by
  simp only [P_cos_factor, show Real.pi*(s+12-2)/6 = Real.pi*(s-2)/6 + 2*Real.pi by ring,
    Real.cos_add_two_pi]
lemma P_reflect (s : ℝ) : P (4-s) = P s := by
  simp only [P_cos_factor, show Real.pi*(4-s-2)/6 = -(Real.pi*(s-2)/6) by ring,
    Real.cos_neg]
lemma P_half : P (1/2) = 3-2*Real.sqrt 2 := by
  rw [P_cos_factor,show Real.pi*((1/2:ℝ)-2)/6 = -(Real.pi/4) by ring,
    Real.cos_neg,Real.cos_pi_div_four]
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have he : 4*(Real.sqrt 2/2)^2-3 = (-1:ℝ) := by nlinarith
  rw [he]
  nlinarith
lemma P_two : P 2 = 1 := by norm_num [P_cos_factor]
lemma P_eight : P 8 = 9 := by
  rw [P_cos_factor,show Real.pi*((8:ℝ)-2)/6 = Real.pi by ring,Real.cos_pi]
  norm_num
lemma P_short_lower : (17/100:ℝ) < P (1/2) := by
  rw [P_half]
  have hh := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hb : Real.sqrt 2 < 283/200 := by nlinarith
  linarith
lemma P_long_lower : (4:ℝ) ≤ P (11/2) := by
  rw [P_cos_factor]
  have ha : Real.pi*((11/2:ℝ)-2)/6 = 7*Real.pi/12 := by ring
  rw [ha]
  have hc1 : Real.cos (7*Real.pi/12) ≤ 0 := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi/2)
      (by linarith [Real.pi_pos] : 7*Real.pi/12 ≤ Real.pi)
      (by linarith [Real.pi_pos] : Real.pi/2 ≤ 7*Real.pi/12)
    simpa using hh
  have hc2 : -(1/2:ℝ) ≤ Real.cos (7*Real.pi/12) := by
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ 7*Real.pi/12)
      (by linarith [Real.pi_pos] : 2*Real.pi/3 ≤ Real.pi)
      (by linarith [Real.pi_pos] : 7*Real.pi/12 ≤ 2*Real.pi/3)
    have he : Real.cos (2*Real.pi/3) = -(1/2:ℝ) := by
      rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring,Real.cos_pi_sub,Real.cos_pi_div_three]
    rwa [he] at hh
  have hsq : Real.cos (7*Real.pi/12)^2 ≤ 1/4 := by nlinarith
  have h1 : (4*Real.cos (7*Real.pi/12)^2-3)^2 ≥ 4 := by nlinarith [sq_nonneg (Real.cos (7*Real.pi/12))]
  have h2 : (1-2*Real.cos (7*Real.pi/12))^2 ≥ 1 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
lemma P_other_midpoints : P (7/2) = P (1/2) ∧ P (21/2) = P (11/2) ∧ P (-3/2) = P (11/2) := by
  constructor
  · convert P_reflect (1/2) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; norm_num)
  constructor
  · have hp := P_period (-(3/2))
    have hr := P_reflect (11/2)
    norm_num at hp hr
    exact hp.trans hr
  · convert P_reflect (11/2) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; norm_num)

lemma barrier_endpoints (a : ℕ) (ha : a ∈ residues) :
    (17/25:ℝ) ≤ dividedP a (-leftHalf a) ∧ (17/25:ℝ) ≤ dividedP a (rightHalf a) := by
  have hl := dividedP_factor a ha (-leftHalf a)
  have hr := dividedP_factor a ha (rightHalf a)
  have hs := P_short_lower
  have ht := P_two
  have he := P_eight
  have hg := P_long_lower
  have hm := P_other_midpoints
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [leftHalf,rightHalf] at hl hr ⊢ <;>
    norm_num at hm <;> constructor <;> nlinarith [hm.1,hm.2.1,hm.2.2]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Barrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Set
lemma dividedP_lower (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : (17/25:ℝ) ≤ dividedP a u := by
  have hpos := half_pos a ha
  have hend := barrier_endpoints a ha
  have hcenter : (17/25:ℝ) ≤ dividedP a 0 := by
    rw [dividedP_zero a (residue_lt ha)]
    have hh := Q_lower a (by simpa only [Nat.mod_eq_of_lt (residue_lt ha)] using ha)
    linarith
  by_cases hu0 : u ≤ 0
  · have hab : -leftHalf a ≤ (0:ℝ) := by linarith
    have hsub : Icc (-leftHalf a) 0 ⊆ Icc (-leftHalf a) (rightHalf a) := by
      intro v hv
      exact ⟨hv.1, le_trans hv.2 hpos.2.le⟩
    have hc := dividedP_log_concave a ha (convex_Icc _ _) hsub (by simp [interior_Icc])
    apply lower_of_log_concave (v := -leftHalf a) (w := 0) (by norm_num)
    · simpa only [uIcc_of_le hab] using fun v hv => dividedP_pos a ha (hsub hv)
    · simpa only [uIcc_of_le hab] using hc
    · exact hend.1
    · exact hcenter
    · simpa only [uIcc_of_le hab] using show u ∈ Icc (-leftHalf a) 0 from ⟨hu.1,hu0⟩
  · have hab : (0:ℝ) ≤ rightHalf a := hpos.2.le
    have hsub : Icc 0 (rightHalf a) ⊆ Icc (-leftHalf a) (rightHalf a) := by
      intro v hv
      exact ⟨le_trans (by linarith) hv.1,hv.2⟩
    have hc := dividedP_log_concave a ha (convex_Icc _ _) hsub (by simp [interior_Icc])
    apply lower_of_log_concave (v := 0) (w := rightHalf a) (by norm_num)
    · simpa only [uIcc_of_le hab] using fun v hv => dividedP_pos a ha (hsub hv)
    · simpa only [uIcc_of_le hab] using hc
    · exact hcenter
    · exact hend.2
    · simpa only [uIcc_of_le hab] using show u ∈ Icc 0 (rightHalf a) from ⟨by linarith,hu.2⟩


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_KernelDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped Topology
lemma kernelMoment_hasDerivAt (ell : ℕ) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => kernelMoment ell s t) (kernelMoment (ell+1) s t) s := by
  have hd := ((((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I*Real.pi*z t)).cexp).const_mul
    (lambda t*(Complex.I*Real.pi*z t)^ell))
  simpa only [kernelMoment,pow_succ,Complex.ofReal_one,id_eq,mul_one,one_mul,mul_assoc,
    mul_left_comm,mul_comm] using hd
lemma continuous_joint_kernel (ell : ℕ) :
    Continuous (fun st : ℝ×ℝ => kernelMoment ell st.1 st.2) := by
  unfold kernelMoment
  exact ((continuous_lambda.comp continuous_snd).mul
    ((continuous_const.mul (continuous_z.comp continuous_snd)).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul (continuous_z.comp continuous_snd)).mul
      (Complex.continuous_ofReal.comp continuous_fst)))
lemma piece_hasDerivAt (p : CardinalData) (ell j : ℕ) (hj : j<6) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * kernelMoment ell s t)
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * kernelMoment (ell+1) s t) s := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (show ContinuousOn (fun st : ℝ×ℝ => kernelMoment (ell+1) st.1 st.2)
      (Set.Icc (s-1) (s+1) ×ˢ Set.Icc (0:ℝ) 1) from (continuous_joint_kernel _).continuousOn)
  have hr := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => density p j t * kernelMoment ell s t)
    (F' := fun s t => density p j t * kernelMoment (ell+1) s t)
    (s := Set.Icc (s-1) (s+1))
    (bound := fun _ => densityBound*(|p.c₀|+|p.d₀|+‖p.x‖)*max C 0)
    (Icc_mem_nhds (by linarith : s-1 < s) (by linarith : s < s+1))
    (Filter.Eventually.of_forall fun x => (intervalIntegrable_iff.mp (piece_integrable p ell j hj x)).aestronglyMeasurable)
    (piece_integrable p ell j hj s)
    (intervalIntegrable_iff.mp (piece_integrable p (ell+1) j hj s)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => by
      rw [norm_mul]
      exact mul_le_mul (density_bound p j (piece_interval_g hj (Set.uIoc_subset_uIcc ht)))
        ((hC (x,t) ⟨hx,piece_interval_g hj (Set.uIoc_subset_uIcc ht)⟩).trans (le_max_left _ _))
        (norm_nonneg _) (by have := densityBound_nonneg; positivity))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ x _ => (kernelMoment_hasDerivAt ell t x).const_mul _)
  exact hr.2
lemma K_hasDerivAt (p : CardinalData) (ell : ℕ) (s : ℝ) :
    HasDerivAt (K p ell) (K p (ell+1) s) s := by
  have ha := ((kernelMoment_hasDerivAt ell 0 s).const_mul (Pcoeff 0)).add
    (HasDerivAt.fun_sum (u := Finset.Icc (1:ℕ) 6) fun j _ =>
      (kernelMoment_hasDerivAt ell ((j:ℝ)/6) s).const_mul (2*Pcoeff j))
  have hi := HasDerivAt.fun_sum (u := Finset.range 6) fun j hj =>
    piece_hasDerivAt p ell j (Finset.mem_range.mp hj) s
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s ((ha.const_mul (p.C:ℂ)).add hi)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_DataSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed and summable parts of cardinal data

Splitting cardinal data separates the fixed coefficients from the absolutely summable interpolation unknowns.
-/

namespace SharpPlanar
open MeasureTheory
lemma density_split (p : CardinalData) (j : ℕ) (t : ℝ) :
    density p j t = density (fixedPart p) j t+density (positiveData p.x) j t := by
  simp only [density,fixedPart,positiveData,lp.coeFn_zero,Pi.zero_apply,
    Complex.ofReal_zero,zero_mul,zero_add,tsum_zero,add_zero]
lemma K_split (p : CardinalData) (ell : ℕ) (s : ℝ) :
    K p ell s = K (fixedPart p) ell s+K (positiveData p.x) ell s := by
  have hp (j : ℕ) (hj : j<6) :
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t*kernelMoment ell s t) =
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (fixedPart p) j t*kernelMoment ell s t)+
      (∫t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t*kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_split,add_mul]
  unfold K
  simp only [fixedPart,positiveData,Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Complex.add_re,add_assoc,← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)
lemma K_fixed₁ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₁ x) ell s=K (fixed₁ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma K_fixed₂ (x : X) (ell : ℕ) (s : ℝ) :
    K (fixed₂ x) ell s=K (fixed₂ 0) ell s+K (positiveData x) ell s := K_split _ _ _
lemma transformedJets_fixed₁ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₁ x) ni=transformedJets (fixed₁ 0) ni + S x ni := by
  change _=transformedJets (fixed₁ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₁ x 0 _,K_fixed₁ x 1 _]; ring
  · rw [K_fixed₁ x 0 _]; ring
lemma transformedJets_fixed₂ (x : X) (ni : Node×Bool) :
    transformedJets (fixed₂ x) ni=transformedJets (fixed₂ 0) ni + S x ni := by
  change _=transformedJets (fixed₂ 0) ni+Scoords x ni
  simp only [transformedJets,Scoords]
  split
  · rw [K_fixed₂ x 0 _,K_fixed₂ x 1 _]; ring
  · rw [K_fixed₂ x 0 _]; ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoupledFull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coupled interpolation system

The finite inverse and tail estimates solve the interpolation equations in the space of absolutely summable coefficients.
-/

namespace SharpPlanar
open Numerical

lemma interpolationInverse_eq (neg : Bool) (r : X) :
    interpolationInverse neg r - signedS neg (interpolationInverse neg r) = r :=
  (Classical.choose_spec (interpolation_exists_unique_g neg r)).1
lemma coupled_equations (g₁ g₂ : X) :
    coupledLeft g₁ g₂-S (coupledRight g₁ g₂)=g₁ ∧
    coupledRight g₁ g₂-S (coupledLeft g₁ g₂)=g₂ := by
  have hp := interpolationInverse_eq false (g₁+g₂)
  have hm := interpolationInverse_eq true (g₁-g₂)
  change interpolationInverse false (g₁+g₂)-S (interpolationInverse false (g₁+g₂))=g₁+g₂ at hp
  change interpolationInverse true (g₁-g₂)- -S (interpolationInverse true (g₁-g₂))=g₁-g₂ at hm
  constructor <;> (apply lp.ext; funext ni)
  all_goals
    have hp' := congrArg (fun x : X => x ni) hp
    have hm' := congrArg (fun x : X => x ni) hm
    simp only [coupledLeft,coupledRight,map_smul,map_add,map_sub,lp.coeFn_sub,lp.coeFn_add,
      lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,lp.coeFn_neg,Pi.neg_apply] at *
    linarith
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FixedRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The exact contact interpolation solution

The inverse interpolation operator determines the coefficient lists for the prescribed contacts.
-/

namespace SharpPlanar
lemma exactLists_equations : exactList₁-S exactList₂=g₁ ∧ exactList₂-S exactList₁=g₂ :=
  coupled_equations g₁ g₂
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_ExactJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
lemma H₁_hasDerivAt (s : ℝ) :
    HasDerivAt H₁ (cardinalSeries exactData₁ 1 s+K exactData₂ 1 s) s :=
  (cardinal_hasDerivAt exactData₁ s).add (K_hasDerivAt exactData₂ 0 s)
lemma H₂_hasDerivAt (s : ℝ) :
    HasDerivAt H₂ (cardinalSeries exactData₂ 1 s+K exactData₁ 1 s) s :=
  (cardinal_hasDerivAt exactData₂ s).add (K_hasDerivAt exactData₁ 0 s)
lemma exactLists_coordinate (ni : Node×Bool) :
    exactList₁ ni=transformedJets exactData₂ ni-contactList ni ∧
    exactList₂ ni=transformedJets exactData₁ ni := by
  have h1 := congrArg (fun x : X => x ni) exactLists_equations.1
  have h2 := congrArg (fun x : X => x ni) exactLists_equations.2
  simp only [g₁,g₂,lp.coeFn_sub,Pi.sub_apply] at h1 h2
  change exactList₁ ni-S exactList₂ ni=transformedJets (fixed₂ 0) ni-contactList ni at h1
  change exactList₂ ni-S exactList₁ ni=transformedJets (fixed₁ 0) ni at h2
  simp only [exactData₁,exactData₂]
  rw [transformedJets_fixed₁ exactList₁ ni,transformedJets_fixed₂ exactList₂ ni]
  constructor <;> linarith
lemma contactList_apply (n : Node) (d : Bool) :
    contactList (n,d)=if n.val=1 ∧ d=true then 1 else 0 := by
  classical
  unfold contactList columnVector
  rw [lp.single_apply]
  by_cases hn : n.val=1
  · have he : n=firstNode := Subtype.ext hn
    subst n
    cases d <;> simp [firstNode]
  · have he : n≠firstNode := by intro hh; exact hn (congrArg Subtype.val hh)
    simp [hn,he]
lemma H₁_jets (n : Node) : H₁ n.val=0 ∧ deriv H₁ n.val=if n.val=1 then -Q n.val else 0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).1
  have hd := (exactLists_coordinate (n,true)).1
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,contactList_apply,
    and_false,and_true] at hc hd
  have hv := (cardinal_jets exactData₁ n).1
  have hj := (cardinal_jets exactData₁ n).2
  change cardinal exactData₁ n.val=Q n.val*exactList₁ (n,false) at hv
  change deriv (cardinal exactData₁) n.val=
    Q n.val*(exactList₁ (n,true)+D n.val*exactList₁ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₁ _).deriv] at hj
  constructor
  · unfold H₁; rw [hv,hc]; field_simp <;> ring
  · rw [(H₁_hasDerivAt _).deriv,hj,hc,hd]
    split <;> field_simp <;> ring
lemma H₂_jets (n : Node) : H₂ n.val=0 ∧ deriv H₂ n.val=0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).2
  have hd := (exactLists_coordinate (n,true)).2
  simp only [transformedJets,Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hc hd
  have hv := (cardinal_jets exactData₂ n).1
  have hj := (cardinal_jets exactData₂ n).2
  change cardinal exactData₂ n.val=Q n.val*exactList₂ (n,false) at hv
  change deriv (cardinal exactData₂) n.val=
    Q n.val*(exactList₂ (n,true)+D n.val*exactList₂ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₂ _).deriv] at hj
  constructor
  · unfold H₂; rw [hv,hc]; field_simp <;> ring
  · rw [(H₂_hasDerivAt _).deriv,hj,hc,hd]
    field_simp <;> ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_JetError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma exactData_x (a : Bool) : (exactData a).x=exactList a := by cases a <;> rfl
lemma cardinalSeries_sub {p q : CardinalData}
    (hC : p.C=q.C) (hc : p.c₀=q.c₀) (hd : p.d₀=q.d₀) (ell : ℕ) (s : ℝ) :
    cardinalSeries p ell s-cardinalSeries q ell s=cardinalSeries (positiveData (p.x-q.x)) ell s := by
  have he := (cardinalSeries_summable p ell s).tsum_sub (cardinalSeries_summable q ell s)
  simp only [cardinalSeries,positiveData,hC,hc,hd,zero_mul,zero_add]
  rw [add_sub_add_left_eq_sub]
  rw [← he]
  apply tsum_congr
  intro n
  simp only [lp.coeFn_sub,Pi.sub_apply]
  ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TailCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation coefficients

Truncating a summable coefficient family contracts its norm. The finite rational
table for OpenAI's sharp planar Fourier construction bounds the tails of the
exact coefficients through the coefficient error estimate.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma tailList_apply (x : X) (N : ℕ) (k : Node×Bool) :
    tailList x N k=if N<k.1.val then x k else 0 := rfl
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TaylorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Set
lemma jet_iteratedDeriv {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) (ell : ℕ) :
    iteratedDeriv ell (J 0)=J ell := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    exact (hJ ell s).deriv
lemma jet_contDiff {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) : ContDiff ℝ (⊤ : ℕ∞) (J 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro ell _
  rw [jet_iteratedDeriv hJ]
  exact fun s => (hJ ell s).differentiableAt
lemma jetTaylor_at_zero (J : ℕ → ℝ → ℝ) (n : ℕ) (m : ℝ) : jetTaylor J n m 0=J 0 m := by
  unfold jetTaylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0; simp [zero_pow hb0]
  · simp
lemma jetTaylor_eq_within {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    {m u : ℝ} (hu : u≠0) (n : ℕ) :
    taylorWithinEval (J 0) n (uIcc m (m+u)) m (m+u)=jetTaylor J n m u := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by intro he; apply hu; linarith))
    ((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffAt (left_mem_uIcc),jet_iteratedDeriv hJ]
  simp only [add_sub_cancel_left,smul_eq_mul]
  ring

lemma jetTaylor_error {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (n : ℕ) (m u M : ℝ)
    (hM : ∀ s ∈ uIcc m (m+u), |J (n+1) s| ≤ M) :
    |J 0 (m+u)-jetTaylor J n m u| ≤ M*|u|^(n+1)/((n+1).factorial:ℝ) := by
  by_cases hu : u=0
  · subst u; simp [jetTaylor_at_zero]
  obtain ⟨s,hs,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := J 0) (n := n) (x₀ := m) (x := m+u) (by intro he; apply hu; linarith : m≠m+u)
    (((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : ((n+1):ℕ∞) ≤ ⊤))).contDiffOn)
  rw [jetTaylor_eq_within hJ hu,jet_iteratedDeriv hJ,add_sub_cancel_left] at he
  rw [he,abs_div,abs_mul,abs_pow,abs_of_pos (show 0 < ((n+1).factorial:ℝ) from Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2.le⟩)
    (pow_nonneg (abs_nonneg u) _)) (Nat.cast_nonneg _)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HalfGapCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma exactJet_zero_false (s : ℝ) : exactJet false 0 s=H₁ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_zero_true (s : ℝ) : exactJet true 0 s=H₂ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_one_false (s : ℝ) : exactJet false 1 s=deriv H₁ s := (H₁_hasDerivAt s).deriv.symm
lemma exactJet_one_true (s : ℝ) : exactJet true 1 s=deriv H₂ s := (H₂_hasDerivAt s).deriv.symm
lemma exactJet_node_zero (a : Bool) (n : Node) : exactJet a 0 n.val=0 := by
  cases a
  · rw [exactJet_zero_false]; exact (H₁_jets n).1
  · rw [exactJet_zero_true]; exact (H₂_jets n).1
lemma exactJet_node_first (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true) :
    exactJet a 1 n.val=0 := by
  cases a
  · rw [exactJet_one_false,(H₁_jets n).2,ite_eq_right (by simpa using hn)]
  · rw [exactJet_one_true]; exact (H₂_jets n).2
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma P_local_lower (k a : ℕ) (ha : a∈residues) {s : ℝ}
    (hu : s-(12*(k:ℝ)+a) ∈ Set.Icc (-leftHalf a) (rightHalf a)) :
    (17/25:ℝ)*(s-(12*(k:ℝ)+a))^2 ≤ P s := by
  have hv:=dividedP_lower a ha hu
  have hf:=dividedP_factor a ha (s-(12*(k:ℝ)+a))
  have he : P ((a:ℝ)+(s-(12*(k:ℝ)+a)))=P s := by
    convert (show Function.Periodic P (12:ℝ) from P_period).sub_int_mul_eq (k:ℤ) (x:=s) using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    congr 1
    ring
  rw [he] at hf
  nlinarith [mul_nonneg (sq_nonneg (s-(12*(k:ℝ)+a))) (sub_nonneg.mpr hv)]
lemma tail_node_of_half (s : ℝ) (hs : (83:ℝ)/2 ≤ s) (k a : ℕ) (ha : a∈residues)
    (hu : s-(12*(k:ℝ)+a) ∈ Set.Icc (-leftHalf a) (rightHalf a))
    (hm : s-(12*(k:ℝ)+a) < (3:ℝ)/2) :
    ∃ n : Node,40 < n.val ∧ (83:ℝ)/2 ≤ n.val ∧ (17/25:ℝ)*(s-n.val)^2 ≤ P s := by
  have hv : (40:ℝ) < 12*(k:ℝ)+a := by linarith
  have hn : 40 < 12*k+a := by exact_mod_cast hv
  have hr : (12*k+a)%12∈residues := by
    simpa only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod,zero_add,
      Nat.mod_eq_of_lt (residue_lt ha)] using ha
  let n : Node:=⟨12*k+a,by omega,hr⟩
  have he : (n.val:ℝ)=12*(k:ℝ)+a := by simp [n]
  have hn43 : 43 ≤ n.val := by
    have hh : 40 < n.val := hn
    have hg:=n.prop.2
    by_contra hh'
    have hc : n.val=41 ∨ n.val=42 := by omega
    rcases hc with hc|hc <;> norm_num [hc,residues] at hg
  have hn43' : (43:ℝ) ≤ n.val := by exact_mod_cast hn43
  exact ⟨n,hn,by linarith,by rw [he]; exact P_local_lower k a ha hu⟩
lemma tail_barrier_node {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    ∃ n : Node,40 < n.val ∧ (83:ℝ)/2 ≤ n.val ∧ (17/25:ℝ)*(s-n.val)^2 ≤ P s := by
  let k : ℕ:=⌊s/12⌋₊
  have hk : (k:ℝ) ≤ s/12 := Nat.floor_le (by linarith : (0:ℝ) ≤ s/12)
  have hk' : s/12 < (k:ℝ)+1 := Nat.lt_floor_add_one _
  let r : ℝ:=s-12*(k:ℝ)
  have hr : 0 ≤ r ∧ r < 12 := by dsimp [r]; constructor <;> linarith
  by_cases h0 : r < (1:ℝ)/2
  · apply tail_node_of_half s hs k 0 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  by_cases h1 : r < 2
  · apply tail_node_of_half s hs k 1 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  by_cases h3 : r < (7:ℝ)/2
  · apply tail_node_of_half s hs k 3 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  by_cases h4 : r < (11:ℝ)/2
  · apply tail_node_of_half s hs k 4 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  by_cases h7 : r < 8
  · apply tail_node_of_half s hs k 7 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  by_cases h9 : r < (21:ℝ)/2
  · apply tail_node_of_half s hs k 9 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf]; dsimp [r] at *; constructor <;> linarith
    · dsimp [r] at * <;> norm_num <;> linarith
  · apply tail_node_of_half s hs (k+1) 0 (by norm_num [residues])
    · norm_num [leftHalf,rightHalf,Nat.cast_add]; dsimp [r] at *; constructor <;> linarith
    · norm_num [Nat.cast_add]; dsimp [r] at * <;> linarith
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma tailErrorJet_deriv (a : Bool) (ell : ℕ) (s : ℝ) :
    HasDerivAt (tailErrorJet a ell) (tailErrorJet a (ell+1) s) s :=
  (cardinalSeries_hasDerivAt _ _ _).add (K_hasDerivAt _ _ _)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma headData_zero (a : Bool) (n : Node) (hn : 40<n.val) (d : Bool) :
    (headData a).x (n,d)=0 := by
  simp only [headData,lp.coeFn_sub,Pi.sub_apply,tailList_apply,hn,ite_true, if_true,sub_self]
lemma exactJet_split (a : Bool) (ell : ℕ) (s : ℝ) :
    exactJet a ell s=cardinalSeries (headData a) ell s+tailErrorJet a ell s := by
  have hh := cardinalSeries_sub (p := exactData a) (q := headData a) rfl rfl rfl ell s
  have he:(exactData a).x-(headData a).x=tailList (exactList a) 40 := by
    simp only [headData,exactData_x]; abel
  rw [he] at hh
  change cardinalSeries (exactData a) ell s-cardinalSeries (headData a) ell s=
    cardinalSeries (tailData a) ell s at hh
  unfold exactJet tailErrorJet
  linarith
lemma headData_jets (a : Bool) (n : Node) (hn : 40<n.val) :
    cardinalSeries (headData a) 0 n.val=0 ∧ cardinalSeries (headData a) 1 n.val=0 := by
  have hh:=cardinal_jets (headData a) n
  rw [headData_zero a n hn false,headData_zero a n hn true] at hh
  simp only [mul_zero,add_zero] at hh
  rw [cardinal_eq_cardinalSeries] at hh
  rw [(cardinal_hasDerivAt (headData a) n.val).deriv] at hh
  exact hh
lemma tailErrorJet_node (a : Bool) (n : Node) (hn : 40<n.val) :
    tailErrorJet a 0 n.val=0 ∧ tailErrorJet a 1 n.val=0 := by
  have hv:=exactJet_node_zero a n
  have hd:=exactJet_node_first a n (Or.inl (by omega))
  rw [exactJet_split,(headData_jets a n hn).1,zero_add] at hv
  rw [exactJet_split,(headData_jets a n hn).2,zero_add] at hd
  exact ⟨hv,hd⟩
lemma tailErrorJet_bound (a : Bool) (n : Node) (hn : 40<n.val)
    {s : ℝ} (hs : (83:ℝ)/2 ≤ s) (hm : (83:ℝ)/2 ≤ n.val) :
    |tailErrorJet a 0 s| ≤ (3:ℝ)/1000*(s-n.val)^2 := by
  have hh:=jetTaylor_error (tailErrorJet_deriv a) 1 (n.val:ℝ) (s-n.val) ((6:ℝ)/1000)
    (fun t ht => (tail_second_bound_g a (by
      have hlow: (83:ℝ)/2 ≤ min (n.val:ℝ) (n.val+(s-n.val)) := by
        apply le_min hm; simpa using hs
      exact hlow.trans ht.1)).le)
  simp only [jetTaylor,Finset.sum_range_succ,Finset.sum_range_zero,
    (tailErrorJet_node a n hn).1,(tailErrorJet_node a n hn).2,zero_div,
    zero_mul,zero_add,sub_zero,Nat.reduceAdd,Nat.factorial,Nat.cast_one,
    sq_abs] at hh
  have he : (n.val:ℝ)+(s-n.val)=s := by ring
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma shortNode_inj : Function.Injective shortNode := by decide +kernel
lemma shortNode_le (i : Fin 21) : (shortNode i).val ≤ 40 := by revert i; decide +kernel
lemma shortNode_cover_check : ∀ n : Fin 41,0<n.val ∧ n.val%12∈residues →
    ∃ i : Fin 21,(shortNode i).val=n.val := by decide +kernel
lemma shortNode_range (n : Node) : (∃ i,shortNode i=n) ↔ n.val≤40 := by
  constructor
  · rintro ⟨i,rfl⟩; exact shortNode_le i
  · intro hn
    obtain ⟨i,hi⟩:=shortNode_cover_check ⟨n.val,Nat.lt_succ_of_le hn⟩ n.prop
    exact ⟨i,Subtype.ext hi⟩
lemma headData_low (a : Bool) (n : Node) (hn : n.val≤40) (d : Bool) :
    (headData a).x (n,d)=(exactData a).x (n,d) := by
  simp only [headData,lp.coeFn_sub,Pi.sub_apply,tailList_apply,not_lt.mpr hn,ite_false, if_false,sub_zero]
lemma head_series_finite (a : Bool) (s : ℝ) :
    cardinalSeries (headData a) 0 s =
      (exactData a).C*P s+(exactData a).c₀*basisMoment false 0 0 s+
        (exactData a).d₀*basisMoment true 0 0 s+
        ∑ i : Fin 21,((exactData a).x (shortNode i,false)*basisMoment false (shortNode i).val 0 s+
          (exactData a).x (shortNode i,true)*basisMoment true (shortNode i).val 0 s) := by
  have ht:=shortNode_inj.tsum_eq (f:=fun n => (headData a).x (n,false)*basisMoment false n.val 0 s+
      (headData a).x (n,true)*basisMoment true n.val 0 s) (by
    intro n hn
    apply (shortNode_range n).mpr
    by_contra hh
    have hgt : 40<n.val := by omega
    exact hn (by simp only [headData_zero a n hgt false,headData_zero a n hgt true,zero_mul,add_zero]))
  simp only [tsum_fintype,headData_low a _ (shortNode_le _)] at ht
  simp only [cardinalSeries,Pmoment_zero]
  rw [← ht]
  rfl
lemma head_rational_factor (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    cardinalSeries (headData a) 0 s=P s*headRational (exactData a) s := by
  have he (n : ℕ) (hn : n≤40) (hr : n%12∈residues) (d : Bool) :
      basisMoment d n 0 s=P s/(s-n)^(if d then 1 else 2) := by
    have hns : (n:ℝ)≤40 := by exact_mod_cast hn
    have hne : s-(n:ℝ)≠0 := by linarith
    cases d
    · simp only [Bool.false_eq_true,ite_false, if_false]
      exact (eq_div_iff (pow_ne_zero 2 hne)).mpr (by nlinarith [basisU_factor n hr s])
    · simp only [ite_true, if_true,pow_one]
      exact (eq_div_iff hne).mpr (by nlinarith [basisV_factor n hr s])
  rw [head_series_finite]
  simp only [he 0 (by omega) (by norm_num [residues]),Nat.cast_zero,sub_zero,
    Bool.false_eq_true,ite_false, if_false,ite_true, if_true,pow_one,
    headRational,Fintype.sum_option,headC,headD,headNodeNat,Nat.cast_zero,sub_zero]
  simp_rw [he _ (shortNode_le _) (shortNode _).prop.2 false,
    he _ (shortNode_le _) (shortNode _).prop.2 true]
  simp only [ite_true, if_true,Bool.false_eq_true,ite_false, if_false,pow_one,
    Finset.mul_sum,Finset.sum_add_distrib,mul_add]
  ring_nf
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
lemma exact_sign_tail_g_oai (a : Bool) {s : ℝ} (hs : (83:ℝ)/2 ≤ s) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 s := by
  obtain ⟨n,hn,hm,hP⟩:=tail_barrier_node hs
  have hR:=exact_head_lower_g a hs
  have he:=abs_le.mp (tailErrorJet_bound a n hn hs hm)
  have hp : 0 ≤ P s := (mul_nonneg (by norm_num : (0:ℝ) ≤ 17/25) (sq_nonneg _)).trans hP
  have hh := mul_le_mul_of_nonneg_left hR.le hp
  rw [exactJet_split,head_rational_factor a hs]
  cases a <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true] at hh ⊢ <;>
    nlinarith [sq_nonneg (s-(n.val:ℝ))]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.exact_sign_tail_g_oai := @OAI.SharpPlanar.exact_sign_tail_g_oai
