-- Prove2me | solution 1 for OAI.EuclideanRamsey.exists_radial_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:53:37.075772+00:00
-- url     : https://prove2.me/submissions/71a990de-29a4-434e-89f5-bf4493677dfb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean:L441-L479
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.exists_radial_smoothing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Theorems.Thm_OAI_EuclideanRamsey_radialPower_halfLaplacian

-- ---- from OAI.Combinatorics.EuclideanRamsey.SmoothingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uDomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
namespace EuclideanRamsey

lemma smoothPositivePart_contDiff : ContDiff ℝ (⊤ : ℕ∞) smoothPositivePart :=
  contDiff_id.mul expNegInvGlue.contDiff

lemma smoothPositivePart_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart (smoothPositivePart' t) t := by
  have hg : HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) t
  have h := (hasDerivAt_id t).mul hg
  change HasDerivAt smoothPositivePart _ t at h
  convert h using 1
  unfold smoothPositivePart'
  by_cases ht : t = 0
  · simp [ht]
  · simp only [id_eq]
    field_simp

lemma smoothPositivePart'_hasDerivAt (t : ℝ) :
    HasDerivAt smoothPositivePart' (smoothPositivePart'' t) t := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 + X : ℝ[X]) t
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X] at h
  change HasDerivAt smoothPositivePart' _ t at h
  apply h.congr_deriv
  simp [smoothPositivePart'']
  left
  ring

lemma smoothPositivePart_nonneg (t : ℝ) : 0 ≤ smoothPositivePart t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]
  · exact mul_nonneg (le_of_not_ge ht) (expNegInvGlue.nonneg t)

lemma smoothPositivePart_pos {t : ℝ} (ht : 0 < t) : 0 < smoothPositivePart t :=
  mul_pos ht (expNegInvGlue.pos_of_pos ht)

lemma smoothPositivePart_zero {t : ℝ} (ht : t ≤ 0) : smoothPositivePart t = 0 := by
  simp [smoothPositivePart, expNegInvGlue.zero_of_nonpos ht]

lemma smoothPositivePart'_bounds (t : ℝ) :
    0 ≤ smoothPositivePart' t ∧ smoothPositivePart' t ≤ 1 := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart', expNegInvGlue.zero_of_nonpos ht]
  have ht0 : 0 < t := lt_of_not_ge ht
  constructor
  · exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)
  · unfold smoothPositivePart'
    rw [expNegInvGlue, ite_eq_right ht, show -t⁻¹ = -1 / t by ring,
      show -1 / t = -(t⁻¹) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    simpa [add_comm] using Real.add_one_le_exp (t⁻¹)

lemma smoothPositivePart''_nonneg (t : ℝ) : 0 ≤ smoothPositivePart'' t := by
  by_cases ht : t ≤ 0
  · simp [smoothPositivePart'', expNegInvGlue.zero_of_nonpos ht]
  · have ht0 : 0 < t := lt_of_not_ge ht
    exact mul_nonneg (by positivity) (expNegInvGlue.nonneg _)

section Radial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radialPower_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialPower (E := E) a p) := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne
    (fun x => ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _)))

lemma radialPower_hasFDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    HasFDerivAt (radialPower a p)
      ((2*p*(a+‖x‖^2)^(p-1)) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))))
  change HasFDerivAt (radialPower a p) _ x at h
  apply h.congr_fderiv
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

lemma scalarComposition_hessian {f : E → ℝ} {g g' g'' : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : ∀ t, HasDerivAt g' (g'' t) t) (x v w : E) :
    iteratedFDeriv ℝ 2 (g ∘ f) x ![v,w] =
      g'' (f x) * (fderiv ℝ f x v) * (fderiv ℝ f x w) +
      g' (f x) * iteratedFDeriv ℝ 2 f x ![v,w] := by
  have hf' (y : E) := (hf.differentiable (by simp) y).hasFDerivAt
  have hG : (fun y => fderiv ℝ (g ∘ f) y) =
      (fun y => g' (f y) • fderiv ℝ f y) := by
    funext y
    exact ((hg (f y)).comp_hasFDerivAt y (hf' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hg' (f x)).comp_hasFDerivAt x (hf' x)).smul
    (hfd x).hasFDerivAt
  change HasFDerivAt (fun y => g' (f y) • fderiv ℝ f y) _ x at hd
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  change ((fderiv ℝ (fun y => fderiv ℝ (g ∘ f) y) x) v) w = _
  rw [hG, hd.fderiv]
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,  smul_eq_mul]
  simp only [show Fin.init ![v,w] 0 = v from rfl, show ![v,w] (Fin.last 1) = w from rfl, Function.comp_apply]
  ring

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma radialBump_contDiff {a : ℝ} (ha : 0 < a) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialBump (E := E) a p) :=
  smoothPositivePart_contDiff.comp ((radialPower_contDiff ha p).sub contDiff_const)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialBump_nonneg (a p : ℝ) (x : E) : 0 ≤ radialBump a p x :=
  smoothPositivePart_nonneg _

lemma radialBump_compact {a p : ℝ} (ha : 0 < a) (hp : p < 0) :
    HasCompactSupport (radialBump (E := E) a p) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) 1) ?_
  intro x hx
  apply smoothPositivePart_zero
  have hx1 : 1 < ‖x‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hq : 1 ≤ a+‖x‖^2 := by nlinarith
  exact sub_nonpos.mpr (Real.rpow_le_one_of_one_le_of_nonpos hq hp.le)

lemma radialBump_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialBump a p) x =
      smoothPositivePart' (radialPower a p x-1) * halfLaplacian (radialPower a p) x +
      2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
        ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by
  classical
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => radialPower a p y - 1) :=
    (radialPower_contDiff ha p).sub contDiff_const
  have he (v w : E) :
      iteratedFDeriv ℝ 2 (radialBump a p) x ![v,w] =
        smoothPositivePart'' (radialPower a p x-1) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x v) *
          (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x w) +
        smoothPositivePart' (radialPower a p x-1) *
          iteratedFDeriv ℝ 2 (radialPower a p) x ![v,w] := by
    change iteratedFDeriv ℝ 2 (smoothPositivePart ∘ fun y => radialPower a p y-1) x _ = _
    rw [scalarComposition_hessian hf smoothPositivePart_hasDerivAt smoothPositivePart'_hasDerivAt]
    simp only [fderiv_sub_const, (radialPower_hasFDerivAt ha p x).fderiv,
      _root_.smul_apply, innerSL_apply_apply,  smul_eq_mul]
    congr 1
    congr 1
    rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply,
      iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
    simp only [fderiv_sub_const]
  let e := stdOrthonormalBasis ℝ E
  have hsum : (∑ i, inner ℝ x (e i) * inner ℝ x (e i)) = ‖x‖^2 := by
    simpa only [real_inner_comm (e _), real_inner_self_eq_norm_sq] using
      e.sum_inner_mul_inner x x
  unfold halfLaplacian
  simp_rw [he, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  have hs : (∑ i, smoothPositivePart'' (radialPower a p x-1) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i)) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i))) =
      (4*smoothPositivePart'' (radialPower a p x-1)*p^2*((a+‖x‖^2)^(p-1))^2)*‖x‖^2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (1/2:ℝ) * ((∑ i, smoothPositivePart'' (radialPower a p x-1) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i)) *
      (2*p*(a+‖x‖^2)^(p-1)*inner ℝ x (e i))) + _) = _
  rw [hs]
  ring

lemma smoothPositivePart_monotone : Monotone smoothPositivePart :=
  monotone_of_hasDerivAt_nonneg smoothPositivePart_hasDerivAt
    (fun t => (smoothPositivePart'_bounds t).1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma radialBump_antitone_parameter {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hp : p ≤ 0) (x : E) : radialBump b p x ≤ radialBump a p x := by
  apply smoothPositivePart_monotone
  exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos
    (by positivity) (by linarith) hp) 1

lemma radialBump_negative_le {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    max (-halfLaplacian (radialBump a p) x) 0 ≤
      max (-halfLaplacian (radialPower a p) x) 0 := by
  rw [radialBump_halfLaplacian ha]
  have hb := smoothPositivePart'_bounds (radialPower a p x-1)
  have hc : 0 ≤ 2 * smoothPositivePart'' (radialPower a p x-1) * p^2 *
      ((a+‖x‖^2)^(p-1))^2 * ‖x‖^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (smoothPositivePart''_nonneg _)) (sq_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)
  apply max_le
  · by_cases h : 0 ≤ halfLaplacian (radialPower a p) x
    · exact le_trans (by nlinarith [mul_nonneg hb.1 h]) (le_max_right _ _)
    · have : smoothPositivePart' (radialPower a p x-1) *
          halfLaplacian (radialPower a p) x ≥ halfLaplacian (radialPower a p) x :=
        by nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (neg_nonneg.mpr (le_of_not_ge h))]
      exact le_trans (by linarith) (le_max_left _ _)
  · exact le_max_right _ _

lemma smoothingExponent_neg (hn : 1 ≤ Module.finrank ℝ E) : smoothingExponent E < 0 := by
  have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
  unfold smoothingExponent
  linarith

lemma radialPower_laplacian_lower {a : ℝ} (ha : 0 < a)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E) :
    smoothingExponent E * (Module.finrank ℝ E : ℝ) * a^(smoothingExponent E-1) ≤
      halfLaplacian (radialPower a (smoothingExponent E)) x := by
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hbracket : n + 2*p-2 = -(3/2:ℝ) := by unfold p n smoothingExponent; ring
  rw [radialPower_halfLaplacian ha]
  change p*n*a^(p-1) ≤ p*(a+‖x‖^2)^(p-2)*(n*a+(n+2*p-2)*‖x‖^2)
  rw [hbracket]
  have hpow := Real.rpow_le_rpow_of_nonpos ha
    (show a ≤ a+‖x‖^2 by nlinarith [sq_nonneg ‖x‖]) (show p-2 ≤ 0 by linarith)
  have hq : 0 ≤ (a+‖x‖^2)^(p-2) := Real.rpow_nonneg (by positivity) _
  have hstep : p*n*a^(p-1) = (p*n*a)*a^(p-2) := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add ha, Real.rpow_one]
    ring
  rw [hstep]
  calc
    (p*n*a)*a^(p-2) ≤ (p*n*a)*(a+‖x‖^2)^(p-2) :=
      mul_le_mul_of_nonpos_left hpow (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hp.le hn0) ha.le)
    _ ≤ p*(a+‖x‖^2)^(p-2)*(n*a+ -(3/2:ℝ)*‖x‖^2) := by
      have := mul_nonneg (neg_nonneg.mpr hp.le) (mul_nonneg hq (sq_nonneg ‖x‖))
      nlinarith

lemma radialPower_laplacian_nonneg_outside {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E)
    (hx : (Module.finrank ℝ E + 1 : ℝ) * ε ≤ ‖x‖) :
    0 ≤ halfLaplacian (radialPower (ε^2) (smoothingExponent E)) x := by
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hbracket : n + 2*p-2 = -(3/2:ℝ) := by unfold p n smoothingExponent; ring
  rw [radialPower_halfLaplacian (sq_pos_of_pos hε)]
  change 0 ≤ p*(ε^2+‖x‖^2)^(p-2)*(n*ε^2+(n+2*p-2)*‖x‖^2)
  rw [hbracket]
  apply mul_nonneg_of_nonpos_of_nonpos
  · exact mul_nonpos_of_nonpos_of_nonneg hp.le (Real.rpow_nonneg (by positivity) _)
  · have hs : ((n+1)*ε)^2 ≤ ‖x‖^2 := sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hx
    have he : 0 ≤ ε^2 := sq_nonneg _
    have hnn : n ≤ (n+1)^2 := by nlinarith [sq_nonneg n]
    have hnn' := mul_le_mul_of_nonneg_right hnn he
    nlinarith

lemma radialBump_weighted_negative_bound {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) (x : E) :
    max (-halfLaplacian (radialBump (ε^2) (smoothingExponent E)) x) 0 * ‖x‖^2 ≤
      (Metric.closedBall (0 : E) ((Module.finrank ℝ E + 1 : ℝ)*ε)).indicator
        (fun _ => (-smoothingExponent E)*(Module.finrank ℝ E : ℝ)*
          (Module.finrank ℝ E + 1 : ℝ)^2*(ε^2)^(smoothingExponent E)) x := by
  classical
  let p := smoothingExponent E
  let n : ℝ := Module.finrank ℝ E
  have hp : p < 0 := smoothingExponent_neg hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hε2 : 0 < ε^2 := sq_pos_of_pos hε
  have hle := radialBump_negative_le hε2 p x
  by_cases hx : x ∈ Metric.closedBall (0 : E) ((n+1)*ε)
  · rw [Set.indicator_of_mem hx]
    have hx' : ‖x‖ ≤ (n+1)*ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hs : ‖x‖^2 ≤ ((n+1)*ε)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx'
    have hlower := radialPower_laplacian_lower hε2 hn x
    have hK : 0 ≤ (-p)*n*(ε^2)^(p-1) :=
      mul_nonneg (mul_nonneg (neg_nonneg.mpr hp.le) hn0) (Real.rpow_nonneg hε2.le _)
    have hmax : max (-halfLaplacian (radialPower (ε^2) p) x) 0 ≤
        (-p)*n*(ε^2)^(p-1) := max_le (by linarith) hK
    calc
      _ ≤ ((-p)*n*(ε^2)^(p-1))*((n+1)*ε)^2 :=
        mul_le_mul (hle.trans hmax) hs (sq_nonneg _) hK
      _ = _ := by
        have hpow : (ε^2)^(p-1)*(ε^2) = (ε^2)^p := by
          calc
            _ = (ε^2)^(p-1)*(ε^2)^(1:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hε2]; congr 1; ring
        change (-p)*n*(ε^2)^(p-1)*((n+1)*ε)^2 = (-p)*n*(n+1)^2*(ε^2)^p
        rw [← hpow]
        ring
  · rw [Set.indicator_of_notMem hx]
    have hx' : (n+1)*ε ≤ ‖x‖ := by
      have := hx
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at this
      exact this.le
    have hnonneg := radialPower_laplacian_nonneg_outside hε hn x hx'
    have hzero : max (-halfLaplacian (radialPower (ε^2) p) x) 0 = 0 :=
      max_eq_right (neg_nonpos.mpr hnonneg)
    rw [hzero] at hle
    exact mul_nonpos_of_nonpos_of_nonneg hle (sq_nonneg _)

section Integration
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma radialBump_integral_pos (hn : 1 ≤ Module.finrank ℝ E) :
    0 < ∫ x, radialBump (1/4) (smoothingExponent E) x ∂μ := by
  apply (radialBump_contDiff (E := E) (by norm_num : (0:ℝ)<1/4)
    (smoothingExponent E)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (radialBump_compact (by norm_num) (smoothingExponent_neg hn))
    (radialBump_nonneg _ _)
  apply ne_of_gt (smoothPositivePart_pos (t := radialPower (1/4) (smoothingExponent E) (0:E)-1) _)
  simp only [radialPower, norm_zero, sq, mul_zero, add_zero]
  exact sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg
    (by norm_num) (by norm_num) (smoothingExponent_neg hn))

lemma radialBump_integral_lower {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (hn : 1 ≤ Module.finrank ℝ E) :
    (∫ x, radialBump (1/4) (smoothingExponent E) x ∂μ) ≤
      ∫ x, radialBump a (smoothingExponent E) x ∂μ := by
  apply integral_mono
  · exact (radialBump_contDiff (by norm_num) _).continuous.integrable_of_hasCompactSupport
      (radialBump_compact (by norm_num) (smoothingExponent_neg hn))
  · exact (radialBump_contDiff ha _).continuous.integrable_of_hasCompactSupport
      (radialBump_compact ha (smoothingExponent_neg hn))
  · exact fun x => radialBump_antitone_parameter ha ha' (smoothingExponent_neg hn).le x

omit [MeasurableSpace E] [BorelSpace E] in
lemma radial_weight_exponent {ε : ℝ} (hε : 0 < ε) :
    ε^(Module.finrank ℝ E) * (ε^2)^(smoothingExponent E) = Real.sqrt ε := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast_mul hε.le 2,
    ← Real.rpow_add hε]
  congr 1
  unfold smoothingExponent
  push_cast
  ring

lemma radialBump_integral_negative_bound {ε : ℝ} (hε : 0 < ε)
    (hn : 1 ≤ Module.finrank ℝ E) :
    (∫ x, max (-halfLaplacian (radialBump (ε^2) (smoothingExponent E)) x) 0 * ‖x‖^2 ∂μ) ≤
      μ.real (Metric.ball (0:E) 1) * (-smoothingExponent E) *
        (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E+2) *
        Real.sqrt ε := by
  let n : ℝ := Module.finrank ℝ E
  let p := smoothingExponent E
  let R := (n+1)*ε
  let K := (-p)*n*(n+1)^2*(ε^2)^p
  have hR : 0 ≤ R := by dsimp [R,n]; positivity
  have hI : Integrable ((Metric.closedBall (0:E) R).indicator (fun _ => K)) μ :=
    (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator measurableSet_closedBall
  have hbound := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => mul_nonneg (le_max_right _ _) (sq_nonneg _))) hI
    (Filter.Eventually.of_forall (radialBump_weighted_negative_bound hε hn))
  refine hbound.trans_eq ?_
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
  rw [Measure.real_def, μ.addHaar_closedBall (0:E) hR, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hR _)]
  dsimp [R,K,n,p]
  rw [mul_pow]
  have he := radial_weight_exponent (E := E) hε
  have he' : ε^(Module.finrank ℝ E)*(ε^2)^(smoothingExponent E) = Real.sqrt ε := he
  change ((Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E)*ε^(Module.finrank ℝ E)*
    μ.real (Metric.ball (0:E) 1)) *
    ((-smoothingExponent E)*(Module.finrank ℝ E : ℝ)*(Module.finrank ℝ E + 1 : ℝ)^2*
    (ε^2)^(smoothingExponent E)) = _
  rw [pow_add, ← he']
  ring

theorem exists_radial_smoothing (hn : 1 ≤ Module.finrank ℝ E) {η : ℝ} (hη : 0 < η) :
    ∃ b : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∂μ ∧
      (∫ x, max (-halfLaplacian b x) 0 * ‖x‖^2 ∂μ) < η * ∫ x, b x ∂μ := by
  let p := smoothingExponent E
  let m := ∫ x, radialBump (1/4) p x ∂μ
  let K := μ.real (Metric.ball (0:E) 1) * (-p) * (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E + 1 : ℝ)^(Module.finrank ℝ E+2)
  have hm : 0 < m := radialBump_integral_pos μ hn
  have hp : p < 0 := smoothingExponent_neg hn
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg (ENNReal.toReal_nonneg)
      (neg_nonneg.mpr hp.le)) (Nat.cast_nonneg _)) (by positivity)
  obtain ⟨t,ht,ht'⟩ := exists_pos_mul_lt (mul_pos hη hm) (K+1)
  let δ := min t (1/2:ℝ)
  have hδ : 0 < δ := lt_min ht (by norm_num)
  have hδt : δ ≤ t := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := min_le_right _ _
  have hsmall : K*δ < η*m := by
    have := mul_le_mul_of_nonneg_left hδt (show 0 ≤ K+1 by linarith)
    nlinarith
  let ε := δ^2
  have hε : 0 < ε := sq_pos_of_pos hδ
  have hεlimit : ε^2 ≤ 1/4 := by
    have hs : δ^2 ≤ 1/4 := by nlinarith
    dsimp [ε]
    calc
      (δ^2)^2 ≤ (1/4:ℝ)^2 := (sq_le_sq₀ (sq_nonneg _) (by norm_num)).mpr hs
      _ ≤ 1/4 := by norm_num
  refine ⟨radialBump (ε^2) p, radialBump_contDiff (sq_pos_of_pos hε) p,
    radialBump_compact (sq_pos_of_pos hε) hp, radialBump_nonneg _ _, ?_, ?_⟩
  · exact hm.trans_le (radialBump_integral_lower μ (sq_pos_of_pos hε) hεlimit hn)
  · have hupper := radialBump_integral_negative_bound μ hε hn
    have hroot : Real.sqrt ε = δ := by dsimp [ε]; rw [Real.sqrt_sq hδ.le]
    change _ ≤ K*Real.sqrt ε at hupper
    rw [hroot] at hupper
    exact hupper.trans_lt (hsmall.trans_le (mul_le_mul_of_nonneg_left
      (radialBump_integral_lower μ (sq_pos_of_pos hε) hεlimit hn) hη.le))

end Integration

end Radial

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial


theorem solution.{uDomain} : type_of% @_root_.OAI.EuclideanRamsey.exists_radial_smoothing.{uDomain} := @_root_.OAI.EuclideanRamsey.exists_radial_smoothing.{uDomain}
