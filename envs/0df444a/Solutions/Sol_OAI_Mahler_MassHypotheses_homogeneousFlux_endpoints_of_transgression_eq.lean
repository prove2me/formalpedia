-- Prove2me | solution 1 for OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:24:33.11999+00:00
-- url     : https://prove2.me/submissions/14f20ff8-e85c-42b7-8735-66b0c37ca726

import Mathlib
import Definitions.Def_OAIQ2Ma000
import Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneousResidualFlux_eq_zero_of_transgression_eq
import Theorems.Thm_OAI_Mahler_MassHypotheses_small_sphere_real_flux_limit_eq

section
-- module Solutions.OAIQ2_Mah.Mahler_HolomorphicRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric Filter MeasureTheory
open scoped Topology Interval

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex Schwarz estimate gives a local bound on the full derivative,
from first-order holomorphicity alone. -/
lemma locally_bounded_fderiv {f : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    ∃ r > 0, ∃ C ≥ 0, ball x r ⊆ U ∧
      ∀ y ∈ ball x r, ‖fderiv ℂ f y‖ ≤ C := by
  have hc := (hf x hx).differentiableAt (hU.mem_nhds hx) |>.continuousAt
  have hn : U ∩ f ⁻¹' ball (f x) 1 ∈ 𝓝 x :=
    inter_mem (hU.mem_nhds hx) (hc.preimage_mem_nhds (ball_mem_nhds _ zero_lt_one))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r / 2, by positivity, 2 / (r / 2), by positivity, ?_, ?_⟩
  · intro y hy
    exact (hsub (ball_subset_ball (by linarith) hy)).1
  · intro y hy
    have hball : ball y (r / 2) ⊆ ball x r := by
      intro z hz
      have := dist_triangle z y x
      rw [mem_ball] at hy hz ⊢
      linarith
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      (hf.mono (hball.trans (fun z hz => (hsub hz).1))) ?_ (by positivity)
    intro z hz
    have hzy := (hsub (hball hz)).2
    have hyx := (hsub (ball_subset_ball (by linarith) hy)).2
    rw [mem_closedBall]
    have := dist_triangle (f z) (f x) (f y)
    change dist (f z) (f x) < 1 at hzy
    change dist (f y) (f x) < 1 at hyx
    rw [dist_comm (f x) (f y)] at this
    linarith

variable [FiniteDimensional ℂ E]

/-- Differentiability of a Cauchy integral in an ambient finite-dimensional
complex parameter. The derivative bound is obtained locally by Schwarz. -/
lemma differentiable_cauchy_parameter {f : E → ℂ} {U : Set E} {x v : E}
    {R C r : ℝ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hR : 0 < R) (hr : 0 < r) (hv : r * ‖v‖ < R / 2)
    (hsub : ball x R ⊆ U)
    (hb : ∀ y ∈ ball x R, ‖fderiv ℂ f y‖ ≤ C) :
    DifferentiableAt ℂ
      (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) x := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let c : ℝ → ℂ := circleMap 0 r
  let k : ℝ → ℂ := fun t => (c t * I) * (1 / c t ^ 2)
  have hc : Continuous c := continuous_circleMap _ _
  have hcn (t : ℝ) : ‖c t‖ = r := by simp [c, abs_of_pos hr]
  have hcz (t : ℝ) : c t ≠ 0 := by
    intro h
    have := hcn t
    rw [h, norm_zero] at this
    linarith
  have hk : Continuous k := (hc.mul continuous_const).mul
    (continuous_const.div (hc.pow 2) (fun t => pow_ne_zero _ (hcz t)))
  have hkn (t : ℝ) : ‖k t‖ = 1 / r := by
    simp [k, norm_pow, hcn, norm_I]
    field_simp
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      y + c t • v ∈ ball x R := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have htri := norm_add_le (y - x) (c t • v)
    have he : y + c t • v - x = (y - x) + c t • v := by abel
    rw [he]
    rw [norm_smul, hcn] at htri
    linarith
  have hcont {y : E} (hy : y ∈ ball x (R / 2)) :
      Continuous (fun t => k t * f (y + c t • v)) := by
    apply hk.mul
    exact hf.continuousOn.comp_continuous (by fun_prop) (fun t => hsub (hshift hy t))
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t => k t • fderiv ℂ f (y + c t • v)
  have hd {y : E} (hy : y ∈ ball x (R / 2)) (t : ℝ) :
      HasFDerivAt (fun y => k t * f (y + c t • v)) (F' y t) y := by
    have hf' := ((hf _ (hsub (hshift hy t))).differentiableAt
      (hU.mem_nhds (hsub (hshift hy t)))).hasFDerivAt
    simpa only [F', Function.comp_apply, id_eq, ContinuousLinearMap.comp_id] using
      (hf'.comp y ((hasFDerivAt_id y).add_const (c t • v))).const_mul (k t)
  have hm : AEStronglyMeasurable (F' x) := by
    apply Measurable.aestronglyMeasurable
    exact hk.measurable.smul ((measurable_fderiv ℂ f).comp
      (show Continuous (fun t => x + c t • v) by fun_prop).measurable)
  have hint := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun y t => k t * f (y + c t • v)) (F' := F')
    (bound := fun _ => (1 / r) * C) (ball_mem_nhds x (by positivity : 0 < R / 2))
    (by filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
        exact (hcont hy).aestronglyMeasurable)
    ((hcont (mem_ball_self (by positivity))).intervalIntegrable _ _)
    hm.restrict
    (by filter_upwards [] with t ht y hy
        simp only [F', norm_smul, hkn]
        exact mul_le_mul_of_nonneg_left (hb _ (hshift hy t)) (by positivity))
    (intervalIntegrable_const)
    (by filter_upwards [] with t ht y hy; exact hd hy t)
  have he : (fun y => ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) =
      (fun y => ∫ t in (0 : ℝ)..2 * Real.pi, k t * f (y + c t • v)) := by
    funext y
    simp only [circleIntegral, deriv_circleMap, smul_eq_mul, c, k, mul_assoc]
  rw [he]
  exact hint.differentiableAt

/-- A directional component of the ambient first derivative is holomorphic.
Only first-order holomorphicity on the open domain is assumed. -/
theorem differentiableAt_fderiv_apply_of_open {f : E → ℂ} {U : Set E} {x v : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  obtain ⟨R, hR, C, hC, hsub, hb⟩ := locally_bounded_fderiv hU hx hf
  let r := (R / 2) / (‖v‖ + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : r * ‖v‖ < R / 2 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)]
    nlinarith
  have hshift {y : E} (hy : y ∈ ball x (R / 2)) {z : ℂ}
      (hz : z ∈ closedBall 0 r) : y + z • v ∈ U := by
    apply hsub
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have hzn : ‖z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
    have htri := norm_add_le (y - x) (z • v)
    have he : y + z • v - x = (y - x) + z • v := by abel
    rw [he]
    rw [norm_smul] at htri
    have hmul := mul_le_mul_of_nonneg_right hzn (norm_nonneg v)
    linarith
  have he : (fun y => fderiv ℂ f y v) =ᶠ[𝓝 x]
      (fun y => (2 * Real.pi * I : ℂ)⁻¹ *
        ∮ z in C(0, r), (1 / z ^ 2) • f (y + z • v)) := by
    filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 2)] with y hy
    have hl : Differentiable ℂ (fun z : ℂ => y + z • v) := by fun_prop
    have hline : DifferentiableOn ℂ (fun z : ℂ => f (y + z • v)) (closedBall 0 r) :=
      hf.comp hl.differentiableOn (fun z hz => hshift hy hz)
    have hcauchy := hline.deriv_eq_smul_circleIntegral hr
    have hfy : DifferentiableAt ℂ f y :=
      (hf y (by simpa using hshift hy (mem_closedBall_self hr.le))).differentiableAt
        (hU.mem_nhds (by simpa using hshift hy (mem_closedBall_self hr.le)))
    have hl' : HasDerivAt (fun z : ℂ => y + z • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have hfy' : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using hfy.hasFDerivAt
    have hder := hfy'.comp_hasDerivAt 0 hl'
    change HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f y v) 0 at hder
    rw [hder.deriv] at hcauchy
    simp only [sub_zero, smul_eq_mul] at hcauchy ⊢
    rw [hcauchy, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  exact ((differentiable_cauchy_parameter hU hf hR hr hv hsub hb).const_mul
    (2 * Real.pi * I : ℂ)⁻¹).congr_of_eventuallyEq he

/-- Holomorphic functions on open finite-dimensional complex domains are C^k
for every finite k. Smoothness is derived, not added to the hypotheses. -/
theorem contDiffOn_nat_of_differentiableOn_open {U : Set E} (hU : IsOpen U)
    (k : ℕ) {f : E → ℂ} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ k f U := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiffOn_succ_of_fderiv_apply hf (by simp)
    intro v
    have hd : DifferentiableOn ℂ (fun y => fderiv ℂ f y v) U :=
      fun y hy => (differentiableAt_fderiv_apply_of_open hU hy hf).differentiableWithinAt
    apply (ih hd).congr
    intro y hy
    rw [fderivWithin_of_isOpen hU hy]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Hessian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

lemma dz_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dz f x v = fderiv ℂ f x v := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v - I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  have hi := I_mul_I
  calc
    _ = (fderiv ℂ f x v - (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [hi]; ring

lemma dbar_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dbar f x v = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v + I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (fderiv ℂ f x v + (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [I_mul_I]; ring

omit isScalarTowerRealComplexE in
lemma dz_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dz (fun y => conj (f y)) x v = conj (dbar f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dz, h.fderiv]
  simp [dbar, map_add, map_mul, conj_I, map_ofNat, sub_eq_add_neg]

omit isScalarTowerRealComplexE in
lemma dbar_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dbar (fun y => conj (f y)) x v = conj (dz f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dbar, h.fderiv]
  simp [dz, map_sub, map_mul, conj_I, map_ofNat]

omit isScalarTowerRealComplexE in
lemma dz_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun y => f y * g y) x v = dz f x v * g x + f x * dz g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dz, h.fderiv]
  simp [dz]
  ; ring

omit isScalarTowerRealComplexE in
lemma dz_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dz (fun y => ∑ j, f j y) x v = ∑ j, dz (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dz, h.fderiv]
  simp only [dz, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

omit isScalarTowerRealComplexE in
lemma dz_clog [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v : E} (hu : DifferentiableAt ℝ u x)
    (hp : u x ∈ slitPlane) :
    dz (fun y => Complex.log (u y)) x v = dz u x v / u x := by
  have h := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (u y)) _ x at h
  rw [dz, h.fderiv]
  simp [dz, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
  ; ring

variable {ι : Type*} [Fintype ι]

omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma tau_nonneg [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : 0 ≤ tau f x :=
  Finset.sum_nonneg (fun j _ => normSq_nonneg (f j x))
omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma energy_eq_tau [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : energy f x = (tau f x : ℂ) := by
  simp [energy, tau, Complex.normSq_eq_conj_mul_self]
lemma logTau_eq (f : ι → E → ℂ) : logTau f = fun x => Complex.log (energy f x) := by
  funext x
  rw [logTau, energy_eq_tau, Complex.ofReal_log (tau_nonneg f x)]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma diff_conj [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

lemma differentiable_energy {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : DifferentiableAt ℝ (energy f) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj ((hf j).restrictScalars ℝ)).mul ((hf j).restrictScalars ℝ))

lemma dz_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dz (energy f) x v = ∑ j, conj (f j x) * fderiv ℂ (f j) x v := by
  change dz (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dz_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dz_conj ((hf j).restrictScalars ℝ), dbar_holomorphic (hf j), dz_holomorphic (hf j)]
  simp

lemma dz_logTau {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dz (logTau f) x v = (∑ j, conj (f j x) * fderiv ℂ (f j) x v) / (tau f x : ℂ) := by
  rw [logTau_eq, dz_clog (differentiable_energy hf) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht), dz_energy hf,
    energy_eq_tau]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Complex
open scoped BigOperators
local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

omit isScalarTowerRealComplexE in
lemma dc_circle [IsScalarTower ℝ ℂ E] (u : E → ℂ) (x : E) :
    dc u x (I • x) = (dz u x x + dbar u x x) / 4 := by
  simp only [dc, dz, dbar, smul_smul, I_mul_I, neg_smul, one_smul, map_neg]
  ring

lemma dbar_real {u : E → ℂ} {x v : E} (hr : ∀ y, conj (u y) = u y)
    (hu : DifferentiableAt ℝ u x) : dbar u x v = conj (dz u x v) := by
  have h := dbar_conj (v := v) hu
  simpa only [hr] using h

omit normedSpaceRealE isScalarTowerRealComplexE in
/-- Euler's identity derived by differentiating the homogeneous scaling identity. -/
lemma homogeneous_euler [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} {m : ℕ}
    (hf : DifferentiableAt ℂ f x) (hh : ∀ c : ℂ, f (c • x) = c^m * f x) :
    fderiv ℂ f x x = (m : ℂ) * f x := by
  have hl : HasDerivAt (fun c : ℂ => c • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℂ)).smul_const x
  have hfd : HasFDerivAt f (fderiv ℂ f x) ((1 : ℂ) • x) := by simpa using hf.hasFDerivAt
  have hleft := hfd.comp_hasDerivAt 1 hl
  have hright : HasDerivAt (fun c : ℂ => c^m * f x) ((m : ℂ) * f x) 1 := by
    simpa using ((hasDerivAt_id (1 : ℂ)).pow m).mul_const (f x)
  have he : (fun c : ℂ => f (c • x)) = (fun c : ℂ => c^m * f x) := funext hh
  change HasDerivAt (fun c : ℂ => f (c • x)) _ 1 at hleft
  rw [he] at hleft
  exact hleft.unique hright

variable {ι : Type*} [Fintype ι]
lemma differentiable_logTau {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    DifferentiableAt ℝ (logTau f) x := by
  rw [logTau_eq]
  have hp : energy f x ∈ slitPlane := by
    rw [energy_eq_tau]
    exact Complex.ofReal_mem_slitPlane.mpr ht
  exact (((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x
    (differentiable_energy hf).hasFDerivAt).differentiableAt

lemma dz_logTau_radial {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x)
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) :
    dz (logTau f) x x = (m : ℂ) := by
  rw [dz_logTau hf ht]
  simp_rw [homogeneous_euler (hf _) (hh _)]
  have hs : (∑ j, conj (f j x) * ((m : ℂ) * f j x)) = (m : ℂ) * energy f x := by
    simp [energy, Finset.mul_sum, mul_left_comm]
  rw [hs, energy_eq_tau]
  have hn : (tau f x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  field_simp [hn]

/-- The homogeneous sphere-flux normalization alpha(V)=m/2, V(z)=iz. -/
theorem homogeneous_dc_circle {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x)
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) :
    dc (logTau f) x (I • x) = (m : ℂ) / 2 := by
  rw [dc_circle, dbar_real (by intro y; simp [logTau]) (differentiable_logTau hf ht),
    dz_logTau_radial hf ht hh]
  simp only [map_natCast]
  ring

omit normedSpaceRealE isScalarTowerRealComplexE in
/-- Scaling of the actual squared norm follows from component homogeneity. -/
lemma tau_homogeneous [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x) (c : ℂ) :
    tau f (c • x) = normSq c ^ m * tau f x := by
  simp [tau, hh, map_mul, map_pow, Finset.mul_sum]

/-- Circle invariance is derived from homogeneity, not assumed. -/
lemma logTau_circle_invariant {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hh : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    {c : ℂ} (hc : normSq c = 1) : logTau f (c • x) = logTau f x := by
  simp only [logTau, tau_homogeneous hh, hc, one_pow, one_mul]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExteriorFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma differentiableAt_oneForm [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) : DifferentiableAt ℝ (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x ha

/-- Exterior differentiation uses the usual unnormalized alternating sum. -/
lemma extDeriv_oneForm {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    extDeriv (oneForm a) x ![v, w] =
      fderiv ℝ (fun y => a y w) x v - fderiv ℝ (fun y => a y v) x w := by
  rw [extDeriv_apply (differentiableAt_oneForm ha)]
  simp [Fin.sum_univ_two, Fin.removeNth, oneForm_apply, sub_eq_add_neg]

lemma hasDerivAt_circle_smul (point : E) :
    HasDerivAt (fun angle : ℝ => circleMap 0 1 angle • point) (I • point) 0 := by
  simpa [circleMap] using (hasDerivAt_circleMap 0 1 0).smul_const point

lemma hasDerivAt_circle_form {form : E → E →L[ℝ] ℂ} {point : E}
    (hform : DifferentiableAt ℝ form point) (argument : E) :
    HasDerivAt
      (fun angle : ℝ => form (circleMap 0 1 angle • point)
        (circleMap 0 1 angle • argument))
      (form point (I • argument) + fderiv ℝ form point (I • point) argument) 0 := by
  have hzero : circleMap 0 1 0 = 1 := by simp [circleMap]
  have hbase : HasFDerivAt form (fderiv ℝ form point) (circleMap 0 1 0 • point) := by
    simpa only [hzero, one_smul] using hform.hasFDerivAt
  have hcomposition : HasDerivAt (fun angle : ℝ => form (circleMap 0 1 angle • point))
      (fderiv ℝ form point (I • point)) 0 :=
    hbase.comp_hasDerivAt 0 (hasDerivAt_circle_smul point)
  simpa only [hzero, one_smul, add_comm] using
    hcomposition.clm_apply (hasDerivAt_circle_smul argument)

lemma fderiv_circle_invariant {a : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x)
    (hinv : ∀ (t : ℝ) (w : E),
      a (circleMap 0 1 t • x) (circleMap 0 1 t • w) = a x w) (w : E) :
    a x (I • w) + fderiv ℝ a x (I • x) w = 0 := by
  have h1 := hasDerivAt_circle_form ha w
  have he : (fun t : ℝ => a (circleMap 0 1 t • x) (circleMap 0 1 t • w)) =
      (fun _ => a x w) := funext (fun t => hinv t w)
  rw [he] at h1
  exact h1.unique (hasDerivAt_const 0 (a x w))

lemma fderiv_circle_contraction {a : E → E →L[ℝ] ℂ} {x : E} {q : ℂ}
    (ha : DifferentiableAt ℝ a x)
    (hconst : (fun y => a y (I • y)) =ᶠ[𝓝 x] (fun _ => q)) (w : E) :
    a x (I • w) + fderiv ℝ a x w (I • x) = 0 := by
  have h2 := ha.hasFDerivAt.clm_apply complexStructure.hasFDerivAt
  change HasFDerivAt (fun y => a y (I • y)) _ x at h2
  have hi2 := congrArg (fun L : E →L[ℝ] ℂ => L w)
    (h2.fderiv.symm.trans hconst.fderiv_eq)
  simpa using hi2

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma fderiv_form_apply {form : E → E →L[ℝ] ℂ} {point : E}
    (hform : DifferentiableAt ℝ form point) (argument direction : E) :
    fderiv ℝ (fun value => form value argument) point direction =
      fderiv ℝ form point direction argument := by
  simpa using congrArg (fun derivative : E →L[ℝ] ℂ => derivative direction)
    (hform.hasFDerivAt.clm_apply (hasFDerivAt_const argument point)).fderiv

/-- Cartan's contraction identity for the circle field, proved using actual
Fréchet derivatives and circle invariance. -/
theorem extDeriv_circle_horizontal {a : E → E →L[ℝ] ℂ} {x : E} {q : ℂ}
    (ha : DifferentiableAt ℝ a x)
    (hinv : ∀ (t : ℝ) (w : E),
      a (circleMap 0 1 t • x) (circleMap 0 1 t • w) = a x w)
    (hconst : (fun y => a y (I • y)) =ᶠ[𝓝 x] (fun _ => q)) (w : E) :
    extDeriv (oneForm a) x ![I • x, w] = 0 := by
  rw [extDeriv_oneForm ha, fderiv_form_apply ha, fderiv_form_apply ha]
  linear_combination fderiv_circle_invariant ha hinv w -
    fderiv_circle_contraction ha hconst w

/-- C^2 regularity of log tau follows from first-order holomorphicity. -/
lemma contDiffAt_logTau_of_open [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) : ContDiffAt ℝ 2 (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ 2 (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := 2) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

/-- d^c respects the circle action when the scalar function does. -/
lemma dcLinear_rotation {u : E → ℂ} {x : E} {c : ℂ}
    (hu : DifferentiableAt ℝ u (c • x))
    (hinv : ∀ y, u (c • y) = u y) (w : E) :
    dcLinear u (c • x) (c • w) = dcLinear u x w := by
  let L : E →L[ℝ] E := (c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have h := hu.hasFDerivAt.comp x L.hasFDerivAt
  have he : (u ∘ L) = u := funext hinv
  change HasFDerivAt (u ∘ L) _ x at h
  rw [he] at h
  have hd := congrArg (fun A : E →L[ℝ] ℂ => A (I • w)) h.fderiv
  simp only [ContinuousLinearMap.comp_apply] at hd
  have hm : L (I • w) = I • (c • w) := by simp [L, smul_smul, mul_comm]
  rw [hm] at hd
  simp only [dcLinear_apply, dc]
  rw [hd]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HorizontalForms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct
namespace Mahler
open AlternatingMap
variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- A horizontal top-degree form vanishes when the contracting vector is nonzero. -/
theorem horizontal_top_eq_zero [FiniteDimensional ℝ T]
    {ι : Type*} [Fintype ι] {a : T [⋀^ι]→ₗ[ℝ] ℂ} {V : T}
    (hdim : Fintype.card ι = Module.finrank ℝ T) (hV : V ≠ 0)
    (ha : Horizontal a V) : a = 0 := by
  classical
  ext v
  by_cases hv : LinearIndependent ℝ v
  · let b := basisOfLinearIndependentOfCardEqFinrank' v hv hdim
    have hb (i : ι) : b i = v i :=
      congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v hv hdim) i
    obtain ⟨i, hi⟩ : ∃ i, b.repr V i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hV
      apply b.repr.injective
      ext i
      simpa using hn i
    have hz := ha (Function.update v i V) i (Function.update_self ..)
    have he : V = ∑ j, b.repr V j • v j := by
      simpa only [← hb] using (b.sum_repr V).symm
    rw [he, a.map_update_sum] at hz
    have hs : (∑ j, a (Function.update v i (b.repr V j • v j))) =
        (b.repr V i) • a v := by
      rw [Finset.sum_eq_single i]
      · rw [a.map_update_smul, Function.update_eq_self]
      · intro j hj hji
        rw [a.map_update_smul, a.map_update_self _ hji.symm, smul_zero]
      · simp
    rw [hs] at hz
    exact (smul_eq_zero.mp hz).resolve_left hi
  · exact a.map_linearDependent v hv

/-- Exterior products of horizontal forms are horizontal. -/
theorem Horizontal.wedge {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {a : T [⋀^ι]→ₗ[ℝ] ℂ} {b : T [⋀^κ]→ₗ[ℝ] ℂ} {V : T}
    (ha : Horizontal a V) (hb : Horizontal b V) : Horizontal (wedge a b) V := by
  intro v i hi
  suffices h : a.domCoprod b v = 0 by
    change (LinearMap.mul' ℝ ℂ) (a.domCoprod b v) = 0
    rw [h, _root_.map_zero]
  change (∑ σ : Equiv.Perm.ModSumCongr ι κ, AlternatingMap.domCoprod.summand a b σ) v = 0
  rw [sum_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [_root_.smul_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply, AlternatingMap.coe_multilinearMap]
    have hpre : v (σ (σ.symm i)) = V := by simpa using hi
    cases he : σ.symm i with
    | inl j =>
      have hz := ha (fun j => v (σ (Sum.inl j))) j (by simpa [he] using hpre)
      simp [hz]
    | inr j =>
      have hz := hb (fun j => v (σ (Sum.inr j))) j (by simpa [he] using hpre)
      simp [hz]

lemma card_wedgePowerSlots (n : ℕ) : Fintype.card (WedgePowerSlots n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 ⊕ WedgePowerSlots n) = _
    rw [Fintype.card_sum, Fintype.card_fin, ih]
    omega

lemma Horizontal.wedgePower {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T}
    (ha : Horizontal a V) (n : ℕ) : Horizontal (wedgePower a n) V := by
  induction n with
  | zero => intro v i; exact Fin.elim0 i
  | succ n ih => exact ha.wedge ih

/-- The form beta wedge (d alpha_t)^(n-1) vanishes in top degree.
Here k = n-1 and T is the sphere tangent space, of dimension 2k+1. -/
theorem beta_wedge_power_eq_zero [FiniteDimensional ℝ T]
    (k : ℕ) {b : T [⋀^Fin 1]→ₗ[ℝ] ℂ} {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T}
    (hdim : Module.finrank ℝ T = 2 * k + 1) (hV : V ≠ 0)
    (hb : Horizontal b V) (ha : Horizontal a V) : wedge b (wedgePower a k) = 0 := by
  apply horizontal_top_eq_zero (V := V) _ hV (hb.wedge (ha.wedgePower k))
  rw [Fintype.card_sum, Fintype.card_fin, card_wedgePowerSlots, hdim]
  omega

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_WedgeAlgebra
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma wedgePower_smul (c : ℂ) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (c • a) k = c ^ k • wedgePower a k := by
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = c ^ 0 * 1
    simp
  | succ k ih =>
    change wedge (c • a) (wedgePower (c • a) k) = c ^ (k + 1) • wedge a (wedgePower a k)
    simp only [ih, wedge_smul_left, wedge_smul_right, smul_smul]
    rw [pow_succ]

lemma wedge_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).compLinearMap L = wedge (a.compLinearMap L) (b.compLinearMap L) := by
  ext v
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod b (fun i => L (v i))) =
    (LinearMap.mul' ℝ ℂ) ((a.compLinearMap L).domCoprod (b.compLinearMap L) v)
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      AlternatingMap.coe_multilinearMap, AlternatingMap.compLinearMap_apply]

lemma wedgePower_compLinearMap {S : Type*} [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    (wedgePower a k).compLinearMap L = wedgePower (a.compLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (wedge a (wedgePower a k)).compLinearMap L = _
    rw [wedge_compLinearMap, ih]
    rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_WedgeCalculus
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Differentiating the actual finite shuffle sum, at each vector tuple. -/
theorem hasDerivAt_wedge_eval {a : ℝ → T [⋀^ι]→ₗ[ℝ] ℂ}
    {b : ℝ → T [⋀^κ]→ₗ[ℝ] ℂ} {da : T [⋀^ι]→ₗ[ℝ] ℂ}
    {db : T [⋀^κ]→ₗ[ℝ] ℂ} {t : ℝ}
    (ha : ∀ v, HasDerivAt (fun s => a s v) (da v) t)
    (hb : ∀ v, HasDerivAt (fun s => b s v) (db v) t) (v : ι ⊕ κ → T) :
    HasDerivAt (fun s => wedge (a s) (b s) v)
      ((wedge da (b t) + wedge (a t) db) v) t := by
  have hterm (σ : Equiv.Perm.ModSumCongr ι κ) :
      HasDerivAt
        (fun s => (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand (a s) (b s) σ v))
        ((LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand da (b t) σ v) +
         (LinearMap.mul' ℝ ℂ) (AlternatingMap.domCoprod.summand (a t) db σ v)) t := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      convert ((ha (fun i => v (σ (Sum.inl i)))).mul
        (hb (fun i => v (σ (Sum.inr i))))).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)) using 1
      all_goals first | rfl | ring
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => hterm σ)
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    sum_apply, map_sum, AlternatingMap.add_apply, Finset.sum_add_distrib] using hs

theorem hasDerivAt_wedgePower_eval {a : ℝ → T [⋀^Fin 2]→ₗ[ℝ] ℂ}
    {da : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {t : ℝ}
    (ha : ∀ v, HasDerivAt (fun s => a s v) (da v) t) (k : ℕ)
    (v : WedgePowerSlots k → T) :
    HasDerivAt (fun s => wedgePower (a s) k v) (wedgePowerVariation (a t) da k v) t := by
  induction k with
  | zero => exact hasDerivAt_const t 1
  | succ k ih =>
    exact hasDerivAt_wedge_eval ha ih v

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_BoundaryJet
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped Topology TensorProduct

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuous_wedge_eval [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [TopologicalSpace X]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {a : X → E [⋀^ι]→ₗ[ℝ] ℂ} {b : X → E [⋀^κ]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun s => a s v))
    (hb : ∀ v, Continuous (fun s => b s v)) (v : ι ⊕ κ → E) :
    Continuous (fun s => wedge (a s) (b s) v) := by
  have ht (σ : Equiv.Perm.ModSumCongr ι κ) :
      Continuous (fun s => (LinearMap.mul' ℝ ℂ)
        (AlternatingMap.domCoprod.summand (a s) (b s) σ v)) := by
    induction σ using Quotient.inductionOn' with
    | h σ =>
      simp only [wedge_summand_eval]
      exact continuous_const.mul ((ha _).mul (hb _))
  simpa only [wedge, LinearMap.compAlternatingMap_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, _root_.map_sum] using continuous_finsetSum Finset.univ (fun σ _ => ht σ)

lemma continuous_wedgePower_eval {X : Type*} [TopologicalSpace X]
    {a : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun s => a s v)) (k : ℕ) (v : WedgePowerSlots k → E) :
    Continuous (fun s => wedgePower (a s) k v) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact continuous_wedge_eval ha ih v

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_CompactFluxDifferentiation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace CompactFluxDifferentiation
variable {X E : Type*} [TopologicalSpace X] [compactSpaceX : CompactSpace X]
  [measurableSpaceX : MeasurableSpace X] [borelSpaceX : BorelSpace X] [secondCountableTopologyX : SecondCountableTopology X]
  [NormedAddCommGroup E] [normedSpaceRealE : NormedSpace ℝ E] [completeSpaceE : CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]
  {F G : ℝ → X → E} {a b t : ℝ}

omit compactSpaceX measurableSpaceX borelSpaceX secondCountableTopologyX normedSpaceRealE completeSpaceE in
lemma continuous_slice [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [NormedSpace ℝ E] [CompleteSpace E] (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2)
    (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) : Continuous (F t) := by
  exact hF.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht, mem_univ x⟩)

lemma integrable_slice (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2)
    (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) : Integrable (F t) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_slice hF ht).continuousOn
  exact Integrable.of_bound (continuous_slice hF ht).aestronglyMeasurable C
    (ae_of_all μ (fun x => hC x (mem_univ x)))

/-- Continuity includes both endpoints of the compact parameter interval. -/
theorem continuousOn_integral
    (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2) (Icc a b ×ˢ univ)) :
    ContinuousOn (fun s => ∫ x, F s x ∂μ) (Icc a b) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hF
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro s hs
    exact (continuous_slice hF hs).aestronglyMeasurable
  · intro s hs
    exact ae_of_all μ (fun x => hC (s,x) ⟨hs, mem_univ x⟩)
  · exact integrable_const C
  · apply ae_of_all
    intro x
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ x⟩)

/-- Joint continuity on a compact parameter interval and compact finite-measure
fiber supplies every domination and measurability obligation. -/
theorem hasDerivAt_integral
    (hF : ContinuousOn (fun p : ℝ × X => F p.1 p.2) (Icc a b ×ˢ univ))
    (hG : ContinuousOn (fun p : ℝ × X => G p.1 p.2) (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => F r x) (G s x) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, G t x ∂μ) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hG
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := G) (s := Ioo a b) (bound := fun _ => C)
    (Ioo_mem_nhds ht.1 ht.2) ?_ (integrable_slice hF ⟨ht.1.le, ht.2.le⟩)
    (continuous_slice hG ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable ?_
    (integrable_const C) ?_).2
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (continuous_slice hF ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
  · exact ae_of_all μ (fun x s hs => hC (s,x) ⟨⟨hs.1.le, hs.2.le⟩, mem_univ x⟩)
  · exact ae_of_all μ (fun x s hs => hd s hs x)

end CompactFluxDifferentiation

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_CovectorVolume
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct BigOperators

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Exterior multiplication of simple forms concatenates their covectors,
with the exact shuffle normalization and slot order. -/
theorem wedge_covectorVolume (l : ι → T →ₗ[ℝ] ℂ) (r : κ → T →ₗ[ℝ] ℂ) :
    wedge (covectorVolume l) (covectorVolume r) = covectorVolume (Sum.elim l r) := by
  unfold covectorVolume wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]
  congr 1
  ext v
  simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    LinearMap.mul'_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

lemma wedge_sum_left {J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : T [⋀^κ]→ₗ[ℝ] ℂ) : wedge (∑ j ∈ s, a j) b = ∑ j ∈ s, wedge (a j) b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.sum_tmul, map_sum]

lemma wedge_sum_right {J : Type*} (s : Finset J) (a : T [⋀^ι]→ₗ[ℝ] ℂ)
    (b : J → T [⋀^κ]→ₗ[ℝ] ℂ) : wedge a (∑ j ∈ s, b j) = ∑ j ∈ s, wedge a (b j) := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply,
    ← LinearMap.compAlternatingMapₗ_apply ℝ, TensorProduct.tmul_sum, map_sum]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExteriorPower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

lemma pairedCovectors_succ {k : ℕ} (p : Fin (k+1) → Fin 2 → T →ₗ[ℝ] ℂ) :
    pairedCovectors p = Sum.elim (p 0) (pairedCovectors (fun i => p i.succ)) := by
  funext s
  cases s <;> rfl

/-- Expand the actual shuffle power as a sum of determinants of selected
covector pairs. This identity includes every term, also repeated selections. -/
theorem wedgePower_sum_pairs {J : Type*} [Fintype J]
    (p : J → Fin 2 → T →ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      ∑ q : Fin k → J, covectorVolume (pairedCovectors (fun i => p (q i))) := by
  classical
  induction k with
  | zero =>
    ext v
    change (1 : ℂ) = (∑ q : Fin 0 → J, covectorVolume
      (pairedCovectors (fun index => p (q index)))) v
    simp only [Fintype.sum_unique]
    rw [covectorVolume_apply]
    let : IsEmpty (WedgePowerSlots 0) := inferInstanceAs (IsEmpty (Fin 0))
    exact Matrix.det_isEmpty.symm
  | succ k ih =>
    change wedge (∑ j, covectorVolume (p j)) (wedgePower (∑ j, covectorVolume (p j)) k) = _
    rw [ih, wedge_sum_left]
    simp_rw [wedge_sum_right, wedge_covectorVolume]
    simp_rw [pairedCovectors_succ]
    trans ∑ q : J × (Fin k → J), covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i))))
    · exact (Fintype.sum_prod_type (fun q : J × (Fin k → J) => covectorVolume (Sum.elim (p q.1) (pairedCovectors (fun i => p (q.2 i)))))).symm
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k+1) => J))
      intro q
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [show wedgePowerSlotsDecidableEq (k+1) =
        (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
      rfl

lemma pairPermutation_sign {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm.sign (pairPermutation σ) = 1 := by
  simp [pairPermutation, Equiv.Perm.sign_prodCongrLeft]

lemma pairedCovectors_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    pairedCovectors (fun i => p (σ i)) = pairedCovectors p ∘ pairPermutation σ := by
  funext s
  simp [pairedCovectors, pairPermutation, Equiv.prodCongrLeft]

lemma covectorVolume_pairs_perm {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (σ : Equiv.Perm (Fin k)) :
    covectorVolume (pairedCovectors (fun i => p (σ i))) = covectorVolume (pairedCovectors p) := by
  ext v
  rw [pairedCovectors_perm, covectorVolume_apply, covectorVolume_apply]
  change Matrix.det ((Matrix.of (fun row column => pairedCovectors p column (v row))).submatrix
    id (pairPermutation σ)) = _
  rw [Matrix.det_permute', pairPermutation_sign]
  simp only [Units.val_one, Int.cast_one, one_mul]

lemma covectorVolume_pairs_noninjective {k : ℕ} (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ)
    (q : Fin k → Fin k) (hq : ¬Function.Injective q) :
    covectorVolume (pairedCovectors (fun i => p (q i))) = 0 := by
  classical
  obtain ⟨i,j,hij,hne⟩ : ∃ i j, q i = q j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, exists_prop] using hq
  ext v
  rw [covectorVolume_apply]
  apply Matrix.det_zero_of_column_eq
    (i := (pairSlotEquiv k).symm (i,0)) (j := (pairSlotEquiv k).symm (j,0))
  · intro h
    have h' := congrArg (fun s => (pairSlotEquiv k s).1) h
    exact hne (by simpa using h')
  · intro s
    simp [pairedCovectors, hij]

/-- The n-fold shuffle power of n simple two-forms is n! times their
interleaved covector volume. Repeated choices vanish; pair permutations have
positive sign. This yields the factorial in the normalization. -/
theorem wedgePower_sum_pairs_top (k : ℕ) (p : Fin k → Fin 2 → T →ₗ[ℝ] ℂ) :
    wedgePower (∑ j, covectorVolume (p j)) k =
      (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
  classical
  rw [wedgePower_sum_pairs]
  calc
    (∑ q : Fin k → Fin k, covectorVolume (pairedCovectors (fun i => p (q i)))) =
        ∑ q : Fin k → Fin k with Function.Bijective q,
          covectorVolume (pairedCovectors (fun i => p (q i))) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun q _ hq => ?_)).symm
      apply covectorVolume_pairs_noninjective p q
      intro hi
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, Finite.surjective_of_injective hi⟩)
    _ = ∑ σ : Equiv.Perm (Fin k), covectorVolume (pairedCovectors (fun i => p (σ i))) :=
      Finset.sum_bij (fun q h => Equiv.ofBijective q (Finset.mem_filter.1 h).2)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => by injection h)
        (fun b _ => ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, b.bijective⟩,
          Equiv.coe_fn_injective rfl⟩) (fun _ _ => rfl)
    _ = (k.factorial : ℂ) • covectorVolume (pairedCovectors p) := by
      simp only [covectorVolume_pairs_perm, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℂ k.factorial _).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceHomogeneous
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators Topology

namespace Mahler

/-- Conversion from the polynomial homogeneity predicate to
its scaling equation; no functional homogeneity assumption is added. -/
lemma eval_homogeneous_scale {σ : Type*} {p : MvPolynomial σ ℂ} {m : ℕ}
    (hp : p.IsHomogeneous m) (z : σ → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun i => c * z i) p = c ^ m * MvPolynomial.eval z p := by
  classical
  simp only [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hd]
  ring

lemma polynomialMap_differentiable {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ) :
    ∀ j, Differentiable ℂ (polynomialMap G j) := by
  intro j x
  have ha : AnalyticAt ℂ (fun z : ComplexEuclidean n =>
      MvPolynomial.eval (fun i => z i) (G j)) x :=
    AnalyticAt.aeval_mvPolynomial
      (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)
  exact ha.differentiableAt

lemma polynomialMap_homogeneous {n N m : ℕ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (hG : ∀ j, (G j).IsHomogeneous m) :
    ∀ j (z : ComplexEuclidean n) (c : ℂ),
      polynomialMap G j (c • z) = c ^ m * polynomialMap G j z := by
  intro j z c
  exact eval_homogeneous_scale (hG j) (fun i => z i) c

lemma tau_pos_of_component_ne_zero {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ι → E → ℂ} {x : E} (hf : ∃ j, f j x ≠ 0) : 0 < tau f x := by
  obtain ⟨j, hj⟩ := hf
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hj)
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (f k x)) (Finset.mem_univ j)

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousDeformation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ E] in
lemma betaLinear_circle [FiniteDimensional ℂ E] {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hfg : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x)
    (hgg : ∀ j (c : ℂ), g j (c • x) = c^1 * g j x) :
    betaLinear f g m x (I • x) = 0 := by
  simp only [betaLinear, _root_.sub_apply, _root_.smul_apply,
    dcLinear_apply, homogeneous_dc_circle hf htf hfg, homogeneous_dc_circle hg htg hgg]
  simp [Complex.real_smul, div_eq_mul_inv]

lemma alphaPath_circle {f : ι → E → ℂ} {g : κ → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (htf : 0 < tau f x)
    (hfg : ∀ j (c : ℂ), f j (c • x) = c^m * f j x)
    (hg : ∀ j, DifferentiableAt ℂ (g j) x) (htg : 0 < tau g x)
    (hgg : ∀ j (c : ℂ), g j (c • x) = c^1 * g j x) (t : ℝ) :
    alphaPath f g m t x (I • x) = (m : ℂ) / 2 := by
  simp only [alphaPath, _root_.add_apply, _root_.smul_apply,
    betaLinear_circle hf htf hfg hg htg hgg, smul_zero, add_zero, dcLinear_apply,
    homogeneous_dc_circle hg htg hgg]
  simp [Complex.real_smul, div_eq_mul_inv]

omit [FiniteDimensional ℂ E] in
lemma homogeneous_dcLinear_rotation [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (ht : 0 < tau f x)
    (hh : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y)
    {c : ℂ} (hc : normSq c = 1) (v : E) :
    dcLinear (logTau f) (c • x) (c • v) = dcLinear (logTau f) x v := by
  apply dcLinear_rotation
  · apply differentiable_logTau (fun j => (hf j).differentiableAt)
    simpa [tau_homogeneous (fun j c => hh j x c), hc] using ht
  · intro y
    exact logTau_circle_invariant (fun j c => hh j y c) hc

omit [FiniteDimensional ℂ E] in
lemma tau_continuousAt [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : ContinuousAt (tau f) x := by
  have h := Complex.continuous_re.continuousAt.comp (differentiable_energy hf).continuousAt
  simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h

/-- Circle horizontality for the actual whole deformation, for every real t.
The only regularity hypotheses are first-order holomorphicity. -/
theorem alphaPath_extDeriv_horizontal {f : ι → E → ℂ} {g : κ → E → ℂ}
    {x : E} {m : ℕ}
    (hf : ∀ j, Differentiable ℂ (f j)) (htf : 0 < tau f x)
    (hfg : ∀ j (y : E) (c : ℂ), f j (c • y) = c^m * f j y)
    (hg : ∀ j, Differentiable ℂ (g j)) (htg : 0 < tau g x)
    (hgg : ∀ j (y : E) (c : ℂ), g j (c • y) = c^1 * g j y)
    (t : ℝ) (v : E) :
    extDeriv (oneForm (alphaPath f g m t)) x ![I • x, v] = 0 := by
  have hdf := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ
    (Set.mem_univ x) (fun j => (hf j).differentiableOn) htf)
  have hdg := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ
    (Set.mem_univ x) (fun j => (hg j).differentiableOn) htg)
  apply extDeriv_circle_horizontal (q := (m : ℂ) / 2)
    ((hdg.const_smul (m : ℝ)).add ((hdf.sub (hdg.const_smul (m : ℝ))).const_smul t))
  · intro s w
    have hc : normSq (circleMap 0 1 s) = 1 := by rw [Complex.normSq_eq_norm_sq]; simp
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, _root_.add_apply,
      _root_.sub_apply, _root_.smul_apply]
    rw [homogeneous_dcLinear_rotation hf htf hfg hc,
      homogeneous_dcLinear_rotation hg htg hgg hc]
  · have hcf := tau_continuousAt (x := x) (fun j => (hf j).differentiableAt)
    have hcg := tau_continuousAt (x := x) (fun j => (hg j).differentiableAt)
    filter_upwards [hcf.eventually (lt_mem_nhds htf), hcg.eventually (lt_mem_nhds htg)] with y hyf hyg
    exact alphaPath_circle (fun j => (hf j).differentiableAt) hyf (fun j c => hfg j y c)
      (fun j => (hg j).differentiableAt) hyg (fun j c => hgg j y c) t

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereForms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma coordinateMap_differentiable (n : ℕ) : ∀ j, Differentiable ℂ (coordinateMap n j) :=
  fun j => (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable

lemma coordinateMap_homogeneous (n : ℕ) : ∀ j (z : ComplexEuclidean n) (c : ℂ),
    coordinateMap n j (c • z) = c^1 * coordinateMap n j z := by
  intros
  simp [coordinateMap]

lemma coordinateMap_tau_pos {n : ℕ} {z : ComplexEuclidean n} (hz : z ≠ 0) :
    0 < tau (coordinateMap n) z := by
  apply tau_pos_of_component_ne_zero
  by_contra h
  push Not at h
  apply hz
  ext i
  exact h i

lemma circleTangent_ne_zero {n : ℕ} {z : ComplexEuclidean n} (hz : z ≠ 0) :
    circleTangent z ≠ 0 := by
  intro h
  have he : I • z = 0 := congrArg Subtype.val h
  exact (smul_eq_zero.mp he).elim I_ne_zero hz

lemma sphereTangent_finrank {n : ℕ} (hn : 1 ≤ n) {z : ComplexEuclidean n} (hz : z ≠ 0) :
    Module.finrank ℝ (sphereTangent z) = 2 * (n - 1) + 1 := by
  have hd : Module.finrank ℝ (ComplexEuclidean n) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexEuclidean n)]
    simp [ComplexEuclidean, Complex.finrank_real_complex]
  let : Fact (Module.finrank ℝ (ComplexEuclidean n) = (2 * (n - 1) + 1) + 1) :=
    ⟨by rw [hd]; omega⟩
  exact Submodule.finrank_orthogonal_span_singleton hz

lemma horizontal_twoForm {T : Type*} [AddCommGroup T] [Module ℝ T]
    {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T} (ha : ∀ w, a ![V, w] = 0) : Horizontal a V := by
  intro v i hi
  fin_cases i
  · have he : v = ![V, v 1] := by ext i; fin_cases i <;> simp_all
    rw [he, ha]
  · have he : v = ![v 0, V] := by ext i; fin_cases i <;> simp_all
    have hs := a.map_swap ![V, v 0] (i := 0) (j := 1) (by decide)
    have he' : ![V, v 0] ∘ Equiv.swap (0 : Fin 2) 1 = ![v 0, V] := by
      ext i; fin_cases i <;> simp
    rw [he', ha, neg_zero] at hs
    rw [he, hs]

lemma Horizontal.tangentForm {n : ℕ} {ι : Type*} {z : ComplexEuclidean n}
    {a : ComplexEuclidean n [⋀^ι]→ₗ[ℝ] ℂ} (ha : Horizontal a (I • z)) :
    Horizontal (tangentForm z a) (circleTangent z) := by
  intro v i hi
  apply ha (fun i => (v i : ComplexEuclidean n)) i
  exact congrArg Subtype.val hi

/-- The top-degree deformation term vanishes on every sphere tangent
space under the polynomial hypotheses. -/
theorem MassHypotheses.sphere_beta_wedge_power_zero {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) :
    wedge
      (tangentForm z (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap)
        (n - 1)) = 0 := by
  have hfG := polynomialMap_differentiable G
  have htG := tau_pos_of_component_ne_zero (f := polynomialMap G) (x := z) (h.leading_nonzero z hz)
  have hhG := polynomialMap_homogeneous h.homogeneous
  apply beta_wedge_power_eq_zero (n - 1) (sphereTangent_finrank h.dimension_pos hz)
    (circleTangent_ne_zero hz)
  · apply Horizontal.tangentForm
    intro v i hi
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    change betaLinear (polynomialMap G) (coordinateMap n) m z (v 0) = 0
    rw [hi]
    exact betaLinear_circle (fun j => (hfG j).differentiableAt) htG (fun j c => hhG j z c)
      (fun j => (coordinateMap_differentiable n j).differentiableAt) (coordinateMap_tau_pos hz)
      (fun j c => coordinateMap_homogeneous n j z c)
  · apply Horizontal.tangentForm
    apply horizontal_twoForm
    intro v
    exact alphaPath_extDeriv_horizontal hfG htG hhG (coordinateMap_differentiable n)
      (coordinateMap_tau_pos hz) (coordinateMap_homogeneous n) t v

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_NormSquareForm
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma normEnergy_contDiff (n : ℕ) : ContDiff ℝ 2 (normEnergy n) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_id.norm_sq (𝕜 := ℝ))

/-- The actual d^c of the Euclidean squared norm. -/
lemma dc_normEnergy {n : ℕ} (x v : ComplexEuclidean n) :
    dc (normEnergy n) x v = (-1 / 2 : ℂ) * (inner ℝ x (I • v) : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (normEnergy n) _ x at hd
  rw [dc, hd.fderiv]
  simp
  ring

lemma real_inner_complexStructure_swap {n : ℕ} (v w : ComplexEuclidean n) :
    inner ℝ w (I • v) = -inner ℝ v (I • w) := by
  simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

/-- The exterior normalization dd^c |z|^2 is the
standard symplectic two-form, with positive dx_k wedge dy_k orientation. -/
theorem extDeriv_dc_normEnergy {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v, w] =
      ((∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) : ℝ) : ℂ) := by
  rw [extDeriv_oneForm (differentiableAt_dcLinear (normEnergy_contDiff n).contDiffAt)]
  have hd (a b : ComplexEuclidean n) :
      fderiv ℝ (fun y => dcLinear (normEnergy n) y a) x b =
        (-1 / 2 : ℂ) * (inner ℝ b (I • a) : ℂ) := by
    have he : (fun y => dcLinear (normEnergy n) y a) =
        (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) := by
      funext y
      rw [dcLinear_apply, dc_normEnergy, real_inner_comm]
    rw [he]
    have hh := ((Complex.ofRealCLM.comp (innerSL ℝ (I • a))).hasFDerivAt (x := x)).const_mul (-1 / 2 : ℂ)
    change HasFDerivAt (fun y => (-1 / 2 : ℂ) * (inner ℝ (I • a) y : ℂ)) _ x at hh
    rw [hh.fderiv]
    simp [real_inner_comm]
  rw [hd, hd, real_inner_complexStructure_swap v w, Complex.ofReal_neg]
  have he : -(inner ℝ v (I • w)) = ∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [← he, Complex.ofReal_neg]
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_LevelForms
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

lemma contDiffAt_energy_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    ContDiffAt ℝ 2 (energy f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  apply ContDiffAt.sum
  intro j hj
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)

omit [FiniteDimensional ℂ E] in
lemma dc_logTau_eq_div [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dc (logTau f) x v = dc (energy f) x v / energy f x := by
  have hp : energy f x ∈ slitPlane := by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht
  have hh := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x
    (differentiable_energy hf).hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (energy f y)) _ x at hh
  rw [logTau_eq, dc, hh.fderiv]
  simp [dc]
  ring

/-- On tangent vectors to an energy level, the actual exterior log form is
energy^{-1} times the energy form. This is local calculus, not Stokes. -/
theorem extDeriv_logTau_on_level {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (v w : E)
    (hv : fderiv ℝ (energy f) x v = 0) (hw : fderiv ℝ (energy f) x w = 0) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![v, w] =
      (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x ![v, w] := by
  have he := contDiffAt_energy_of_open hU hx hf
  have hde := differentiableAt_dcLinear he
  have hdl := differentiableAt_dcLinear (contDiffAt_logTau_of_open hU hx hf ht)
  have hfe := differentiable_energy (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hn : energy f x ≠ 0 := by rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht
  have hc : ContinuousAt (tau f) x := tau_continuousAt
    (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hval (a b : E) (hb : fderiv ℝ (energy f) x b = 0) :
      fderiv ℝ (fun y => dcLinear (logTau f) y a) x b =
        (energy f x)⁻¹ * fderiv ℝ (fun y => dcLinear (energy f) y a) x b := by
    have heq : (fun y => dcLinear (logTau f) y a) =ᶠ[𝓝 x]
        (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) := by
      filter_upwards [hU.mem_nhds hx, hc.eventually (lt_mem_nhds ht)] with y hy hty
      simp only [dcLinear_apply, dc_logTau_eq_div
        (fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)) hty, div_eq_mul_inv]
      ring
    rw [heq.fderiv_eq]
    have hi := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp x hfe.hasFDerivAt
    have ha := hde.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
    have hh := hi.mul ha
    change HasFDerivAt (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) _ x at hh
    rw [hh.fderiv]
    have hae := congrArg (fun L : E →L[ℝ] ℂ => L b) ha.fderiv
    simp at hae
    simp [hb, hae]
  rw [extDeriv_oneForm hdl, extDeriv_oneForm hde, hval w v hv, hval v w hw]
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferenceSphere
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

/-- Restriction to any linear space of vectors tangent to an energy level. -/
theorem level_oneForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E) :
    (oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change dcLinear (logTau f) x (v 0) = (energy f x)⁻¹ * dcLinear (energy f) x (v 0)
  rw [dcLinear_apply, dcLinear_apply,
    dc_logTau_eq_div (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx)) ht]
  ring

theorem level_twoForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) :
    (extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype =
      (energy f x)⁻¹ •
        (extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype := by
  ext v
  change extDeriv (oneForm (dcLinear (logTau f))) x (fun i => (v i : E)) =
    (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x (fun i => (v i : E))
  have hv : (fun i => (v i : E)) = ![(v 0 : E), (v 1 : E)] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact extDeriv_logTau_on_level hU hx hf ht (v 0) (v 1) (hS (v 0)) (hS (v 1))

/-- The complete boundary form scales by tau^(-(k+1)), with the actual
shuffle exterior power. No integration identity is assumed. -/
theorem level_boundaryForm_scaling {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (S : Submodule ℝ E)
    (hS : ∀ v : S, fderiv ℝ (energy f) x v = 0) (k : ℕ) :
    wedge ((oneForm (dcLinear (logTau f)) x).toAlternatingMap.compLinearMap S.subtype)
      (wedgePower ((extDeriv (oneForm (dcLinear (logTau f))) x).toAlternatingMap.compLinearMap S.subtype) k) =
    ((energy f x)⁻¹) ^ (k+1) •
      wedge ((oneForm (dcLinear (energy f)) x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (dcLinear (energy f))) x).toAlternatingMap.compLinearMap S.subtype) k) := by
  rw [level_oneForm_scaling hU hx hf ht S, level_twoForm_scaling hU hx hf ht S hS,
    wedgePower_smul, wedge_smul_left, wedge_smul_right, smul_smul, pow_succ']

lemma coordinateMap_energy (n : ℕ) : energy (coordinateMap n) = normEnergy n := by
  funext z
  rw [energy_eq_tau]
  simp [tau, coordinateMap, normEnergy, EuclideanSpace.norm_sq_eq,
    Complex.normSq_eq_norm_sq, Complex.ofReal_sum]

lemma normEnergy_fderiv {n : ℕ} (x v : ComplexEuclidean n) :
    fderiv ℝ (normEnergy n) x v = (2 * inner ℝ x v : ℝ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (normEnergy n) _ x at hd
  rw [hd.fderiv]
  simp

lemma normEnergy_sphere_tangent {n : ℕ} (x : ComplexEuclidean n)
    (v : sphereTangent x) : fderiv ℝ (normEnergy n) x v = 0 := by
  rw [normEnergy_fderiv]
  have hv : inner ℝ x (v : ComplexEuclidean n) = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property)
  simp [hv]

/-- The reference logarithmic boundary form equals the actual squared-norm
boundary form on the unit sphere, in every exterior degree. -/
theorem reference_sphere_boundaryForm {n : ℕ} {z : ComplexEuclidean n}
    (hz : ‖z‖ = 1) (k : ℕ) :
    wedge (tangentForm z (oneForm (dcLinear (logTau (coordinateMap n))) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (dcLinear (logTau (coordinateMap n)))) z).toAlternatingMap) k) =
    wedge (tangentForm z (oneForm (dcLinear (normEnergy n)) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (dcLinear (normEnergy n))) z).toAlternatingMap) k) := by
  have hnz : z ≠ 0 := by intro h; simp [h] at hz
  have h := level_boundaryForm_scaling isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn)
    (coordinateMap_tau_pos hnz) (sphereTangent z)
    (by rw [coordinateMap_energy]; exact normEnergy_sphere_tangent z) k
  simpa only [coordinateMap_energy, normEnergy, hz, one_pow, Complex.ofReal_one,
    inv_one, one_smul, tangentForm] using h

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_FluxVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma oneForm_add [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a b : E → E →L[ℝ] ℂ) : oneForm (a+b) = oneForm a + oneForm b := by
  funext x
  ext v
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma oneForm_smul [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (c : ℝ) (a : E → E →L[ℝ] ℂ) : oneForm (c • a) = c • oneForm a := by
  funext x
  ext v
  rfl

lemma extDeriv_oneForm_affine {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (t : ℝ) :
    extDeriv (oneForm (a+t • b)) x =
      extDeriv (oneForm a) x + t • extDeriv (oneForm b) x := by
  rw [oneForm_add, oneForm_smul, extDeriv_add (differentiableAt_oneForm ha)
    ((differentiableAt_oneForm hb).const_smul t), extDeriv_smul]

/-- Actual parameter derivative of the boundary form, at each vector tuple.
The spatial derivatives are exterior derivatives. -/
theorem hasDerivAt_boundaryForm {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (S : Submodule ℝ E) (t : ℝ) (k : ℕ) (v : Fin 1 ⊕ WedgePowerSlots k → S) :
    HasDerivAt
      (fun s => wedge
        ((oneForm (a+s • b) x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (a+s • b)) x).toAlternatingMap.compLinearMap S.subtype) k) v)
      ((wedge ((oneForm b x).toAlternatingMap.compLinearMap S.subtype)
        (wedgePower ((extDeriv (oneForm (a+t • b)) x).toAlternatingMap.compLinearMap S.subtype) k) +
        wedge ((oneForm (a+t • b) x).toAlternatingMap.compLinearMap S.subtype)
          (wedgePowerVariation
            ((extDeriv (oneForm (a+t • b)) x).toAlternatingMap.compLinearMap S.subtype)
            ((extDeriv (oneForm b) x).toAlternatingMap.compLinearMap S.subtype) k)) v) t := by
  apply hasDerivAt_wedge_eval
  · intro w
    change HasDerivAt (fun s : ℝ => a x (w 0) + s • b x (w 0)) (b x (w 0)) t
    have hh := (hasDerivAt_const t (a x (w 0))).add ((hasDerivAt_id t).smul_const (b x (w 0)))
    change HasDerivAt (fun s : ℝ => a x (w 0) + s • b x (w 0)) (0 + (1 : ℝ) • b x (w 0)) t at hh
    simpa only [zero_add, one_smul] using hh
  · apply hasDerivAt_wedgePower_eval
    intro w
    simp only [extDeriv_oneForm_affine ha hb]
    change HasDerivAt
      (fun s : ℝ => extDeriv (oneForm a) x (fun i => (w i : E)) +
        s • extDeriv (oneForm b) x (fun i => (w i : E)))
      (extDeriv (oneForm b) x (fun i => (w i : E))) t
    have hh := (hasDerivAt_const t (extDeriv (oneForm a) x (fun i => (w i : E)))).add
      ((hasDerivAt_id t).smul_const (extDeriv (oneForm b) x (fun i => (w i : E))))
    change HasDerivAt (fun s : ℝ => extDeriv (oneForm a) x (fun i => (w i : E)) + s • extDeriv (oneForm b) x (fun i => (w i : E))) (0 + (1 : ℝ) • extDeriv (oneForm b) x (fun i => (w i : E))) t at hh
    simpa only [zero_add, one_smul] using hh

/-- The first variation term vanishes for the homogeneous path.
The remaining term is displayed explicitly; this is not flux constancy. -/
theorem MassHypotheses.sphere_boundaryForm_derivative {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ)
    (v : Fin 1 ⊕ WedgePowerSlots (n-1) → sphereTangent z) :
    HasDerivAt
      (fun s => wedge
        (tangentForm z (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m s) z).toAlternatingMap)
        (wedgePower (tangentForm z
          (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m s)) z).toAlternatingMap) (n-1)) v)
      (wedge
        (tangentForm z (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t) z).toAlternatingMap)
        (wedgePowerVariation
          (tangentForm z (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap)
          (tangentForm z (extDeriv (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m)) z).toAlternatingMap)
          (n-1)) v) t := by
  have hfG := polynomialMap_differentiable G
  have htG := tau_pos_of_component_ne_zero (f := polynomialMap G) (x := z) (h.leading_nonzero z hz)
  have hdG := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ z)
    (fun j => (hfG j).differentiableOn) htG)
  have hd0 := differentiableAt_dcLinear (contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn) (coordinateMap_tau_pos hz))
  have hdA : DifferentiableAt ℝ ((m : ℝ) • dcLinear (logTau (coordinateMap n))) z := hd0.const_smul _
  have hdB : DifferentiableAt ℝ (betaLinear (polynomialMap G) (coordinateMap n) m) z :=
    hdG.sub hdA
  have hh := hasDerivAt_boundaryForm hdA hdB (sphereTangent z) t (n-1) v
  change HasDerivAt _
    ((wedge (tangentForm z (oneForm (betaLinear (polynomialMap G) (coordinateMap n) m) z).toAlternatingMap)
      (wedgePower (tangentForm z
        (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t)) z).toAlternatingMap) (n-1))) v + _) t at hh
  rw [h.sphere_beta_wedge_power_zero hz t] at hh
  convert hh using 1 <;> simp only [tangentForm, AlternatingMap.zero_apply, zero_add]
  all_goals rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_NormExteriorPower
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma alternatingMap_sum_apply {T : Type*} [AddCommGroup T] [Module ℝ T]
    {ι J : Type*} (s : Finset J) (a : J → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ j ∈ s, a j) v = ∑ j ∈ s, a j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    change a j v + (∑ i ∈ s, a i) v = _
    rw [ih]

lemma extDeriv_normEnergy_covectors {n : ℕ} (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap =
      ∑ j : Fin n, covectorVolume (coordinatePair j) := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [alternatingMap_sum_apply]
  change extDeriv (oneForm (dcLinear (normEnergy n))) x v = _
  rw [hv, extDeriv_dc_normEnergy]
  simp only [covectorVolume_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro coordinate hcoordinate
  simp only [Matrix.det_fin_two, Matrix.of_apply, coordinatePair,
    Matrix.cons_val_zero, Matrix.cons_val_one, realCoordinate_apply, imagCoordinate_apply,
    Complex.ofReal_sub, Complex.ofReal_mul]

/-- Full squared-norm exterior normalization, in arbitrary dimension, for the
actual exterior derivative and standard shuffle powers. -/
theorem extDeriv_normEnergy_top (n : ℕ) (x : ComplexEuclidean n) :
    wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap n =
      (n.factorial : ℂ) • interleavedVolume n := by
  rw [extDeriv_normEnergy_covectors, wedgePower_sum_pairs_top]
  rfl

/-- The normalization is positive on dx_1,dy_1,..., not just determined up
to an unspecified orientation sign. -/
theorem interleavedVolume_basis (n : ℕ) : interleavedVolume n interleavedBasis = 1 := by
  rw [interleavedVolume, covectorVolume_apply]
  have hm : Matrix.of (fun a b : WedgePowerSlots n =>
      pairedCovectors (coordinatePair (n := n)) b (interleavedBasis a)) =
      (1 : Matrix (WedgePowerSlots n) (WedgePowerSlots n) ℂ) := by
    ext a b
    obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv n a = (i,α) := ⟨_,_,rfl⟩
    obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv n b = (j,β) := ⟨_,_,rfl⟩
    have hab : a = b ↔ i = j ∧ α = β := by
      rw [← (pairSlotEquiv n).injective.eq_iff, ha, hb, Prod.mk.injEq]
    fin_cases α <;> fin_cases β <;>
      simp [pairedCovectors, interleavedBasis, ha, hb, coordinatePair,
        Matrix.of_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all
  rw [hm, Matrix.det_one]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereNormalization
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric
open scoped BigOperators
namespace Mahler

lemma complexEuclidean_finrank_real (n : ℕ) :
    Module.finrank ℝ (ComplexEuclidean n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexEuclidean n)]
  simp [ComplexEuclidean, Complex.finrank_real_complex]

/-- The numerical integral for sphere normalization. This does not
assume equality of the constant density and the reference exterior form. -/
theorem reference_sphere_density_integral (n : ℕ) (hn : 1 ≤ n) :
    (∫ _z : sphere (0 : ComplexEuclidean n) 1,
      ((n - 1).factorial : ℝ) / 2 ∂sphereArea n) = Real.pi ^ n := by
  have hdim := complexEuclidean_finrank_real n
  have : Nontrivial (ComplexEuclidean n) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  have hv : (volume : Measure (ComplexEuclidean n)).real (ball 0 1) =
      Real.pi ^ n / (n.factorial : ℝ) := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even hdim]
    simp
    positivity
  rw [integral_const, sphereArea, Measure.toSphere_real_apply_univ, hdim, hv, smul_eq_mul]
  have hn' : n = (n - 1) + 1 := by omega
  have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    conv_lhs => rw [hn', Nat.factorial_succ]
    push_cast
    congr 1
    exact_mod_cast hn'.symm
  rw [hfac]
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfn : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
  push_cast
  field_simp

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_OrientedSphereDensity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory Metric

namespace Mahler

section Cofactors
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {d : ℕ}

lemma orientedDensity_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) (c : ℂ) :
    orientedDensity b Ω (c • B) x = c * orientedDensity b Ω B x := by
  unfold orientedDensity
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [← mul_div_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma normalWedge_basis (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B b =
      ∑ i : Fin (d+1), (b.repr x i : ℂ) * (-1 : ℂ)^i.val * B (i.removeNth b) := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [LinearMap.smulRight_apply, AlternatingMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, OrthonormalBasis.repr_apply_apply,
    real_inner_comm x (b i), Complex.real_smul, zsmul_eq_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  ring

lemma orientedDensity_eq_normalWedge (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    orientedDensity b Ω B x = normalWedge x B b / Ω b := by
  rw [normalWedge_basis]; rfl

/-- On a unit sphere, the normal wedge evaluates on outward normal followed
by tangent vectors as exactly the boundary form. This checks the sign and
shows which surface restriction the cofactor formula represents. -/
theorem normalWedge_outward_tangent (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E}
    (hx : ‖x‖ = 1) (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    normalWedge x B (Matrix.vecCons x v) = B v := by
  rw [normalWedge, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have hzero : (∑ i : Fin d, (-1 : ℤ)^i.succ.val •
      ((innerSL ℝ x).toLinearMap.smulRight B) (Matrix.vecCons x v i.succ)
        (i.succ.removeNth (Matrix.vecCons x v))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Matrix.vecCons, LinearMap.smulRight_apply, hv i]
  rw [hzero]
  simp [LinearMap.smulRight_apply, hx, Matrix.vecCons]

lemma topForm_ext_on_basis (b : Module.Basis (Fin (d+1)) ℝ E)
    {A C : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ} (h : A b = C b) : A = C := by
  classical
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin (d+1)) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change A (b ∘ e) = C (b ∘ e)
  rw [A.map_perm, C.map_perm, h]

lemma normalWedge_eq_density_smul (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) (x : E) :
    normalWedge x B = orientedDensity b Ω B x • Ω := by
  apply topForm_ext_on_basis b.toBasis
  change normalWedge x B b = orientedDensity b Ω B x * Ω b
  rw [orientedDensity_eq_normalWedge, div_mul_cancel₀ _ hΩ]

/-- The density multiplies the outward area form to give the actual
restriction of B to every tuple of tangent vectors. -/
theorem orientedDensity_spec (b : OrthonormalBasis (Fin (d+1)) ℝ E)
    (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ) (hΩ : Ω b ≠ 0)
    (B : E [⋀^Fin d]→ₗ[ℝ] ℂ) {x : E} (hx : ‖x‖ = 1)
    (v : Fin d → E) (hv : ∀ i, inner ℝ x (v i) = 0) :
    B v = orientedDensity b Ω B x * Ω (Matrix.vecCons x v) := by
  rw [← normalWedge_outward_tangent B hx v hv, normalWedge_eq_density_smul b Ω hΩ]
  rfl

end Cofactors

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereFluxIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric
open scoped BigOperators

namespace Mahler

lemma topForm_basis_ne_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {d : ℕ} (b : Module.Basis (Fin d) ℝ E)
    {Ω : E [⋀^Fin d]→ₗ[ℝ] ℂ} (hΩ : Ω ≠ 0) : Ω b ≠ 0 := by
  classical
  intro hz
  apply hΩ
  apply b.ext_alternating
  intro v hv
  let e : Equiv.Perm (Fin d) := Equiv.ofBijective v ⟨hv, Finite.surjective_of_injective hv⟩
  change Ω (b ∘ e) = 0
  rw [Ω.map_perm, hz, smul_zero]

lemma sphereVolume_frame_ne_zero (k : ℕ) : sphereVolume k (sphereFrame k) ≠ 0 := by
  apply topForm_basis_ne_zero (sphereFrame k).toBasis
  intro hz
  have h := congrArg (fun a => a (interleavedBasis ∘ (ambientFinEquiv k).symm)) hz
  have he : ((interleavedBasis ∘ (ambientFinEquiv k).symm) ∘ ambientFinEquiv k) =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext i; simp
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he,
    interleavedVolume_basis, AlternatingMap.zero_apply] at h
  exact one_ne_zero h

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_UnitaryReference
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma normEnergy_twoForm_inner {n : ℕ} (x v w : ComplexEuclidean n) :
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v,w] =
      -(inner ℝ v (I • w) : ℂ) := by
  rw [extDeriv_dc_normEnergy]
  have h : (∑ j : Fin n, ((v j).re * (w j).im - (v j).im * (w j).re)) =
      -inner ℝ v (I • w) := by
    simp only [PiLp.inner_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.inner, Complex.mul_re, Complex.mul_im]
    ring
  rw [h, Complex.ofReal_neg]

lemma unitary_real_inner {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (v w : ComplexEuclidean n) :
    inner ℝ (L v) (L w) = inner ℝ v w := by
  let Lr : ComplexEuclidean n ≃ₗᵢ[ℝ] ComplexEuclidean n :=
    { L.toLinearEquiv.restrictScalars ℝ with norm_map' := L.norm_map }
  exact Lr.inner_map_map v w

lemma normEnergy_oneForm_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) :
    (oneForm (dcLinear (normEnergy n)) (L x)).toAlternatingMap.compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      (oneForm (dcLinear (normEnergy n)) x).toAlternatingMap := by
  ext v
  change dcLinear (normEnergy n) (L x) (L (v 0)) = dcLinear (normEnergy n) x (v 0)
  simp only [dcLinear_apply]
  rw [dc_normEnergy, dc_normEnergy, ← L.map_smul, unitary_real_inner]

lemma normEnergy_twoForm_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) :
    (extDeriv (oneForm (dcLinear (normEnergy n))) (L x)).toAlternatingMap.compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap := by
  ext v
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) = _
  have he : (fun i => L (![v 0,v 1] i)) = ![L (v 0), L (v 1)] := by
    ext i; fin_cases i <;> rfl
  change extDeriv (oneForm (dcLinear (normEnergy n))) (L x) (fun i => L (![v 0,v 1] i)) =
    extDeriv (oneForm (dcLinear (normEnergy n))) x ![v 0,v 1]
  rw [he, normEnergy_twoForm_inner, normEnergy_twoForm_inner, ← L.map_smul,
    unitary_real_inner]

/-- Unitary maps preserve the actual positive coordinate volume. The proof
uses the normalized symplectic top power, so no determinant sign is assumed. -/
theorem interleavedVolume_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) :
    (interleavedVolume n).compLinearMap (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
      interleavedVolume n := by
  have h := congrArg (fun a => wedgePower a n) (normEnergy_twoForm_unitary L 0)
  rw [← wedgePower_compLinearMap, extDeriv_normEnergy_top, extDeriv_normEnergy_top] at h
  ext v
  have hv := congrArg (fun a => a v) h
  change (n.factorial : ℂ) * interleavedVolume n (fun i => L (v i)) =
    (n.factorial : ℂ) * interleavedVolume n v at hv
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n) hv

lemma normEnergy_boundary_unitary {n : ℕ}
    (L : ComplexEuclidean n ≃ₗᵢ[ℂ] ComplexEuclidean n) (x : ComplexEuclidean n) (k : ℕ) :
    (wedge (oneForm (dcLinear (normEnergy n)) (L x)).toAlternatingMap
      (wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) (L x)).toAlternatingMap k)).compLinearMap
      (L.toLinearEquiv.toLinearMap.restrictScalars ℝ) =
    wedge (oneForm (dcLinear (normEnergy n)) x).toAlternatingMap
      (wedgePower (extDeriv (oneForm (dcLinear (normEnergy n))) x).toAlternatingMap k) := by
  rw [wedge_compLinearMap, wedgePower_compLinearMap, normEnergy_oneForm_unitary,
    normEnergy_twoForm_unitary]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferencePole
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma referencePole_pair_zero (k : ℕ) :
    (covectorVolume (coordinatePair (0 : Fin (k+1)))).compLinearMap
      (sphereTangent (referencePole k)).subtype = 0 := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, covectorVolume_apply, Matrix.det_fin_two, Matrix.of_apply,
    coordinatePair, Matrix.cons_val_zero, Matrix.cons_val_one, realCoordinate_apply,
    imagCoordinate_apply, AlternatingMap.zero_apply]
  have h0 := (referencePole_tangent_iff _).mp (v 0).property
  have h1 := (referencePole_tangent_iff _).mp (v 1).property
  simp [h0,h1]

lemma referencePole_twoForm (k : ℕ) :
    tangentForm (referencePole k)
      (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap =
      ∑ j : Fin k, covectorVolume (fun i =>
        (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype) := by
  rw [extDeriv_normEnergy_covectors, Fin.sum_univ_succ]
  change ((covectorVolume (coordinatePair 0) + ∑ j : Fin k, covectorVolume (coordinatePair j.succ))).compLinearMap _ = _
  ext v
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.add_apply,
    alternatingMap_sum_apply]
  have hz := congrArg (fun a => a v) (referencePole_pair_zero k)
  change covectorVolume (coordinatePair 0) (fun i => (v i : ComplexEuclidean (k+1))) = 0 at hz
  simp only [Submodule.subtype_apply]
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [covectorVolume_apply, LinearMap.comp_apply, Submodule.subtype_apply]

lemma referencePole_oneForm (k : ℕ) :
    tangentForm (referencePole k) (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap =
      (1/2 : ℂ) • covectorVolume (fun _ : Fin 1 =>
        (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype) := by
  ext v
  change dcLinear (normEnergy (k+1)) (referencePole k) (v 0) = _
  rw [dcLinear_apply, dc_normEnergy, referencePole_inner]
  simp [covectorVolume_apply, Matrix.det_unique, Complex.mul_re]
  ring

/-- At the standard pole, the reference boundary form is the determinant of
the positively ordered tangent covectors, with the exact k!/2 coefficient. -/
theorem referencePole_boundary (k : ℕ) :
    wedge (tangentForm (referencePole k)
      (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap)
      (wedgePower (tangentForm (referencePole k)
        (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap) k) =
    ((k.factorial : ℂ)/2) • covectorVolume
      (Sum.elim
        (fun _ : Fin 1 => (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype)
        (pairedCovectors (fun j : Fin k => fun i =>
          (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype))) := by
  rw [referencePole_oneForm, referencePole_twoForm, wedgePower_sum_pairs_top,
    wedge_smul_left, wedge_smul_right, wedge_covectorVolume, smul_smul]
  congr 1
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferencePoleFrame
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

lemma pole_covector_matrix (k : ℕ) :
    Matrix.of (fun a b : Fin 1 ⊕ WedgePowerSlots k =>
      (Sum.elim
        (fun _ : Fin 1 => (imagCoordinate (0 : Fin (k+1))).comp (sphereTangent (referencePole k)).subtype)
        (pairedCovectors (fun j : Fin k => fun i =>
          (coordinatePair j.succ i).comp (sphereTangent (referencePole k)).subtype))) b
        (poleTangentFrame k a)) = (1 : Matrix (Fin 1 ⊕ WedgePowerSlots k) (Fin 1 ⊕ WedgePowerSlots k) ℂ) := by
  ext a b
  simp only [Matrix.of_apply]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp [poleTangentFrame, poleFrameVector, Matrix.one_apply]
      exact Subsingleton.elim _ _
    | inr b =>
      obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv k b = (j,β) := ⟨_,_,rfl⟩
      fin_cases β <;> simp [pairedCovectors, hb, coordinatePair, poleTangentFrame,
        poleFrameVector]
  | inr a =>
    cases b with
    | inl b => simp [poleTangentFrame, poleFrameVector]
    | inr b =>
      obtain ⟨i,α,ha⟩ : ∃ i α, pairSlotEquiv k a = (i,α) := ⟨_,_,rfl⟩
      obtain ⟨j,β,hb⟩ : ∃ j β, pairSlotEquiv k b = (j,β) := ⟨_,_,rfl⟩
      have hab : a = b ↔ i = j ∧ α = β := by
        rw [← (pairSlotEquiv k).injective.eq_iff, ha, hb, Prod.mk.injEq]
      fin_cases α <;> fin_cases β <;>
        simp [pairedCovectors, poleTangentFrame, poleFrameVector, ha, hb, coordinatePair,
          PiLp.single_apply, Matrix.one_apply, hab, eq_comm] <;> split_ifs <;> simp_all

lemma referencePole_boundary_value (k : ℕ) :
    wedge (tangentForm (referencePole k)
      (oneForm (dcLinear (normEnergy (k+1))) (referencePole k)).toAlternatingMap)
      (wedgePower (tangentForm (referencePole k)
        (extDeriv (oneForm (dcLinear (normEnergy (k+1)))) (referencePole k)).toAlternatingMap) k)
      (poleTangentFrame k) = (k.factorial : ℂ)/2 := by
  rw [referencePole_boundary]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, covectorVolume_apply,
    pole_covector_matrix, Matrix.det_one, mul_one]

lemma ambientFinEquiv_real_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 0) = 0 := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_imag_zero (k : ℕ) :
    ambientFinEquiv k (Sum.inl 1) = (boundaryFinEquiv k (Sum.inl 0)).succ := by
  apply Fin.ext
  rfl

lemma ambientFinEquiv_tail (k : ℕ) (s : WedgePowerSlots k) :
    ambientFinEquiv k (Sum.inr s) = (boundaryFinEquiv k (Sum.inr s)).succ := by
  apply Fin.ext
  change 2 + (powerFinEquiv k s).val = (1 + (powerFinEquiv k s).val) + 1
  omega

lemma poleFrameFin_volume (k : ℕ) :
    sphereVolume k (Matrix.vecCons (referencePole k) (poleFrameFin k)) = 1 := by
  have he : (Matrix.vecCons (referencePole k) (poleFrameFin k)) ∘ ambientFinEquiv k =
      (interleavedBasis : WedgePowerSlots (k+1) → ComplexEuclidean (k+1)) := by
    funext s
    cases s with
    | inl j =>
      fin_cases j
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 0)) = _
        rw [ambientFinEquiv_real_zero]
        simp [Matrix.vecCons, referencePole, interleavedBasis, pairSlotEquiv]
        rfl
      · change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inl 1)) = _
        rw [ambientFinEquiv_imag_zero]
        simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
        rfl
    | inr s =>
      change Matrix.vecCons (referencePole k) (poleFrameFin k) (ambientFinEquiv k (Sum.inr s)) = _
      rw [ambientFinEquiv_tail]
      simp [Matrix.vecCons, poleFrameFin, interleavedBasis, pairSlotEquiv, poleFrameVector]
      rfl
  simp only [sphereVolume, AlternatingMap.domDomCongr_apply, he, interleavedVolume_basis]

lemma referencePole_boundaryFin_value (k : ℕ) :
    boundaryFormFin (dcLinear (normEnergy (k+1))) (referencePole k) (poleFrameFin k) =
      (k.factorial : ℂ)/2 := by
  have h := referencePole_boundary_value k
  have he : (poleFrameFin k ∘ boundaryFinEquiv k) = poleFrameVector k := by
    ext s; simp [poleFrameFin]
  simp only [boundaryFormFin, AlternatingMap.domDomCongr_apply, he]
  simpa only [tangentForm, ← wedgePower_compLinearMap, ← wedge_compLinearMap,
    AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, poleTangentFrame] using h

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ReferenceSphereIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric
open scoped BigOperators

namespace Mahler

lemma exists_unitary_referencePole {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1) :
    ∃ L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1), L (referencePole k) = x := by
  classical
  have hv : Orthonormal ℂ (({0} : Set (Fin (k+1))).domRestrict (fun _ => x)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by simpa using i.property.trans j.property.symm)
    simp [hij, Set.domRestrict, inner_self_eq_norm_sq_to_K, hx]
  obtain ⟨b,hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [ComplexEuclidean])
  refine ⟨b.repr.symm, ?_⟩
  rw [referencePole, b.repr_symm_single]
  exact hb 0 (Set.mem_singleton 0)

lemma sphereVolume_unitary {k : ℕ}
    (L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1))
    (v : Fin ((2*k+1)+1) → ComplexEuclidean (k+1)) :
    sphereVolume k (L ∘ v) = sphereVolume k v := by
  have h := congrArg (fun A => A (v ∘ ambientFinEquiv k)) (interleavedVolume_unitary L)
  simpa only [sphereVolume, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

lemma normEnergy_boundaryFin_unitary {k : ℕ}
    (L : ComplexEuclidean (k+1) ≃ₗᵢ[ℂ] ComplexEuclidean (k+1))
    (x : ComplexEuclidean (k+1)) (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    boundaryFormFin (dcLinear (normEnergy (k+1))) (L x) (L ∘ v) =
      boundaryFormFin (dcLinear (normEnergy (k+1))) x v := by
  have h := congrArg (fun A => A (v ∘ boundaryFinEquiv k)) (normEnergy_boundary_unitary L x k)
  simpa only [boundaryFormFin, AlternatingMap.domDomCongr_apply,
    AlternatingMap.compLinearMap_apply, Function.comp_def, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv] using h

lemma reference_boundaryFin_on_tangent {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1) (v : Fin (2*k+1) → ComplexEuclidean (k+1))
    (hv : ∀ i, inner ℝ x (v i) = 0) :
    boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x v =
      boundaryFormFin (dcLinear (normEnergy (k+1))) x v := by
  let w : Fin 1 ⊕ WedgePowerSlots k → sphereTangent x := fun s =>
    ⟨v (boundaryFinEquiv k s), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have h := congrArg (fun A => A w) (reference_sphere_boundaryForm hx k)
  simpa only [boundaryFormFin, AlternatingMap.domDomCongr_apply, tangentForm,
    ← wedgePower_compLinearMap, ← wedge_compLinearMap, AlternatingMap.compLinearMap_apply,
    Submodule.subtype_apply, w, Function.comp_def] using h

/-- The actual reference logarithmic boundary form has the constant outward
sphere density k!/2 in complex dimension k+1. -/
theorem reference_boundary_density {k : ℕ} {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) :
    orientedDensity (sphereFrame k) (sphereVolume k)
      (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x =
      (k.factorial : ℂ)/2 := by
  obtain ⟨L,hL⟩ := exists_unitary_referencePole hx
  let v := L ∘ poleFrameFin k
  have hv0 (i : Fin (2*k+1)) : inner ℝ (referencePole k) (poleFrameFin k i) = 0 := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (poleFrameVector_tangent _)
  have hv (i : Fin (2*k+1)) : inner ℝ x (v i) = 0 := by
    rw [← hL]
    exact (unitary_real_inner L _ _).trans (hv0 i)
  have hvol : sphereVolume k (Matrix.vecCons x v) = 1 := by
    have he : Matrix.vecCons x v = L ∘ Matrix.vecCons (referencePole k) (poleFrameFin k) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [Matrix.vecCons] using hL.symm
      · rfl
    rw [he, sphereVolume_unitary, poleFrameFin_volume]
  have hb : boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x v =
      (k.factorial : ℂ)/2 := by
    rw [reference_boundaryFin_on_tangent hx v hv, ← hL]
    exact (normEnergy_boundaryFin_unitary L (referencePole k) (poleFrameFin k)).trans
      (referencePole_boundaryFin_value k)
  have h := orientedDensity_spec (sphereFrame k) (sphereVolume k) (sphereVolume_frame_ne_zero k)
    (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) hx v hv
  rw [hvol, mul_one, hb] at h
  exact h.symm

/-- Integration of the reference boundary form against Euclidean
sphere area, with outward orientation and the dc convention. -/
theorem reference_boundary_flux (k : ℕ) :
    sphereFlux k (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1))))) =
      Real.pi^(k+1) := by
  unfold sphereFlux
  convert reference_sphere_density_integral (k+1) (by omega) using 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : ‖(x : ComplexEuclidean (k+1))‖ = 1 := by
    simpa only [mem_sphere_iff_norm, sub_zero] using x.property
  rw [reference_boundary_density hx]
  simp

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereDensityRestriction
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
namespace Mahler

/-- Pointwise adapted tangent frames suffice; no global tangent frame is
chosen or assumed continuous. -/
theorem exists_outward_tangent_frame {k : ℕ} {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) :
    ∃ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) ∧ sphereVolume k (Matrix.vecCons x v) = 1 := by
  obtain ⟨L,hL⟩ := exists_unitary_referencePole hx
  refine ⟨L ∘ poleFrameFin k, ?_, ?_⟩
  · intro i
    rw [← hL]
    exact (unitary_real_inner L _ _).trans
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (poleFrameVector_tangent _))
  · have he : Matrix.vecCons x (L ∘ poleFrameFin k) =
        L ∘ Matrix.vecCons (referencePole k) (poleFrameFin k) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simpa [Matrix.vecCons] using hL.symm
    rw [he, sphereVolume_unitary, poleFrameFin_volume]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousSphereIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric

namespace Mahler

lemma boundaryFormFin_smul {k : ℕ}
    (a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ) (c : ℝ)
    (x : ComplexEuclidean (k+1)) :
    boundaryFormFin (c • a) x = (c : ℂ)^(k+1) • boundaryFormFin a x := by
  have ho : (oneForm (c • a) x).toAlternatingMap = (c : ℂ) • (oneForm a x).toAlternatingMap := by
    ext v
    simp [oneForm_apply, Complex.real_smul]
  have hd : (extDeriv (oneForm (c • a)) x).toAlternatingMap =
      (c : ℂ) • (extDeriv (oneForm a) x).toAlternatingMap := by
    rw [oneForm_smul, extDeriv_smul]
    ext v
    simp [Complex.real_smul]
  unfold boundaryFormFin
  rw [ho, hd, wedgePower_smul, wedge_smul_left, wedge_smul_right, smul_smul, ← pow_succ']
  ext v
  rfl

lemma alphaPath_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ) :
    alphaPath f g m 0 = (m : ℝ) • dcLinear (logTau g) := by
  funext x
  simp [alphaPath]
  exact zero_smul ℝ (betaLinear f g m x)

lemma alphaPath_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → E → ℂ) (g : κ → E → ℂ) (m : ℕ) :
    alphaPath f g m 1 = dcLinear (logTau f) := by
  funext x
  simp [alphaPath, betaLinear]

theorem homogeneousPathFlux_zero (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) :
    homogeneousPathFlux k N m G 0 = (Real.pi * (m : ℝ))^(k+1) := by
  unfold homogeneousPathFlux sphereFlux
  simp only [alphaPath_zero, boundaryFormFin_smul]
  have he : (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      (orientedDensity (sphereFrame k) (sphereVolume k)
        ((↑(m : ℝ) : ℂ)^(k+1) • boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x).re) =
      (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 =>
        (m : ℝ)^(k+1) * (orientedDensity (sphereFrame k) (sphereVolume k)
          (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1)))) x) x).re) := by
    funext x
    rw [orientedDensity_smul, ← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, integral_const_mul]
  change (m : ℝ)^(k+1) * sphereFlux k (boundaryFormFin (dcLinear (logTau (coordinateMap (k+1))))) = _
  rw [reference_boundary_flux, mul_pow, mul_comm]

lemma homogeneousPathFlux_one (k N m : ℕ)
    (G : Fin N → MvPolynomial (Fin (k+1)) ℂ) :
    homogeneousPathFlux k N m G 1 = homogeneousSphereFlux k N G := by
  simp only [homogeneousPathFlux, homogeneousSphereFlux, alphaPath_one]

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousDensityVariation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

lemma wedgePowerVariation_compLinearMap {T S : Type*}
    [AddCommGroup T] [Module ℝ T] [AddCommGroup S] [Module ℝ S]
    (L : S →ₗ[ℝ] T) (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    (wedgePowerVariation a da k).compLinearMap L =
      wedgePowerVariation (a.compLinearMap L) (da.compLinearMap L) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hadd {ι : Type} (A C : T [⋀^ι]→ₗ[ℝ] ℂ) :
        (A+C).compLinearMap L = A.compLinearMap L + C.compLinearMap L := by ext v; rfl
    simp only [wedgePowerVariation]
    have h1 := wedge_compLinearMap L da (wedgePower a k)
    have h2 := wedge_compLinearMap L a (wedgePowerVariation a da k)
    rw [wedgePower_compLinearMap] at h1
    rw [ih] at h2
    exact congrArg₂ (fun A B => A+B) h1 h2

/-- Pointwise parameter derivative of the actual oriented sphere density.
The horizontal term is eliminated; the residual is kept explicit. -/
theorem MassHypotheses.sphere_density_derivative {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    {x : ComplexEuclidean (k+1)} (hx : ‖x‖ = 1) (t : ℝ) :
    HasDerivAt
      (fun s => orientedDensity (sphereFrame k) (sphereVolume k)
        (boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s) x) x)
      (orientedDensity (sphereFrame k) (sphereVolume k)
        (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
          (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x) x) t := by
  obtain ⟨v,hv,hvol⟩ := exists_outward_tangent_frame hx
  let w : Fin 1 ⊕ WedgePowerSlots k → sphereTangent x := fun s =>
    ⟨v (boundaryFinEquiv k s), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hd := h.sphere_boundaryForm_derivative hxn t w
  have hval (B : ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ) :
      B v = orientedDensity (sphereFrame k) (sphereVolume k) B x := by
    simpa only [hvol, mul_one] using orientedDensity_spec (sphereFrame k)
      (sphereVolume k) (sphereVolume_frame_ne_zero k) B hx v hv
  have he : HasDerivAt
      (fun s => boundaryFormFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s) x v)
      (boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x v) t := by
    simp only [boundaryFormFin, boundaryResidualFin,
      AlternatingMap.domDomCongr_apply, tangentForm, ← wedgePower_compLinearMap,
      ← wedgePowerVariation_compLinearMap, ← wedge_compLinearMap,
      AlternatingMap.compLinearMap_apply, Submodule.subtype_apply, w, Function.comp_def] at hd ⊢
    convert hd using 1 <;> rfl
  simpa only [hval] using he

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereFluxDifferentiation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set Filter
open scoped Topology BigOperators

namespace Mahler

lemma continuousOn_orientedDensity {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ)
    {B : X → E [⋀^Fin d]→ₗ[ℝ] ℂ} {x : X → E} {K : Set X}
    (hB : ∀ v, ContinuousOn (fun p => B p v) K) (hx : ContinuousOn x K) :
    ContinuousOn (fun p => orientedDensity b Ω (B p) (x p)) K := by
  unfold orientedDensity
  apply ContinuousOn.div_const
  apply continuousOn_finsetSum
  intro i hi
  have hc : ContinuousOn (fun p => (b.repr (x p) i : ℂ)) K :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj i).continuous.comp_continuousOn (b.repr.continuous.comp_continuousOn hx))
  exact (hc.mul continuousOn_const).mul (hB _)

theorem sphereFlux_continuousOn {k : ℕ}
    {B : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ} {a b : ℝ}
    (hB : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)
      (Icc a b ×ˢ univ)) :
    ContinuousOn (fun s => sphereFlux k (B s)) (Icc a b) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  unfold sphereFlux
  apply CompactFluxDifferentiation.continuousOn_integral
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hB
      (continuous_subtype_val.comp continuous_snd).continuousOn)

theorem sphereFlux_continuous {k : ℕ}
    {B : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ}
    (hB : ∀ v, Continuous
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)) :
    Continuous (fun s => sphereFlux k (B s)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (sphereFlux_continuousOn (a := t-1) (b := t+1)
    (fun v => (hB v).continuousOn)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- A tangent-restricted pointwise calculation can be supplied directly as a
density derivative; no ambient extension of that derivative is required. -/
theorem sphereFlux_hasDerivAt_of_density {k : ℕ}
    {B D : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ} {a b t : ℝ}
    (hB : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hD : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => D p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      HasDerivAt (fun r => orientedDensity (sphereFrame k) (sphereVolume k) (B r x) x)
        (orientedDensity (sphereFrame k) (sphereVolume k) (D s x) x) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => sphereFlux k (B s)) (sphereFlux k (D t)) t := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  unfold sphereFlux
  apply CompactFluxDifferentiation.hasDerivAt_integral (a := a) (b := b)
    (G := fun s (x : sphere (0 : ComplexEuclidean (k+1)) 1) => (orientedDensity (sphereFrame k) (sphereVolume k) (D s x) x).re)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hB
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hD
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · intro s hs x
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs x)
  · exact ht

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousFluxDifferentiation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set Filter ContinuousAlternatingMap
open scoped Topology BigOperators

namespace Mahler

lemma contDiffAt_dcLinear_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {u : E → ℂ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

lemma continuous_sphere_oneForm {k : ℕ}
    {a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x) :
    Continuous (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 => a x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (ha x).continuousAt.comp continuous_subtype_val.continuousAt

lemma continuous_sphere_extDeriv {k : ℕ}
    {a : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x) :
    Continuous (fun x : sphere (0 : ComplexEuclidean (k+1)) 1 => extDeriv (oneForm a) x) := by
  rw [continuous_iff_continuousAt]
  intro x
  have ho : ContDiffAt ℝ 1 (oneForm a) (x : ComplexEuclidean (k+1)) :=
    (ofSubsingletonLIE (𝕜 := ℝ) (E := ComplexEuclidean (k+1)) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp (x : ComplexEuclidean (k+1)) (ha x)
  have hf : ContDiffAt ℝ 0 (fderiv ℝ (oneForm a)) (x : ComplexEuclidean (k+1)) :=
    ho.fderiv_right (by norm_num)
  exact ((alternatizeUncurryFinCLM ℝ (ComplexEuclidean (k+1)) ℂ).continuous.continuousAt.comp
    hf.continuousAt).comp continuous_subtype_val.continuousAt

lemma continuous_sphere_affine_oneForm_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin 1 → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      oneForm (a + p.1 • b) p.2 v) := by
  change Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
    a p.2 (v 0) + p.1 • b p.2 (v 0))
  exact ((continuous_sphere_oneForm ha).comp continuous_snd).clm_apply continuous_const |>.add
    (continuous_fst.smul (((continuous_sphere_oneForm hb).comp continuous_snd).clm_apply continuous_const))

lemma continuous_sphere_affine_extDeriv_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin 2 → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      extDeriv (oneForm (a + p.1 • b)) p.2 v) := by
  have he (p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1) :
      extDeriv (oneForm (a + p.1 • b)) p.2 v =
        extDeriv (oneForm a) p.2 v + p.1 • extDeriv (oneForm b) p.2 v := by
    rw [extDeriv_oneForm_affine ((ha p.2).differentiableAt (by norm_num))
      ((hb p.2).differentiableAt (by norm_num))]
    rfl
  simp_rw [he]
  exact ((continuous_eval_const v).comp ((continuous_sphere_extDeriv ha).comp continuous_snd)).add
    (continuous_fst.smul ((continuous_eval_const v).comp
      ((continuous_sphere_extDeriv hb).comp continuous_snd)))

lemma continuous_wedgePowerVariation_eval {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [TopologicalSpace X] {a b : X → E [⋀^Fin 2]→ₗ[ℝ] ℂ}
    (ha : ∀ v, Continuous (fun p => a p v))
    (hb : ∀ v, Continuous (fun p => b p v)) (k : ℕ)
    (v : WedgePowerSlots k → E) :
    Continuous (fun p => wedgePowerVariation (a p) (b p) k v) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    exact (continuous_wedge_eval hb (continuous_wedgePower_eval ha k) _).add
      (continuous_wedge_eval ha ih _)

lemma continuous_sphere_affine_boundary_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      boundaryFormFin (a + p.1 • b) p.2 v) := by
  unfold boundaryFormFin
  simp only [AlternatingMap.domDomCongr_apply]
  apply continuous_wedge_eval
  · exact continuous_sphere_affine_oneForm_eval ha hb
  · exact continuous_wedgePower_eval (continuous_sphere_affine_extDeriv_eval ha hb) k

lemma continuous_sphere_affine_residual_eval {k : ℕ}
    {a b : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) →L[ℝ] ℂ}
    (ha : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 a x)
    (hb : ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ContDiffAt ℝ 1 b x)
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      boundaryResidualFin (a + p.1 • b) b p.2 v) := by
  unfold boundaryResidualFin
  simp only [AlternatingMap.domDomCongr_apply]
  apply continuous_wedge_eval
  · exact continuous_sphere_affine_oneForm_eval ha hb
  · apply continuous_wedgePowerVariation_eval (continuous_sphere_affine_extDeriv_eval ha hb)
    intro w
    change Continuous (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 =>
      extDeriv (oneForm b) p.2 w)
    exact (continuous_eval_const w).comp ((continuous_sphere_extDeriv hb).comp continuous_snd)

lemma MassHypotheses.homogeneous_path_C1 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    (∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 1 ((m : ℝ) • dcLinear (logTau (coordinateMap (k+1)))) x) ∧
    (∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 1 (betaLinear (polynomialMap G) (coordinateMap (k+1)) m) x) := by
  have hg (x : sphere (0 : ComplexEuclidean (k+1)) 1) :
      ContDiffAt ℝ 1 (dcLinear (logTau (polynomialMap G))) (x : ComplexEuclidean (k+1)) := by
    have hx : (x : ComplexEuclidean (k+1)) ≠ 0 := by
      intro hx
      have := x.property
      simp [hx] at this
    exact contDiffAt_dcLinear_one (contDiffAt_logTau_of_open isOpen_univ (mem_univ _)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
      (tau_pos_of_component_ne_zero (h.leading_nonzero x hx)))
  have h0 (x : sphere (0 : ComplexEuclidean (k+1)) 1) :
      ContDiffAt ℝ 1 ((m : ℝ) • dcLinear (logTau (coordinateMap (k+1))))
        (x : ComplexEuclidean (k+1)) := by
    have hx : (x : ComplexEuclidean (k+1)) ≠ 0 := by
      intro hx
      have := x.property
      simp [hx] at this
    exact (contDiffAt_dcLinear_one (contDiffAt_logTau_of_open isOpen_univ (mem_univ _)
      (fun j => (coordinateMap_differentiable (k+1) j).differentiableOn)
      (coordinateMap_tau_pos hx))).const_smul (m : ℝ)
  exact ⟨h0, fun x => (hg x).sub (h0 x)⟩

/-- The homogeneous flux has the residual flux as derivative,
from the mass hypotheses. No integral regularity premise remains.
The residual integral is retained; this theorem does not assert it is zero. -/
theorem MassHypotheses.homogeneousPathFlux_hasDerivAt {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (t : ℝ) :
    HasDerivAt (homogeneousPathFlux k N m G)
      (sphereFlux k (boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))) t := by
  obtain ⟨ha, hb⟩ := h.homogeneous_path_C1
  unfold homogeneousPathFlux
  apply sphereFlux_hasDerivAt_of_density (a := t-1) (b := t+1)
    (D := fun s => boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+1)) m s)
      (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))
  · intro v
    exact (continuous_sphere_affine_boundary_eval ha hb v).continuousOn
  · intro v
    exact (continuous_sphere_affine_residual_eval ha hb v).continuousOn
  · intro s hs x
    exact h.sphere_density_derivative (by
      simpa only [mem_sphere_iff_norm, sub_zero] using x.property) s
  · constructor <;> linarith

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousFluxFTC
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set Filter
open scoped Topology

namespace Mahler

/-- The residual flux is continuous on the entire parameter line. -/
theorem MassHypotheses.homogeneousResidualFlux_continuous {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Continuous (fun t => sphereFlux k (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+1)) m))) := by
  obtain ⟨ha, hb⟩ := h.homogeneous_path_C1
  exact sphereFlux_continuous (continuous_sphere_affine_residual_eval ha hb)

/-- A finite, integrated variation formula for the literal homogeneous path.
This supplies endpoint control as well as the pointwise derivative. The exact
residual integral is not replaced by zero. -/
theorem MassHypotheses.homogeneousPathFlux_sub_eq_integral {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (a b : ℝ) :
    homogeneousPathFlux k N m G b - homogeneousPathFlux k N m G a =
      ∫ t in a..b, sphereFlux k (boundaryResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+1)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+1)) m)) := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => h.homogeneousPathFlux_hasDerivAt t)
    (h.homogeneousResidualFlux_continuous.intervalIntegrable a b)).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HomogeneousTransgressionFTC
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric
open scoped Topology

noncomputable section
namespace Mahler

/-- The fundamental theorem of calculus with an explicit local transgression formula.
The local algebraic identity is retained as a conditional premise. -/
theorem MassHypotheses.homogeneousPathFlux_constant_of_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (ht : ∀ (t : ℝ) (x : ComplexEuclidean (k+2)), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v)
    (a b : ℝ) : homogeneousPathFlux (k+1) N m G b = homogeneousPathFlux (k+1) N m G a := by
  have he := h.homogeneousPathFlux_sub_eq_integral (k := k+1) a b
  have hz (t : ℝ) := h.homogeneousResidualFlux_eq_zero_of_transgression_eq t (ht t)
  simp_rw [hz] at he
  exact sub_eq_zero.mp (by simpa using he)

/-- Both flux endpoints follow from the explicit local formula.
This theorem retains the local transgression identity as a hypothesis. -/
theorem MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq_oai {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (ht : ∀ (t : ℝ) (x : ComplexEuclidean (k+2)), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
    homogeneousSphereFlux (k+1) N G = (Real.pi * (m : ℝ))^(k+2) ∧
    Filter.Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
      (nhdsWithin 0 (Ioi 0)) (nhds ((Real.pi * (m : ℝ))^(k+2))) := by
  have hv : homogeneousSphereFlux (k+1) N G = (Real.pi * (m : ℝ))^(k+2) := by
    simpa only [homogeneousPathFlux_one, homogeneousPathFlux_zero] using
      h.homogeneousPathFlux_constant_of_transgression ht 0 1
  exact ⟨hv, by simpa only [hv] using h.small_sphere_real_flux_limit_eq (k := k+1)⟩

end Mahler

end

end OAI
end

theorem solution : type_of% @OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq_oai := @OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq_oai
