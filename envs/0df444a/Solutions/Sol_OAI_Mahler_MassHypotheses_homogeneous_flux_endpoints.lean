-- Prove2me | solution 1 for OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:43:12.60273+00:00
-- url     : https://prove2.me/submissions/14cbc5e0-3096-4d89-bebb-355c65a521e2

import Mathlib
import Definitions.Def_OAISMh000
import Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneousFlux_endpoints_of_transgression

section
-- module Solutions.OAIS_Mahler.Mahler_HolomorphicRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_Hessian
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_ExteriorFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_HorizontalForms
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_WedgeAlgebra
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped TensorProduct

namespace Mahler
variable {T : Type*} [AddCommGroup T] [Module ℝ T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

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
-- module Solutions.OAIS_Mahler.Mahler_CovectorVolume
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

lemma covectorVolume_reindex_apply (l : ι → T →ₗ[ℝ] ℂ) (e : κ ≃ ι) (v : κ → T) :
    covectorVolume (l ∘ e) v = covectorVolume l (v ∘ e.symm) := by
  rw [covectorVolume_apply, covectorVolume_apply]
  convert (Matrix.det_submatrix_equiv_self e (fun i j => l j (v (e.symm i)))) using 1 <;>
    first | rfl | (congr 1; ext i j; change _ = l (e j) (v (e.symm (e i))); simp)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeDecomposition
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι : Type*} [AddCommGroup T] [Module ℝ T]
  [Fintype J] [Fintype ι] [DecidableEq ι]

lemma multilinear_basis_expansion (b : Module.Basis J ℝ T)
    (a : MultilinearMap ℝ (fun _ : ι => T) ℂ) :
    a = ∑ q : ι → J, a (b ∘ q) •
      ((MultilinearMap.mkPiAlgebra ℝ ι ℂ).compLinearMap (complexCoord b ∘ q)) := by
  classical
  ext v
  calc
    a v = a (fun i => ∑ j, b.repr (v i) j • b j) := by
      congr 1
      funext i
      exact (b.sum_repr (v i)).symm
    _ = ∑ q : ι → J, (∏ i, b.repr (v i) (q i)) • a (b ∘ q) := by
      rw [a.map_sum]
      simp only [MultilinearMap.map_smul_univ, Function.comp_def]
    _ = _ := by
      simp only [sum_apply, smul_apply, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, Function.comp_apply, complexCoord_apply]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Complex.real_smul, Complex.ofReal_prod]
      ring
/-- Every finite-dimensional form is an explicit finite sum of simple forms.
The factorial is retained, matching the unnormalized alternatization. -/
theorem alternating_basis_expansion (b : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) :
    (Fintype.card ι).factorial • a =
      ∑ q : ι → J, a (b ∘ q) • covectorVolume (complexCoord b ∘ q) := by
  have hs (c : ℂ) (f : MultilinearMap ℝ (fun _ : ι => T) ℂ) :
      MultilinearMap.alternatization (c • f) = c • MultilinearMap.alternatization f := by
    ext v
    simp only [MultilinearMap.alternatization_apply, smul_apply,
      MultilinearMap.domDomCongr_apply, AlternatingMap.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    exact smul_comm _ _ _
  have h := congrArg MultilinearMap.alternatization
    (multilinear_basis_expansion b a.toMultilinearMap)
  simpa only [AlternatingMap.coe_alternatization, map_sum,
    hs, covectorVolume, AlternatingMap.coe_multilinearMap] using h

theorem alternating_basis_expansion_normalized (b : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) :
    a = ∑ q : ι → J, (a (b ∘ q) / (Fintype.card ι).factorial) •
      covectorVolume (complexCoord b ∘ q) := by
  have hf : ((Fintype.card ι).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card ι)
  have h := congrArg (fun A : T [⋀^ι]→ₗ[ℝ] ℂ =>
    (((Fintype.card ι).factorial : ℂ)⁻¹) • A) (alternating_basis_expansion b a)
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hf, one_smul] at h
  simpa only [Finset.smul_sum, smul_smul, div_eq_mul_inv, mul_comm] using h

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeAssociativity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι κ ν : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

lemma domDomCongr_sum {A B Q : Type*} [Fintype Q] (e : A ≃ B)
    (f : Q → T [⋀^A]→ₗ[ℝ] ℂ) :
    (∑ q, f q).domDomCongr e = ∑ q, (f q).domDomCongr e := by
  exact map_sum (AlternatingMap.domDomCongrₗ ℂ e) f Finset.univ

lemma covectorVolume_domDomCongr (l : ι → T →ₗ[ℝ] ℂ) (e : ι ≃ κ) :
    (covectorVolume l).domDomCongr e = covectorVolume (l ∘ e.symm) := by
  ext v
  simpa only [AlternatingMap.domDomCongr_apply, Equiv.symm_symm] using
    (covectorVolume_reindex_apply l e.symm v).symm

/-- Associativity of the actual shuffle product, with the ordered slot
reassociation made explicit. -/
theorem wedge_assoc (basis : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) (c : T [⋀^ν]→ₗ[ℝ] ℂ) :
    (wedge (wedge a b) c).domDomCongr (Equiv.sumAssoc ι κ ν) = wedge a (wedge b c) := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b,
    alternating_basis_expansion_normalized basis c]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    domDomCongr_sum, AlternatingMap.domDomCongr_smul, wedge_covectorVolume, Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  rcases i with i | i | i <;> rfl

/-- Swapping blocks means reindexing by the actual block swap; signs arise
when both sides are subsequently put into the same Fin order. -/
theorem wedge_swap (basis : Module.Basis J ℝ T)
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).domDomCongr (Equiv.sumComm ι κ) = wedge b a := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    domDomCongr_sum, AlternatingMap.domDomCongr_smul, wedge_covectorVolume, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_comm]
  congr 1
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  cases i <;> rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeOne
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]

lemma covectorVolume_cons_apply {n : ℕ} (a : T →ₗ[ℝ] ℂ)
    (l : Fin n → T →ₗ[ℝ] ℂ) (v : Fin (n+1) → T) :
    covectorVolume (Fin.cons a l) v =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val * a (v i) * covectorVolume l (i.removeNth v) := by
  rw [covectorVolume_apply]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [covectorVolume_apply]
  congr 2

lemma covectorVolume_prepend {n : ℕ} (a : T →ₗ[ℝ] ℂ)
    (l : Fin n → T →ₗ[ℝ] ℂ) :
    (covectorVolume (Sum.elim (fun _ : Fin 1 => a) l)).domDomCongr (prependFinEquiv n) =
      covectorVolume (Fin.cons a l) := by
  rw [covectorVolume_domDomCongr]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [prependFinEquiv]
  · simp [prependFinEquiv]

lemma alternating_sum_eval {Q ι : Type*} (s : Finset Q)
    (f : Q → T [⋀^ι]→ₗ[ℝ] ℂ) (v : ι → T) :
    (∑ q ∈ s, f q) v = ∑ q ∈ s, f q v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AlternatingMap.zero_apply]
  | @insert q s hq ih =>
    simp only [Finset.sum_insert hq, AlternatingMap.add_apply, ih]

/-- One-form wedge evaluation in standard Fin order, with the unnormalized
exterior-derivative signs. -/
theorem wedge_one_eval (basis : Module.Basis J ℝ T) {n : ℕ}
    (a : T →ₗ[ℝ] ℂ) (B : T [⋀^Fin n]→ₗ[ℝ] ℂ) (v : Fin (n+1) → T) :
    (wedge (covectorVolume (fun _ : Fin 1 => a)) B).domDomCongr (prependFinEquiv n) v =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val * a (v i) * B (i.removeNth v) := by
  rw [alternating_basis_expansion_normalized basis B]
  simp only [wedge_sum_right, wedge_smul_right, domDomCongr_sum,
    AlternatingMap.domDomCongr_smul, wedge_covectorVolume, covectorVolume_prepend]
  simp only [alternating_sum_eval, AlternatingMap.smul_apply,
    covectorVolume_cons_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro q hq
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeEven
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {T J ι κ ν : Type*} [AddCommGroup T] [Module ℝ T] [Fintype J]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

lemma wedge_reindex (basis : Module.Basis J ℝ T)
    {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (e : ι ≃ ι') (f : κ ≃ κ')
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    (wedge a b).domDomCongr (Equiv.sumCongr e f) =
      wedge (a.domDomCongr e) (b.domDomCongr f) := by
  rw [alternating_basis_expansion_normalized basis a,
    alternating_basis_expansion_normalized basis b]
  simp only [domDomCongr_sum, AlternatingMap.domDomCongr_smul,
    wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    wedge_covectorVolume, Finset.smul_sum, smul_smul, covectorVolume_domDomCongr]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  funext i
  cases i <;> rfl

/-- The swap of two two-slot blocks has positive sign. -/
lemma two_block_swap_sign : Equiv.Perm.sign (Equiv.sumComm (Fin 2) (Fin 2)) = 1 := by
  decide

lemma wedge_two_comm (basis : Module.Basis J ℝ T)
    (a b : T [⋀^Fin 2]→ₗ[ℝ] ℂ) : wedge a b = wedge b a := by
  have h := wedge_swap basis a b
  rw [AlternatingMap.domDomCongr_perm, two_block_swap_sign, one_smul] at h
  exact h

/-- Two degree-two factors commute in their original nested slot order. -/
lemma wedge_two_left_comm (basis : Module.Basis J ℝ T)
    (a b : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (c : T [⋀^ν]→ₗ[ℝ] ℂ) :
    wedge a (wedge b c) = wedge b (wedge a c) := by
  rw [← wedge_assoc basis, ← wedge_assoc basis, wedge_two_comm basis a b]

lemma wedge_add_left (a a' : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (a+a') b = wedge a b + wedge a' b := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply, TensorProduct.add_tmul,
    map_add, LinearMap.compAlternatingMap_add]

lemma wedge_add_right (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b b' : T [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge a (b+b') = wedge a b + wedge a b' := by
  simp only [wedge, ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_add,
    map_add, LinearMap.compAlternatingMap_add]

/-- The k+1 genuine variation placements are equal, with no suppressed signs
or reassociations. This is the multiplicity in homogeneous transgression. -/
theorem wedgePowerVariation_succ (basis : Module.Basis J ℝ T)
    (a da : T [⋀^Fin 2]→ₗ[ℝ] ℂ) (k : ℕ) :
    wedgePowerVariation a da (k+1) =
      ((k+1 : ℕ) : ℂ) • wedge da (wedgePower a k) := by
  induction k with
  | zero =>
    have hz : wedge a (0 : T [⋀^WedgePowerSlots 0]→ₗ[ℝ] ℂ) = 0 := by
      have h := wedge_smul_right 0 a (0 : T [⋀^WedgePowerSlots 0]→ₗ[ℝ] ℂ)
      simpa only [zero_smul] using h
    have hzero : wedgePowerVariation a da (0+1) = wedge da (wedgePower a 0) := by
      change wedge da (wedgePower a 0) + wedge a 0 = wedge da (wedgePower a 0)
      rw [hz, add_zero]
    rw [hzero]
    simp only [Nat.cast_one, zero_add, one_smul]
    rfl
  | succ k ih =>
    have hc : wedge a (wedge da (wedgePower a k)) =
        wedge da (wedge a (wedgePower a k)) :=
      wedge_two_left_comm basis a da (wedgePower a k)
    have hdec : (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) =
        wedgePowerSlotsDecidableEq (k+1) := Subsingleton.elim _ _
    have hfin : (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) =
        wedgePowerSlotsFintype (k+1) := Subsingleton.elim _ _
    let B : T [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ := wedge da (wedgePower a k)
    have hc' : wedge a B =
        wedge da (wedgePower a (k+1)) := by
      dsimp only [B, wedgePower]
      rw [← hdec]
      exact hc
    change wedge da (wedgePower a (k+1)) + wedge a (wedgePowerVariation a da (k+1)) =
      ((k+1+1 : ℕ) : ℂ) • wedge da (wedgePower a (k+1))
    calc
      _ = wedge da (wedgePower a (k+1)) +
          ((k+1 : ℕ) : ℂ) • wedge a B := by
        exact congrArg (fun D : T [⋀^Fin 2 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          wedge da (wedgePower a (k+1)) + D)
          ((congrArg (fun C : T [⋀^WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ => wedge a C) ih).trans
            (wedge_smul_right _ a B))
      _ = wedge da (wedgePower a (k+1)) +
          ((k+1 : ℕ) : ℂ) • wedge da (wedgePower a (k+1)) := by
        exact congrArg (fun B : T [⋀^Fin 2 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
          wedge da (wedgePower a (k+1)) + ((k+1 : ℕ) : ℂ) • B) hc'
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        module

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_BasisContinuousWedge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma basisContinuousWedge_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (basis : Module.Basis J ℝ E)
    (A : E [⋀^ι]→L[ℝ] ℂ) (B : E [⋀^κ]→L[ℝ] ℂ) :
    (basisContinuousWedge basis A B).toAlternatingMap = wedge A.toAlternatingMap B.toAlternatingMap := by
  rw [alternating_basis_expansion_normalized basis A.toAlternatingMap,
    alternating_basis_expansion_normalized basis B.toAlternatingMap]
  simp only [wedge_sum_left, wedge_sum_right, wedge_smul_left, wedge_smul_right,
    wedge_covectorVolume, Finset.smul_sum, smul_smul]
  unfold basisContinuousWedge
  ext v
  simp only [ContinuousAlternatingMap.sum_apply, alternating_sum_eval,
    continuousCovectorVolume, ContinuousAlternatingMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  ring_nf
  rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ContinuousWedgeDerivative
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma differentiableAt_formCoefficient [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] {A : E → E [⋀^ι]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : ι → E) (c : ℂ) :
    DifferentiableAt ℝ (fun y => A y v / c) x := by
  simpa only [div_eq_mul_inv, Function.comp_def, ContinuousAlternatingMap.apply_apply] using
    ((ContinuousAlternatingMap.apply ℝ E ℂ v).differentiableAt.comp x hA).mul_const c⁻¹

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] in
lemma fderiv_formCoefficient [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [DecidableEq ι] {A : E → E [⋀^ι]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : ι → E) (c : ℂ) (u : E) :
    fderiv ℝ (fun y => A y v / c) x u = fderiv ℝ A x u v / c := by
  have h := ((ContinuousAlternatingMap.apply ℝ E ℂ v).hasFDerivAt.comp x
    hA.hasFDerivAt).mul_const c⁻¹
  simpa only [div_eq_mul_inv, Function.comp_def, ContinuousAlternatingMap.apply_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_comm] using
    congrArg (fun L : E →L[ℝ] ℂ => L u) h.fderiv

lemma differentiableAt_basisContinuousWedge (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^ι]→L[ℝ] ℂ} {B : E → E [⋀^κ]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x := by
  unfold basisContinuousWedge
  exact DifferentiableAt.fun_sum (fun q _ => DifferentiableAt.fun_sum (fun r _ =>
    ((differentiableAt_formCoefficient hA _ _).mul
      (differentiableAt_formCoefficient hB _ _)).smul_const _))

/-- The Frechet product rule for the continuous, actual shuffle wedge. -/
theorem fderiv_basisContinuousWedge (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^ι]→L[ℝ] ℂ} {B : E → E [⋀^κ]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (u : E) :
    fderiv ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x u =
      basisContinuousWedge basis (fderiv ℝ A x u) (B x) +
      basisContinuousWedge basis (A x) (fderiv ℝ B x u) := by
  have hc (q : ι → J) (r : κ → J) :=
    ((differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ)).mul
      (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))).smul_const
        (continuousCovectorVolume (Sum.elim (complexCoord basis ∘ q) (complexCoord basis ∘ r)))
  simp only [Pi.mul_apply] at hc
  unfold basisContinuousWedge
  rw [fderiv_fun_sum (u := Finset.univ) (fun q _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun r _ => hc q r))]
  simp only [_root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fderiv_fun_sum (u := Finset.univ) (fun r _ => hc q r)]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  have hm := (differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ)).mul
    (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))
  change DifferentiableAt ℝ (fun y =>
    (A y (basis ∘ q) / ((Fintype.card ι).factorial : ℂ)) *
    (B y (basis ∘ r) / ((Fintype.card κ).factorial : ℂ))) x at hm
  rw [fderiv_smul_const hm]
  rw [fderiv_fun_mul (differentiableAt_formCoefficient hA (basis ∘ q) ((Fintype.card ι).factorial : ℂ))
    (differentiableAt_formCoefficient hB (basis ∘ r) ((Fintype.card κ).factorial : ℂ))]
  simp only [ContinuousLinearMap.smulRight_apply, _root_.add_apply,
    _root_.smul_apply, fderiv_formCoefficient hA,
    fderiv_formCoefficient hB, smul_eq_mul, add_smul]
  rw [add_comm]
  congr 1 ; congr 1 ; ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorDirectional
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
/-- The actual exterior derivative is the sum of coordinate one-forms wedged
with directional derivatives. No Leibniz rule is assumed. -/
theorem extDeriv_directional [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (basis : Module.Basis J ℝ E) {n : ℕ}
    {A : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E} (hA : DifferentiableAt ℝ A x) :
    (extDeriv A x).toAlternatingMap =
      ∑ j : J, (wedge (covectorVolume (fun _ : Fin 1 => complexCoord basis j))
        (fderiv ℝ A x (basis j)).toAlternatingMap).domDomCongr (prependFinEquiv n) := by
  ext v
  simp only [alternating_sum_eval, wedge_one_eval basis, complexCoord_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [extDeriv_apply hA, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he : fderiv ℝ (fun y => A y (i.removeNth v)) x (v i) =
      fderiv ℝ A x (v i) (i.removeNth v) := by
    exact congrArg (fun L : E →L[ℝ] ℂ => L (v i))
      ((ContinuousAlternatingMap.apply ℝ E ℂ (i.removeNth v)).hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  rw [he]
  conv_lhs => rw [← basis.sum_repr (v i)]
  simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, Complex.real_smul, Finset.smul_sum, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceHomogeneous
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousDeformation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SphereForms
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_NormExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_WedgeTwoDifferentialAlgebra
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

lemma twoOnePermutation_sign : Equiv.Perm.sign twoOnePermutation = 1 := by decide

lemma wedge_two_one_fin (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ) (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) :
    (wedge A a).domDomCongr finSumFinEquiv =
      (wedge a A).domDomCongr finSumFinEquiv := by
  have h := congrArg (fun C : E [⋀^Fin 1 ⊕ Fin 2]→ₗ[ℝ] ℂ =>
    C.domDomCongr finSumFinEquiv) (wedge_swap basis A a)
  rw [← AlternatingMap.domDomCongr_trans] at h
  have he : (Equiv.sumComm (Fin 2) (Fin 1)).trans finSumFinEquiv =
      (finSumFinEquiv (m := 2) (n := 1)).trans twoOnePermutation := by
    ext i
    simp [twoOnePermutation]
  rw [he, AlternatingMap.domDomCongr_trans, AlternatingMap.domDomCongr_perm,
    twoOnePermutation_sign, one_smul] at h
  exact h

lemma wedge_derivative_assoc (basis : Module.Basis J ℝ E) {n : ℕ}
    (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (B : E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (wedge a ((wedge A B).domDomCongr finSumFinEquiv)).domDomCongr
        (prependFinEquiv (2+n)) =
      (wedge ((wedge a A).domDomCongr (prependFinEquiv 2)) B).domDomCongr
        (derivativeLeftEquiv n) := by
  have h1 := wedge_reindex basis (Equiv.refl (Fin 1))
    (finSumFinEquiv (m := 2) (n := n)) a (wedge A B)
  have h2 := wedge_reindex basis (prependFinEquiv 2) (Equiv.refl (Fin n))
    (wedge a A) B
  simp only [AlternatingMap.domDomCongr_refl] at h1 h2
  rw [← h1, ← h2, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i
  · fin_cases i ; rfl
  · fin_cases i <;> rfl
  · simp [derivativeLeftEquiv, prependFinEquiv, finSumFinEquiv]
    omega

lemma wedge_derivative_move_two (basis : Module.Basis J ℝ E) {n : ℕ}
    (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (B : E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (wedge a ((wedge A B).domDomCongr finSumFinEquiv)).domDomCongr
        (prependFinEquiv (2+n)) =
      (wedge A ((wedge a B).domDomCongr (prependFinEquiv n))).domDomCongr
        (derivativeRightEquiv n) := by
  rw [wedge_derivative_assoc basis]
  have hp : prependFinEquiv 2 = (finSumFinEquiv (m := 1) (n := 2)) := by
    ext i
    cases i with
    | inl i => fin_cases i; rfl
    | inr i => fin_cases i <;> rfl
  rw [hp, ← wedge_two_one_fin basis]
  have h1 := wedge_reindex basis (finSumFinEquiv (m := 2) (n := 1))
    (Equiv.refl (Fin n)) (wedge A a) B
  have h2 := wedge_reindex basis (Equiv.refl (Fin 2)) (prependFinEquiv n) A (wedge a B)
  simp only [AlternatingMap.domDomCongr_refl] at h1 h2
  rw [← h1, ← h2, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i
  · fin_cases i <;> rfl
  · fin_cases i ; rfl
  · change 3 + i.val = 2 + (i.val + 1)
    omega

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorLeibnizTwo
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

@[simp] lemma continuousWedgeFin_toAlternatingMap (basis : Module.Basis J ℝ E) {p q : ℕ}
    (A : E [⋀^Fin p]→L[ℝ] ℂ) (B : E [⋀^Fin q]→L[ℝ] ℂ) :
    (continuousWedgeFin basis A B).toAlternatingMap =
      (wedge A.toAlternatingMap B.toAlternatingMap).domDomCongr finSumFinEquiv := by
  rw [continuousWedgeFin, continuousReindex_toAlternatingMap, basisContinuousWedge_toAlternatingMap]

lemma differentiableAt_continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    {A : E → E [⋀^Fin p]→L[ℝ] ℂ} {B : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    DifferentiableAt ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x :=
  (continuousReindex finSumFinEquiv).differentiableAt.comp x
    (differentiableAt_basisContinuousWedge basis hA hB)

lemma fderiv_continuousWedgeFin (basis : Module.Basis J ℝ E) {p q : ℕ}
    {A : E → E [⋀^Fin p]→L[ℝ] ℂ} {B : E → E [⋀^Fin q]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (u : E) :
    fderiv ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x u =
      continuousWedgeFin basis (fderiv ℝ A x u) (B x) +
      continuousWedgeFin basis (A x) (fderiv ℝ B x u) := by
  have h := (continuousReindex (E := E) (finSumFinEquiv (m := p) (n := q))).hasFDerivAt.comp x
    (differentiableAt_basisContinuousWedge basis hA hB).hasFDerivAt
  have he := congrArg (fun L => L u) h.fderiv
  change fderiv ℝ (fun y => continuousWedgeFin basis (A y) (B y)) x u =
    continuousReindex finSumFinEquiv
      (fderiv ℝ (fun y => basisContinuousWedge basis (A y) (B y)) x u) at he
  rw [he, fderiv_basisContinuousWedge basis hA hB, map_add]
  rfl

/-- Exterior Leibniz rule for an actual two-form times an arbitrary-degree
form. The sign is positive because the left degree is two. -/
theorem extDeriv_continuousWedge_two (basis : Module.Basis J ℝ E) {n : ℕ}
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {B : E → E [⋀^Fin n]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    (extDeriv (fun y => continuousWedgeFin basis (A y) (B y)) x).toAlternatingMap =
      (wedge (extDeriv A x).toAlternatingMap (B x).toAlternatingMap).domDomCongr
        (derivativeLeftEquiv n) +
      (wedge (A x).toAlternatingMap (extDeriv B x).toAlternatingMap).domDomCongr
        (derivativeRightEquiv n) := by
  rw [extDeriv_directional basis (differentiableAt_continuousWedgeFin basis hA hB),
    extDeriv_directional basis hA, extDeriv_directional basis hB]
  simp only [fderiv_continuousWedgeFin basis hA hB,
    ContinuousAlternatingMap.toAlternatingMap_add, continuousWedgeFin_toAlternatingMap,
    wedge_add_right, AlternatingMap.domDomCongr_add, Finset.sum_add_distrib,
    wedge_sum_left, wedge_sum_right, domDomCongr_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact wedge_derivative_assoc basis _ _ _
  · apply Finset.sum_congr rfl
    intro j hj
    exact wedge_derivative_move_two basis _ _ _

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousSmoothForms
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The required local smoothness follows from the literal holomorphic data,
for every finite order, wherever tau is positive. -/
lemma contDiffAt_logTau_order [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {U : Set E} {x : E}
    (q : ℕ) (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (ht : 0 < tau f x) :
    ContDiffAt ℝ q (logTau f) x := by
  have hc (j : ι) : ContDiffAt ℝ q (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU q (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  have he : ContDiffAt ℝ q (energy f) x := by
    apply ContDiffAt.sum
    intro j hj
    exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := q) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht)).restrict_scalars ℝ).comp x he

lemma contDiffAt_dcLinear_order {u : E → ℂ} {x : E} (q : ℕ)
    (hu : ContDiffAt ℝ (q+1) u x) : ContDiffAt ℝ q (dcLinear u) x := by
  have hd : ContDiffAt ℝ q (fderiv ℝ u) x := hu.fderiv_right (by norm_cast)
  exact (hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_oneForm_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a : E → E →L[ℝ] ℂ} {x : E} (q : ℕ)
    (ha : ContDiffAt ℝ q a x) : ContDiffAt ℝ q (oneForm a) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp x ha

theorem MassHypotheses.alpha_beta_contDiffAt {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) (q : ℕ) :
    ContDiffAt ℝ q (alphaPath (polynomialMap G) (coordinateMap n) m t) z ∧
    ContDiffAt ℝ q (betaLinear (polynomialMap G) (coordinateMap n) m) z := by
  have hg := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (polynomialMap_differentiable G j).differentiableOn)
    (tau_pos_of_component_ne_zero (h.leading_nonzero z hz)))
  have h0 := contDiffAt_dcLinear_order q (contDiffAt_logTau_order (q+1)
    isOpen_univ (Set.mem_univ z)
    (fun j => (coordinateMap_differentiable n j).differentiableOn)
    (coordinateMap_tau_pos hz))
  have hb := hg.sub (h0.const_smul (m : ℝ))
  exact ⟨(h0.const_smul (m : ℝ)).add (hb.const_smul t), hb⟩

/-- The d squared term vanishes along the homogeneous path; no
closedness or higher smoothness premise is added. -/
theorem MassHypotheses.alphaPath_extDeriv_extDeriv {n N m : ℕ}
    {U : Set (ComplexEuclidean n)} {f : Fin N → ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (h : MassHypotheses n N m U f G)
    {z : ComplexEuclidean n} (hz : z ≠ 0) (t : ℝ) :
    extDeriv (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap n) m t))) z = 0 := by
  apply extDeriv_extDeriv_apply
    (contDiffAt_oneForm_order 2 (h.alpha_beta_contDiffAt hz t 2).1)
  norm_num

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ClosedWedgePowers
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousReindex_finCongr_extDeriv [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {p q : ℕ} (h : p = q)
    (A : E → E [⋀^Fin p]→L[ℝ] ℂ) (x : E) :
    extDeriv (fun y => continuousReindex (finCongr h) (A y)) x =
      continuousReindex (finCongr (congrArg (·+1) h)) (extDeriv A x) := by
  subst q
  rfl

lemma basisContinuousWedgePower_toAlternatingMap (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (basisContinuousWedgePower basis A k).toAlternatingMap =
      (wedgePower A.toAlternatingMap k).domDomCongr (powerFinEquiv k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [basisContinuousWedgePower, continuousReindex_toAlternatingMap,
      continuousWedgeFin_toAlternatingMap, ih, powerFinEquiv]
    have he := wedge_reindex basis (Equiv.refl (Fin 2)) (powerFinEquiv k)
      A.toAlternatingMap (wedgePower A.toAlternatingMap k)
    simp only [AlternatingMap.domDomCongr_refl] at he
    rw [← he]
    rfl

lemma differentiableAt_basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (k : ℕ) :
    DifferentiableAt ℝ (fun y => basisContinuousWedgePower basis (A y) k) x := by
  induction k with
  | zero => exact differentiableAt_const _
  | succ k ih =>
    exact (continuousReindex (finCongr (by omega))).differentiableAt.comp x
      (differentiableAt_continuousWedgeFin basis hA ih)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_power_zero_right [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : E [⋀^ι]→ₗ[ℝ] ℂ) :
    wedge A (0 : E [⋀^κ]→ₗ[ℝ] ℂ) = 0 := by
  simpa only [zero_smul] using wedge_smul_right 0 A (0 : E [⋀^κ]→ₗ[ℝ] ℂ)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_power_zero_left [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : E [⋀^κ]→ₗ[ℝ] ℂ) :
    wedge (0 : E [⋀^ι]→ₗ[ℝ] ℂ) A = 0 := by
  simpa only [zero_smul] using wedge_smul_left 0 (0 : E [⋀^ι]→ₗ[ℝ] ℂ) A

/-- Every power of an actual closed differentiable two-form is closed. -/
theorem extDeriv_basisContinuousWedgePower (basis : Module.Basis J ℝ E)
    {A : E → E [⋀^Fin 2]→L[ℝ] ℂ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hclosed : extDeriv A x = 0) (k : ℕ) :
    extDeriv (fun y => basisContinuousWedgePower basis (A y) k) x = 0 := by
  induction k with
  | zero =>
    simp only [basisContinuousWedgePower, extDeriv, fderiv_fun_const]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
  | succ k ih =>
    change extDeriv (fun y => continuousReindex (finCongr (by omega))
      (continuousWedgeFin basis (A y) (basisContinuousWedgePower basis (A y) k))) x = 0
    rw [continuousReindex_finCongr_extDeriv]
    have he := extDeriv_continuousWedge_two basis hA
      (differentiableAt_basisContinuousWedgePower basis hA k)
    rw [hclosed, ih] at he
    simp only [ContinuousAlternatingMap.toAlternatingMap_zero, wedge_power_zero_left,
      wedge_power_zero_right, AlternatingMap.domDomCongr_zero, add_zero] at he
    have hz : extDeriv (fun y => continuousWedgeFin basis (A y)
        (basisContinuousWedgePower basis (A y) k)) x = 0 := by
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      exact he
    rw [hz, map_zero]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma contDiffAt_extDeriv_power_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {p : ℕ} {A : E → E [⋀^Fin p]→L[ℝ] ℂ}
    {x : E} (q : ℕ) (hA : ContDiffAt ℝ (q+1) A x) :
    ContDiffAt ℝ q (extDeriv A) x :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x
    (hA.fderiv_right (by norm_cast))

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousVariationCoefficient
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler

lemma wedge_wedgePowerVariation_succ {Space : Type*} [AddCommGroup Space]
    [Module ℝ Space] [FiniteDimensional ℝ Space]
    (leadingForm : Space [⋀^Fin 1]→ₗ[ℝ] ℂ) (form variation : Space [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (degree : ℕ) :
    wedge leadingForm (wedgePowerVariation form variation (degree+1)) =
      ((degree+1 : ℕ) : ℂ) • wedge leadingForm
        (show Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ from
          wedge variation (wedgePower form degree)) := by
  let residual : Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ :=
    wedge variation (wedgePower form degree)
  calc
    _ = wedge leadingForm (((degree+1 : ℕ) : ℂ) • residual) :=
      congrArg (fun alternatingForm : Space [⋀^WedgePowerSlots (degree+1)]→ₗ[ℝ] ℂ =>
        wedge leadingForm alternatingForm)
        (wedgePowerVariation_succ (Module.finBasis ℝ Space) form variation degree)
    _ = _ := wedge_smul_right _ leadingForm residual

/-- All residual placements combine with the positive multiplicity k+1.
The residual is retained; its integral is not assumed to vanish. -/
theorem boundaryResidualFin_succ {k : ℕ}
    (a b : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) →L[ℝ] ℂ)
    (x : ComplexEuclidean (k+2)) :
    boundaryResidualFin (k := k+1) a b x =
      ((k+1 : ℕ) : ℂ) • boundarySingleResidualFin a b x := by
  have variationIdentity := wedge_wedgePowerVariation_succ (oneForm a x).toAlternatingMap
    (extDeriv (oneForm a) x).toAlternatingMap
    (extDeriv (oneForm b) x).toAlternatingMap k
  have reindexedIdentity := congrArg
    (fun form : ComplexEuclidean (k+2) [⋀^Fin 1 ⊕ WedgePowerSlots (k+1)]→ₗ[ℝ] ℂ =>
      form.domDomCongr (boundaryFinEquiv (k+1)))
    variationIdentity
  exact reindexedIdentity.trans (AlternatingMap.domDomCongr_smul _ _ _)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PairTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma pairExterior_apply [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a b : E →L[ℝ] ℂ) (v : Fin 2 → E) :
    pairExterior a b v = a (v 0) * b (v 1) - a (v 1) * b (v 0) := by
  simp [pairExterior, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, sub_eq_add_neg]

lemma pairExterior_toAlternatingMap (a b : E →L[ℝ] ℂ) :
    (pairExterior a b).toAlternatingMap = covectorVolume ![a.toLinearMap,b.toLinearMap] := by
  ext v
  rw [covectorVolume_apply, Matrix.det_fin_two]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap, pairExterior_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]
  ring

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma differentiableAt_pairExterior [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    DifferentiableAt ℝ (fun y => pairExterior (a y) (b y)) x := by
  unfold pairExterior ContinuousLinearMap.bilinearComp
  change DifferentiableAt ℝ
    (fun y => ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
        (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((((ContinuousLinearMap.mul ℝ ℂ).comp (a y)).flip.comp (b y)).flip))) x
  apply (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).differentiableAt.comp x
  have hf1 := (ContinuousLinearMap.flipₗᵢ ℝ E ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.differentiable
  have hf2 := (ContinuousLinearMap.flipₗᵢ ℝ E E ℂ).toContinuousLinearEquiv.toContinuousLinearMap.differentiable
  change Differentiable ℝ (fun L : E →L[ℝ] ℂ →L[ℝ] ℂ => L.flip) at hf1
  change Differentiable ℝ (fun L : E →L[ℝ] E →L[ℝ] ℂ => L.flip) at hf2
  fun_prop

lemma fderiv_pairExterior_eval {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (v : Fin 2 → E) (u : E) :
    fderiv ℝ (fun y => pairExterior (a y) (b y) v) x u =
      fderiv ℝ a x u (v 0) * b x (v 1) + a x (v 0) * fderiv ℝ b x u (v 1) -
      (fderiv ℝ a x u (v 1) * b x (v 0) + a x (v 1) * fderiv ℝ b x u (v 0)) := by
  have hh := ((ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)).mul
    (hb.hasFDerivAt.clm_apply (hasFDerivAt_const (v 1) x))).sub
    ((ha.hasFDerivAt.clm_apply (hasFDerivAt_const (v 1) x)).mul
      (hb.hasFDerivAt.clm_apply (hasFDerivAt_const (v 0) x)))
  convert congrArg (fun L : E →L[ℝ] ℂ => L u) hh.fderiv using 1 <;>
    simp [pairExterior_apply] <;> first | rfl | ring

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma covectorVolume_one [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (a : E →L[ℝ] ℂ) :
    covectorVolume (fun _ : Fin 1 => a.toLinearMap) =
      (oneForm (fun _ : E => a) 0).toAlternatingMap := by
  ext v
  simp [covectorVolume_apply, Matrix.det_unique, oneForm_apply]

/-- The negative-sign exterior Leibniz identity for two actual one-forms.
All derivatives are exterior derivatives, and the shuffle order is
identified explicitly with the standard three slots. -/
theorem extDeriv_pairExterior {J : Type*} [Fintype J]
    (basis : Module.Basis J ℝ E) {a b : E → E →L[ℝ] ℂ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    (extDeriv (fun y => pairExterior (a y) (b y)) x).toAlternatingMap =
      (wedge (oneForm b x).toAlternatingMap (extDeriv (oneForm a) x).toAlternatingMap).domDomCongr
        (prependFinEquiv 2) -
      (wedge (oneForm a x).toAlternatingMap (extDeriv (oneForm b) x).toAlternatingMap).domDomCongr
        (prependFinEquiv 2) := by
  ext v
  have hvol (c : E → E →L[ℝ] ℂ) :
      (oneForm c x).toAlternatingMap = covectorVolume (fun _ : Fin 1 => (c x).toLinearMap) := by
    rw [covectorVolume_one]
    rfl
  simp only [AlternatingMap.sub_apply, hvol, wedge_one_eval basis,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [extDeriv_apply (differentiableAt_pairExterior ha hb)]
  simp only [fderiv_pairExterior_eval ha hb]
  have hev (c : E → E →L[ℝ] ℂ) (hc : DifferentiableAt ℝ c x) (w u : E) :
      fderiv ℝ (fun y => c y w) x u = fderiv ℝ c x u w := by
    simpa using congrArg (fun L : E →L[ℝ] ℂ => L u)
      (hc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv
  have hd (c : E → E →L[ℝ] ℂ) (hc : DifferentiableAt ℝ c x) (w : Fin 2 → E) :
      extDeriv (oneForm c) x w =
        fderiv ℝ c x (w 0) (w 1) - fderiv ℝ c x (w 1) (w 0) := by
    have he : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    rw [he, extDeriv_oneForm hc, hev c hc, hev c hc]
    rfl
  simp only [hd a ha, hd b hb,
    ContinuousLinearMap.coe_coe]
  simp [Fin.sum_univ_three, Fin.removeNth, Fin.succAbove]
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PairExteriorBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The continuous primitive is the shuffle wedge, with
its two slots kept in their specified order. -/
lemma pairExterior_is_wedge (a b : E →L[ℝ] ℂ) :
    (pairExterior a b).toAlternatingMap =
      (wedge (oneForm (fun _ : E => a) 0).toAlternatingMap
        (oneForm (fun _ : E => b) 0).toAlternatingMap).domDomCongr (prependFinEquiv 1) := by
  rw [← covectorVolume_one a, ← covectorVolume_one b, wedge_covectorVolume,
    covectorVolume_prepend, pairExterior_toAlternatingMap]
  congr 1
  funext i
  fin_cases i <;> rfl

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PowerTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype J]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma wedge_triple_power_order [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℝ E] (basis : Module.Basis J ℝ E) (k : ℕ)
    (c : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (D A : E [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    ((wedge ((wedge c D).domDomCongr (prependFinEquiv 2))
      ((wedgePower A k).domDomCongr (powerFinEquiv k))).domDomCongr
        (derivativeLeftEquiv (2*k))).domDomCongr (finCongr (by omega)) =
    (wedge c (wedge D (wedgePower A k))).domDomCongr (boundaryFinEquiv (k+1)) := by
  rw [← wedge_derivative_assoc basis]
  have h1 := wedge_reindex basis (Equiv.refl (Fin 2)) (powerFinEquiv k) D (wedgePower A k)
  simp only [AlternatingMap.domDomCongr_refl] at h1
  rw [← h1]
  simp only [← AlternatingMap.domDomCongr_trans]
  have h2 := wedge_reindex basis (Equiv.refl (Fin 1))
    (((Equiv.refl (Fin 2)).sumCongr (powerFinEquiv k)).trans finSumFinEquiv)
    c (wedge D (wedgePower A k))
  simp only [AlternatingMap.domDomCongr_refl] at h2
  rw [← h2, ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with i | (i | i)
  · fin_cases i; rfl
  · fin_cases i <;> rfl
  · change 2 + (powerFinEquiv k i).val + 1 = 1 + (2 + (powerFinEquiv k i).val)
    omega

/-- The continuous primitive is the ordered shuffle product. -/
lemma powerTransgressionPrimitive_is_wedge (basis : Module.Basis J ℝ E)
    (a b : E → E →L[ℝ] ℂ) (k : ℕ) (x : E) :
    (powerTransgressionPrimitive basis a b k x).toAlternatingMap =
      (wedge (oneForm a x).toAlternatingMap
        (wedge (oneForm b x).toAlternatingMap
          (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (primitiveFinEquiv k) := by
  unfold powerTransgressionPrimitive
  rw [continuousReindex_toAlternatingMap, continuousWedgeFin_toAlternatingMap,
    pairExterior_is_wedge, basisContinuousWedgePower_toAlternatingMap,
    ← wedge_reindex basis, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i <;> rfl

/-- Full ambient transgression identity in every degree. The hypotheses are
actual differentiability and d squared alpha = 0, not a formal product law. -/
theorem extDeriv_powerTransgressionPrimitive (basis : Module.Basis J ℝ E)
    {a b : E → E →L[ℝ] ℂ} {x : E} (k : ℕ)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hda : DifferentiableAt ℝ (extDeriv (oneForm a)) x)
    (hclosed : extDeriv (extDeriv (oneForm a)) x = 0) :
    (extDeriv (powerTransgressionPrimitive basis a b k) x).toAlternatingMap =
      (wedge (oneForm b x).toAlternatingMap
        (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) -
      (wedge (oneForm a x).toAlternatingMap
        (wedge (extDeriv (oneForm b) x).toAlternatingMap
          (wedgePower (extDeriv (oneForm a) x).toAlternatingMap k))).domDomCongr
        (boundaryFinEquiv (k+1)) := by
  unfold powerTransgressionPrimitive
  rw [continuousReindex_finCongr_extDeriv, continuousReindex_toAlternatingMap,
    extDeriv_continuousWedge_two basis (differentiableAt_pairExterior ha hb)
      (differentiableAt_basisContinuousWedgePower basis hda k),
    extDeriv_basisContinuousWedgePower basis hda hclosed k]
  simp only [ContinuousAlternatingMap.toAlternatingMap_zero, wedge_power_zero_right,
    AlternatingMap.domDomCongr_zero, add_zero]
  rw [extDeriv_pairExterior basis ha hb, basisContinuousWedgePower_toAlternatingMap]
  have hsub (A B : E [⋀^Fin 3]→ₗ[ℝ] ℂ) (C : E [⋀^Fin (2*k)]→ₗ[ℝ] ℂ) :
      wedge (A-B) C = wedge A C - wedge B C := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ B, wedge_add_left, wedge_smul_left]
    simp only [neg_one_smul, sub_eq_add_neg]
  have hr {ι κ : Type} (e : ι ≃ κ) (C D : E [⋀^ι]→ₗ[ℝ] ℂ) :
      (C-D).domDomCongr e = C.domDomCongr e - D.domDomCongr e :=
    map_sub (AlternatingMap.domDomCongrₗ ℂ e) C D
  rw [hsub, hr, hr,
    wedge_triple_power_order basis, wedge_triple_power_order basis]
  have hdec : wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  have hfin : wedgePowerSlotsFintype (k+1) =
      (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  simp only [wedgePower]
  rw [hdec, hfin]
  congr 3

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousTransgression
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

lemma homogeneousPrimitive_is_wedge {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    (homogeneousPrimitive (m := m) G t x).toAlternatingMap =
      (wedge (oneForm (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t) x).toAlternatingMap
        (wedge (oneForm (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x).toAlternatingMap
          (wedgePower (extDeriv (oneForm (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)) x).toAlternatingMap k))).domDomCongr
        (primitiveFinEquiv k) :=
  powerTransgressionPrimitive_is_wedge (sphereFrame (k+1)).toBasis _ _ k x

/-- The full ambient identity; the horizontal term has not been discarded. -/
theorem MassHypotheses.homogeneousPrimitive_extDeriv {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ) :
    (extDeriv (homogeneousPrimitive (m := m) G t) x).toAlternatingMap =
      (wedge (oneForm (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x).toAlternatingMap
        (wedgePower (extDeriv (oneForm
          (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)) x).toAlternatingMap
          (k+1))).domDomCongr (boundaryFinEquiv (k+1)) -
      boundarySingleResidualFin
        (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x := by
  have hs := h.alpha_beta_contDiffAt hx t 1
  have hda := (contDiffAt_extDeriv_power_order 1
      (contDiffAt_oneForm_order 2 (h.alpha_beta_contDiffAt hx t 2).1)).differentiableAt
      (by norm_num)
  have he := extDeriv_powerTransgressionPrimitive (sphereFrame (k+1)).toBasis k
    (hs.1.differentiableAt (by norm_num)) (hs.2.differentiableAt (by norm_num))
    hda (h.alphaPath_extDeriv_extDeriv hx t)
  unfold homogeneousPrimitive boundarySingleResidualFin
  have hdec : wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  have hfin : wedgePowerSlotsFintype (k+1) =
      (inferInstance : Fintype (Fin 2 ⊕ WedgePowerSlots k)) := Subsingleton.elim _ _
  rw [hdec, hfin] at he ⊢
  exact he

/-- Exact negative-sign residual transgression on sphere tangents, with the
actual multiplicity n-1, in all complex dimensions n=k+2. -/
theorem MassHypotheses.sphere_residual_transgression {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    {x : ComplexEuclidean (k+2)} (hx : x ≠ 0) (t : ℝ)
    (v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2))
    (hv : ∀ i, inner ℝ x (v i) = 0) :
    boundaryResidualFin (k := k+1)
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
      -((k+1 : ℕ) : ℂ) * extDeriv (homogeneousPrimitive (m := m) G t) x v := by
  let a := alphaPath (polynomialMap G) (coordinateMap (k+2)) m t
  let b := betaLinear (polynomialMap G) (coordinateMap (k+2)) m
  have hzero : (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) v = 0 := by
    let w : Fin 1 ⊕ WedgePowerSlots (k+1) → sphereTangent x := fun i =>
      ⟨v (boundaryFinEquiv (k+1) i), Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hv _)⟩
    have hz0 := h.sphere_beta_wedge_power_zero hx t
    rw [show k+2-1=k+1 by omega] at hz0
    have hz := congrArg (fun B => B w) hz0
    simpa only [show k+2-1 = k+1 by omega, tangentForm, ← wedgePower_compLinearMap,
      ← wedge_compLinearMap, AlternatingMap.compLinearMap_apply,
      AlternatingMap.domDomCongr_apply, Submodule.subtype_apply,
      AlternatingMap.zero_apply, w, a, b, Function.comp_def] using hz
  have he := congrArg (fun B => B v) (h.homogeneousPrimitive_extDeriv hx t)
  change extDeriv (homogeneousPrimitive (m := m) G t) x v =
    (wedge (oneForm b x).toAlternatingMap
      (wedgePower (extDeriv (oneForm a) x).toAlternatingMap (k+1))).domDomCongr
        (boundaryFinEquiv (k+1)) v - boundarySingleResidualFin a b x v at he
  rw [hzero, zero_sub] at he
  rw [boundaryResidualFin_succ, AlternatingMap.smul_apply, he]
  change _ * _ = _ * _
  ring

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_PrimitiveRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap
open scoped TensorProduct

noncomputable section
namespace Mahler
variable {E X J ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype J] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype J] in
lemma basisVolumeContinuous_eq [Fintype J] (b : Module.Basis J ℝ E) (q : ι → J) :
    (basisVolumeContinuous b q).toAlternatingMap = covectorVolume (complexCoord b ∘ q) := by
  ext v
  simp [basisVolumeContinuous, covectorVolume,
    MultilinearMap.alternatization_apply]

lemma bundleFiniteForm_eq (b : Module.Basis J ℝ E) (a : E [⋀^ι]→ₗ[ℝ] ℂ) :
    (bundleFiniteForm b a).toAlternatingMap = a := by
  classical
  conv_rhs => rw [alternating_basis_expansion_normalized b a]
  ext v
  simp only [bundleFiniteForm, ContinuousAlternatingMap.coe_toAlternatingMap,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    alternatingMap_sum_apply, AlternatingMap.smul_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← basisVolumeContinuous_eq b q]
  rfl

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousPrimitiveRegularity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set

noncomputable section
namespace Mahler

theorem sourceHomogeneousPrimitive_eq {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ)
    (x : ComplexEuclidean (k+2)) :
    (sourceHomogeneousPrimitive (m := m) G t x).toAlternatingMap =
      sourcePrimitiveFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x :=
  bundleFiniteForm_eq _ _

end Mahler

end

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HomogeneousEndpoint
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Mahler

/-- The two independent continuous primitive constructions use the same
ordered slots: alpha, beta, followed by the interleaved d-alpha factors. -/
lemma sourcePrimitiveSlots_eq_primitiveFinEquiv (k : ℕ) :
    sourcePrimitiveSlots k = primitiveFinEquiv k := by
  ext i
  rcases i with i | (i | i)
  · fin_cases i; rfl
  · fin_cases i; rfl
  · rfl

/-- Equality of the actual continuous fields identifies their exterior
 derivatives; no additional integration or regularity premise is introduced. -/
lemma sourceHomogeneousPrimitive_eq_homogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ) :
    sourceHomogeneousPrimitive (m := m) G t = homogeneousPrimitive (m := m) G t := by
  funext x
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [sourceHomogeneousPrimitive_eq, homogeneousPrimitive_is_wedge]
  unfold sourcePrimitiveFin
  rw [sourcePrimitiveSlots_eq_primitiveFinEquiv]

/-- The homogeneous value and radius-sphere limit in all complex
dimensions at least two, from the mass hypotheses alone. -/
theorem MassHypotheses.homogeneous_flux_endpoints_oai {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G) :
    homogeneousSphereFlux (k+1) N G = (Real.pi*(m:ℝ))^(k+2) ∧
    Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(k+2))) := by
  apply h.homogeneousFlux_endpoints_of_transgression
  intro t x hx v hv
  have hn : x ≠ 0 := by intro he; simp [he] at hx
  have ht := h.sphere_residual_transgression hn t v hv
  rwa [← sourceHomogeneousPrimitive_eq_homogeneousPrimitive G t] at ht

end Mahler

end

end OAI
end

theorem solution : type_of% @OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints_oai := @OAI.Mahler.MassHypotheses.homogeneous_flux_endpoints_oai
