-- Prove2me | solution 1 for OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T10:47:31.05567+00:00
-- url     : https://prove2.me/submissions/c56e653e-e118-46ef-a56a-262eaca8f63c

import Mathlib
import Definitions.Def_OAISMh000

section
-- module Solutions.OAIS_Mahler.Compat
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

lemma card_wedgePowerSlots (n : ℕ) : Fintype.card (WedgePowerSlots n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 ⊕ WedgePowerSlots n) = _
    rw [Fintype.card_sum, Fintype.card_fin, ih]
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
-- module Solutions.OAIS_Mahler.Mahler_DilationTransport
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Filter
open scoped Topology
namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

lemma dcLinear_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : DifferentiableAt ℝ u (r • x)) (v : E) :
    dcLinear (fun y => u (r • y)) x v = dcLinear u (r • x) (r • v) := by
  have hd := hu.hasFDerivAt.comp x (realDilation r).hasFDerivAt
  change HasFDerivAt (fun y => u (r • y)) _ x at hd
  simp only [dcLinear_apply, dc]
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, realDilation_apply]
  rw [smul_comm r I v]

lemma dcLinear_sub_const (u : E → ℂ) (c : ℂ) (x : E) :
    dcLinear (fun y => u y - c) x = dcLinear u x := by
  unfold dcLinear
  congr 2
  exact fderiv_sub_const c

lemma oneForm_dilation_eventually {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) :
    oneForm (dcLinear (fun y => u (r • y))) =ᶠ[𝓝 x]
      (fun y => (oneForm (dcLinear u) (r • y)).compContinuousLinearMap (realDilation r)) := by
  have hev : ∀ᶠ y in 𝓝 (r • x), DifferentiableAt ℝ u y :=
    (hu.eventually (by norm_num)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have hc : Tendsto (fun y : E => r • y) (𝓝 x) (𝓝 (r • x)) :=
    (realDilation r).continuous.continuousAt
  filter_upwards [hc.eventually hev] with y hy
  ext v
  exact dcLinear_dilation hy (v 0)

/-- Pullback of the actual dd^c under a real dilation. -/
theorem extDeriv_dc_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) :
    extDeriv (oneForm (dcLinear (fun y => u (r • y)))) x =
      (extDeriv (oneForm (dcLinear u)) (r • x)).compContinuousLinearMap (realDilation r) := by
  have hn := extDeriv_pullback (f := realDilation r)
    (differentiableAt_oneForm (differentiableAt_dcLinear hu))
    ((realDilation r).contDiff.contDiffAt : ContDiffAt ℝ 2 (realDilation r) x)
    (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
  simp only [ContinuousLinearMap.fderiv, realDilation_apply] at hn
  rw [← hn]
  unfold extDeriv
  rw [(oneForm_dilation_eventually hu).fderiv_eq]

/-- Every tangent slot is transported by the derivative of dilation; the
constant subtracted from the logarithm disappears from both derivatives. -/
theorem boundaryForm_dilation {u : E → ℂ} {r : ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (r • x)) (c : ℂ) (k : ℕ) :
    boundaryForm (fun y => u (r • y) - c) k x =
      (boundaryForm u k (r • x)).compLinearMap (realDilation r).toLinearMap := by
  have he : dcLinear (fun y => u (r • y) - c) = dcLinear (fun y => u (r • y)) :=
    funext (dcLinear_sub_const _ c)
  unfold boundaryForm
  rw [he, wedge_compLinearMap, wedgePower_compLinearMap, extDeriv_dc_dilation hu]
  congr 1
  ext v
  exact dcLinear_dilation (hu.differentiableAt (by norm_num)) (v 0)

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_BoundaryJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

lemma dcOneOperator_fderiv (u : E → ℂ) (x : E) :
    dcOneOperator (fderiv ℝ u x) = oneForm (dcLinear u) x := rfl

theorem extDeriv_dc_eq_twoJet {u : E → ℂ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    extDeriv (oneForm (dcLinear u)) x = ddcTwoJet (fderiv ℝ (fderiv ℝ u) x) := by
  have hd := dcOneOperator.hasFDerivAt.comp x hu.hasFDerivAt
  change HasFDerivAt (oneForm (dcLinear u)) _ x at hd
  unfold extDeriv ddcTwoJet
  rw [hd.fderiv]

lemma continuous_ddcTwoJet : Continuous (ddcTwoJet (E := E)) := by
  unfold ddcTwoJet alternatizeUncurryFin
  exact (alternatizeUncurryFinCLM ℝ E ℂ).continuous.comp
    (continuous_const.clm_comp continuous_id)

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

lemma continuous_boundaryJet_eval (k : ℕ) (v : Fin 1 ⊕ WedgePowerSlots k → E) :
    Continuous (fun p : RealComplexTwoJet E => boundaryJet p k v) := by
  apply continuous_wedge_eval
  · intro w
    change Continuous (fun p : RealComplexTwoJet E => dcOperator p.1 (w 0))
    exact (dcOperator.continuous.comp continuous_fst).clm_apply continuous_const
  · apply continuous_wedgePower_eval
    intro w
    change Continuous (fun p : RealComplexTwoJet E => ddcTwoJet p.2 w)
    exact (continuous_eval_const w).comp
      (continuous_ddcTwoJet.comp continuous_snd)

theorem boundaryForm_eq_jet {u : E → ℂ} {x : E}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (k : ℕ) :
    boundaryForm u k x = boundaryJet (fderiv ℝ u x, fderiv ℝ (fderiv ℝ u) x) k := by
  unfold boundaryForm boundaryJet
  rw [dcOneOperator_fderiv, extDeriv_dc_eq_twoJet hu]

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

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ExteriorPower
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_LogUniform
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology
namespace SymmetricMahler

/-- Compactness supplies a single positive bound, and uniform convergence
preserves half of it simultaneously at every point. -/
theorem eventually_uniform_pos {X I : Type*} [TopologicalSpace X]
    {K : Set X} {l : Filter I} {u : I → X → ℝ} {t : X → ℝ}
    (hK : IsCompact K) (ht : ContinuousOn t K)
    (hp : ∀ x ∈ K, 0 < t x) (hu : TendstoUniformlyOn u t l K) :
    ∃ c : ℝ, 0 < c ∧ (∀ x ∈ K, 2*c ≤ t x) ∧
      ∀ᶠ i in l, ∀ x ∈ K, c ≤ u i x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn ht
    refine ⟨t x / 2, by linarith [hp x hx], ?_, ?_⟩
    · intro y hy
      have hb : t x ≤ t y := hmin hy
      linarith
    · have hc : 0 < t x / 2 := by linarith [hp x hx]
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (t x / 2) hc] with i hi
      intro y hy
      have hd := hi y hy
      rw [Real.dist_eq] at hd
      have ha := (abs_lt.mp hd).2
      have hb : t x ≤ t y := hmin hy
      linarith
  · refine ⟨1, by norm_num, ?_, Filter.Eventually.of_forall ?_⟩ <;>
      simp_all [Set.not_nonempty_iff_eq_empty]

/-- A continuous operation preserves uniform convergence when its inputs
converge uniformly to a continuous function on a compact set in a proper space. -/
theorem uniform_comp_of_compact {X I E H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [ProperSpace E] [UniformSpace H]
    {K : Set X} {l : Filter I} {u : I → X → E} {t : X → E}
    (hK : IsCompact K) (ht : ContinuousOn t K)
    (hu : TendstoUniformlyOn u t l K) {g : E → H} (hg : Continuous g) :
    TendstoUniformlyOn (fun i x => g (u i x)) (fun x => g (t x)) l K := by
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn ht).isBounded.subset_closedBall (0 : E)
  have hf : ∀ x ∈ K, t x ∈ closedBall (0 : E) (R+1) := by
    intro x hx
    exact closedBall_subset_closedBall (by linarith) (hR (mem_image_of_mem t hx))
  have he : ∀ᶠ i in l, ∀ x ∈ K, u i x ∈ closedBall (0 : E) (R+1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with i hi
    intro x hx
    have hb := hR (mem_image_of_mem t hx)
    have hd := hi x hx
    rw [mem_closedBall] at hb ⊢
    calc
      dist (u i x) 0 ≤ dist (u i x) (t x) + dist (t x) 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by rw [dist_comm] at hd; linarith
  exact (isCompact_closedBall (0 : E) (R+1)).uniformContinuousOn_of_continuous hg.continuousOn
    |>.comp_tendstoUniformlyOn_eventually he hf hu

/-- Uniform convergence of a finite family, in its product norm. -/
theorem uniform_finite_pi {X I J V : Type*} [Fintype J] [PseudoMetricSpace V]
    {K : Set X} {l : Filter I} {u : I → J → X → V} {t : J → X → V}
    (h : ∀ j, TendstoUniformlyOn (fun i => u i j) (t j) l K) :
    TendstoUniformlyOn (fun i x j => u i j x) (fun x j => t j x) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : ∀ᶠ i in l, ∀ j, ∀ x ∈ K, dist (t j x) (u i j x) < ε :=
    (Filter.eventually_all).mpr (fun j => Metric.tendstoUniformlyOn_iff.mp (h j) ε hε)
  filter_upwards [he] with i hi
  intro x hx
  exact (dist_pi_lt_iff hε).mpr (fun j => hi j x hx)

/-- Same-parameter product version of uniform convergence. -/
theorem uniform_pair {X I V W : Type*} [UniformSpace V] [UniformSpace W]
    {K : Set X} {l : Filter I} {u : I → X → V} {v : I → X → W}
    {t : X → V} {s : X → W}
    (hu : TendstoUniformlyOn u t l K) (hv : TendstoUniformlyOn v s l K) :
    TendstoUniformlyOn (fun i x => (u i x, v i x)) (fun x => (t x, s x)) l K := by
  intro d hd
  exact ((hu.prodMk hv) d hd).diag_of_prod

end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogScalarJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasFDerivAt_logD {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : HasFDerivAt f (a x) x) (ha : HasFDerivAt a b x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => logD (f y) (a y)) (logD2 (f x) (a x) b) x := by
  exact ((hasDerivAt_inv hx).comp_hasFDerivAt x hf).fun_smul ha

/-- Actual nested real derivative, from the local derivative field and the
inverse/product rule. Positivity is used locally, not assumed as a log jet. -/
lemma fderiv_log_twice {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (a y) y)
    (ha : HasFDerivAt a b x) (hx : f x ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (f y))) x = logD2 (f x) (a x) b := by
  have hfx := hf.self_of_nhds
  have he : (fun y => logD (f y) (a y)) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => Real.log (f y)) := by
    filter_upwards [hf, hfx.continuousAt.eventually_ne hx] with y hy hne
    exact (hy.log hne).fderiv.symm
  exact ((hasFDerivAt_logD hfx ha hx).congr_of_eventuallyEq he.symm).fderiv

/-- Uniform convergence of the explicit logarithmic jets. The positive
cutoff makes each algebraic operation globally continuous; it agrees with
the actual formula on the limit and eventually on the entire compact set. -/
theorem uniform_log_jets [FiniteDimensional ℝ E]
    {I X : Type*} [TopologicalSpace X] {K : Set X} {l : Filter I}
    {u : I → X → ℝ} {a : I → X → (E →L[ℝ] ℝ)}
    {b : I → X → (E →L[ℝ] (E →L[ℝ] ℝ))}
    {t : X → ℝ} {A : X → (E →L[ℝ] ℝ)} {B : X → (E →L[ℝ] (E →L[ℝ] ℝ))}
    (hK : IsCompact K) (ht : ContinuousOn t K) (hA : ContinuousOn A K)
    (hB : ContinuousOn B K) (hp : ∀ x ∈ K, 0 < t x)
    (hu : TendstoUniformlyOn u t l K) (ha : TendstoUniformlyOn a A l K)
    (hb : TendstoUniformlyOn b B l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ u i x) ∧
    TendstoUniformlyOn (fun i x => Real.log (u i x)) (fun x => Real.log (t x)) l K ∧
    TendstoUniformlyOn (fun i x => logD (u i x) (a i x))
      (fun x => logD (t x) (A x)) l K ∧
    TendstoUniformlyOn (fun i x => logD2 (u i x) (a i x) (b i x))
      (fun x => logD2 (t x) (A x) (B x)) l K := by
  obtain ⟨c, hc, htc, huc⟩ := eventually_uniform_pos hK ht hp hu
  have htc' : ∀ x ∈ K, c ≤ t x := fun x hx => by linarith [htc x hx]
  have hab : TendstoUniformlyOn (fun i x => (a i x, b i x))
      (fun x => (A x, B x)) l K := uniform_pair ha hb
  have hq : TendstoUniformlyOn (fun i x => (u i x, a i x, b i x))
      (fun x => (t x, A x, B x)) l K := uniform_pair hu hab
  have hcont := ht.prodMk (hA.prodMk hB)
  have hg0 : Continuous (fun r : ℝ => Real.log (max c r)) := by
    apply Continuous.log (continuous_const.max continuous_id)
    intro r
    exact ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _))
  have h0 := uniform_comp_of_compact hK ht hu hg0
  have hg1 : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) =>
      logD (max c q.1) q.2.1) := by
    have hv : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => max c q.1) :=
      continuous_const.max continuous_fst
    exact (hv.inv₀ (fun q => ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _)))).smul
      (continuous_fst.comp continuous_snd)
  have hg2 : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) =>
      logD2 (max c q.1) q.2.1 q.2.2) := by
    have : ContinuousAdd (E →L[ℝ] (E →L[ℝ] ℝ)) :=
      (inferInstance : IsTopologicalAddGroup (E →L[ℝ] (E →L[ℝ] ℝ))).toContinuousAdd
    have hv : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => max c q.1) :=
      continuous_const.max continuous_fst
    have hn (q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) : max c q.1 ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _))
    have hpa : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => q.2.1) :=
      continuous_fst.comp continuous_snd
    have hpb : Continuous (fun q : ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ)) => q.2.2) :=
      continuous_snd.comp continuous_snd
    exact ((hv.inv₀ hn).smul hpb).add
      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((((hv.pow 2).inv₀ (fun q => pow_ne_zero _ (hn q))).neg).smul hpa)).clm_apply hpa)
  have h1 := uniform_comp_of_compact (E := ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) (H := E →L[ℝ] ℝ) hK hcont hq hg1
  have h2 := uniform_comp_of_compact (E := ℝ × (E →L[ℝ] ℝ) × (E →L[ℝ] (E →L[ℝ] ℝ))) (H := E →L[ℝ] (E →L[ℝ] ℝ)) hK hcont hq hg2
  refine ⟨⟨c, hc, huc⟩, ?_, ?_, ?_⟩
  · apply (h0.congr_right (fun x hx => by rw [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    simp only [max_eq_right (hi x hx)]
  · apply (h1.congr_right (fun x hx => by simp only [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    dsimp only
    simp only [max_eq_right (hi x hx)]
  · apply (h2.congr_right (fun x hx => by simp only [max_eq_right (htc' x hx)])).congr
    filter_upwards [huc] with i hi
    intro x hx
    dsimp only
    simp only [max_eq_right (hi x hx)]

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E] [NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

lemma hasFDerivAt_project {f : E → ℂ} {A : E →L[ℂ] ℂ} {x : E}
    (hf : HasFDerivAt f A x) (p : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (fun y => p (f y)) (projectD p A) x :=
  p.hasFDerivAt.comp x (hf.restrictScalars ℝ)

lemma hasFDerivAt_projectD {a : E → (E →L[ℂ] ℂ)}
    {B : E →L[ℂ] (E →L[ℂ] ℂ)} {x : E}
    (ha : HasFDerivAt a B x) (p : ℂ →L[ℝ] ℝ) :
    HasFDerivAt (fun y => projectD p (a y)) (projectD2 p B) x :=
  (projectD p).hasFDerivAt.comp x (ha.restrictScalars ℝ)

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma hasFDerivAt_square [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℝ} {a : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f a x) : HasFDerivAt (fun y => (f y)^2) (squareD (f x) a) x := by
  simpa only [squareD, pow_two, two_mul, add_smul, Pi.mul_apply] using hf.fun_mul hf

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma hasFDerivAt_squareD [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℝ} {a : E → (E →L[ℝ] ℝ)}
    {b : E →L[ℝ] (E →L[ℝ] ℝ)} {x : E}
    (hf : HasFDerivAt f (a x) x) (ha : HasFDerivAt a b x) :
    HasFDerivAt (fun y => squareD (f y) (a y)) (squareD2 (f x) (a x) b) x := by
  simpa only [squareD, squareD2, Pi.smul_apply] using (hf.const_mul 2).fun_smul ha

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_NormSquareJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

lemma continuous_sumNormSq : Continuous (sumNormSq : (J → ℂ) → ℝ) := by
  unfold sumNormSq
  exact continuous_finsetSum _ (fun j _ => Complex.continuous_normSq.comp (continuous_apply j))

lemma continuous_sumNormSqD :
    Continuous (fun q : ComplexTwoJet E J => sumNormSqD q.1 q.2.1) := by
  apply continuous_finsetSum
  intro j _
  have hv : Continuous (fun q : ComplexTwoJet E J => q.1 j) :=
    (continuous_apply j).comp continuous_fst
  have ha : Continuous (fun q : ComplexTwoJet E J => q.2.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  exact ((continuous_const.mul (Complex.continuous_re.comp hv)).smul
    ((projectD Complex.reCLM).continuous.comp ha)).add
    ((continuous_const.mul (Complex.continuous_im.comp hv)).smul
    ((projectD Complex.imCLM).continuous.comp ha))

lemma continuous_sumNormSqD2 :
    Continuous (fun q : ComplexTwoJet E J => sumNormSqD2 q.1 q.2.1 q.2.2) := by
  have : ContinuousAdd (E →L[ℝ] (E →L[ℝ] ℝ)) :=
    (inferInstance : IsTopologicalAddGroup (E →L[ℝ] (E →L[ℝ] ℝ))).toContinuousAdd
  unfold sumNormSqD2
  apply continuous_finsetSum
  intro j _
  have hv : Continuous (fun q : ComplexTwoJet E J => q.1 j) :=
    (continuous_apply j).comp continuous_fst
  have ha : Continuous (fun q : ComplexTwoJet E J => q.2.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun q : ComplexTwoJet E J => q.2.2 j) :=
    (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  have hp (p : ℂ →L[ℝ] ℝ) : Continuous (fun q : ComplexTwoJet E J =>
      squareD2 (p (q.1 j)) (projectD p (q.2.1 j)) (projectD2 p (q.2.2 j))) := by
    have hpa := (projectD p).continuous.comp ha
    have hpb := (compL ℝ E (E →L[ℂ] ℂ) (E →L[ℝ] ℝ) (projectD p)).continuous.comp
      ((restrictScalarsL ℂ E (E →L[ℂ] ℂ) ℝ ℝ).continuous.comp hb)
    exact ((continuous_const.mul (p.continuous.comp hv)).smul hpb).add
      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((continuous_const (y := (2 : ℝ))).smul hpa)).clm_apply hpa)
  exact (hp Complex.reCLM).add (hp Complex.imCLM)

lemma hasFDerivAt_sumNormSq {f : J → E → ℂ} {a : J → E →L[ℂ] ℂ} {x : E}
    (hf : ∀ j, HasFDerivAt (f j) (a j) x) :
    HasFDerivAt (fun y => sumNormSq (fun j => f j y))
      (sumNormSqD (fun j => f j x) a) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_square (hasFDerivAt_project (hf j) Complex.reCLM)).fun_add
      (hasFDerivAt_square (hasFDerivAt_project (hf j) Complex.imCLM)))
  simpa [sumNormSq, sumNormSqD, Complex.normSq_apply, pow_two] using h

lemma hasFDerivAt_sumNormSqD {f : J → E → ℂ} {a : J → E → (E →L[ℂ] ℂ)}
    {b : J → E →L[ℂ] (E →L[ℂ] ℂ)} {x : E}
    (hf : ∀ j, HasFDerivAt (f j) (a j x) x)
    (ha : ∀ j, HasFDerivAt (a j) (b j) x) :
    HasFDerivAt (fun y => sumNormSqD (fun j => f j y) (fun j => a j y))
      (sumNormSqD2 (fun j => f j x) (fun j => a j x) b) x := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasFDerivAt_squareD (hasFDerivAt_project (hf j) Complex.reCLM)
      (hasFDerivAt_projectD (ha j) Complex.reCLM)).fun_add
    (hasFDerivAt_squareD (hasFDerivAt_project (hf j) Complex.imCLM)
      (hasFDerivAt_projectD (ha j) Complex.imCLM)))
  simpa [sumNormSqD, sumNormSqD2] using h

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogNormSquare
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter ContinuousLinearMap
open scoped Topology

namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [normedSpaceRealE : NormedSpace ℝ E]
    [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E] [fintypeJ : Fintype J]

lemma C2_log_normSq_derivatives {U : Set E} (hU : IsOpen U)
    {f : J → E → ℂ} (hf : ∀ j, ContDiffOn ℂ 2 (f j) U)
    {x : E} (hx : x ∈ U) (hp : sumNormSq (fun j => f j x) ≠ 0) :
    fderiv ℝ (fun y => Real.log (sumNormSq (fun j => f j y))) x =
      logD (sumNormSq (fun j => f j x))
        (sumNormSqD (fun j => f j x) (fun j => fderiv ℂ (f j) x)) ∧
    fderiv ℝ (fderiv ℝ (fun y => Real.log (sumNormSq (fun j => f j y)))) x =
      logD2 (sumNormSq (fun j => f j x))
        (sumNormSqD (fun j => f j x) (fun j => fderiv ℂ (f j) x))
        (sumNormSqD2 (fun j => f j x) (fun j => fderiv ℂ (f j) x)
          (fun j => fderiv ℂ (fderiv ℂ (f j)) x)) := by
  have hd (j) := (hf j).differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hv (y) (hy : y ∈ U) (j) := ((hd j y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  refine ⟨(hasFDerivAt_sumNormSq (hv x hx) |>.log hp).fderiv, ?_⟩
  apply fderiv_log_twice
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact hasFDerivAt_sumNormSq (hv y hy)
  · exact hasFDerivAt_sumNormSqD (hv x hx)
      (fun j => ((((hf j).fderiv_of_isOpen (m := 1) hU (by norm_num)).differentiableOn
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt)
  · exact hp

omit normedSpaceRealE isScalarTowerRealComplexE fintypeJ in
lemma continuousOn_actualComplexTwoJet [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [Fintype J] {U : Set E} (hU : IsOpen U) {f : J → E → ℂ}
    (hf : ∀ j, ContDiffOn ℂ 2 (f j) U) :
    ContinuousOn (actualComplexTwoJet f) U := by
  exact (continuousOn_pi.mpr (fun j => (hf j).continuousOn)).prodMk
    ((continuousOn_pi.mpr (fun j => (hf j).continuousOn_fderiv_of_isOpen hU (by norm_num))).prodMk
      (continuousOn_pi.mpr (fun j =>
        ((hf j).fderiv_of_isOpen (m := 1) hU (by norm_num)).continuousOn_fderiv_of_isOpen
          hU (by norm_num))))

omit normedSpaceRealE isScalarTowerRealComplexE in
lemma uniform_actualComplexTwoJet [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {I : Type*} {l : Filter I} {K : Set E}
    {f : I → J → E → ℂ} {g : J → E → ℂ}
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    TendstoUniformlyOn (fun i => actualComplexTwoJet (f i)) (actualComplexTwoJet g) l K := by
  have v0 := uniform_finite_pi (V := ℂ) h0
  have v1 := uniform_finite_pi (V := E →L[ℂ] ℂ) h1
  have v2 := uniform_finite_pi (V := E →L[ℂ] (E →L[ℂ] ℂ)) h2
  have v12 := uniform_pair v1 v2
  exact uniform_pair v0 v12

/-- The analytic composition passage in the fixed-annulus argument.
Every convergence hypothesis concerns the original complex functions and
their actual complex derivatives. Every derivative in the conclusion is
an actual real Fréchet derivative of the logarithm of the finite norm sum. -/
theorem uniform_C2_log_sumNormSq [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {K U : Set E} {f : I → J → E → ℂ} {g : J → E → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ∀ j, ContDiffOn ℂ 2 (g j) U)
    (hf : ∀ᶠ i in l, ∀ j, ContDiffOn ℂ 2 (f i j) U)
    (hp : ∀ x ∈ K, 0 < ∑ j, Complex.normSq (g j x))
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ ∑ j, Complex.normSq (f i j x)) ∧
    TendstoUniformlyOn (fun i x => Real.log (∑ j, Complex.normSq (f i j x)))
      (fun x => Real.log (∑ j, Complex.normSq (g j x))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x))))
      (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x)))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x)))))
      (fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x))))) l K := by
  let : ProperSpace (ComplexTwoJet E J) := FiniteDimensional.proper ℂ (ComplexTwoJet E J)
  have hq := uniform_actualComplexTwoJet h0 h1 h2
  have hqc := (continuousOn_actualComplexTwoJet hU hg).mono hKU
  have c0 : Continuous (fun q : ComplexTwoJet E J => sumNormSq q.1) :=
    continuous_sumNormSq.comp continuous_fst
  have c1 := continuous_sumNormSqD (E := E) (J := J)
  have c2 := continuous_sumNormSqD2 (E := E) (J := J)
  have u0 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := ℝ) hK hqc hq c0
  have u1 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := E →L[ℝ] ℝ) hK hqc hq c1
  have u2 := uniform_comp_of_compact (E := ComplexTwoJet E J) (H := E →L[ℝ] (E →L[ℝ] ℝ)) hK hqc hq c2
  obtain ⟨⟨c, hc, hpos⟩, v0, v1, v2⟩ := uniform_log_jets hK
    (c0.comp_continuousOn hqc) (c1.comp_continuousOn hqc) (c2.comp_continuousOn hqc) hp u0 u1 u2
  have eg1 : ∀ x ∈ K,
      logD (sumNormSq (fun j => g j x))
        (sumNormSqD (fun j => g j x) (fun j => fderiv ℂ (g j) x)) =
      fderiv ℝ (fun y => Real.log (∑ j, Complex.normSq (g j y))) x := by
    intro x hx
    exact (C2_log_normSq_derivatives hU hg (hKU hx) (ne_of_gt (hp x hx))).1.symm
  have eg2 : ∀ x ∈ K,
      logD2 (sumNormSq (fun j => g j x))
        (sumNormSqD (fun j => g j x) (fun j => fderiv ℂ (g j) x))
        (sumNormSqD2 (fun j => g j x) (fun j => fderiv ℂ (g j) x)
          (fun j => fderiv ℂ (fderiv ℂ (g j)) x)) =
      fderiv ℝ (fderiv ℝ (fun y => Real.log (∑ j, Complex.normSq (g j y)))) x := by
    intro x hx
    exact (C2_log_normSq_derivatives hU hg (hKU hx) (ne_of_gt (hp x hx))).2.symm
  refine ⟨⟨c, hc, hpos⟩, v0, ?_, ?_⟩
  · apply (v1.congr_right eg1).congr
    filter_upwards [hf, hpos] with i hi hpi
    intro x hx
    exact (C2_log_normSq_derivatives hU hi (hKU hx)
      (ne_of_gt (lt_of_lt_of_le hc (hpi x hx)))).1.symm
  · apply (v2.congr_right eg2).congr
    filter_upwards [hf, hpos] with i hi hpi
    intro x hx
    exact (C2_log_normSq_derivatives hU hi (hKU hx)
      (ne_of_gt (lt_of_lt_of_le hc (hpi x hx)))).2.symm

end
end SymmetricMahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_HolomorphicLogC2
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology
namespace SymmetricMahler
noncomputable section
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype J]

theorem uniform_C2_log_sumNormSq_of_holomorphic [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {K U : Set E} {f : I → J → E → ℂ} {g : J → E → ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ∀ j, DifferentiableOn ℂ (g j) U)
    (hf : ∀ᶠ i in l, ∀ j, DifferentiableOn ℂ (f i j) U)
    (hp : ∀ x ∈ K, 0 < ∑ j, Complex.normSq (g j x))
    (h0 : ∀ j, TendstoUniformlyOn (fun i => f i j) (g j) l K)
    (h1 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (f i j)) (fderiv ℂ (g j)) l K)
    (h2 : ∀ j, TendstoUniformlyOn (fun i => fderiv ℂ (fderiv ℂ (f i j)))
      (fderiv ℂ (fderiv ℂ (g j))) l K) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, ∀ x ∈ K, c ≤ ∑ j, Complex.normSq (f i j x)) ∧
    TendstoUniformlyOn (fun i x => Real.log (∑ j, Complex.normSq (f i j x)))
      (fun x => Real.log (∑ j, Complex.normSq (g j x))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x))))
      (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x)))) l K ∧
    TendstoUniformlyOn
      (fun i => fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (f i j x)))))
      (fderiv ℝ (fderiv ℝ (fun x => Real.log (∑ j, Complex.normSq (g j x))))) l K := by
  apply uniform_C2_log_sumNormSq hK hU hKU
    (fun j => Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 (hg j))
    (hf.mono (fun i hi j => Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 (hi j)))
    hp h0 h1 h2

lemma isCompact_logCompactAnnulus (n : ℕ) : IsCompact (logCompactAnnulus n) :=
  (isCompact_closedBall _ _).diff isOpen_ball

lemma logCompactAnnulus_subset_ball (n : ℕ) :
    logCompactAnnulus n ⊆ ball 0 4 :=
  sdiff_subset.trans (closedBall_subset_ball (by norm_num : (2 : ℝ) < 4))

lemma logCompactAnnulus_ne_zero {n : ℕ} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ logCompactAnnulus n) : z ≠ 0 := by
  intro he
  exact hz.2 (he ▸ mem_ball_self (by norm_num : (0 : ℝ) < 1/2))

end
end SymmetricMahler

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

lemma polynomialMap_differentiable {n N : ℕ} (G : Fin N → MvPolynomial (Fin n) ℂ) :
    ∀ j, Differentiable ℂ (polynomialMap G j) := by
  intro j x
  have ha : AnalyticAt ℂ (fun z : ComplexEuclidean n =>
      MvPolynomial.eval (fun i => z i) (G j)) x :=
    AnalyticAt.aeval_mvPolynomial
      (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)
  exact ha.differentiableAt

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
-- module Solutions.OAIS_Mahler.Mahler_NormSquareForm
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SphereFlux
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology BigOperators

namespace Mahler

lemma continuous_sphereJetDensity (k : ℕ) : Continuous (sphereJetDensity k) := by
  apply continuous_wedge_eval
  · intro v
    change Continuous (fun p : ComplexEuclidean (k+1) × RealComplexTwoJet _ =>
      (inner ℝ p.1 (v 0) : ℂ))
    exact Complex.continuous_ofReal.comp (continuous_fst.inner continuous_const)
  · intro v
    exact (continuous_boundaryJet_eval k v).comp continuous_snd

lemma boundaryForm_pullback_scale {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (u : E → ℂ) (k : ℕ) (x : E) (r : ℝ) :
    (boundaryForm u k x).compLinearMap (realDilation r).toLinearMap =
      ((r : ℂ)^(2*k+1)) • boundaryForm u k x := by
  ext v
  change boundaryForm u k x (fun i => r • v i) = _
  rw [AlternatingMap.map_smul_univ]
  simp [AlternatingMap.smul_apply, smul_eq_mul, Complex.real_smul,
    Fintype.card_sum, card_wedgePowerSlots, add_comm]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereFluxLimit
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

/-- Uniform first and second derivative convergence gives uniform convergence
of the actual outward sphere densities. The nonlinear operation is a continuous
finite shuffle polynomial. -/
theorem sphereDensity_tendstoUniformlyOn {k : ℕ} {I : Type*} {l : Filter I}
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    TendstoUniformlyOn
      (fun i x => sphereJetDensity k (x, actualRealComplexJet (u i) x))
      (fun x => sphereJetDensity k (x, actualRealComplexJet v x)) l K := by
  have hj := SymmetricMahler.uniform_pair
    (V := ComplexEuclidean (k+1) →L[ℝ] ℂ)
    (W := ComplexEuclidean (k+1) →L[ℝ] (ComplexEuclidean (k+1) →L[ℝ] ℂ)) h1 h2
  have hid : TendstoUniformlyOn (fun (_ : I) (x : ComplexEuclidean (k+1)) => x) id l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (by intro i x hx; simpa using hε)
  exact SymmetricMahler.uniform_comp_of_compact hK (continuousOn_id.prodMk hv)
    (SymmetricMahler.uniform_pair hid hj) (continuous_sphereJetDensity k)

/-- A genuine area integral limit; continuity gives measurability, compactness
gives a bounded limit density, and uniform convergence supplies a common
integrable constant bound. No integral convergence is a hypothesis. -/
theorem sphereJetIntegral_tendsto {k : ℕ} {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated]
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (hu : ∀ᶠ i in l, ContinuousOn (actualRealComplexJet (u i)) K)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    Tendsto (fun i => ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)
        ∂sphereArea (k+1)) l
      (𝓝 (∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)
          ∂sphereArea (k+1))) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  have hc : ContinuousOn (fun x => sphereJetDensity k (x, actualRealComplexJet v x)) K :=
    (continuous_sphereJetDensity k).comp_continuousOn (continuousOn_id.prodMk hv)
  have huni := sphereDensity_tendstoUniformlyOn hK hv h1 h2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [hu] with i hi
    have hci : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)) :=
      ((continuous_sphereJetDensity k).comp_continuousOn
        (continuousOn_id.prodMk hi)).comp_continuous continuous_subtype_val
          (fun z => hS z.property)
    exact hci.aestronglyMeasurable
  · refine ⟨C+1, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp huni 1 (by norm_num)] with i hi
    apply ae_of_all
    intro z
    have hb := hC z (hS z.property)
    have hd := hi z (hS z.property)
    have hh := dist_triangle
      (sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z))
      (sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)) 0
    simp only [dist_zero_right] at hh
    rw [dist_comm] at hd
    linarith
  · apply ae_of_all
    intro z
    exact huni.tendsto_at (hS z.property)

/-- The limit for actual d^c u wedge (dd^c u)^k, not a surrogate jet integral. -/
theorem unitSphereFlux_tendsto {k : ℕ} {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated]
    {u : I → ComplexEuclidean (k+1) → ℂ} {v : ComplexEuclidean (k+1) → ℂ}
    {K : Set (ComplexEuclidean (k+1))} (hK : IsCompact K)
    (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ContinuousOn (actualRealComplexJet v) K)
    (hu : ∀ᶠ i in l, ContinuousOn (actualRealComplexJet (u i)) K)
    (hdv : ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ v) x)
    (hdu : ∀ᶠ i in l, ∀ x ∈ K, DifferentiableAt ℝ (fderiv ℝ (u i)) x)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i)))
      (fderiv ℝ (fderiv ℝ v)) l K) :
    Tendsto (fun i => unitSphereFlux k (u i)) l (𝓝 (unitSphereFlux k v)) := by
  have ht := sphereJetIntegral_tendsto hK hS hv hu h1 h2
  have he : (fun i => unitSphereFlux k (u i)) =ᶠ[l]
      (fun i => ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet (u i) z)
          ∂sphereArea (k+1)) := by
    filter_upwards [hdu] with i hi
    apply integral_congr_ae
    apply ae_of_all
    intro z
    exact congrArg (sphereDensity k z) (boundaryForm_eq_jet (hi z (hS z.property)) k)
  have hev : unitSphereFlux k v =
      ∫ z : sphere (0 : ComplexEuclidean (k+1)) 1,
        sphereJetDensity k ((z : ComplexEuclidean (k+1)), actualRealComplexJet v z)
          ∂sphereArea (k+1) := by
    apply integral_congr_ae
    apply ae_of_all
    intro z
    exact congrArg (sphereDensity k z) (boundaryForm_eq_jet (hdv z (hS z.property)) k)
  rw [hev]
  exact ht.congr' he.symm

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_LogDilation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

lemma boundaryForm_congr {u v : E → ℂ} {x : E} (h : u =ᶠ[𝓝 x] v) (k : ℕ) :
    boundaryForm u k x = boundaryForm v k x := by
  have hf : oneForm (dcLinear u) =ᶠ[𝓝 x] oneForm (dcLinear v) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [oneForm, dcLinear, hy]
  unfold boundaryForm extDeriv
  rw [hf.eq_of_nhds, hf.fderiv_eq]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma rescaledLog_eventually [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {τ : E → ℝ} {r : ℝ} {x : E} (m : ℕ)
    (hr : 0 < r) (hτ : ContinuousAt τ (r • x)) (hp : 0 < τ (r • x)) :
    rescaledLog τ m r =ᶠ[𝓝 x]
      (fun y => (Real.log (τ (r • y)) : ℂ) - ((2*m : ℕ) : ℂ) * (Real.log r : ℂ)) := by
  have hc : ContinuousAt (fun y : E => τ (r • y)) x :=
    hτ.comp (realDilation r).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hp)] with y hy
  unfold rescaledLog
  rw [Real.log_mul (inv_ne_zero (pow_ne_zero _ hr.ne')) hy.ne', Real.log_inv, Real.log_pow]
  push_cast
  ring

/-- Literal logarithmic rescaling pulls back d^c log tau and every dd^c
factor, with no extra scale or orientation sign. -/
theorem boundaryForm_rescaledLog {τ : E → ℝ} {r : ℝ} {x : E}
    (hr : 0 < r) (hτ : ContinuousAt τ (r • x)) (hp : 0 < τ (r • x))
    (hu : ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • x)) (m k : ℕ) :
    boundaryForm (rescaledLog τ m r) k x =
      (boundaryForm (fun y => (Real.log (τ y) : ℂ)) k (r • x)).compLinearMap
        (realDilation r).toLinearMap := by
  rw [boundaryForm_congr (rescaledLog_eventually m hr hτ hp) k]
  exact boundaryForm_dilation hu _ k

/-- Equality for actual Euclidean surface integrals, before taking a limit. -/
theorem smallSphereFlux_log_eq {k m : ℕ} {τ : ComplexEuclidean (k+1) → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hτ : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContinuousAt τ (r • (z : ComplexEuclidean (k+1))))
    (hp : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      0 < τ (r • (z : ComplexEuclidean (k+1))))
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • (z : ComplexEuclidean (k+1)))) :
    smallSphereFlux k (fun y => (Real.log (τ y) : ℂ)) r =
      unitSphereFlux k (rescaledLog τ m r) := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [boundaryForm_rescaledLog hr (hτ z) (hp z) (hu z) m k, boundaryForm_pullback_scale]
  unfold sphereDensity
  rw [wedge_smul_right]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuousOn_actualRealComplexJet [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {u : E → ℂ} {K : Set E}
    (hu : ∀ x ∈ K, ContDiffAt ℝ 2 u x) : ContinuousOn (actualRealComplexJet u) K := by
  intro x hx
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) x := (hu x hx).fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ u)) x := h1.fderiv_right (by norm_num)
  exact (h1.continuousAt.prodMk h2.continuousAt).continuousWithinAt

/-- A limit theorem whose analytic inputs are C^2 regularity
and uniform first/second log jets on a compact annulus (or any compact set
containing the sphere). Transport and integral convergence are conclusions. -/
theorem smallSphereFlux_log_tendsto {k m : ℕ} {τ : ComplexEuclidean (k+1) → ℝ}
    {v : ComplexEuclidean (k+1) → ℂ} {K : Set (ComplexEuclidean (k+1))}
    (hK : IsCompact K) (hS : sphere (0 : ComplexEuclidean (k+1)) 1 ⊆ K)
    (hv : ∀ x ∈ K, ContDiffAt ℝ 2 v x)
    (hu : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ x ∈ K, ContDiffAt ℝ 2 (rescaledLog τ m r) x)
    (hτ : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContinuousAt τ (r • (z : ComplexEuclidean (k+1))))
    (hp : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      0 < τ (r • (z : ComplexEuclidean (k+1))))
    (hlog : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 (fun y => (Real.log (τ y) : ℂ)) (r • (z : ComplexEuclidean (k+1))))
    (h1 : TendstoUniformlyOn (fun r => fderiv ℝ (rescaledLog τ m r))
      (fderiv ℝ v) (𝓝[>] 0) K)
    (h2 : TendstoUniformlyOn (fun r => fderiv ℝ (fderiv ℝ (rescaledLog τ m r)))
      (fderiv ℝ (fderiv ℝ v)) (𝓝[>] 0) K) :
    Tendsto (smallSphereFlux k (fun y => (Real.log (τ y) : ℂ))) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k v)) := by
  have ht := unitSphereFlux_tendsto hK hS (continuousOn_actualRealComplexJet hv)
    (hu.mono (fun r hr => continuousOn_actualRealComplexJet hr))
    (fun x hx => ((hv x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (hu.mono (fun r hr x hx => ((hr x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))) h1 h2
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin, hτ, hp, hlog] with r hr htr hpr hlr
  exact (smallSphereFlux_log_eq hr htr hpr hlr).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_OrientedSphereDensity
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_RescalingEstimates
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology

section Schwarz
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A centered Schwarz bound with a uniform bound on values. -/
lemma fderiv_bound_of_ball_bound {f : E → F} {x : E} {R r C : ℝ}
    (hr : 0 < r) (hx : ‖x‖ + r ≤ R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hbound : ∀ z ∈ ball (0 : E) R, ‖f z‖ ≤ C) :
    ‖fderiv ℂ f x‖ ≤ 2*C/r := by
  have hsub : ball x r ⊆ ball (0 : E) R := by
    intro z hz
    have htri := norm_add_le (z-x) x
    have hdist : ‖z-x‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    rw [sub_add_cancel] at htri
    rw [mem_ball,dist_zero_right]
    linarith
  have hxin : x ∈ ball (0 : E) R := hsub (mem_ball_self hr)
  apply Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) _ hr
  intro z hz
  rw [mem_closedBall,dist_eq_norm]
  exact (norm_sub_le _ _).trans (by linarith [hbound z (hsub hz),hbound x hxin])

/-- Two nested Schwarz estimates give uniform first and second derivative
bounds on a fixed neighborhood of the unit sphere. -/
theorem two_derivative_bounds {f : E → F} {C : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 4))
    (hf' : DifferentiableOn ℂ (fderiv ℂ f) (ball 0 4))
    (hbound : ∀ z ∈ ball (0 : E) 4, ‖f z‖ ≤ C) :
    ∀ z ∈ closedBall (0 : E) 2,
      ‖f z‖ ≤ C ∧ ‖fderiv ℂ f z‖ ≤ 2*C ∧
        ‖fderiv ℂ (fderiv ℂ f) z‖ ≤ 4*C := by
  have hfirst : ∀ z ∈ ball (0 : E) 3, ‖fderiv ℂ f z‖ ≤ 2*C := by
    intro z hz
    have hz' : ‖z‖ < 3 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [div_one] using fderiv_bound_of_ball_bound (r := 1) (by norm_num)
      (by linarith : ‖z‖+1 ≤ 4) hf hbound
  intro z hz
  have hz' : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hz3 : z ∈ ball (0 : E) 3 := by rw [mem_ball,dist_zero_right]; linarith
  refine ⟨hbound z (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4) hz3),hfirst z hz3,?_⟩
  have h := fderiv_bound_of_ball_bound (f := fderiv ℂ f) (r := 1) (by norm_num)
    (by linarith : ‖z‖+1 ≤ 3) (hf'.mono (ball_subset_ball (by norm_num : (3 : ℝ) ≤ 4))) hfirst
  nlinarith
end Schwarz

section Remainder
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The punctured Taylor estimate yields a uniform O(epsilon) bound after
rescaling on any prescribed bounded ball. This includes the center. -/
theorem rescaled_remainder_bound {f : E → F} {m : ℕ} (hf0 : f 0 = 0)
    (hf : f =O[𝓝[≠] 0] (fun z : E => ‖z‖^(m+1))) {B : ℝ} (hB : 0 < B) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ z : E, ‖z‖ ≤ B → ‖(ε^m)⁻¹ • f (ε • z)‖ ≤ C*ε := by
  obtain ⟨c,hc,hcf⟩ := hf.exists_pos
  have hfull : IsBigOWith c (𝓝 (0 : E)) f (fun z : E => ‖z‖^(m+1)) := by
    have h := hcf.insert (by simp [hf0])
    have hs : insert (0 : E) ({0}ᶜ : Set E) = univ := by
      ext z
      simp
      tauto
    rw [hs,nhdsWithin_univ] at h
    exact h
  obtain ⟨r,hr,hrbound⟩ := Metric.eventually_nhds_iff.mp hfull.bound
  refine ⟨c*B^(m+1),by positivity,r/B,by positivity,?_⟩
  intro ε hε hεδ z hz
  have hzball : dist (ε • z) (0 : E) < r := by
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left hz hε.le).trans_lt ((lt_div_iff₀ hB).mp hεδ)
  have hb := hrbound hzball
  have hm : 0 < ε^m := pow_pos hε m
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (ε^m)⁻¹ * (c*‖ε • z‖^(m+1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm.le)
      simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hb
    _ ≤ (ε^m)⁻¹ * (c*(ε*B)^(m+1)) := by
      gcongr
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
      exact mul_le_mul_of_nonneg_left hz hε.le
    _ = c*B^(m+1)*ε := by
      rw [mul_pow,pow_succ ε m]
      field_simp
end Remainder

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RescaledHolomorphic
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

/-- Uniform control of the entire second-order jet of a holomorphic Taylor
remainder near the unit sphere, derived from the punctured bound. -/
theorem rescaled_holomorphic_remainder_C2_bound {f : E → ℂ} {m : ℕ} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0) (hrem : f =O[𝓝[≠] 0] (fun z : E => ‖z‖^(m+1))) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      DifferentiableOn ℂ (rescale f m ε) (ball 0 4) ∧
      ∀ z ∈ closedBall (0 : E) 2,
        ‖rescale f m ε z‖ ≤ C*ε ∧
        ‖fderiv ℂ (rescale f m ε) z‖ ≤ C*ε ∧
        ‖fderiv ℂ (fderiv ℂ (rescale f m ε)) z‖ ≤ C*ε := by
  obtain ⟨C,hC,δ,hδ,hbound⟩ := rescaled_remainder_bound hf0 hrem (by norm_num : (0 : ℝ) < 4)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  refine ⟨4*C,by positivity,min δ (r/4),lt_min hδ (by positivity),?_⟩
  intro ε hε hεδ
  have hεδ' := (lt_min_iff.mp hεδ).1
  have hεr := (lt_min_iff.mp hεδ).2
  have hmaps : MapsTo (fun z : E => ε • z) (ball 0 4) U := by
    intro z hz
    apply hrU
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε]
    have hz' : ‖z‖ < 4 := by simpa only [mem_ball,dist_zero_right] using hz
    have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hεr
    nlinarith
  have hd : DifferentiableOn ℂ (rescale f m ε) (ball 0 4) :=
    (hf.comp ((differentiable_id.const_smul ε).differentiableOn) hmaps).const_smul (ε^m)⁻¹
  have hcd := Mahler.contDiffOn_nat_of_differentiableOn_open isOpen_ball 2 hd
  have hcd' : ContDiffOn ℂ 1 (fderiv ℂ (rescale f m ε)) (ball 0 4) :=
    hcd.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hdb := two_derivative_bounds hd (hcd'.differentiableOn (by norm_num))
    (fun z hz => hbound ε hε hεδ' z (by
      exact le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)))
  refine ⟨hd,?_⟩
  intro z hz
  obtain ⟨h0,h1,h2⟩ := hdb z hz
  exact ⟨h0.trans (by nlinarith),h1.trans (by nlinarith),by nlinarith⟩

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RescaledMassMap
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter Asymptotics
open scoped Topology
variable {n N m : ℕ}

lemma leadingComponent_differentiable (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N) :
    Differentiable ℂ (leadingComponent G j) := by
  intro x
  exact (AnalyticAt.aeval_mvPolynomial
    (fun i : Fin n => (EuclideanSpace.proj (𝕜 := ℂ) i).analyticAt x) (G j)).differentiableAt

lemma homogeneous_eval_scale {p : MvPolynomial (Fin n) ℂ} (hp : p.IsHomogeneous m)
    (z : Fin n → ℂ) (c : ℂ) :
    MvPolynomial.eval (fun i => c*z i) p = c^m * MvPolynomial.eval z p := by
  classical
  simp only [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,← hp.degree_eq_sum_deg_support hd]
  ring

lemma leadingComponent_scale (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N)
    (hG : (G j).IsHomogeneous m) (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    leadingComponent G j (ε • z) = (ε^m) • leadingComponent G j z := by
  simpa only [leadingComponent,PiLp.smul_apply,Complex.real_smul,Complex.ofReal_pow] using!
    homogeneous_eval_scale hG (fun i => z i) (ε : ℂ)

lemma leadingComponent_zero (G : Fin N → MvPolynomial (Fin n) ℂ) (j : Fin N)
    (hG : (G j).IsHomogeneous m) (hm : 0 < m) : leadingComponent G j 0 = 0 := by
  simpa only [zero_smul,zero_pow (Nat.ne_of_gt hm)] using leadingComponent_scale G j hG 0 0

lemma source_remainder_bound {U : Set (Mahler.ComplexEuclidean n)}
    {f : Fin N → Mahler.ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    taylorRemainder f G j =O[𝓝[≠] 0] (fun z : Mahler.ComplexEuclidean n => ‖z‖^(m+1)) := by
  have hc := (EuclideanSpace.proj (𝕜 := ℂ) j).isBigO_comp
    (fun z => (WithLp.toLp 2 (fun j => f j z - MvPolynomial.eval (fun i => z i) (G j)) :
      Mahler.ComplexEuclidean N)) (𝓝[≠] (0 : Mahler.ComplexEuclidean n))
  exact hc.trans h.taylor_remainder

lemma source_remainder_zero {U : Set (Mahler.ComplexEuclidean n)}
    {f : Fin N → Mahler.ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}
    (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) : taylorRemainder f G j 0 = 0 := by
  have hf := (h.isolated_zero 0 h.zero_mem).mpr rfl
  simp only [taylorRemainder,hf j,leadingComponent_zero G j (h.homogeneous j) (by have hm := h.degree_pos; omega),sub_self]

lemma rescaled_source_remainder {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
    {G : Fin N → MvPolynomial (Fin n) ℂ} (hG : ∀ j, (G j).IsHomogeneous m)
    {ε : ℝ} (hε : ε ≠ 0) (j : Fin N) :
    rescale (taylorRemainder f G j) m ε =
      fun z => rescale (f j) m ε z - leadingComponent G j z := by
  funext z
  simp only [rescale,taylorRemainder,smul_sub,leadingComponent_scale G j (hG j) ε z,
    inv_smul_smul₀ (pow_ne_zero m hε)]

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_UniformJet
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter
open scoped Topology

theorem uniform_of_linear_error {X H : Type*} [NormedAddCommGroup H]
    {F : ℝ → X → H} {g : X → H} {K : Set X} {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < δ → ∀ x ∈ K, ‖F ε x-g x‖ ≤ C*ε) :
    TendstoUniformlyOn F g (𝓝[>] 0) K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min δ (η/C) :=
    (eventually_lt_nhds (lt_min hδ (div_pos hη hC))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hsmall] with ε hε hsmall'
  intro x hx
  have hεpos : 0 < ε := hε
  have hb := hbound ε hεpos (lt_min_iff.mp hsmall').1 x hx
  rw [dist_eq_norm']
  exact hb.trans_lt (by
    have h := (lt_div_iff₀ hC).mp (lt_min_iff.mp hsmall').2
    nlinarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Differentiating the actual first derivative on an open set preserves
subtraction through order two; holomorphicity supplies the required smoothness. -/
lemma second_fderiv_sub_of_open {f g : E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    fderiv ℂ (fderiv ℂ (fun y => f y-g y)) x =
      fderiv ℂ (fderiv ℂ f) x - fderiv ℂ (fderiv ℂ g) x := by
  have he : fderiv ℂ (fun y => f y-g y) =ᶠ[𝓝 x]
      fun y => fderiv ℂ f y - fderiv ℂ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_fun_sub ((hf y hy).differentiableAt (hU.mem_nhds hy))
      ((hg y hy).differentiableAt (hU.mem_nhds hy))
  rw [he.fderiv_eq]
  have hfc : ContDiffOn ℂ 1 (fderiv ℂ f) U :=
    (Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 hf).fderiv_of_isOpen hU (by norm_num)
  have hgc : ContDiffOn ℂ 1 (fderiv ℂ g) U :=
    (Mahler.contDiffOn_nat_of_differentiableOn_open hU 2 hg).fderiv_of_isOpen hU (by norm_num)
  exact fderiv_fun_sub ((hfc.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx))
    ((hgc.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx))

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceRescaling
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MahlerRescaling
open Set Metric Filter
open scoped Topology
variable {n N m : ℕ} {U : Set (Mahler.ComplexEuclidean n)}
  {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
  {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The rescaled functions themselves, with their actual Frechet derivatives,
converge at order epsilon to the stated homogeneous leading polynomial. -/
theorem source_rescaling_C2_bound (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) ∧
      ∀ z ∈ closedBall (0 : Mahler.ComplexEuclidean n) 2,
        ‖rescale (f j) m ε z-leadingComponent G j z‖ ≤ C*ε ∧
        ‖fderiv ℂ (rescale (f j) m ε) z-fderiv ℂ (leadingComponent G j) z‖ ≤ C*ε ∧
        ‖fderiv ℂ (fderiv ℂ (rescale (f j) m ε)) z-
          fderiv ℂ (fderiv ℂ (leadingComponent G j)) z‖ ≤ C*ε := by
  obtain ⟨C,hC,δ,hδ,hb⟩ := rescaled_holomorphic_remainder_C2_bound
    (f := taylorRemainder f G j) h.open_domain h.zero_mem
    ((h.holomorphic j).sub (leadingComponent_differentiable G j).differentiableOn)
    (source_remainder_zero h j) (source_remainder_bound h j)
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hdr,hbound⟩ := hb ε hε hεδ
  have he := rescaled_source_remainder (f := f) h.homogeneous hε.ne' j
  have headd : rescale (f j) m ε =
      fun z => rescale (taylorRemainder f G j) m ε z+leadingComponent G j z := by
    funext z
    rw [he]
    exact (sub_add_cancel _ _).symm
  have hdf : DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) := by
    rw [headd]
    exact hdr.add (leadingComponent_differentiable G j).differentiableOn
  refine ⟨hdf,?_⟩
  intro z hz
  have hz4 : z ∈ ball (0 : Mahler.ComplexEuclidean n) 4 :=
    closedBall_subset_ball (by norm_num : (2 : ℝ) < 4) hz
  have hd1 : fderiv ℂ (rescale (taylorRemainder f G j) m ε) z =
      fderiv ℂ (rescale (f j) m ε) z - fderiv ℂ (leadingComponent G j) z := by
    rw [he]
    exact fderiv_fun_sub ((hdf z hz4).differentiableAt (isOpen_ball.mem_nhds hz4))
      (leadingComponent_differentiable G j z)
  have hd2 : fderiv ℂ (fderiv ℂ (rescale (taylorRemainder f G j) m ε)) z =
      fderiv ℂ (fderiv ℂ (rescale (f j) m ε)) z-
        fderiv ℂ (fderiv ℂ (leadingComponent G j)) z := by
    rw [he]
    exact second_fderiv_sub_of_open isOpen_ball hz4 hdf
      (leadingComponent_differentiable G j).differentiableOn
  obtain ⟨h0,h1,h2⟩ := hbound z hz
  refine ⟨?_,?_,?_⟩
  · simpa only [he] using h0
  · rwa [hd1] at h1
  · rwa [hd2] at h2

/-- The exact C² convergence used at the small-sphere limit, expressed in
uniform convergence of the function and its first two complex derivatives. -/
theorem source_rescaling_uniform_C2 (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    TendstoUniformlyOn (fun ε : ℝ => rescale (f j) m ε) (leadingComponent G j)
      (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (rescale (f j) m ε))
      (fderiv ℂ (leadingComponent G j)) (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale (f j) m ε)))
      (fderiv ℂ (fderiv ℂ (leadingComponent G j))) (𝓝[>] 0) (closedBall 0 2) := by
  obtain ⟨C,hC,δ,hδ,hb⟩ := source_rescaling_C2_bound h j
  refine ⟨uniform_of_linear_error hC hδ ?_,uniform_of_linear_error hC hδ ?_,?_⟩
  · intro ε hε hεδ z hz
    exact ((hb ε hε hεδ).2 z hz).1
  · intro ε hε hεδ z hz
    exact ((hb ε hε hεδ).2 z hz).2.1
  · exact uniform_of_linear_error (F := fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale (f j) m ε)))
      (g := fderiv ℂ (fderiv ℂ (leadingComponent G j))) hC hδ
      (fun ε hε hεδ z hz => ((hb ε hε hεδ).2 z hz).2.2)

end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceLogC2
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology
namespace MahlerRescaling
noncomputable section
variable {n N m : ℕ} {U : Set (Mahler.ComplexEuclidean n)}
  {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
  {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The norm sum is the rescaled tau, with no
normalization factor omitted. This identity also holds at epsilon=0. -/
lemma rescaled_sumNormSq_eq_tau (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    (∑ j, Complex.normSq (rescale (f j) m ε z)) =
      (ε^(2*m))⁻¹ * Mahler.tau f (ε • z) := by
  simp only [rescale, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two, ← inv_pow, ← pow_mul, Nat.mul_comm m 2, Mahler.tau, Finset.mul_sum]

lemma rescaledLogEnergy_eq_log_tau (ε : ℝ) (z : Mahler.ComplexEuclidean n) :
    rescaledLogEnergy f m ε z = Real.log ((ε^(2*m))⁻¹ * Mahler.tau f (ε • z)) := by
  rw [rescaledLogEnergy, rescaled_sumNormSq_eq_tau]

theorem source_rescaling_log_uniform_C2 (h : Mahler.MassHypotheses n N m U f G) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ z ∈ SymmetricMahler.logCompactAnnulus n,
        c ≤ ∑ j, Complex.normSq (rescale (f j) m ε z)) ∧
    TendstoUniformlyOn (rescaledLogEnergy f m) (leadingLogEnergy G)
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn (fun ε => fderiv ℝ (rescaledLogEnergy f m ε))
      (fderiv ℝ (leadingLogEnergy G)) (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) ∧
    TendstoUniformlyOn (fun ε => fderiv ℝ (fderiv ℝ (rescaledLogEnergy f m ε)))
      (fderiv ℝ (fderiv ℝ (leadingLogEnergy G)))
      (𝓝[>] 0) (SymmetricMahler.logCompactAnnulus n) := by
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j,
      DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) := by
    apply Filter.eventually_all.mpr
    intro j
    obtain ⟨C, hC, δ, hδ, hb⟩ := source_rescaling_C2_bound h j
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεδ
    exact (hb ε hε hεδ).1
  have hp : ∀ z ∈ SymmetricMahler.logCompactAnnulus n,
      0 < ∑ j, Complex.normSq (leadingComponent G j z) := by
    intro z hz
    obtain ⟨j, hj⟩ := h.leading_nonzero z (SymmetricMahler.logCompactAnnulus_ne_zero hz)
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩
  have hk : SymmetricMahler.logCompactAnnulus n ⊆
      closedBall (0 : Mahler.ComplexEuclidean n) 2 := sdiff_subset
  exact SymmetricMahler.uniform_C2_log_sumNormSq_of_holomorphic
    (SymmetricMahler.isCompact_logCompactAnnulus n) isOpen_ball
    (SymmetricMahler.logCompactAnnulus_subset_ball n)
    (fun j => (leadingComponent_differentiable G j).differentiableOn) he hp
    (fun j => ((source_rescaling_uniform_C2 h j).1).mono hk)
    (fun j => ((source_rescaling_uniform_C2 h j).2.1).mono hk)
    (fun j => ((source_rescaling_uniform_C2 h j).2.2).mono hk)

end
end MahlerRescaling

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SourceSphereLimit
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Filter Set
open scoped Topology

namespace Mahler

lemma isCompact_sphereAnnulus (n : ℕ) : IsCompact (sphereAnnulus n) :=
  (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

lemma sphere_subset_annulus (n : ℕ) : sphere (0 : ComplexEuclidean n) 1 ⊆ sphereAnnulus n := by
  intro z hz
  have hn : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
  constructor <;> norm_num [mem_closedBall, dist_zero_right, hn]

lemma sphereAnnulus_ne_zero {n : ℕ} {z : ComplexEuclidean n} (hz : z ∈ sphereAnnulus n) : z ≠ 0 := by
  intro he
  have := hz.2
  norm_num [he] at this

/-- All regularity and positivity for small rescaled points follows from the
literal open-domain and isolated-zero hypotheses. -/
theorem MassHypotheses.eventually_sphereAnnulus_log_regular {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ sphereAnnulus (k+1),
      ContinuousAt (tau f) (r • z) ∧ 0 < tau f (r • z) ∧
      ContDiffAt ℝ 2 (logTau f) (r • z) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp h.open_domain 0 h.zero_mem
  have hd : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ/3 :=
    (eventually_lt_nhds (by linarith : (0 : ℝ) < δ/3)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hd] with r hr hdr
  intro z hz
  have hz2 : ‖z‖ ≤ 2 := by simpa [mem_closedBall, dist_zero_right] using hz.1
  have hmem : r • z ∈ U := by
    apply hball
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hr0 : 0 < r := hr
    nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hz2)]
  have hnz : r • z ≠ 0 := smul_ne_zero hr.ne' (sphereAnnulus_ne_zero hz)
  have hp : 0 < tau f (r • z) := by
    apply tau_pos_of_component_ne_zero
    by_contra he
    push Not at he
    exact hnz ((h.isolated_zero _ hmem).mp he)
  have hf := fun j => (h.holomorphic j (r • z) hmem).differentiableAt (h.open_domain.mem_nhds hmem)
  have hc : ContinuousAt (tau f) (r • z) := by
    have hc := Complex.continuous_re.continuousAt.comp (differentiable_energy hf).continuousAt
    simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using hc
  exact ⟨hc, hp, contDiffAt_logTau_of_open h.open_domain hmem h.holomorphic hp⟩

/-- C^2 regularity of the actual rescaled logarithm; no regularity premise is
added to MassHypotheses. -/
theorem MassHypotheses.eventually_rescaledLog_C2 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ sphereAnnulus (k+1),
      ContDiffAt ℝ 2 (rescaledLog (tau f) m r) z := by
  filter_upwards [self_mem_nhdsWithin, h.eventually_sphereAnnulus_log_regular] with r hr hreg
  intro z hz
  obtain ⟨hc, hp, hl⟩ := hreg z hz
  have he := rescaledLog_eventually m hr hc hp
  have hs : ContDiffAt ℝ 2 (fun y => logTau f (r • y) - ((2*m : ℕ) : ℂ) * (Real.log r : ℂ)) z :=
    (hl.comp z (realDilation r).contDiff.contDiffAt).sub contDiffAt_const
  exact hs.congr_of_eventuallyEq he

theorem MassHypotheses.actual_small_sphere_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (h1 : TendstoUniformlyOn (fun r => fderiv ℝ (rescaledLog (tau f) m r))
      (fderiv ℝ (logTau (polynomialMap G))) (𝓝[>] 0) (sphereAnnulus (k+1)))
    (h2 : TendstoUniformlyOn (fun r => fderiv ℝ (fderiv ℝ (rescaledLog (tau f) m r)))
      (fderiv ℝ (fderiv ℝ (logTau (polynomialMap G)))) (𝓝[>] 0) (sphereAnnulus (k+1))) :
    Tendsto (smallSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  have hg : ∀ z ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (logTau (polynomialMap G)) z := by
    intro z hz
    apply contDiffAt_logTau_of_open isOpen_univ (mem_univ z)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
    exact tau_pos_of_component_ne_zero (h.leading_nonzero z (sphereAnnulus_ne_zero hz))
  have hc := h.eventually_sphereAnnulus_log_regular
  apply smallSphereFlux_log_tendsto (isCompact_sphereAnnulus (k+1)) (sphere_subset_annulus (k+1))
    hg h.eventually_rescaledLog_C2
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).1)
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).2.1)
  · exact hc.mono (fun r hr z => (hr z (sphere_subset_annulus _ z.property)).2.2)
  · exact h1
  · exact h2

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_RealLogBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Filter Set
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_ofReal_eq {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x = complexifyDerivative (fderiv ℝ u x) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  exact hd.fderiv

lemma fderiv_twice_ofReal_eq {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    fderiv ℝ (fderiv ℝ (fun y => (u y : ℂ))) x =
      complexifySecondDerivative (fderiv ℝ (fderiv ℝ u) x) := by
  have he : fderiv ℝ (fun y => (u y : ℂ)) =ᶠ[𝓝 x]
      (fun y => complexifyDerivative (fderiv ℝ u y)) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact fderiv_ofReal_eq (hy.differentiableAt (by norm_num))
  have hd := complexifyDerivative.hasFDerivAt.comp x
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [he.fderiv_eq]
  exact hd.fderiv

/-- Scalar extension from real log jets to complex-valued real differential forms. -/
theorem uniform_log_jets_ofReal [FiniteDimensional ℝ E]
    {I : Type*} {l : Filter I} {u : I → E → ℝ} {v : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hv : ∀ x ∈ K, ContDiffAt ℝ 2 v x)
    (hu : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ 2 (u i) x)
    (h1 : TendstoUniformlyOn (fun i => fderiv ℝ (u i)) (fderiv ℝ v) l K)
    (h2 : TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (u i))) (fderiv ℝ (fderiv ℝ v)) l K) :
    TendstoUniformlyOn (fun i => fderiv ℝ (fun x => (u i x : ℂ)))
      (fderiv ℝ (fun x => (v x : ℂ))) l K ∧
    TendstoUniformlyOn (fun i => fderiv ℝ (fderiv ℝ (fun x => (u i x : ℂ))))
      (fderiv ℝ (fderiv ℝ (fun x => (v x : ℂ)))) l K := by
  have hc1 : ContinuousOn (fderiv ℝ v) K := by
    intro x hx
    exact ((hv x hx).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fderiv ℝ (fderiv ℝ v)) K := by
    intro x hx
    exact (((hv x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.continuousWithinAt
  have h1' := SymmetricMahler.uniform_comp_of_compact hK hc1 h1 complexifyDerivative.continuous
  have h2' := SymmetricMahler.uniform_comp_of_compact
    (E := E →L[ℝ] (E →L[ℝ] ℝ)) (H := E →L[ℝ] (E →L[ℝ] ℂ))
    hK hc2 h2 (complexifySecondDerivative (E := E)).continuous
  constructor
  · apply (h1'.congr_right (fun x hx => (fderiv_ofReal_eq
      ((hv x hx).differentiableAt (by norm_num))).symm)).congr
    filter_upwards [hu] with i hi
    intro x hx
    exact (fderiv_ofReal_eq ((hi x hx).differentiableAt (by norm_num))).symm
  · apply (h2'.congr_right (fun x hx => (fderiv_twice_ofReal_eq (hv x hx)).symm)).congr
    filter_upwards [hu] with i hi
    intro x hx
    exact (fderiv_twice_ofReal_eq (hi x hx)).symm

lemma sphereAnnulus_eq_logCompactAnnulus (n : ℕ) :
    sphereAnnulus n = SymmetricMahler.logCompactAnnulus n := by
  ext z
  simp [sphereAnnulus, SymmetricMahler.logCompactAnnulus, Metric.mem_ball, dist_zero_right]

theorem MassHypotheses.small_sphere_flux_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (smallSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  let u := MahlerRescaling.rescaledLogEnergy f m
  let v := MahlerRescaling.leadingLogEnergy G
  have eu (r : ℝ) : (fun x => (u r x : ℂ)) = rescaledLog (tau f) m r := by
    funext x
    rw [show u r x = Real.log ((r^(2*m))⁻¹ * tau f (r • x)) from
      MahlerRescaling.rescaledLogEnergy_eq_log_tau r x]
    rfl
  have ev : (fun x => (v x : ℂ)) = logTau (polynomialMap G) := rfl
  have hvC : ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (logTau (polynomialMap G)) x := by
    intro x hx
    exact contDiffAt_logTau_of_open isOpen_univ (mem_univ x)
      (fun j => (polynomialMap_differentiable G j).differentiableOn)
      (tau_pos_of_component_ne_zero (h.leading_nonzero x (sphereAnnulus_ne_zero hx)))
  have hvR : ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 v x := by
    intro x hx
    have hc := Complex.reCLM.contDiff.contDiffAt.comp x (hvC x hx)
    change ContDiffAt ℝ 2 (fun y => (logTau (polynomialMap G) y).re) x at hc
    simpa only [← ev, Complex.ofReal_re] using hc
  have huR : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ x ∈ sphereAnnulus (k+1), ContDiffAt ℝ 2 (u r) x := by
    filter_upwards [h.eventually_rescaledLog_C2] with r hr
    intro x hx
    have hc := Complex.reCLM.contDiff.contDiffAt.comp x (hr x hx)
    change ContDiffAt ℝ 2 (fun y => (rescaledLog (tau f) m r y).re) x at hc
    simpa only [← eu r, Complex.ofReal_re] using hc
  obtain ⟨_, _, h1, h2⟩ := MahlerRescaling.source_rescaling_log_uniform_C2 h
  rw [← sphereAnnulus_eq_logCompactAnnulus] at h1 h2
  obtain ⟨hc1, hc2⟩ := uniform_log_jets_ofReal (isCompact_sphereAnnulus (k+1)) hvR huR h1 h2
  simp only [eu, ev] at hc1 hc2
  exact h.actual_small_sphere_limit hc1 hc2

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereFluxIntegral
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_UnitaryReference
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ReferencePoleFrame
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

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

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_ReferenceSphereIntegral
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereAreaTransport
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric Set
open scoped ENNReal

namespace Mahler

lemma continuous_sphereDilation {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Continuous (sphereDilation (n := n) r hr) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : sphere (0 : ComplexEuclidean n) 1 => r • (z : ComplexEuclidean n))
  exact (continuous_const : Continuous (fun _ : sphere (0 : ComplexEuclidean n) 1 => r)).smul
    (continuous_subtype_val : Continuous (fun z : sphere (0 : ComplexEuclidean n) 1 => (z : ComplexEuclidean n)))

/-- The surface measure change of variables for an actual Bochner integral. -/
theorem integral_radiusSphereArea {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : sphere (0 : ComplexEuclidean n) r → ℂ)
    (hg : AEStronglyMeasurable g ((sphereArea n).map (sphereDilation r hr))) :
    (∫ z, g z ∂radiusSphereArea n r hr) =
      (r^(2*n-1)) • ∫ z : sphere (0 : ComplexEuclidean n) 1,
        g (sphereDilation r hr z) ∂sphereArea n := by
  rw [radiusSphereArea, integral_smul_measure, integral_map
    (continuous_sphereDilation r hr).aemeasurable hg]
  rw [ENNReal.toReal_ofReal (le_of_lt (pow_pos hr _))]

/-- The parameterized flux is also an integral on the actual radius-r sphere,
with its outward normal and Euclidean area measure. -/
theorem smallSphereFlux_eq_radiusIntegral {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (r : ℝ) (hr : 0 < r)
    (hg : AEStronglyMeasurable
      (fun z : sphere (0 : ComplexEuclidean (k+1)) r =>
        sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z))
      ((sphereArea (k+1)).map (sphereDilation r hr))) :
    smallSphereFlux k u r =
      ∫ z : sphere (0 : ComplexEuclidean (k+1)) r,
        sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)
          ∂radiusSphereArea (k+1) r hr := by
  rw [integral_radiusSphereArea r hr _ hg, ← integral_smul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have he : 2*(k+1)-1 = 2*k+1 := by omega
  simp only [sphereDilation, he, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp [Complex.real_smul]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereOrientation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set
open scoped Topology

namespace Mahler

lemma sphereDilation_surjective {n : ℕ} (r : ℝ) (hr : 0 < r) :
    Function.Surjective (sphereDilation (n := n) r hr) := by
  intro z
  have hz : ‖(z : ComplexEuclidean n)‖ = r := by simp
  let w : sphere (0 : ComplexEuclidean n) 1 := ⟨r⁻¹ • (z : ComplexEuclidean n), by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, hr.ne']⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r • (r⁻¹ • (z : ComplexEuclidean n)) = z
  simp [smul_smul, hr.ne']

lemma continuous_radiusFluxDensity {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ} (r : ℝ)
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r =>
      sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))) (boundaryForm u k z)) := by
  have hc : ContinuousOn (actualRealComplexJet u) (sphere (0 : ComplexEuclidean (k+1)) r) :=
    continuousOn_actualRealComplexJet (fun x hx => hu ⟨x,hx⟩)
  have hj : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => actualRealComplexJet u z) :=
    hc.comp_continuous continuous_subtype_val (fun z => z.property)
  have hn : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => r⁻¹ • (z : ComplexEuclidean (k+1))) :=
    (continuous_const : Continuous (fun _ : sphere (0 : ComplexEuclidean (k+1)) r => r⁻¹)).smul
      (continuous_subtype_val : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) r => (z : ComplexEuclidean (k+1))))
  have ht := (continuous_sphereJetDensity k).comp (hn.prodMk hj)
  convert ht using 1
  funext z
  exact congrArg (sphereDensity k (r⁻¹ • (z : ComplexEuclidean (k+1))))
    (boundaryForm_eq_jet ((hu z).fderiv_right (m := 1) (by norm_num)
      |>.differentiableAt (by norm_num)) k)

/-- No measurability premise is needed: C2 regularity supplies it. -/
theorem radiusSphereFlux_eq_small {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (r : ℝ) (hr : 0 < r)
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    radiusSphereFlux k u r = smallSphereFlux k u r := by
  rw [radiusSphereFlux, dite_eq_left hr]
  exact (smallSphereFlux_eq_radiusIntegral u r hr
    (continuous_radiusFluxDensity r hu).aestronglyMeasurable).symm

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SmallSphereLimits
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Metric Filter
open scoped Topology
namespace Mahler

/-- The small-sphere limit of Bochner integrals
on varying radius spheres, under the mass hypotheses alone. -/
theorem MassHypotheses.small_sphere_surface_integral_limit {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (radiusSphereFlux k (logTau f)) (𝓝[>] 0)
      (𝓝 (unitSphereFlux k (logTau (polynomialMap G)))) := by
  apply h.small_sphere_flux_limit.congr'
  filter_upwards [self_mem_nhdsWithin, h.eventually_sphereAnnulus_log_regular] with r hr hreg
  symm
  apply radiusSphereFlux_eq_small r hr
  intro z
  obtain ⟨w, hw⟩ := sphereDilation_surjective r hr z
  have he : r • (w : ComplexEuclidean (k+1)) = z := congrArg Subtype.val hw
  rw [← he]
  exact (hreg w (sphere_subset_annulus _ w.property)).2.2

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereDensityRestriction
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIS_Mahler.Mahler_SphereVolumeOrientation
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex

namespace Mahler

/-- The cofactor frame is the actual interleaved real orthonormal coordinate
frame, with the same index equivalence used for the volume form. -/
lemma sphereFrame_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sphereFrame k (ambientFinEquiv k s) = interleavedBasis s := by
  simp only [sphereFrame, OrthonormalBasis.reindex_apply,
    Pi.orthonormalBasis_apply]
  obtain ⟨j,α,h⟩ : ∃ j α, pairSlotEquiv (k+1) s = (j,α) := ⟨_,_,rfl⟩
  fin_cases α <;> simp [interleavedBasis, h, Complex.coe_orthonormalBasisOneI]

/-- The volume form evaluates to +1 on a real orthonormal frame.
This verifies its Euclidean metric normalization as well as its sign. -/
theorem sphereVolume_orthonormalFrame (k : ℕ) : sphereVolume k (sphereFrame k) = 1 := by
  rw [sphereVolume, AlternatingMap.domDomCongr_apply]
  have he : sphereFrame k ∘ ambientFinEquiv k = interleavedBasis :=
    funext (sphereFrame_interleaved k)
  rw [he, interleavedVolume_basis]

end Mahler

end OAI
end

section
-- module Solutions.OAIS_Mahler.Mahler_SphereDensityBridge
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators TensorProduct
open MeasureTheory Metric

namespace Mahler

private lemma restMap_spec {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) (j : κ) :
    Sum.inr (restMap σ h j) = σ (Sum.inr j) := by
  unfold restMap
  split
  · rename_i i he
    have hi : i = 0 := Subsingleton.elim _ _
    have hh := σ.injective (he.trans (by simpa [hi] using h.symm))
    cases hh
  · rename_i k he
    exact he.symm

private lemma perm_fixed_first_mem {κ : Type*} (σ : Equiv.Perm (Fin 1 ⊕ κ))
    (h : σ (Sum.inl 0) = Sum.inl 0) :
    σ ∈ (Equiv.Perm.sumCongrHom (Fin 1) κ).range := by
  have hs : σ.symm (Sum.inl 0) = Sum.inl 0 := by
    apply σ.injective
    simpa using h.symm
  let e : Equiv.Perm κ :=
    { toFun := restMap σ h
      invFun := restMap σ.symm hs
      left_inv := by
        intro j
        apply Sum.inr_injective (α := Fin 1)
        rw [restMap_spec, restMap_spec, σ.symm_apply_apply]
      right_inv := by
        intro j
        apply Sum.inr_injective (α := Fin 1)
        rw [restMap_spec, restMap_spec, σ.apply_symm_apply] }
  refine ⟨(Equiv.refl _, e), ?_⟩
  ext s
  cases s with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h.symm
  | inr j => exact restMap_spec σ h j

/-- The shuffle product has coefficient one on an outward normal followed
by tangent vectors. This includes its normalization, in arbitrary degree. -/
lemma wedge_one_outward {T κ : Type*} [AddCommGroup T] [Module ℝ T]
    [Fintype κ] [DecidableEq κ]
    (a : T [⋀^Fin 1]→ₗ[ℝ] ℂ) (B : T [⋀^κ]→ₗ[ℝ] ℂ)
    (x : T) (v : κ → T) (hx : a (fun _ => x) = 1)
    (hv : ∀ j, a (fun _ => v j) = 0) :
    wedge a B (Sum.elim (fun _ => x) v) = B v := by
  classical
  let q0 : Equiv.Perm.ModSumCongr (Fin 1) κ := Quotient.mk'' (1 : Equiv.Perm (Fin 1 ⊕ κ))
  change (LinearMap.mul' ℝ ℂ) (a.domCoprod B (Sum.elim (fun _ => x) v)) = _
  simp only [AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  rw [Finset.sum_eq_single q0]
  · simp [q0, AlternatingMap.domCoprod.summand_mk'', hx,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply]
  · intro q hq hne
    induction q using Quotient.inductionOn' with
    | h σ =>
      have hn : σ (Sum.inl 0) ≠ Sum.inl 0 := by
        intro he
        apply hne
        apply QuotientGroup.eq.mpr
        simpa using perm_fixed_first_mem σ he
      obtain ⟨j, hj⟩ : ∃ j, σ (Sum.inl 0) = Sum.inr j := by
        cases he : σ (Sum.inl 0) with
        | inl i => exact False.elim (hn (he.trans (congrArg Sum.inl (Subsingleton.elim i 0))))
        | inr j => exact ⟨j, rfl⟩
      have hz : a (fun i => Sum.elim (fun _ => x) v (σ (Sum.inl i))) = 0 := by
        convert hv j using 1
        congr 1
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simp [hi, hj]
      simp [AlternatingMap.domCoprod.summand_mk'',
        MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, hz]
  · simp

lemma densityBridgeSlots_normal (k : ℕ) (i : Fin 1) :
    densityBridgeSlots k (Sum.inl i) = 0 := by
  exact ambientFinEquiv_real_zero k

lemma densityBridgeSlots_tangent (k : ℕ) (j : Fin 1 ⊕ WedgePowerSlots k) :
    densityBridgeSlots k (Sum.inr j) = (boundaryFinEquiv k j).succ := by
  cases j with
  | inl i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ambientFinEquiv_imag_zero k
  | inr j => exact ambientFinEquiv_tail k j

lemma densityBridgeSlots_frame (k : ℕ) :
    sphereFrame k ∘ densityBridgeSlots k = sphereFluxFrame k := by
  funext s
  exact sphereFrame_interleaved k (sphereFrameSlots k s)

lemma densityBridgeSlots_cons (k : ℕ) (x : ComplexEuclidean (k+1))
    (v : Fin (2*k+1) → ComplexEuclidean (k+1)) :
    Matrix.vecCons x v ∘ densityBridgeSlots k =
      Sum.elim (fun _ => x) (v ∘ boundaryFinEquiv k) := by
  funext s
  cases s with
  | inl i => simp [Function.comp_def, densityBridgeSlots_normal]
  | inr j => simp [Function.comp_def, densityBridgeSlots_tangent]

/-- The recursive shuffle density is the normalized outward cofactor
coefficient. The slot equivalence preserves its positive orientation. -/
theorem sphereDensity_eq_orientedDensity {k : ℕ} {x : ComplexEuclidean (k+1)}
    (hx : ‖x‖ = 1)
    (B : ComplexEuclidean (k+1) [⋀^Fin 1 ⊕ WedgePowerSlots k]→ₗ[ℝ] ℂ) :
    sphereDensity k x B = orientedDensity (sphereFrame k) (sphereVolume k)
      (B.domDomCongr (boundaryFinEquiv k)) x := by
  classical
  let A := (wedge (sphereNormal x) B).domDomCongr (densityBridgeSlots k)
  have hframe : A (sphereFrame k) = sphereDensity k x B := by
    change wedge (sphereNormal x) B (sphereFrame k ∘ densityBridgeSlots k) = _
    rw [densityBridgeSlots_frame]
    rfl
  have hA : A = A (sphereFrame k) • sphereVolume k := by
    apply topForm_ext_on_basis (sphereFrame k).toBasis
    change A (sphereFrame k) = A (sphereFrame k) * sphereVolume k (sphereFrame k)
    rw [sphereVolume_orthonormalFrame, mul_one]
  obtain ⟨v, hv, hvol⟩ := exists_outward_tangent_frame hx
  have hnormal : sphereNormal x (fun _ => x) = 1 := by
    change (inner ℝ x x : ℂ) = 1
    simp [hx]
  have hav : A (Matrix.vecCons x v) = B (v ∘ boundaryFinEquiv k) := by
    change wedge (sphereNormal x) B (Matrix.vecCons x v ∘ densityBridgeSlots k) = _
    rw [densityBridgeSlots_cons]
    apply wedge_one_outward _ _ _ _ hnormal
    intro j
    change (inner ℝ x (v (boundaryFinEquiv k j)) : ℂ) = 0
    simp [hv]
  have he := congrArg (fun C => C (Matrix.vecCons x v)) hA
  change A (Matrix.vecCons x v) = A (sphereFrame k) * sphereVolume k (Matrix.vecCons x v) at he
  rw [hav, hframe, hvol, mul_one] at he
  have hd := orientedDensity_spec (sphereFrame k) (sphereVolume k)
    (sphereVolume_frame_ne_zero k) (B.domDomCongr (boundaryFinEquiv k)) hx v hv
  rw [hvol, mul_one] at hd
  exact he.symm.trans hd

/-- The actual boundary density is integrable: C2 regularity and compactness
supply this premise, rather than assuming an integral exists. -/
lemma integrable_sphereBoundaryDensity {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    Integrable (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k z)) (sphereArea (k+1)) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  let : CompactSpace (sphere (0 : ComplexEuclidean (k+1)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ComplexEuclidean (k+1)) 1)
  have hc : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k z)) := by
    simpa using continuous_radiusFluxDensity 1 hu
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The complex flux used for the rescaling limit and the real cofactor flux
used for homogeneous deformation have exactly the same real part. -/
theorem unitSphereFlux_re_eq_sphereFlux {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    (hu : ∀ z : sphere (0 : ComplexEuclidean (k+1)) 1,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1))) :
    (unitSphereFlux k u).re = sphereFlux k (boundaryFormFin (dcLinear u)) := by
  unfold unitSphereFlux sphereFlux
  have hi := integral_re (integrable_sphereBoundaryDensity hu)
  simp only [RCLike.re_eq_complex_re] at hi
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
  exact congrArg Complex.re (sphereDensity_eq_orientedDensity hz (boundaryForm u k z))

/-- For the homogeneous polynomial, the endpoint equality
requires only the mass hypotheses. -/
theorem MassHypotheses.unitSphereFlux_re_eq_homogeneousSphereFlux {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    (unitSphereFlux k (logTau (polynomialMap G))).re = homogeneousSphereFlux k N G := by
  apply unitSphereFlux_re_eq_sphereFlux
  intro z
  apply contDiffAt_logTau_of_open isOpen_univ (Set.mem_univ (z : ComplexEuclidean (k+1)))
    (fun j => (polynomialMap_differentiable G j).differentiableOn)
  have hz : (z : ComplexEuclidean (k+1)) ≠ 0 := by
    intro he
    have hh : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
    simp [he] at hh
  exact tau_pos_of_component_ne_zero (h.leading_nonzero z hz)

/-- The varying-radius surface integrals converge to the actual homogeneous
cofactor endpoint. No unproved homogeneous-flux constancy is used here. -/
theorem MassHypotheses.small_sphere_real_flux_limit_oai {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Filter.Tendsto (fun r => (radiusSphereFlux k (logTau f) r).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (homogeneousSphereFlux k N G)) := by
  rw [← h.unitSphereFlux_re_eq_homogeneousSphereFlux]
  exact Complex.continuous_re.continuousAt.tendsto.comp h.small_sphere_surface_integral_limit

end Mahler

end OAI
end

theorem solution : type_of% @OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit_oai := @OAI.Mahler.MassHypotheses.small_sphere_real_flux_limit_oai
