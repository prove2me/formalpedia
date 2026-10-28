-- Prove2me | solution 1 for OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:29:00.202728+00:00
-- url     : https://prove2.me/submissions/d26a5dfe-952e-40b4-9ae3-ec1c217833fb

import Mathlib
import Definitions.Def_OAIQ2Ma000
import Theorems.Thm_OAI_Mahler_MassHypotheses_small_sphere_real_flux_limit_eq

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

lemma differentiableAt_dcLinear {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) : DifferentiableAt ℝ (dcLinear u) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact ((hd.clm_comp contDiffAt_const).const_smul (-1 / 4 : ℂ)).differentiableAt (by norm_num)

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
-- module Solutions.OAIQ2_Mah.Mahler_CoordinateBall
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace MahlerStokes

lemma measurableSet_coordBall (n : ℕ) (R : ℝ) : MeasurableSet (coordBall n R) := by
  apply IsOpen.measurableSet
  exact isOpen_lt (by unfold radiusSq; fun_prop) continuous_const

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ShellRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma continuous_radiusSq (n : ℕ) : Continuous (radiusSq (n := n)) := by
  unfold radiusSq; fun_prop

lemma isCompact_coordClosedBall (n : ℕ) (R : ℝ) : IsCompact (coordClosedBall n R) := by
  have hs : coordClosedBall n R ⊆ Icc (fun _ => -|R|) (fun _ => |R|) := by
    intro x hx
    have hi (i : Fin n) : |x i| ≤ |R| := by
      have hsum : x i ^ 2 ≤ radiusSq x := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have hx' : radiusSq x ≤ R^2 := hx
      nlinarith [sq_abs (x i), sq_abs R, abs_nonneg (x i), abs_nonneg R]
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_le (continuous_radiusSq n) continuous_const) hs

lemma radiusSq_boundary {n : ℕ} (i : Fin (n+1)) (R : ℝ) {y : Fin n → ℝ}
    (hy : y ∈ coordClosedBall n R) :
    radiusSq (i.insertNth (chord R y) y) = R^2 ∧
    radiusSq (i.insertNth (-chord R y) y) = R^2 := by
  have hc : (chord R y)^2 = R^2 - radiusSq y := Real.sq_sqrt (sub_nonneg.mpr hy)
  simp only [radiusSq_insertNth, neg_sq]
  constructor <;> linarith

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ComplexCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory WithLp
open scoped ENNReal
namespace MahlerStokes

lemma complexCoordinates_apply (n : ℕ) (x : Fin (n*2) → ℝ) (i : Fin n) :
    complexCoordinates n x i = ⟨x (finProdFinEquiv (i,0)), x (finProdFinEquiv (i,1))⟩ := rfl

/-- The coordinate map sends the ordered real basis to x_i,y_i without a
sign or scale change. -/
theorem complexCoordinates_basis (n : ℕ) (i : Fin n) (b : Fin 2) :
    complexCoordinates n (Pi.single (finProdFinEquiv (i,b)) 1) =
      EuclideanSpace.single i (if b = 0 then 1 else Complex.I) := by
  ext j : 1
  rw [complexCoordinates_apply]
  by_cases hij : i = j
  · subst j
    fin_cases b <;> simp <;> rfl
  · have hji : j ≠ i := Ne.symm hij
    fin_cases b <;> simp [hji] <;> rfl

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ContinuousWedge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma contDiffAt_continuousWedge [FiniteDimensional ℝ E]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : WithTop ℕ∞}
    {a : X → E [⋀^ι]→L[ℝ] ℂ} {b : X → E [⋀^κ]→L[ℝ] ℂ} {x : X}
    (ha : ContDiffAt ℝ r a x) (hb : ContDiffAt ℝ r b x) :
    ContDiffAt ℝ r (fun y => continuousWedge (a y) (b y)) x := by
  let W := continuousWedgeCLM (E := E) (ι := ι) (κ := κ)
  have hw := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := r)
    (E := E [⋀^ι]→L[ℝ] ℂ)
    (F := (E [⋀^κ]→L[ℝ] ℂ) →L[ℝ] E [⋀^ι ⊕ κ]→L[ℝ] ℂ) W
  have hw' := hw.contDiffAt.comp x ha
  exact hw'.clm_apply hb

end
end Mahler

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
-- module Solutions.OAIQ2_Mah.Mahler_SphereTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric
open scoped Pointwise
namespace MahlerStokes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma sphereIsometry_cone_preimage (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereIsometry e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r, hr, e z, ⟨sphereIsometry e z, hz, rfl⟩, (e.map_smul r z).symm⟩
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, he⟩
    refine ⟨r, hr, e.symm z, ⟨(sphereIsometry e).symm z, ?_, rfl⟩, ?_⟩
    · simpa using hz
    · apply e.injective
      simpa using he

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Surface area induced by ambient volume is transported without a factor
by a volume-preserving real linear isometry. -/
theorem measurePreserving_sphereIsometry (e : E ≃ₗᵢ[ℝ] F)
    (μ : Measure E) (ν : Measure F) (he : MeasurePreserving e μ ν) :
    MeasurePreserving (sphereIsometry e) μ.toSphere ν.toSphere := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereIsometry e).measurable hs,
    Measure.toSphere_apply' _ ((sphereIsometry e).measurable hs),
    Measure.toSphere_apply' _ hs, sphereIsometry_cone_preimage]
  rw [e.toLinearEquiv.finrank_eq]
  congr 1
  exact he.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

end MahlerStokes

end

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
-- module Solutions.OAIQ2_Mah.Mahler_SphereVolumeOrientation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_ExactFormCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Mahler

lemma fluxCoordinates_basis (k : ℕ) (i : Fin ((2*k+1)+1)) :
    fluxCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) i) = sphereFrame k i := by
  apply (sphereFrame k).repr.injective
  simp [fluxCoordinates, MahlerStokes.coordinateBasis, OrthonormalBasis.repr_self]

lemma fluxCoordinates_repr (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    (sphereFrame k).repr (fluxCoordinates k x) = WithLp.toLp 2 x := by
  simp [fluxCoordinates]

lemma norm_fluxCoordinates_sq (k : ℕ) (x : Fin ((2*k+1)+1) → ℝ) :
    ‖fluxCoordinates k x‖^2 = MahlerStokes.radiusSq x := by
  rw [MahlerStokes.radiusSq_eq_euclidean_norm_sq]
  exact congrArg (fun t : ℝ => t^2) ((sphereFrame k).repr.symm.norm_map _)

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereChart
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma radiusSq_smul {n : ℕ} (r : ℝ) (x : Fin n → ℝ) :
    radiusSq (r • x) = r^2 * radiusSq x := by
  simp only [radiusSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma chord_pos {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    0 < chord 1 y := Real.sqrt_pos.2 (sub_pos.mpr hy)

lemma radiusSq_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) : radiusSq (hemisphereCone i x) = (x i)^2 := by
  rw [hemisphereCone, radiusSq_smul, radiusSq_hemisphereGraph i hx.2, mul_one]

lemma hemisphereCone_injOn {n : ℕ} (i : Fin (n+1)) :
    InjOn (hemisphereCone i) (hemisphereConeDomain i) := by
  intro x hx y hy h
  have hr : x i = y i := (sq_eq_sq₀ hx.1.1.le hy.1.1.le).mp
    ((radiusSq_hemisphereCone i hx).symm.trans ((congrArg radiusSq h).trans
      (radiusSq_hemisphereCone i hy)))
  have hv : i.removeNth x = i.removeNth y := by
    funext j
    have hj := congrFun h (i.succAbove j)
    simp only [hemisphereCone, hemisphereGraph, Pi.smul_apply, smul_eq_mul,
      Fin.insertNth_apply_succAbove] at hj
    rw [hr] at hj
    exact mul_left_cancel₀ hy.1.1.ne' hj
  apply funext
  rw [i.forall_iff_succAbove]
  exact ⟨hr, fun k => congrFun hv k⟩

lemma hasFDerivAt_radiusSq {n : ℕ} (y : Fin n → ℝ) :
    HasFDerivAt radiusSq (2 • coordinateDot y) y := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := y)).pow 2)
  convert! h using 1
  ext v
  simp [coordinateDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hasFDerivAt_chord {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    HasFDerivAt (chord 1) (chordDerivative y) y := by
  have h := ((hasFDerivAt_radiusSq y).const_sub (1^2)).sqrt (sub_pos.mpr hy).ne'
  convert! h using 1
  ext v
  simp [chordDerivative, chord]
  ring

lemma hasFDerivAt_hemisphereGraph {n : ℕ} (i : Fin (n+1)) {y : Fin n → ℝ}
    (hy : y ∈ coordBall n 1) :
    HasFDerivAt (hemisphereGraph i) (hemisphereGraphDerivative i y) y := by
  apply hasFDerivAt_pi.2
  rw [i.forall_iff_succAbove]
  constructor
  · simpa [hemisphereGraph, hemisphereGraphDerivative] using hasFDerivAt_chord hy
  · intro j
    simp only [hemisphereGraph, Fin.insertNth_apply_succAbove]
    exact hasFDerivAt_apply j y

lemma hasFDerivAt_hemisphereCone {n : ℕ} (i : Fin (n+1)) {x : Fin (n+1) → ℝ}
    (hx : x ∈ hemisphereConeDomain i) :
    HasFDerivAt (hemisphereCone i) (hemisphereConeDerivative i x) x := by
  exact (ContinuousLinearMap.proj i : (Fin (n+1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.smul
    ((hasFDerivAt_hemisphereGraph i hx.2).comp x (removeCoordinate i).hasFDerivAt)

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereJacobian
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace MahlerStokes

lemma det_hemisphereFrameMatrix {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ coordBall n 1) :
    (hemisphereFrameMatrix y).det = (chord 1 y)⁻¹ := by
  change (Matrix.fromBlocks (Matrix.of (fun (_ : Fin 1) (_ : Fin 1) => chord 1 y))
    (Matrix.of (fun _ j => -(chord 1 y)⁻¹ * y j))
    (Matrix.of (fun j _ => y j)) (1 : Matrix (Fin n) (Fin n) ℝ)).det = _
  rw [Matrix.det_fromBlocks_one₂₂, Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply]
  have hs : (∑ j, (-(chord 1 y)⁻¹ * y j) * y j) =
      -(chord 1 y)⁻¹ * radiusSq y := by
    rw [radiusSq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hc := chord_sq hy
  have hn := (chord_pos hy).ne'
  field_simp
  nlinarith

lemma hemisphereConeDerivative_matrix {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    (LinearMap.toMatrix' (hemisphereConeDerivative i x).toLinearMap).submatrix
      (splitCoordinate i) (splitCoordinate i) =
    Matrix.updateCol (x i • hemisphereFrameMatrix (i.removeNth x)) (Sum.inl 0)
      (fun j => hemisphereFrameMatrix (i.removeNth x) j (Sum.inl 0)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals try (have hb : b = (0 : Fin 1) := Subsingleton.elim _ _; subst b)
  all_goals
    simp [LinearMap.toMatrix'_apply, hemisphereConeDerivative,
      hemisphereGraphDerivative, removeCoordinate, hemisphereGraph, chordDerivative,
      coordinateDot, hemisphereFrameMatrix, Matrix.updateCol, Matrix.fromBlocks,
      Fin.removeNth, Pi.single_apply, Function.update,
      Fin.ne_succAbove, eq_comm, mul_comm, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The actual ambient Jacobian of radial hemisphere coordinates. The
singularity is only at the equator, outside the open parameter domain. -/
theorem det_hemisphereConeDerivative {n : ℕ} (i : Fin (n+1))
    {x : Fin (n+1) → ℝ} (hx : x ∈ hemisphereConeDomain i) :
    (hemisphereConeDerivative i x).toLinearMap.det =
      (x i)^n * (chord 1 (i.removeNth x))⁻¹ := by
  rw [← LinearMap.det_toMatrix', ← Matrix.det_submatrix_equiv_self (splitCoordinate i),
    hemisphereConeDerivative_matrix, Matrix.det_updateCol_smul_left,
    Matrix.updateCol_eq_self, det_hemisphereFrameMatrix hx.2]
  simp

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereMeasure
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace MahlerStokes

/-- Nonnegative Fubini in the distinguished coordinate; no integrability
assumption is needed for the singular hemisphere area density. -/
theorem setLIntegral_slice {n : ℕ} (i : Fin (n+1)) {s : Set (Fin (n+1) → ℝ)}
    (hs : MeasurableSet s) (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in s, f x) = ∫⁻ y : Fin n → ℝ,
      ∫⁻ t in {t | i.insertNth t y ∈ s}, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  calc
    (∫⁻ x in s, f x) = ∫⁻ p : ℝ × (Fin n → ℝ), s.indicator f (i.insertNth p.1 p.2) := by
      rw [← lintegral_indicator hs]
      exact (hp.lintegral_comp_emb e.symm.measurableEmbedding (s.indicator f)).symm
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ t : ℝ, s.indicator f (i.insertNth t y) := by
      exact (lintegral_prod _ ((hf.indicator hs).comp e.symm.measurable).aemeasurable).trans
        (lintegral_lintegral_swap ((hf.indicator hs).comp e.symm.measurable).aemeasurable)
    _ = _ := by
      apply lintegral_congr
      intro y
      change _ = ∫⁻ t in (fun t : ℝ => i.insertNth t y) ⁻¹' s, f (i.insertNth t y)
      rw [← lintegral_indicator (hs.preimage (by fun_prop : Measurable (fun t : ℝ => i.insertNth t y)))]
      rfl

lemma lintegral_pow_unitInterval (n : ℕ) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t^n)) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal ((continuous_pow n).intervalIntegrable (0 : ℝ) 1).1]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg ht.1.le n

lemma measurableSet_coneStrip {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) : MeasurableSet (coneStrip i S) :=
  ((measurable_pi_apply i) measurableSet_Ioo).inter ((removeCoordinate i).measurable hS)

lemma coneStrip_subset {n : ℕ} (i : Fin (n+1)) {S : Set (Fin n → ℝ)}
    (hS : S ⊆ coordBall n 1) : coneStrip i S ⊆ hemisphereConeDomain i :=
  fun _ hx => ⟨hx.1, hS hx.2⟩

/-- Integrating the exact radial Jacobian leaves the hemisphere area density,
with the inverse dimension factor appearing in the cone definition of area. -/
theorem volume_hemisphereCone_strip {n : ℕ} (i : Fin (n+1))
    {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hSB : S ⊆ coordBall n 1) :
    volume (hemisphereCone i '' coneStrip i S) =
      ENNReal.ofReal ((n+1 : ℝ)⁻¹) * ∫⁻ y in S, ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hs := measurableSet_coneStrip i hS
  have hsub := coneStrip_subset i hSB
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hs
    (fun x hx => (hasFDerivAt_hemisphereCone i (hsub hx)).hasFDerivWithinAt)
    ((hemisphereCone_injOn i).mono hsub)]
  have he : (∫⁻ x in coneStrip i S, ENNReal.ofReal |(hemisphereConeDerivative i x).det|) =
      ∫⁻ x in coneStrip i S,
        ENNReal.ofReal ((x i)^n) * ENNReal.ofReal (chord 1 (i.removeNth x))⁻¹ := by
    apply setLIntegral_congr_fun hs
    intro x hx
    change ENNReal.ofReal |(hemisphereConeDerivative i x).toLinearMap.det| = _
    rw [det_hemisphereConeDerivative i (hsub hx), abs_of_pos
      (mul_pos (pow_pos hx.1.1 _) (inv_pos.2 (chord_pos (hSB hx.2)))),
      ENNReal.ofReal_mul (pow_nonneg hx.1.1.le n)]
  rw [he, setLIntegral_slice i hs _ (by unfold chord radiusSq Fin.removeNth; fun_prop)]
  rw [← lintegral_indicator hS, ← lintegral_const_mul _ (by unfold chord radiusSq; fun_prop)]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ S
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = Ioo 0 1 := by
      ext t; simp [coneStrip, hy]
    simp only [ht, Fin.insertNth_apply_same, Fin.removeNth_insertNth,
      indicator_of_mem hy]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_pow_unitInterval]
  · have ht : {t : ℝ | i.insertNth t y ∈ coneStrip i S} = ∅ := by
      ext t; simp [coneStrip, hy]
    simp [ht, hy]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereArea
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
open scoped ENNReal Pointwise
namespace MahlerStokes

lemma continuous_hemisphereGraph {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereGraph i) := by
  unfold hemisphereGraph chord radiusSq
  fun_prop

lemma continuous_hemisphereParam {n : ℕ} (i : Fin (n+1)) : Continuous (hemisphereParam i) := by
  apply continuous_induced_rng.2
  exact (PiLp.continuous_toLp 2 _).comp ((continuous_hemisphereGraph i).comp continuous_subtype_val)

lemma hemisphereParam_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (hemisphereParam i) := by
  intro y z h
  apply Subtype.ext
  funext j
  have he := congrArg (fun w : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
    (w : EuclideanSpace ℝ (Fin (n+1))) (i.succAbove j)) h
  simpa [hemisphereParam, hemisphereGraph] using he

lemma hemisphereParam_range {n : ℕ} (i : Fin (n+1)) :
    range (hemisphereParam i) =
      {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    simpa [hemisphereParam, hemisphereGraph] using chord_pos y.property
  · intro hz
    let x : Fin (n+1) → ℝ := ofLp (z : EuclideanSpace ℝ (Fin (n+1)))
    have hnorm : ‖(z : EuclideanSpace ℝ (Fin (n+1)))‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using z.property
    have hr : radiusSq x = 1 := by rw [radiusSq_eq_euclidean_norm_sq]; simp [x, hnorm]
    have hs : radiusSq x = (x i)^2 + radiusSq (i.removeNth x) := by
      have he : i.insertNth (x i) (i.removeNth x) = x := by simp
      rw [← he, radiusSq_insertNth]; simp
    have hi : 0 < x i := hz
    have hy : i.removeNth x ∈ coordBall n 1 := by
      change radiusSq (i.removeNth x) < 1^2
      nlinarith
    have hc : chord 1 (i.removeNth x) = x i := by
      apply (sq_eq_sq₀ (chord_pos hy).le hi.le).1
      rw [chord_sq hy]
      linarith
    refine ⟨⟨i.removeNth x, hy⟩, ?_⟩
    apply Subtype.ext
    change toLp 2 (hemisphereGraph i (i.removeNth x)) = toLp 2 x
    congr 1
    simp [hemisphereGraph, hc]

lemma hemisphereParam_measurableEmbedding {n : ℕ} (i : Fin (n+1)) :
    MeasurableEmbedding (hemisphereParam i) := by
  let := (measurableSet_coordBall n 1).standardBorel
  exact (continuous_hemisphereParam i).measurable.measurableEmbedding (hemisphereParam_injective i)

lemma hemisphereCone_image_toLp {n : ℕ} (i : Fin (n+1)) (S : Set (Fin n → ℝ)) :
    (toLp 2 : (Fin (n+1) → ℝ) → EuclideanSpace ℝ (Fin (n+1))) ''
      (hemisphereCone i '' coneStrip i S) =
    Ioo (0 : ℝ) 1 • ((fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' S) := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x i, hx.1, toLp 2 (hemisphereGraph i (i.removeNth x)),
      ⟨i.removeNth x, hx.2, rfl⟩, rfl⟩
  · rintro ⟨r, hr, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨hemisphereCone i (i.insertNth r y), ⟨i.insertNth r y, ?_, rfl⟩, ?_⟩
    · simpa [coneStrip] using And.intro hr hy
    · simp [hemisphereCone]

lemma volume_toLp_image {n : ℕ} (S : Set (Fin n → ℝ)) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (toLp 2 '' S) = volume S := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
  have h := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' S)
  change volume (e ⁻¹' (e '' S)) = volume (e '' S) at h
  rw [e.injective.preimage_image] at h
  exact h.symm

/-- The hemisphere chart pushes forward exactly the reciprocal-chord area
measure. This is proved from the cone definition of volume.toSphere. -/
theorem toSphere_hemisphereParam_image {n : ℕ} (i : Fin (n+1))
    {S : Set (coordBall n 1)} (hS : MeasurableSet S) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere (hemisphereParam i '' S) =
      ∫⁻ y in (Subtype.val '' S), ENNReal.ofReal (chord 1 y)⁻¹ := by
  have hm := (hemisphereParam_measurableEmbedding i).measurableSet_image.mpr hS
  rw [Measure.toSphere_apply' _ hm]
  have he : Subtype.val '' (hemisphereParam i '' S) =
      (fun y => (toLp 2 (hemisphereGraph i y) : EuclideanSpace ℝ (Fin (n+1)))) '' (Subtype.val '' S) := by
    rw [← image_comp, image_image]
    rfl
  rw [he, ← hemisphereCone_image_toLp, volume_toLp_image,
    volume_hemisphereCone_strip i
      ((MeasurableEmbedding.subtype_coe (measurableSet_coordBall n 1)).measurableSet_image.mpr hS)
      (by rintro y ⟨z, hz, rfl⟩; exact z.property)]
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1 := by simp
  rw [hd, ← mul_assoc]
  have hc : (↑(n+1) : ℝ≥0∞) * ENNReal.ofReal ((n+1 : ℝ)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    push_cast
    rw [mul_inv_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0)]
    simp
  rw [hc, one_mul]

lemma measurableSet_hemisphereRange {n : ℕ} (i : Fin (n+1)) :
    MeasurableSet (range (hemisphereParam i)) :=
  (hemisphereParam_measurableEmbedding i).measurableSet_range

/-- Full measure equality, sufficient for Bochner as well as nonnegative
integration. No sphere integration identity is a premise. -/
theorem measurePreserving_hemisphereParam {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (hemisphereParam i) (hemisphereParameterArea n)
      ((volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere.restrict
        (range (hemisphereParam i))) := by
  refine ⟨(continuous_hemisphereParam i).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_hemisphereParam i).measurable hs,
    hemisphereParameterArea, withDensity_apply _ ((continuous_hemisphereParam i).measurable hs),
    setLIntegral_subtype (measurableSet_coordBall n 1) _
      (fun y : Fin n → ℝ => ENNReal.ofReal (chord 1 y)⁻¹),
    Measure.restrict_apply hs]
  rw [← toSphere_hemisphereParam_image i ((continuous_hemisphereParam i).measurable hs),
    image_preimage_eq_inter_range]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_HemisphereFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

/-- The positive normal coordinate cancels the reciprocal-chord surface
Jacobian, giving exactly the coordinate hemisphere integral used by Stokes. -/
theorem integral_upperHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in range (hemisphereParam i),
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1, f (toLp 2 (hemisphereGraph i y)) := by
  have hw : Measurable (fun y : coordBall n 1 => ENNReal.ofReal ((chord 1 (y : Fin n → ℝ))⁻¹)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.inv
    exact ((show Continuous (chord (n := n) 1) by unfold chord radiusSq; fun_prop).comp continuous_subtype_val).measurable
  rw [← (measurePreserving_hemisphereParam i).integral_comp
    (hemisphereParam_measurableEmbedding i)
    (fun z => (z : EuclideanSpace ℝ (Fin (n+1))) i * f z),
    hemisphereParameterArea, integral_withDensity_eq_integral_toReal_smul
      hw (by simp)]
  calc
    _ = ∫ y : coordBall n 1, f (toLp 2 (hemisphereGraph i y)) ∂volume.comap Subtype.val := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hc := chord_pos y.property
      simp [hemisphereParam, hemisphereGraph, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le),
        smul_eq_mul, hc.ne']
    _ = _ := integral_subtype_comap (measurableSet_coordBall n 1) (fun y => f (toLp 2 (hemisphereGraph i y)))

lemma coordBall_neg_preimage (n : ℕ) :
    (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' coordBall n 1 = coordBall n 1 := by
  ext y
  simp [coordBall, radiusSq]

lemma neg_hemisphereGraph {n : ℕ} (i : Fin (n+1)) (y : Fin n → ℝ) :
    -(hemisphereGraph i y) = i.insertNth (-chord 1 (-y)) (-y) := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp [hemisphereGraph, chord, radiusSq]
  · intro j; simp [hemisphereGraph]

/-- Lower hemisphere, with the negative normal coordinate and the same
positive coordinate measure on the parameter ball. -/
theorem integral_lowerHemisphere {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ) :
    (∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
        (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    -(∫ y in coordBall n 1, f (toLp 2 (i.insertNth (-chord 1 y) y))) := by
  let e := sphereIsometry (LinearIsometryEquiv.neg ℝ :
    EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
  have hp := measurePreserving_sphereIsometry
    (LinearIsometryEquiv.neg ℝ : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] _) volume volume
    (LinearIsometryEquiv.neg ℝ).measurePreserving
  have hpre : e ⁻¹' {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} = range (hemisphereParam i) := by
    rw [hemisphereParam_range]
    ext z
    simp [e, sphereIsometry]
  have hi := hp.setIntegral_preimage_emb e.measurableEmbedding
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
    {z | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0}
  rw [hpre] at hi
  rw [← hi]
  have he : (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (e z : EuclideanSpace ℝ (Fin (n+1))) i * f (e z)) =
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 => -((z : EuclideanSpace ℝ (Fin (n+1))) i * f (-(z : EuclideanSpace ℝ (Fin (n+1)))))) := by
    funext z
    simp [e, sphereIsometry]
  rw [he, integral_neg, integral_upperHemisphere i (fun z => f (-z))]
  congr 1
  have hnegPi : MeasurePreserving (Neg.neg : (Fin n → ℝ) → (Fin n → ℝ)) :=
    volume_preserving_pi (fun _ : Fin n =>
      (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving)
  have hb := hnegPi.setIntegral_preimage_emb
    (MeasurableEquiv.neg (Fin n → ℝ)).measurableEmbedding
    (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)
  rw [coordBall_neg_preimage] at hb
  convert! hb using 1
  apply setIntegral_congr_fun (measurableSet_coordBall n 1)
  intro y _
  dsimp only
  rw [← neg_hemisphereGraph]
  rfl

lemma integral_sphere_coordinate_of_integrable {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : Integrable (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z)
      (volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere)
    (hp : IntegrableOn (fun y => f (toLp 2 (hemisphereGraph i y))) (coordBall n 1))
    (hm : IntegrableOn (fun y => f (toLp 2 (i.insertNth (-chord 1 y) y))) (coordBall n 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  have hneg : MeasurableSet {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 |
      (z : EuclideanSpace ℝ (Fin (n+1))) i < 0} := by
    exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have he : (∫ z in (range (hemisphereParam i))ᶜ,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
      ∫ z in {z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 | (z : EuclideanSpace ℝ (Fin (n+1))) i < 0},
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
    rw [← integral_indicator (measurableSet_hemisphereRange i).compl, ← integral_indicator hneg]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : (z : EuclideanSpace ℝ (Fin (n+1))) i < 0
    · have hn : ¬0 < (z : EuclideanSpace ℝ (Fin (n+1))) i := by linarith
      simp [hemisphereParam_range, hz, hn]
    · by_cases hp : 0 < (z : EuclideanSpace ℝ (Fin (n+1))) i
      · simp [hemisphereParam_range, hp, hz]
      · have hzero : (z : EuclideanSpace ℝ (Fin (n+1))) i = 0 := by linarith
        simp [hzero]
  rw [← integral_add_compl (measurableSet_hemisphereRange i) hf, he,
    integral_upperHemisphere, integral_lowerHemisphere, ← sub_eq_add_neg, ← integral_sub hp hm]
  rfl

lemma mem_unitSphere_of_radiusSq {n : ℕ} {x : Fin n → ℝ} (hx : radiusSq x = 1) :
    (toLp 2 x : EuclideanSpace ℝ (Fin n)) ∈ sphere 0 1 := by
  simp only [mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← radiusSq_eq_euclidean_norm_sq, hx, one_pow]

/-- Continuity only on the sphere supplies every integrability premise.
The integrand may be singular at the origin. -/
theorem integral_sphere_coordinate {n : ℕ} (i : Fin (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hf : ContinuousOn f (sphere 0 1)) :
    (∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
      (z : EuclideanSpace ℝ (Fin (n+1))) i * f z
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere) =
    ∫ y in coordBall n 1,
      f (toLp 2 (i.insertNth (chord 1 y) y)) - f (toLp 2 (i.insertNth (-chord 1 y) y)) := by
  apply integral_sphere_coordinate_of_integrable i f
  · let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
    have hc : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i * f z) :=
      (by fun_prop : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
        (z : EuclideanSpace ℝ (Fin (n+1))) i)).mul (hf.comp_continuous continuous_subtype_val (fun z => z.property))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp ((PiLp.continuous_toLp 2 _).comp (continuous_hemisphereGraph i)).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa [hemisphereGraph] using (radiusSq_boundary i 1 hy).1
  · refine IntegrableOn.mono_set (s := coordBall n 1) (t := coordClosedBall n 1) ?_
      (fun y hy => (show radiusSq y < 1^2 from hy).le)
    apply ContinuousOn.integrableOn_compact (isCompact_coordClosedBall n 1)
    apply hf.comp (show Continuous (fun y : Fin n → ℝ =>
      (toLp 2 (i.insertNth (-chord 1 y) y) : EuclideanSpace ℝ (Fin (n+1)))) by
        unfold chord radiusSq; fun_prop).continuousOn
    intro y hy
    apply mem_unitSphere_of_radiusSq
    simpa using (radiusSq_boundary i 1 hy).2

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereRadius
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
namespace MahlerStokes

lemma smul_coordBall_unit {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (fun x : Fin n → ℝ => r • x) '' coordBall n 1 = coordBall n r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change radiusSq (r • x) < r^2
    rw [radiusSq_smul]
    have hh : radiusSq x < 1 := by simpa [coordBall] using hx
    nlinarith [sq_pos_of_pos hr]
  · intro hy
    refine ⟨r⁻¹ • y, ?_, by simp [smul_smul, hr.ne']⟩
    change radiusSq (r⁻¹ • y) < 1^2
    rw [radiusSq_smul, inv_pow, inv_mul_eq_div, one_pow]
    exact (div_lt_one (sq_pos_of_pos hr)).2 hy

/-- Positive dilation of the actual coordinate Lebesgue integral. -/
theorem setIntegral_coordBall_scale {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ y in coordBall n r, f y) = r^n * ∫ x in coordBall n 1, f (r • x) := by
  rw [← smul_coordBall_unit hr]
  have hd (x : Fin n → ℝ) : HasFDerivAt (fun x : Fin n → ℝ => r • x)
      (r • ContinuousLinearMap.id ℝ (Fin n → ℝ)) x := (hasFDerivAt_id x).const_smul r
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_coordBall n 1)
    (fun x _ => (hd x).hasFDerivWithinAt) (by
      intro x _ y _ h
      exact (smul_right_injective _ hr.ne') h)]
  have he : (r • ContinuousLinearMap.id ℝ (Fin n → ℝ)).det = r^n := by
    change LinearMap.det (r • LinearMap.id) = _
    rw [LinearMap.det_smul]
    simp
  simp only [he, abs_of_pos (pow_pos hr n), smul_eq_mul]
  exact integral_const_mul _ _

lemma chord_pos_scale {n : ℕ} {r : ℝ} (hr : 0 < r) (y : Fin n → ℝ) :
    chord r (r • y) = r * chord 1 y := by
  unfold chord
  rw [radiusSq_smul]
  have he : r^2-r^2*radiusSq y = r^2*(1^2-radiusSq y) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]

lemma insertNth_smul_boundary {n : ℕ} (i : Fin (n+1)) (r t : ℝ) (y : Fin n → ℝ) :
    i.insertNth (r*t) (r • y) = r • i.insertNth t y := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp
  · intro j; simp

/-- Radius scaling of the coordinate sphere flux, without exterior
algebra or flux-form identities. -/
theorem sphereFlux_pos_scale {n : ℕ} {r : ℝ} (hr : 0 < r)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    sphereFlux r ω = r^n * sphereFlux 1 (fun x => ω (r • x)) := by
  unfold sphereFlux
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_coordBall_scale hr]
  rw [mul_left_comm]
  congr 2
  apply setIntegral_congr_fun (measurableSet_coordBall n 1)
  intro y _
  dsimp only
  rw [chord_pos_scale hr, insertNth_smul_boundary, ← mul_neg, insertNth_smul_boundary]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereCoordinateIntegral
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Metric WithLp
namespace MahlerStokes

lemma continuousOn_sphere_coefficient {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) (i : Fin (n+1)) :
    ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) =>
      ω (ofLp z) (i.removeNth (coordinateBasis (n+1)))) (sphere 0 1) := by
  have hw : ContinuousOn (fun z : EuclideanSpace ℝ (Fin (n+1)) => ω (ofLp z)) (sphere 0 1) := by
    apply hω.comp (PiLp.continuous_ofLp 2 _).continuousOn
    intro z hz
    change radiusSq (ofLp z) = 1
    rw [radiusSq_eq_euclidean_norm_sq]
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    simp [hn]
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth (coordinateBasis (n+1)))).continuous.comp_continuousOn hw

/-- Exact equality of the hemisphere-coordinate Stokes integral and the
outward cofactor density integrated against volume.toSphere. -/
theorem sphereFlux_unit_eq_areaIntegral {n : ℕ}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContinuousOn ω {x | radiusSq x = 1}) :
    sphereFlux 1 ω =
      ∫ z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1,
        coordinateSphereDensity 1 ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1))))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (n+1)))).toSphere := by
  let : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc (i : Fin (n+1)) : Continuous (fun z : sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 =>
      (-1 : ℝ)^i.val * (z : EuclideanSpace ℝ (Fin (n+1))) i *
      ω (ofLp (z : EuclideanSpace ℝ (Fin (n+1)))) (i.removeNth (coordinateBasis (n+1)))) :=
    ((continuous_const.mul (by fun_prop)).mul
      ((continuousOn_sphere_coefficient ω hω i).comp_continuous continuous_subtype_val (fun z => z.property)))
  simp only [coordinateSphereDensity, one_smul]
  rw [integral_finsetSum _ (fun i _ =>
    (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold sphereFlux
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_sphere_coordinate i _ (continuousOn_sphere_coefficient ω hω i)]

end MahlerStokes

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_ExactSphereFluxBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators
namespace Mahler

/-- The real coordinate cofactor sum is the actual complex sphereFlux density.
The volume of the chosen frame is +1, so no orientation or normalization factor remains. -/
theorem coordinateSphereDensity_fluxPullback {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (x : Fin ((2*k+1)+1) → ℝ) :
    MahlerStokes.coordinateSphereDensity 1 (fluxPullback B) x =
      (orientedDensity (sphereFrame k) (sphereVolume k)
        (B (fluxCoordinates k x)).toAlternatingMap (fluxCoordinates k x)).re := by
  classical
  unfold MahlerStokes.coordinateSphereDensity orientedDensity
  rw [sphereVolume_orthonormalFrame, div_one]
  simp only [one_smul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : (fluxCoordinates k).toContinuousLinearMap ∘
      i.removeNth (MahlerStokes.coordinateBasis ((2*k+1)+1)) = i.removeNth (sphereFrame k) := by
    funext j
    exact fluxCoordinates_basis k (i.succAbove j)
  simp only [fluxPullback, realFormCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, hv, fluxCoordinates_repr]
  have hs : (-1 : ℂ)^i.val = (((-1 : ℝ)^i.val : ℝ) : ℂ) := by push_cast; rfl
  rw [hs]
  simp only [Complex.mul_re, Complex.mul_im, ContinuousAlternatingMap.coe_toAlternatingMap, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

lemma continuousOn_fluxPullback_sphere {k q : ℕ}
    {B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin q]→L[ℝ] ℂ}
    (hB : ContinuousOn B (sphere 0 1)) :
    ContinuousOn (fluxPullback B) {x | MahlerStokes.radiusSq x = 1} := by
  apply (realFormCLM _ q).continuous.comp_continuousOn
  apply (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (fluxCoordinates k).toContinuousLinearMap).continuous.comp_continuousOn
  apply hB.comp (fluxCoordinates k).continuous.continuousOn
  intro x hx
  simp only [mem_sphere, dist_zero_right]
  have hh := norm_fluxCoordinates_sq k x
  rw [hx] at hh
  nlinarith [norm_nonneg (fluxCoordinates k x)]

/-- The hemisphere-coordinate Stokes flux is exactly Mahler's real flux of a
complex form. Only continuity on the sphere is required. -/
theorem sphereFlux_eq_coordinateFlux {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (hB : ContinuousOn B (sphere 0 1)) :
    sphereFlux k (fun x => (B x).toAlternatingMap) =
      MahlerStokes.sphereFlux 1 (fluxPullback B) := by
  rw [MahlerStokes.sphereFlux_unit_eq_areaIntegral _ (continuousOn_fluxPullback_sphere hB)]
  let e := (sphereFrame k).repr.symm
  have hm := MahlerStokes.measurePreserving_sphereIsometry e volume volume e.measurePreserving
  have he := hm.integral_comp (MahlerStokes.sphereIsometry e).measurableEmbedding
    (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      (orientedDensity (sphereFrame k) (sphereVolume k) (B z).toAlternatingMap z).re)
  unfold sphereFlux sphereArea
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with z
  exact (coordinateSphereDensity_fluxPullback B (WithLp.ofLp z.val)).symm

end Mahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SphereFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_LogDilation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma continuousOn_actualRealComplexJet [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {u : E → ℂ} {K : Set E}
    (hu : ∀ x ∈ K, ContDiffAt ℝ 2 u x) : ContinuousOn (actualRealComplexJet u) K := by
  intro x hx
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) x := (hu x hx).fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ u)) x := h1.fderiv_right (by norm_num)
  exact (h1.continuousAt.prodMk h2.continuousAt).continuousWithinAt

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

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceLevelFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex ContinuousAlternatingMap Set Filter
open scoped Topology

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- Smoothness of the literal energy, at any finite order, is derived from
first-order holomorphicity on the open source domain. -/
theorem MassHypotheses.contDiffAt_energy (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) :
    ContDiffAt ℝ r (energy f) x := by
  apply ContDiffAt.sum
  intro j _
  have hj : ContDiffAt ℝ r (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open h.open_domain r (h.holomorphic j)).contDiffAt
      (h.open_domain.mem_nhds hx)).restrict_scalars ℝ
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x hj).mul hj

theorem MassHypotheses.tau_pos (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) : 0 < tau f x := by
  have hnot : ¬∀ j, f j x = 0 := fun hz => hne ((h.isolated_zero x hx).mp hz)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨j, Finset.mem_univ j, Complex.normSq_pos.mpr hj⟩

theorem MassHypotheses.contDiffAt_logTau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (hne : x ≠ 0) (r : ℕ) :
    ContDiffAt ℝ r (logTau f) x := by
  rw [logTau_eq]
  exact ((Complex.contDiffAt_log (x := energy f x) (n := r) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr (h.tau_pos hx hne))).restrict_scalars ℝ).comp x
    (h.contDiffAt_energy hx r)

/-- The existing Stokes coordinates carry the wedge slots to the exact
positive interleaved frame used by the Hessian normalization. -/
theorem complexCoordinates_wedge_basis (s : WedgePowerSlots n) :
    MahlerStokes.complexCoordinates n
      (MahlerStokes.coordinateBasis (n*2) (finProdFinEquiv (pairSlotEquiv n s))) =
      interleavedBasis s := by
  exact MahlerStokes.complexCoordinates_basis n (pairSlotEquiv n s).1 (pairSlotEquiv n s).2

end
end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceFluxRegularity
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open ContinuousAlternatingMap
open scoped Topology

namespace Mahler
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma contDiffAt_sourceDC [FiniteDimensional ℝ E] {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+1) u x) : ContDiffAt ℝ r (oneForm (dcLinear u)) x := by
  have hd : ContDiffAt ℝ r (fderiv ℝ u) x := hu.fderiv_right (by norm_num)
  exact sourceDCOperator.contDiff.contDiffAt.comp x hd

lemma contDiffAt_sourceDDC {u : E → ℂ} {x : E} {r : ℕ}
    (hu : ContDiffAt ℝ (r+2) u x) :
    ContDiffAt ℝ r (extDeriv (oneForm (dcLinear u))) x := by
  have hd : ContDiffAt ℝ (r+1) (oneForm (dcLinear u)) x :=
    contDiffAt_sourceDC (by convert hu using 1 ; norm_num [add_assoc])
  have hdd : ContDiffAt ℝ r (fderiv ℝ (oneForm (dcLinear u))) x :=
    hd.fderiv_right (by norm_num)
  exact (alternatizeUncurryFinCLM ℝ E ℂ).contDiff.contDiffAt.comp x hdd

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
lemma continuousWedgePower_toAlternatingMap [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] (a : E [⋀^Fin 2]→L[ℝ] ℂ) (k : ℕ) :
    (continuousWedgePower a k).toAlternatingMap = wedgePower a.toAlternatingMap k := by
  induction k with
  | zero => rfl
  | succ k ih => change wedge _ _ = _; rw [ih]; rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
lemma contDiffAt_continuousWedgePower [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → E [⋀^Fin 2]→L[ℝ] ℂ} {x : X} {r : WithTop ℕ∞}
    (ha : ContDiffAt ℝ r a x) (k : ℕ) :
    ContDiffAt ℝ r (fun y => continuousWedgePower (a y) k) x := by
  induction k with
  | zero => exact contDiffAt_const
  | succ k ih => exact contDiffAt_continuousWedge ha ih

lemma continuousSourceBoundaryForm_eq {n : ℕ} (u : ComplexEuclidean n → ℂ)
    (k : ℕ) (x : ComplexEuclidean n) :
    (continuousSourceBoundaryForm u k x).toAlternatingMap = sourceBoundaryForm u k x := by
  unfold continuousSourceBoundaryForm sourceBoundaryForm
  change wedge _ _ = _
  rw [continuousWedgePower_toAlternatingMap]

/-- C1 regularity of the whole actual flux form uses C3 of its potential. -/
theorem contDiffAt_sourceBoundaryForm {u : E → ℂ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (k : ℕ) :
    ContDiffAt ℝ 1 (continuousSourceBoundaryForm u k) x := by
  exact contDiffAt_continuousWedge
    (contDiffAt_sourceDC (hu.of_le (by norm_num) : ContDiffAt ℝ (1+1) u x))
    (contDiffAt_continuousWedgePower
      (contDiffAt_sourceDDC (hu : ContDiffAt ℝ (1+2) u x)) k)

end
end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceTopCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Mahler
noncomputable section

/-- The calculated top-slot order is the positive
interleaved real/imaginary order. -/
theorem sourceTopSlots_interleaved (k : ℕ) (s : WedgePowerSlots (k+1)) :
    (sourceTopSlots k s).val = (finProdFinEquiv (pairSlotEquiv (k+1) s)).val := by
  cases s with
  | inl b => fin_cases b <;> rfl
  | inr s =>
    change 1 + (1 + ((pairSlotEquiv k s).2.val + 2 * (pairSlotEquiv k s).1.val)) =
      (pairSlotEquiv k s).2.val + 2 * ((pairSlotEquiv k s).1.val + 1)
    omega

lemma coordinateCast_basis {a b : ℕ} (h : a = b) (i : Fin a) :
    coordinateCast h (MahlerStokes.coordinateBasis a i) =
      MahlerStokes.coordinateBasis b (finCongr h i) := by
  subst b
  rfl

/-- No unproved orientation factor remains in the coordinate frame. -/
theorem sourceCoordinates_top_basis (k : ℕ) (s : WedgePowerSlots (k+1)) :
    sourceCoordinates k (MahlerStokes.coordinateBasis ((2*k+1)+1) (sourceTopSlots k s)) =
      interleavedBasis s := by
  change MahlerStokes.complexCoordinates (k+1)
    (coordinateCast _ (MahlerStokes.coordinateBasis _ (sourceTopSlots k s))) = _
  rw [coordinateCast_basis]
  have hi : finCongr (show (2*k+1)+1 = (k+1)*2 by omega) (sourceTopSlots k s) =
      finProdFinEquiv (pairSlotEquiv (k+1) s) :=
    Fin.ext (sourceTopSlots_interleaved k s)
  rw [hi]
  exact complexCoordinates_wedge_basis s

end
end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceFluxCoordinates
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace Mahler

lemma powerFinEquiv_interleaved (k : ℕ) (s : WedgePowerSlots k) :
    (powerFinEquiv k s).val = (finProdFinEquiv (pairSlotEquiv k s)).val := by
  induction k with
  | zero => exact Fin.elim0 s
  | succ k ih =>
    cases s with
    | inl b => fin_cases b <;> rfl
    | inr s =>
      change 2 + (powerFinEquiv k s).val =
        (pairSlotEquiv k s).2.val + 2 * ((pairSlotEquiv k s).1.val + 1)
      rw [ih]
      change 2 + ((pairSlotEquiv k s).2.val + 2 * (pairSlotEquiv k s).1.val) = _
      omega

lemma sourceBoundarySlots_eq_boundaryFinEquiv (k : ℕ) :
    sourceBoundarySlots k = boundaryFinEquiv k := by
  ext s
  cases s with
  | inl i => rfl
  | inr s =>
    change 1 + (finProdFinEquiv (pairSlotEquiv k s)).val = 1 + (powerFinEquiv k s).val
    rw [powerFinEquiv_interleaved]

lemma sourceTopSlots_eq_ambientFinEquiv (k : ℕ) :
    sourceTopSlots k = ambientFinEquiv k := by
  ext s
  exact (sourceTopSlots_interleaved k s).trans (powerFinEquiv_interleaved (k+1) s).symm

/-- Coordinate Stokes and cofactor sphere integration use the
positive interleaved coordinate map, including the ambient degree cast. -/
theorem sourceCoordinates_eq_fluxCoordinates (k : ℕ) :
    sourceCoordinates k = fluxCoordinates k := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℝ (Fin ((2*k+1)+1))).ext
  intro i
  obtain ⟨s, rfl⟩ := (sourceTopSlots k).surjective i
  simp only [Pi.basisFun_apply]
  change sourceCoordinates k (MahlerStokes.coordinateBasis _ (sourceTopSlots k s)) =
    fluxCoordinates k (MahlerStokes.coordinateBasis _ (sourceTopSlots k s))
  rw [sourceCoordinates_top_basis, fluxCoordinates_basis,
    sourceTopSlots_eq_ambientFinEquiv, sphereFrame_interleaved]

lemma sourceCoordinateForm_eq_fluxPullback {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ) :
    sourceCoordinateForm (sourceCoordinates k) u k = fluxPullback (sourceFluxForm u) := by
  rw [sourceCoordinates_eq_fluxCoordinates]
  rfl

lemma sourceFluxForm_toAlternatingMap {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (x : ComplexEuclidean (k+1)) :
    (sourceFluxForm u x).toAlternatingMap = boundaryFormFin (dcLinear u) x := by
  change (continuousSourceBoundaryForm u k x).toAlternatingMap.domDomCongr
    (sourceBoundarySlots k) = _
  rw [continuousSourceBoundaryForm_eq, sourceBoundarySlots_eq_boundaryFinEquiv]
  rfl

lemma contDiffAt_sourceFluxForm {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    {x : ComplexEuclidean (k+1)} (hu : ContDiffAt ℝ 3 u x) :
    ContDiffAt ℝ 1 (sourceFluxForm u) x :=
  (sourceReindexCLM (E := ComplexEuclidean (k+1)) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
    (contDiffAt_sourceBoundaryForm hu k)

end Mahler

end

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
-- module Solutions.OAIQ2_Mah.Mahler_SphereAreaTransport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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
-- module Solutions.OAIQ2_Mah.Mahler_SphereOrientation
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex MeasureTheory Metric Set
open scoped Topology

namespace Mahler

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
-- module Solutions.OAIQ2_Mah.Mahler_SphereDensityBridge
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
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

end Mahler

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_SourceRadiusFlux
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Mahler

lemma continuousOn_sourceFluxForm_sphere {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    {r : ℝ} (hu : ∀ z ∈ sphere (0 : ComplexEuclidean (k+1)) r, ContDiffAt ℝ 3 u z) :
    ContinuousOn (sourceFluxForm u) (sphere 0 r) :=
  fun z hz => (contDiffAt_sourceFluxForm (hu z hz)).continuousAt.continuousWithinAt

/-- Positive dilation of the coordinate integral uses the tangential degree
2k+1, with no change in the outward orientation. -/
theorem sphereFlux_pos_eq_coordinateFlux {k : ℕ} {r : ℝ} (hr : 0 < r)
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ)
    (hB : ContinuousOn B (sphere 0 r)) :
    MahlerStokes.sphereFlux r (fluxPullback B) =
      r^(2*k+1) * sphereFlux k (fun x => (B (r • x)).toAlternatingMap) := by
  rw [MahlerStokes.sphereFlux_pos_scale hr]
  have hc : ContinuousOn (fun x => B (r • x)) (sphere 0 1) := by
    apply hB.comp (by fun_prop) (fun x hx => ?_)
    have hx' : ‖x‖ = 1 := by simpa using hx
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx']
  rw [sphereFlux_eq_coordinateFlux _ hc]
  congr 1
  congr 1
  funext x
  simp only [fluxPullback, map_smul]

/-- The coordinate Stokes flux equals the real part of the
radius-sphere area integral. C3 is required only at the radius sphere. -/
theorem sourceCoordinateFlux_eq_radiusSphereFlux {k : ℕ}
    {u : ComplexEuclidean (k+1) → ℂ} {r : ℝ} (hr : 0 < r)
    (hu : ∀ z ∈ sphere (0 : ComplexEuclidean (k+1)) r, ContDiffAt ℝ 3 u z) :
    MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) u k) =
      (radiusSphereFlux k u r).re := by
  rw [sourceCoordinateForm_eq_fluxPullback,
    sphereFlux_pos_eq_coordinateFlux hr _ (continuousOn_sourceFluxForm_sphere hu)]
  simp only [sourceFluxForm_toAlternatingMap]
  have hu2 : ∀ z : sphere (0 : ComplexEuclidean (k+1)) r,
      ContDiffAt ℝ 2 u (z : ComplexEuclidean (k+1)) :=
    fun z => (hu z z.property).of_le (by norm_num)
  have hsmall := radiusSphereFlux_eq_small (k := k) (u := u) r hr hu2
  conv_rhs => rw [hsmall]
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  let : CompactSpace (sphere (0 : ComplexEuclidean (k+1)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc : Continuous (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))) := by
    convert (continuous_radiusFluxDensity (k := k) (u := u) r hu2).comp
      (continuous_sphereDilation (n := k+1) r hr) using 1
    funext z
    simp [sphereDilation, smul_smul, hr.ne']
  have hi : Integrable (fun z : sphere (0 : ComplexEuclidean (k+1)) 1 =>
      sphereDensity k z (boundaryForm u k (r • (z : ComplexEuclidean (k+1)))))
      (sphereArea (k+1)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold smallSphereFlux
  rw [integral_const_mul]
  have hp : (r : ℂ)^(2*k+1) = ((r^(2*k+1) : ℝ) : ℂ) := by simp
  rw [hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hre := integral_re hi
  simp only [RCLike.re_eq_complex_re] at hre
  rw [← hre]
  unfold sphereFlux
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : ‖(z : ComplexEuclidean (k+1))‖ = 1 := by simp
  exact congrArg Complex.re (sphereDensity_eq_orientedDensity hz
    (boundaryForm u k (r • (z : ComplexEuclidean (k+1))))).symm

/-- The mass hypotheses supply every regularity premise. Only the
positive radius and inclusion of its sphere in the source domain remain. -/
theorem MassHypotheses.sourceCoordinateFlux_eq_radiusSphereFlux {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    {r : ℝ} (hr : 0 < r) (hSU : sphere (0 : ComplexEuclidean (k+1)) r ⊆ U) :
    MahlerStokes.sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) =
      (radiusSphereFlux k (logTau f) r).re := by
  apply Mahler.sourceCoordinateFlux_eq_radiusSphereFlux hr
  intro z hz
  apply h.contDiffAt_logTau (hSU hz) _ 3
  intro he
  have hn : ‖z‖ = r := by simpa using hz
  simp [he] at hn
  linarith

/-- The coordinate small-sphere limit, with no flux-bridge premise. -/
theorem MassHypotheses.sourceCoordinateFlux_limit_eq_oai {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    Tendsto (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] 0) (𝓝 (homogeneousSphereFlux k N G)) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp h.open_domain 0 h.zero_mem
  apply h.small_sphere_real_flux_limit_eq.congr'
  filter_upwards [self_mem_nhdsWithin, (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ) : Iio δ ∈ 𝓝[>] (0 : ℝ))] with r hr hrδ
  symm
  apply h.sourceCoordinateFlux_eq_radiusSphereFlux hr
  intro z hz
  apply hδU
  have hn : ‖z‖ = r := by simpa using hz
  simpa [mem_ball, dist_zero_right, hn] using hrδ

end Mahler

end

end OAI
end

theorem solution : type_of% @OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq_oai := @OAI.Mahler.MassHypotheses.sourceCoordinateFlux_limit_eq_oai
