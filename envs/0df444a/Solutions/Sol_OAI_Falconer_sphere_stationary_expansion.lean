-- Prove2me | solution 1 for OAI.Falconer.sphere_stationary_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:32:39.669925+00:00
-- url     : https://prove2.me/submissions/ae2dc880-f6d5-43f7-9a78-87a363e641b3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

/-- The error in a graph perpendicular test from both point and cap
replacement is controlled uniformly in the dimension. -/
theorem perpendicularPart_test_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (u v : E) :
    ‖perpendicularPart w u - perpendicularPart z v‖ ≤
      ‖u-v‖ + 2 * ‖w-z‖ * ‖v‖ := by
  calc
    _ ≤ ‖perpendicularPart w u - perpendicularPart w v‖ +
        ‖perpendicularPart w v - perpendicularPart z v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖u-v‖ + 2 * ‖w-z‖ * ‖v‖ := by
      rw [← perpendicularPart_sub]
      exact add_le_add (norm_perpendicularPart_le hw _) (perpendicularPart_direction_error hw hz v)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NonstationaryGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonstationary directions for discarded graph edges

The sphere vector field is the tangential projection of one fixed unit
vector. Its phase derivative stays large on a cap when a perpendicular
center test fails. This is the geometric part of `graph:localization`;
integration by parts is a separate analytic step.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_self_adjoint (w u v : E) :
    inner ℝ (perpendicularPart w u) v = inner ℝ u (perpendicularPart w v) := by
  simp only [perpendicularPart, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm u w]
  ring

theorem perpendicularPart_orthogonal {w : E} (hw : ‖w‖ = 1) (v : E) :
    inner ℝ w (perpendicularPart w v) = 0 := by
  simp only [perpendicularPart, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hw, one_pow, mul_one, sub_self]

theorem perpendicularPart_inner_original {w : E} (hw : ‖w‖ = 1) (v : E) :
    inner ℝ (perpendicularPart w v) v = ‖perpendicularPart w v‖^2 := by
  have hp := perpendicularPart_orthogonal hw v
  have hp' : inner ℝ (perpendicularPart w v) w = 0 := by
    rw [real_inner_comm, hp]
  have hid : v = perpendicularPart w v + inner ℝ w v • w := by
    dsimp [perpendicularPart]
    abel
  calc
    _ = inner ℝ (perpendicularPart w v)
        (perpendicularPart w v + inner ℝ w v • w) :=
      congrArg (inner ℝ (perpendicularPart w v)) hid
    _ = _ := by
      rw [inner_add_right, real_inner_smul_right, hp', mul_zero, add_zero,
        real_inner_self_eq_norm_sq]

/-- A fixed unit tangent at the cap center whose scalar product with the
center displacement equals its perpendicular length. -/
theorem exists_unit_tangent {w : E} (hw : ‖w‖ = 1) (v : E)
    (hne : perpendicularPart w v ≠ 0) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w t = 0 ∧
      inner ℝ t v = ‖perpendicularPart w v‖ := by
  let p := perpendicularPart w v
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr hne
  refine ⟨‖p‖⁻¹ • p, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  · rw [real_inner_smul_right, perpendicularPart_orthogonal hw v, mul_zero]
  · rw [real_inner_smul_left, perpendicularPart_inner_original hw v]
    dsimp only [p]
    field_simp

/-- The sphere field `t - ⟪w,t⟫ w` is tangent and has the expected
uniform phase-derivative error under cap and point replacement. -/
theorem angular_phase_derivative_error {w w₀ t : E}
    (hw : ‖w‖ = 1) (hw₀ : ‖w₀‖ = 1) (ht : ‖t‖ = 1)
    (htan : inner ℝ w₀ t = 0) (v d : E) :
    |inner ℝ (perpendicularPart w t) v - inner ℝ t d| ≤
      ‖v-d‖ + 2 * ‖w-w₀‖ * ‖d‖ := by
  have hbase : inner ℝ t (perpendicularPart w₀ d) = inner ℝ t d := by
    have htzero : inner ℝ t w₀ = 0 := by rw [real_inner_comm, htan]
    simp only [perpendicularPart, inner_sub_right, real_inner_smul_right,
      htzero, mul_zero, sub_zero]
  rw [perpendicularPart_self_adjoint, ← hbase, ← inner_sub_right]
  calc
    _ ≤ ‖t‖ * ‖perpendicularPart w v - perpendicularPart w₀ d‖ := abs_real_inner_le_norm _ _
    _ = ‖perpendicularPart w v - perpendicularPart w₀ d‖ := by rw [ht, one_mul]
    _ ≤ _ := perpendicularPart_test_error hw hw₀ v d

/-- One fixed tangent direction witnesses nonstationarity throughout the
allowed perturbations of a discarded perpendicular edge. -/
theorem perpendicular_failure_nonstationary {w₀ d : E} (hw₀ : ‖w₀‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hbad : τ < ‖perpendicularPart w₀ d‖) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w₀ t = 0 ∧
      ∀ w v : E, ‖w‖ = 1 →
        ‖v-d‖ + 2 * ‖w-w₀‖ * ‖d‖ ≤ τ/2 →
        τ/2 ≤ |inner ℝ (perpendicularPart w t) v| := by
  have hne : perpendicularPart w₀ d ≠ 0 := by
    intro he
    rw [he, norm_zero] at hbad
    linarith
  obtain ⟨t, ht, htan, hvalue⟩ := exists_unit_tangent hw₀ d hne
  refine ⟨t, ht, htan, ?_⟩
  intro w v hw herr
  have he := (angular_phase_derivative_error hw hw₀ ht htan v d).trans herr
  rw [hvalue] at he
  have habs := abs_sub_le ‖perpendicularPart w₀ d‖
    (inner ℝ (perpendicularPart w t) v) 0
  rw [sub_zero, abs_of_nonneg (norm_nonneg _), sub_zero, abs_sub_comm] at habs
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularChart
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A normalized affine line in a spherical chart

Differentiation in a gnomonic chart is the tangential projection of the
coordinate direction divided by the normalization. This connects the
failed perpendicular test to an ordinary one-variable phase derivative.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalizedLine_norm (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    ‖normalizedLine a t u‖ = 1 := by
  rw [normalizedLine,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

private theorem norm_line_hasDerivAt (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (fun x : ℝ => ‖a + x • t‖)
      (inner ℝ (a + u • t) t / ‖a + u • t‖) u := by
  have hz : HasDerivAt (fun x : ℝ => a + x • t) t u := by
    simpa using ((hasDerivAt_id u).smul_const t).const_add a
  have hsq := hz.norm_sq
  have hh := hsq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  have he : (2 * inner ℝ (a + u • t) t) / (2 * Real.sqrt (‖a+u•t‖^2)) =
      inner ℝ (a+u•t) t / ‖a+u•t‖ := by
    rw [Real.sqrt_sq (norm_nonneg _)]
    ring
  rw [he] at hh
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hh

theorem normalizedLine_hasDerivAt (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (normalizedLine a t)
      (‖a + u • t‖⁻¹ • perpendicularPart (normalizedLine a t u) t) u := by
  have hz : HasDerivAt (fun x : ℝ => a + x • t) t u := by
    simpa using ((hasDerivAt_id u).smul_const t).const_add a
  have hi := (norm_line_hasDerivAt a t hne).inv (norm_ne_zero_iff.mpr hne)
  have hh := hi.smul hz
  refine hh.congr_deriv ?_
  · simp only [normalizedLine,perpendicularPart,real_inner_smul_left,smul_sub,smul_smul,
      div_eq_mul_inv,neg_mul]
    module

theorem normalizedLine_phase_hasDerivAt (a t Δ : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (fun x => inner ℝ (normalizedLine a t x) Δ)
      (‖a+u•t‖⁻¹ * inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ) u := by
  simpa only [inner_zero_right,add_zero,zero_add,real_inner_smul_left] using
    (normalizedLine_hasDerivAt a t hne).inner ℝ (hasDerivAt_const u Δ)

/-- The normalization costs at most two in the failed-test lower bound. -/
theorem normalizedLine_phase_nonstationary (a t Δ : E) {u τ : ℝ}
    (hne : a+u•t ≠ 0) (hnorm : ‖a+u•t‖ ≤ 2) (hτ : 0 ≤ τ)
    (hderiv : τ/2 ≤ |inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ|) :
    τ/4 ≤ |deriv (fun x => inner ℝ (normalizedLine a t x) Δ) u| := by
  rw [(normalizedLine_phase_hasDerivAt a t Δ hne).deriv,abs_mul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
  have hhalf : (1/2 : ℝ) ≤ ‖a+u•t‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hne) hnorm
  calc
    τ/4 = (1/2 : ℝ)*(τ/2) := by ring
    _ ≤ ‖a+u•t‖⁻¹ * |inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ| :=
      mul_le_mul hhalf hderiv (by positivity) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularDifferentialBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem smooth_finite {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ) :
    ContDiffAt ℝ m f x :=
  (hf.of_le (WithTop.coe_le_coe.mpr (show (m:ℕ∞) ≤ ⊤ from le_top))).contDiffAt

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_InheritedCircleRegularity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun θ => (f θ : ℂ)) = fun θ => ((iteratedDeriv j f θ : ℝ) : ℂ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    have hd := (hf.differentiable_iteratedDeriv j
      (by exact_mod_cast (ENat.natCast_lt_top j))).differentiableAt (x := θ)
    simpa only [iteratedDeriv_succ] using hd.hasDerivAt.ofReal_comp.deriv

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CompactStationaryAmplitude
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTransportBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem angularTransportIterate_contDiff {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (angularTransportIterate q n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (contDiff_infty_iff_deriv.mp (hq.mul ih)).2

 theorem angularTransportIterate_support (q f : ℝ → ℂ) (n : ℕ) :
    tsupport (angularTransportIterate q n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans ih)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereRotations
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance of the actual sphere measure

The sphere measure used by the energy is defined from Euclidean volume.
Its invariance follows directly by transporting its defining truncated
cones through a linear isometry.
-/

namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem sphereMap_cone_preimage {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (s : Set (Sphere d)) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((sphereMap e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨r,hr,e w,⟨sphereMap e w,hw,rfl⟩,by simp⟩
  · rintro ⟨r,hr,y,⟨w,hw,rfl⟩,heq⟩
    refine ⟨r,hr,e.symm w,⟨sphereMap e.symm w,?_,rfl⟩,?_⟩
    · change sphereMap e (sphereMap e.symm w) ∈ s
      convert hw using 1
      all_goals try with_reducible_and_instances rfl
      apply Subtype.ext
      simp [sphereMap]
    · have hh := congrArg e.symm heq
      simpa using hh

theorem sphereMap_measurePreserving {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d) :
    MeasurePreserving (sphereMap e) (sphereMeasure d) (sphereMeasure d) := by
  have hm := (continuous_sphereMap e).measurable
  refine ⟨hm,Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs]
  unfold sphereMeasure
  rw [Measure.toSphere_apply' _ (hm hs),Measure.toSphere_apply' _ hs,sphereMap_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphere_integral_rotation {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (f : Sphere d → ℂ) :
    (∫ w, f (sphereMap e w) ∂sphereMeasure d) = ∫ w, f w ∂sphereMeasure d :=
  (sphereMap_measurePreserving e).integral_comp (sphereHomeomorph e).measurableEmbedding f

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The failed perpendicular test in an actual spherical chart

The normalized affine chart stays within twice its tangent displacement
of the cap center. Its coordinate derivative therefore inherits the
uniform lower bound proved for the tangential sphere field.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_normalization_sub_le {w z : E} (hw : ‖w‖ = 1) (hz : z ≠ 0) :
    ‖‖z‖⁻¹ • z - w‖ ≤ 2*‖z-w‖ := by
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have he : ‖z‖⁻¹ • z - w = (z-w) + (‖z‖⁻¹-1) • z := by module
  have hnorm : ‖(‖z‖⁻¹-1) • z‖ = |‖z‖-1| := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ = |(‖z‖⁻¹-1)*‖z‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg z)]
      _ = |1-‖z‖| := by rw [sub_mul,inv_mul_cancel₀ hzn,one_mul]
      _ = _ := abs_sub_comm _ _
  rw [he]
  calc
    _ ≤ ‖z-w‖ + ‖(‖z‖⁻¹-1) • z‖ := norm_add_le _ _
    _ = ‖z-w‖ + |‖z‖-1| := by rw [hnorm]
    _ ≤ ‖z-w‖ + ‖z-w‖ := by
      exact add_le_add le_rfl (by simpa only [hw] using abs_norm_sub_norm_le z w)
    _ = _ := by ring

theorem tangent_chart_nonzero {w h : E} (hw : ‖w‖ = 1) (hh : inner ℝ w h = 0) :
    w+h ≠ 0 := by
  intro he
  have hi := congrArg (inner ℝ w) he
  simp only [inner_add_right,real_inner_self_eq_norm_sq,hw,one_pow,hh,add_zero,
    inner_zero_right] at hi
  norm_num at hi

/-- A single coordinate direction works for every allowed point and
direction replacement in the discarded cell--cap term. -/
theorem perpendicular_failure_chart_nonstationary {w₀ d : E}
    (hw₀ : ‖w₀‖ = 1) {τ : ℝ} (hτ : 0 < τ)
    (hbad : τ < ‖perpendicularPart w₀ d‖) :
    ∃ t : E, ‖t‖ = 1 ∧ inner ℝ w₀ t = 0 ∧
      ∀ (y v : E) (u : ℝ), inner ℝ w₀ y = 0 → ‖y+u•t‖ ≤ 1 →
        ‖v-d‖ + 4*‖y+u•t‖*‖d‖ ≤ τ/2 →
        τ/4 ≤ |deriv (fun x => inner ℝ (normalizedLine (w₀+y) t x) v) u| := by
  obtain ⟨t,ht,htan,hfield⟩ := perpendicular_failure_nonstationary hw₀ hτ hbad
  refine ⟨t,ht,htan,?_⟩
  intro y v u hy hsmall herr
  have hh : inner ℝ w₀ (y+u•t) = 0 := by
    simp only [inner_add_right,real_inner_smul_right,hy,htan,mul_zero,add_zero]
  have hne : (w₀+y)+u•t ≠ 0 := by
    rw [add_assoc]
    exact tangent_chart_nonzero hw₀ hh
  have hnorm : ‖(w₀+y)+u•t‖ ≤ 2 := by
    rw [add_assoc]
    exact (norm_add_le _ _).trans (by rw [hw₀]; linarith)
  have hnear : ‖normalizedLine (w₀+y) t u - w₀‖ ≤ 2*‖y+u•t‖ := by
    have hp := norm_normalization_sub_le hw₀ hne
    simpa only [normalizedLine,add_assoc,add_sub_cancel_left] using hp
  have hfield' := hfield (normalizedLine (w₀+y) t u) v
    (normalizedLine_norm _ _ hne) (by
      have hm := mul_le_mul_of_nonneg_right hnear (norm_nonneg d)
      nlinarith)
  exact normalizedLine_phase_nonstationary _ _ _ hne hnorm hτ.le hfield'

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartDerivatives
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of the normalized line chart

The scalar denominator is a smooth function of two real variables on a
fixed compact square. Its bounds are independent of the chart center,
tangent direction, and displacement. No analytic input is assumed here.
-/

namespace Falconer
open Set
open scoped ContDiff

private theorem partialSecond_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) : ContDiff ℝ ∞ (partialSecond F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    exact (ih.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

private theorem partialSecond_eq {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) (s u : ℝ) :
    partialSecond F n (s,u) = iteratedDeriv n (fun x => F (s,x)) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have hp : HasDerivAt (fun x : ℝ => (s,x)) (0,1) u :=
      (hasDerivAt_const u s).prodMk (hasDerivAt_id u)
    have hh := ((partialSecond_smooth hF n).differentiable (by simp) (s,u)).hasFDerivAt.comp_hasDerivAt u hp
    rw [iteratedDeriv_succ]
    change fderiv ℝ (partialSecond F n) (s,u) (0,1) = _
    rw [← hh.deriv]
    congr 1
    funext x
    exact ih x

private theorem uniform_section_derivatives {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => F (s,x)) u| ≤ C := by
  have hc := (partialSecond_smooth hF n).continuous.abs
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s hs u hu
  rw [← partialSecond_eq hF]
  exact (hC ⟨(s,u),⟨hs,hu⟩,rfl⟩).trans (le_max_left _ _)

theorem chartLineKernel_smooth : ContDiff ℝ ∞ chartLineKernel := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact (h.sqrt (fun p => by positivity)).inv (fun p => by positivity)

theorem chartLineKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives chartLineKernel_smooth n

theorem chartLineLinearKernel_derivatives (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => x * chartLineKernel (s,x)) u| ≤ C :=
  uniform_section_derivatives (contDiff_snd.mul chartLineKernel_smooth) n

theorem chartDensityKernel_smooth (d : ℕ) : ContDiff ℝ ∞ (chartDensityKernel d) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => 1+p.1^2+p.2^2) := by fun_prop
  exact h.rpow_const_of_ne (fun p => by positivity)

theorem chartDensityKernel_derivatives (d n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-1 : ℝ) 1, ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => chartDensityKernel d (s,x)) u| ≤ C :=
  uniform_section_derivatives (chartDensityKernel_smooth d) n

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_norm_sq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    ‖(w+y)+u•t‖^2 = 1+‖y‖^2+u^2 := by
  rw [norm_add_sq_real,norm_add_sq_real,inner_add_left,real_inner_smul_right,
    real_inner_smul_right,hwy,hwt,hyt,hw,norm_smul,ht,Real.norm_eq_abs]
  simp only [one_pow,mul_zero,zero_add,mul_one,sq_abs]
  ring

theorem tangent_line_phase_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (v : E) (u : ℝ) :
    inner ℝ (normalizedLine (w+y) t u) v =
      inner ℝ (w+y) v * chartLineKernel (‖y‖,u) +
        inner ℝ t v * (u * chartLineKernel (‖y‖,u)) := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,real_inner_smul_left,inner_add_left,hn,chartLineKernel]
  ring

theorem tangent_line_phase_smooth {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (v : E) :
    ContDiff ℝ ∞ (fun u => inner ℝ (normalizedLine (w+y) t u) v) := by
  simp_rw [tangent_line_phase_eq hw ht hwy hwt hyt]
  have hk : ContDiff ℝ ∞ (fun u => chartLineKernel (‖y‖,u)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  exact (contDiff_const.mul hk).add (contDiff_const.mul (contDiff_id.mul hk))

/-- All phase derivatives on the unit chart are bounded by the displacement
norm, with constants independent of the ambient dimension and chart. -/
theorem tangent_line_phase_derivatives (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t v : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (fun x => inner ℝ (normalizedLine (w+y) t x) v) u| ≤ B*‖v‖ := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives n
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives n
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t v hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x * chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have ha : |inner ℝ (w+y) v| ≤ 2*‖v‖ := by
    apply (abs_real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_add_le _ _).trans (by rw [hw]; linarith)
  have hb : |inner ℝ t v| ≤ ‖v‖ := by
    simpa only [ht,one_mul] using abs_real_inner_le_norm t v
  simp_rw [tangent_line_phase_eq hw ht hwy hwt hyt]
  rw [iteratedDeriv_fun_add (f := fun x => inner ℝ (w+y) v * chartLineKernel (‖y‖,x))
    (g := fun x => inner ℝ t v * (x * chartLineKernel (‖y‖,x)))
    ((contDiff_const.mul hk).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    ((contDiff_const.mul hl).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  calc
    _ ≤ |inner ℝ (w+y) v * iteratedDeriv n (fun x => chartLineKernel (‖y‖,x)) u| +
        |inner ℝ t v * iteratedDeriv n (fun x => x*chartLineKernel (‖y‖,x)) u| := abs_add_le _ _
    _ = |inner ℝ (w+y) v| * |iteratedDeriv n (fun x => chartLineKernel (‖y‖,x)) u| +
        |inner ℝ t v| * |iteratedDeriv n (fun x => x*chartLineKernel (‖y‖,x)) u| := by rw [abs_mul,abs_mul]
    _ ≤ (2*‖v‖)*C + ‖v‖*D := add_le_add
      (mul_le_mul ha (hCb _ hys _ hu) (abs_nonneg _) (by positivity))
      (mul_le_mul hb (hDb _ hys _ hu) (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

end InnerProduct

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

theorem gnomonicDensity_pos {n : ℕ} (x : Space n) : 0 < gnomonicDensity x :=
  Real.rpow_pos_of_pos (by positivity) _

theorem gnomonicDensity_continuous (n : ℕ) : Continuous (@gnomonicDensity n) := by
  change Continuous (fun x : Space n => (1+‖x‖^2)^(-((n+1 : ℕ) : ℝ)/2))
  have h : Continuous (fun x : Space n => 1+‖x‖^2) :=
    continuous_const.add (continuous_norm.pow 2)
  exact h.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CoordinateIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Isolating one Euclidean chart coordinate

This change of coordinates preserves the actual Euclidean volume. It
therefore allows the scalar nonstationary bound to be integrated in the
remaining chart coordinates without any additional measure assumption.
-/

namespace Falconer
open MeasureTheory Set

theorem coordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinateEquiv n) (volume : Measure (Space (n+1)))
      ((volume : Measure (Space n)).prod volume) := by
  have h₀ := PiLp.volume_preserving_ofLp (Fin (n+1))
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have h₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  have h₃ : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure (Space n)))
      ((volume : Measure (Space n)).prod volume) := Measure.measurePreserving_swap
  exact h₃.comp (h₂.comp (h₁.comp h₀))

theorem coordinate_integral {n : ℕ} (f : Space (n+1) → ℂ) :
    (∫ z, f z) = ∫ z : Space n × ℝ, f (coordinateJoin z.1 z.2)
      ∂(volume : Measure (Space n)).prod volume := by
  have h := (coordinateEquiv_measurePreserving n).symm
  exact (h.integral_comp' f).symm

theorem coordinate_iterated_integral {n : ℕ} (f : Space (n+1) → ℂ)
    (hf : Integrable f) :
    (∫ z, f z) = ∫ x : Space n, ∫ u : ℝ, f (coordinateJoin x u) := by
  have h := (coordinateEquiv_measurePreserving n).symm
  have hi : Integrable (fun z : Space n × ℝ => f (coordinateJoin z.1 z.2))
      ((volume : Measure (Space n)).prod volume) :=
    h.integrable_comp_of_integrable hf
  rw [coordinate_integral,integral_prod _ hi]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartCoordinates
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized line sections of the gnomonic chart

The first tangent coordinate is isolated exactly. The other coordinates
give a vector perpendicular to both the pole and the chosen tangent axis.
-/

namespace Falconer

theorem coordinateJoin_inner {n : ℕ} (x y : Space n) (u v : ℝ) :
    inner ℝ (coordinateJoin x u) (coordinateJoin y v) = u*v + inner ℝ x y := by
  rw [PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  simp [coordinateJoin_eq]
  ring

theorem coordinateJoin_norm_sq {n : ℕ} (x : Space n) (u : ℝ) :
    ‖coordinateJoin x u‖^2 = u^2+‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,coordinateJoin_inner,real_inner_self_eq_norm_sq]
  ring

@[simp] theorem chartPole_norm (n : ℕ) : ‖chartPole n‖ = 1 := by
  have h := coordinateJoin_norm_sq (0 : Space (n+1)) 1
  norm_num at h
  dsimp [chartPole]
  rcases h with h | h
  · exact h
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space (n+1)) 1)]

@[simp] theorem chartAxis_norm (n : ℕ) : ‖chartAxis n‖ = 1 := by
  have h₁ := coordinateJoin_norm_sq (0 : Space n) 1
  have h₂ := coordinateJoin_norm_sq (coordinateJoin (0 : Space n) 1) 0
  dsimp [chartAxis]
  norm_num at h₁ h₂
  rcases h₁ with h₁ | h₁
  · nlinarith
  · nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]

@[simp] theorem transverseLift_norm {n : ℕ} (x : Space n) : ‖transverseLift x‖ = ‖x‖ := by
  have h₁ := coordinateJoin_norm_sq x 0
  have h₂ := coordinateJoin_norm_sq (coordinateJoin x 0) 0
  dsimp [transverseLift]
  norm_num at h₁ h₂
  nlinarith [norm_nonneg (coordinateJoin (coordinateJoin x 0) 0),norm_nonneg x]

@[simp] theorem chartPole_inner_transverse {n : ℕ} (x : Space n) :
    inner ℝ (chartPole n) (transverseLift x) = 0 := by
  simp [chartPole,transverseLift,coordinateJoin_inner]

@[simp] theorem chartPole_inner_axis (n : ℕ) :
    inner ℝ (chartPole n) (chartAxis n) = 0 := by
  simp [chartPole,chartAxis,coordinateJoin_inner]

@[simp] theorem transverseLift_inner_axis {n : ℕ} (x : Space n) :
    inner ℝ (transverseLift x) (chartAxis n) = 0 := by
  simp [transverseLift,chartAxis,coordinateJoin_inner]

theorem northLift_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    northLift (coordinateJoin x u) =
      (chartPole n + transverseLift x) + u • chartAxis n := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]
    · simp [northLift,chartPole,transverseLift,chartAxis,coordinateJoin_eq]

theorem gnomonicChart_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    (gnomonicChart (coordinateJoin x u) : Space (n+2)) =
      normalizedLine (chartPole n + transverseLift x) (chartAxis n) u := by
  simp only [gnomonicChart,normalizedLine,northLift_coordinateJoin]

theorem gnomonicDensity_coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) :
    gnomonicDensity (coordinateJoin x u) = chartDensityKernel (n+2) (‖x‖,u) := by
  simp only [gnomonicDensity,chartDensityKernel,coordinateJoin_norm_sq]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing a frame adapted to a failed perpendicular test

Two Householder reflections map a fixed orthonormal pair to a prescribed
one. This places the nonstationary tangent direction in the first chart
coordinate without any loss depending on the cap center.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthonormal_pair_isometry {a b w t : E}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0)
    (hw : ‖w‖ = 1) (ht : ‖t‖ = 1) (hwt : inner ℝ w t = 0) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e a = w ∧ e b = t := by
  let e₁ := (ℝ ∙ (a-w))ᗮ.reflection
  have h₁ : e₁ a = w := Submodule.reflection_sub (ha.trans hw.symm)
  have horth : inner ℝ w (e₁ b) = 0 := by
    rw [← h₁,e₁.inner_map_map]
    exact hab
  let e₂ := (ℝ ∙ (e₁ b-t))ᗮ.reflection
  have h₂ : e₂ (e₁ b) = t :=
    Submodule.reflection_sub ((e₁.norm_map b).trans (hb.trans ht.symm))
  have hfix : e₂ w = w := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left,inner_sub_right,horth,hwt]
    ring
  exact ⟨e₁.trans e₂,by simpa only [LinearIsometryEquiv.trans_apply,h₁] using hfix,h₂⟩

theorem exists_adapted_chart_frame {n : ℕ} {w t : Space (n+2)}
    (hw : ‖w‖ = 1) (ht : ‖t‖ = 1) (hwt : inner ℝ w t = 0) :
    ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧ e (chartAxis n) = t :=
  orthonormal_pair_isometry (chartPole_norm n) (chartAxis_norm n)
    (chartPole_inner_axis n) hw ht hwt

theorem inner_isometry_pullback (e : E ≃ₗᵢ[ℝ] E) (x v : E) :
    inner ℝ (e x) v = inner ℝ x (e.symm v) := by
  rw [← e.inner_map_map x (e.symm v),e.apply_symm_apply]

theorem normalizedLine_isometry (e : E ≃ₗᵢ[ℝ] E) (a t : E) (u : ℝ) :
    normalizedLine (e a) (e t) u = e (normalizedLine a t u) := by
  simp only [normalizedLine,← e.map_smul,← e.map_add,e.norm_map]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small sphere caps have small gnomonic coordinates

This estimate converts the geometric cap support of an angular partition
into the compact coordinate support required by nonstationary integration.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem small_cap_chart_displacement {w h : E} (hw : ‖w‖ = 1)
    (horth : inner ℝ w h = 0) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ‖‖w+h‖⁻¹ • (w+h)-w‖ ≤ δ) : ‖h‖ ≤ 2*δ := by
  have hne := tangent_chart_nonzero hw horth
  have hr : 0 < ‖w+h‖ := norm_pos_iff.mpr hne
  have he : perpendicularPart w (‖w+h‖⁻¹ • (w+h)-w) = ‖w+h‖⁻¹ • h := by
    simp only [perpendicularPart,inner_sub_right,real_inner_smul_right,inner_add_right,
      real_inner_self_eq_norm_sq,hw,one_pow,horth,add_zero,mul_one]
    module
  have hp := (norm_perpendicularPart_le hw (‖w+h‖⁻¹ • (w+h)-w)).trans hcap
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)] at hp
  have hh : ‖h‖ ≤ ‖w+h‖*δ := by
    have hh := mul_le_mul_of_nonneg_left hp hr.le
    rwa [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at hh
  have ht : ‖w+h‖ ≤ 1+‖h‖ := by simpa only [hw] using norm_add_le w h
  have hbound := hh.trans (mul_le_mul_of_nonneg_right ht hδ)
  have hm : δ*‖h‖ ≤ (1/2 : ℝ)*‖h‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg h)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SmoothReciprocal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth reciprocal of a nonstationary phase derivative

The reciprocal is extended smoothly across zero by a scalar bump. At a
point where the denominator is bounded below, its derivative bounds
depend only on the normalized derivatives of that denominator.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem smoothReciprocal_eq {τ u : ℝ} (hτ : 0 < τ) (hu : τ ≤ |u|) :
    u * smoothReciprocal τ hτ u = 1 := by
  have hb : PlanarFalconer.sineZeroCutoff τ hτ u = 0 :=
    (PlanarFalconer.sineZeroCutoff τ hτ).zero_of_le_dist
      (by simpa [PlanarFalconer.sineZeroCutoff, Real.dist_eq] using hu)
  have hune : u ≠ 0 := by intro he; simp [he] at hu; linarith
  simp [smoothReciprocal,hb,hune]

theorem smoothReciprocal_half_germ {g : ℝ → ℝ} (hg : Continuous g)
    {τ x : ℝ} (hτ : 0 < τ) (hx : τ ≤ |g x|) :
    (fun y => smoothReciprocal (τ/2) (half_pos hτ) (g y) * g y)
      =ᶠ[𝓝 x] (fun _ => 1) := by
  have hlt : τ/2 < |g x| := (half_lt_self hτ).trans_le hx
  have he : ∀ᶠ y in 𝓝 x, τ/2 < |g y| := hg.abs.continuousAt.eventually (lt_mem_nhds hlt)
  filter_upwards [he] with y hy
  simpa only [mul_comm] using smoothReciprocal_eq (half_pos hτ) hy.le

/-- The derivative constants are independent of the denominator, its
lower bound, and the frequency scale. Only positive-order derivatives
of the denominator enter the recurrence. -/
theorem reciprocal_germ_derivatives (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g q : ℝ → ℝ), ContDiff ℝ ∞ g → ContDiff ℝ ∞ q →
      ∀ (τ D x : ℝ), 0 < τ → 0 ≤ D → τ ≤ |g x| →
      (fun y => q y * g y) =ᶠ[𝓝 x] (fun _ => 1) →
      (∀ k, 1 ≤ k → k ≤ n → |iteratedDeriv k g x| ≤ B k * τ * D^k) →
      |iteratedDeriv n q x| ≤ C * τ⁻¹ * D^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro g q hg hq τ D x hτ hD hx he _
      have hgne : g x ≠ 0 := by intro hz; simp [hz] at hx; linarith
      have hqv : q x = (g x)⁻¹ := by
        calc
          q x = q x * g x * (g x)⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ hgne,mul_one]
          _ = _ := by rw [he.eq_of_nhds,one_mul]
      simp only [iteratedDeriv_zero,hqv,abs_inv,pow_zero,mul_one,one_mul]
      exact (inv_le_inv₀ (lt_of_lt_of_le hτ hx) hτ).mpr hx
    | succ n =>
      let C₀ : ℕ → ℝ := fun k => if hk : k < n+1 then (ih k hk).choose else 0
      have hC₀ (k : ℕ) : 0 ≤ C₀ k := by
        dsimp [C₀]
        split_ifs with hk
        · exact (ih k hk).choose_spec.1
        · exact le_rfl
      let C := ∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) * C₀ k * B (n+1-k)
      have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC₀ k)) (hB _))
      refine ⟨C,hC,?_⟩
      intro g q hg hq τ D x hτ hD hx he hgb
      have hqfin : ContDiffAt ℝ (n+1 : ℕ) q x :=
        (hq.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hgfin : ContDiffAt ℝ (n+1 : ℕ) g x :=
        (hg.of_le (WithTop.coe_le_coe.mpr (show ((n+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      have hid := he.iteratedDeriv_eq (n+1)
      rw [iteratedDeriv_fun_mul hqfin hgfin, Finset.sum_range_succ] at hid
      simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,iteratedDeriv_zero,
        iteratedDeriv_const,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte] at hid
      have hlast : iteratedDeriv (n+1) q x * g x =
          -(∑ k ∈ Finset.range (n+1), ((n+1).choose k : ℝ) *
            iteratedDeriv k q x * iteratedDeriv (n+1-k) g x) := by linarith
      have hsum : |iteratedDeriv (n+1) q x| * |g x| ≤ C * D^(n+1) := by
        rw [← abs_mul,hlast,abs_neg]
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        change _ ≤ (∑ k ∈ Finset.range (n+1), _) * _
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k < n+1 := Finset.mem_range.mp hk
        have hqk := (ih k hk').choose_spec.2 g q hg hq τ D x hτ hD hx he
          (fun j hj hjk => hgb j hj (by omega))
        have hCk : C₀ k = (ih k hk').choose := dite_eq_left hk'
        rw [← hCk] at hqk
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        calc
          _ ≤ ((n+1).choose k : ℝ) * (C₀ k * τ⁻¹ * D^k) *
              (B (n+1-k) * τ * D^(n+1-k)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqk (Nat.cast_nonneg _))
              (hgb (n+1-k) (by omega) (by omega)) (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (mul_nonneg (hC₀ k) (inv_nonneg.mpr hτ.le)) (pow_nonneg hD k)))
          _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) * D^(n+1) := by
            have hpow : D^k * D^(n+1-k) = D^(n+1) := by
              rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ n+1)]
            calc
              _ = ((n+1).choose k : ℝ) * C₀ k * B (n+1-k) *
                  (τ⁻¹*τ) * (D^k*D^(n+1-k)) := by ring
              _ = _ := by rw [inv_mul_cancel₀ hτ.ne',mul_one,hpow]
      have hsmall : |iteratedDeriv (n+1) q x| * τ ≤ C * D^(n+1) :=
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans hsum
      have hh := (le_div_iff₀ hτ).mpr hsmall
      simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PublishedGnomonic
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published surface-measure formula used for angular integration

Besau, Hack, Pivovarov, Schuster, *Spherical centroid bodies*,
American Journal of Mathematics **145** (2023), 515–542,
DOI 10.1353/ajm.2023.0012, Lemma 2.3(a), with the inverse chart of
Lemma 2.2(a). The authors assume sphere dimension at least two.

Only the exact density of ordinary spherical Lebesgue measure under the
gnomonic chart is assumed. This input contains no incidence or oscillatory
estimate. The resulting integral formulas retain the actual sphere measure
used in `independentAngularEnergy`.
-/

namespace Falconer
open Set MeasureTheory

theorem gnomonic_integrable (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 2 ≤ n) {f : Sphere (n+1) → ℂ}
    (hf : Integrable f (sphereMeasure (n+1))) :
    Integrable (fun x : Space n => gnomonicDensity x • f (gnomonicChart x)) := by
  have hm : MeasurePreserving (@gnomonicChart n)
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x)))
      ((sphereMeasure (n+1)).restrict (northHemisphere n)) :=
    ⟨(gnomonicChart_continuous n).measurable,hpublished n hn⟩
  have hi : Integrable (fun x : Space n => f (gnomonicChart x))
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) :=
    hm.integrable_comp_of_integrable hf.restrict
  have hh := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Space n)))
    ((gnomonicDensity_continuous n).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  simpa only [ENNReal.toReal_ofReal (gnomonicDensity_pos _).le] using hh

theorem gnomonic_sphere_integral (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 2 ≤ n) (f : Sphere (n+1) → ℂ) (hf : Measurable f)
    (hs : ∀ w, w ∉ northHemisphere n → f w = 0) :
    (∫ w, f w ∂sphereMeasure (n+1)) =
      ∫ x : Space n, gnomonicDensity x • f (gnomonicChart x) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs,← hpublished n hn,
    integral_map_of_stronglyMeasurable (gnomonicChart_continuous n).measurable hf.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      ((gnomonicDensity_continuous n).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (gnomonicDensity_pos x).le]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereChartIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One-coordinate formula for the actual sphere integral

The sole measure input is the published gnomonic density identity. The
remaining coordinate split is an ordinary volume-preserving equivalence.
-/

namespace Falconer
open Set MeasureTheory

theorem gnomonic_sphere_iterated_integral (hpublished : PublishedGnomonicSurface)
    {n : ℕ} (hn : 1 ≤ n) (f : Sphere (n+2) → ℂ) (hf : Measurable f)
    (hfi : Integrable f (sphereMeasure (n+2)))
    (hs : ∀ w, w ∉ northHemisphere (n+1) → f w = 0) :
    (∫ w, f w ∂sphereMeasure (n+2)) =
      ∫ y : Space n, ∫ u : ℝ,
        gnomonicDensity (coordinateJoin y u) • f (gnomonicChart (coordinateJoin y u)) := by
  rw [gnomonic_sphere_integral hpublished (by omega) f hf hs]
  exact coordinate_iterated_integral _ (gnomonic_integrable hpublished (by omega) hfi)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_InverseStationaryCutoff
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

theorem complex_product_derivative_bound {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {A B D : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : 0 ≤ D) (m : ℕ) (x : ℝ)
    (hfb : ∀ k ≤ m, ‖iteratedDeriv k f x‖ ≤ A*D^k)
    (hgb : ∀ k ≤ m, ‖iteratedDeriv k g x‖ ≤ B*D^k) :
    ‖iteratedDeriv m (fun y => f y*g y) x‖ ≤ 2^m*A*B*D^m := by
  rw [iteratedDeriv_fun_mul (AngularDifferentialExpr.smooth_finite hf m x)
    (AngularDifferentialExpr.smooth_finite hg m x)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), (m.choose k:ℝ)*(A*D^k)*(B*D^(m-k)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ m := by have := Finset.mem_range.mp hk; omega
      simp only [norm_mul, Complex.norm_natCast]
      gcongr
      · exact hfb k hk'
      · exact hgb (m-k) (Nat.sub_le _ _)
    _ = A*B*(D+D)^m := by
      rw [add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [← two_mul, mul_pow]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_ScaledAngularTransport
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem scaledAngularTransportCost_nonneg {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k)
    (n m : ℕ) : 0 ≤ scaledAngularTransportCost Q n m := by
  induction n generalizing m with
  | zero => exact zero_le_one
  | succ n ih =>
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQ k)) (ih _))

theorem angularTransportIterate_scaled_bound {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    {Q : ℕ → ℝ} (hQ : ∀ k, 0 ≤ Q k) {C U D : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U) (hD : 0 ≤ D) (n m : ℕ) (x : ℝ)
    (hbq : ∀ k ≤ n+m, ‖iteratedDeriv k q x‖ ≤ Q k * U * D^k)
    (hbf : ∀ k ≤ n+m, ‖iteratedDeriv k f x‖ ≤ C * D^k) :
    ‖iteratedDeriv m (angularTransportIterate q n f) x‖ ≤
      scaledAngularTransportCost Q n m * C * U^n * D^(n+m) := by
  induction n generalizing m with
  | zero => simpa [angularTransportIterate, scaledAngularTransportCost] using hbf m (by omega)
  | succ n ih =>
    have hqn : ContDiffAt ℝ (m+1 : ℕ) q x :=
      (hq.of_le (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    have hfn : ContDiffAt ℝ (m+1 : ℕ) (angularTransportIterate q n f) x :=
      ((angularTransportIterate_contDiff hq hf n).of_le
        (WithTop.coe_le_coe.mpr (show ((m+1 : ℕ) : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    change ‖iteratedDeriv m (deriv (fun y => q y * angularTransportIterate q n f y)) x‖ ≤ _
    rw [← iteratedDeriv_succ', iteratedDeriv_fun_mul hqn hfn]
    change ‖_‖ ≤ (∑ k ∈ Finset.range (m+2), _) * C * U^(n+1) * D^(n+1+m)
    simp only [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ m+1 := by simp only [Finset.mem_range] at hk; omega
    have hl : n+(m+1-k) ≤ n+1+m := by omega
    have hb := ih (m+1-k) (fun j hj => hbq j (hj.trans hl))
      (fun j hj => hbf j (hj.trans hl))
    simp only [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ((m+1).choose k : ℝ) * (Q k * U * D^k) *
          (scaledAngularTransportCost Q n (m+1-k) * C * U^n * D^(n+(m+1-k))) := by
        apply mul_le_mul_of_nonneg
        · exact mul_le_mul_of_nonneg_left (hbq k (by omega)) (Nat.cast_nonneg _)
        · exact hb
        · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (scaledAngularTransportCost_nonneg hQ _ _) hC)
              (pow_nonneg hU _)) (pow_nonneg hD _)
      _ = _ := by
        have he : k+(n+(m+1-k)) = n+1+m := by omega
        rw [pow_succ]
        calc
          _ = ((m+1).choose k : ℝ) * Q k * scaledAngularTransportCost Q n (m+1-k) *
              C * (U^n * U) * (D^k * D^(n+(m+1-k))) := by ring
          _ = _ := by rw [← pow_add, he]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PhaseIntegration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate integration by parts for the angular localization

For an arbitrary smooth real phase in a sphere chart, coordinate integration
by parts gives a scale bound through the reciprocal phase derivative.
The transport derivative identities concern functions on the real line and
are independent of the ambient sphere dimension.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

theorem phaseOscillator_norm (φ : ℝ → ℝ) (Λ x : ℝ) :
    ‖phaseOscillator φ Λ x‖ = 1 := by
  simp [phaseOscillator, Complex.norm_exp]

theorem phaseOscillator_hasDerivAt {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ)
    (Λ x : ℝ) : HasDerivAt (phaseOscillator φ Λ)
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) x := by
  have hh := (((hφ x).hasDerivAt.ofReal_comp).const_mul (Complex.I * (Λ : ℂ))).cexp
  refine hh.congr_deriv ?_
  · dsimp [phaseOscillator]
    ring

theorem phase_integration_by_parts {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1) (Λ : ℝ) :
    (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) =
      (-Complex.I * (Λ : ℂ)) * ∫ x, phaseOscillator φ Λ x * f x := by
  let v : ℝ → ℂ := fun x => q x * f x
  have hv : ContDiff ℝ ∞ v := hq.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hE : Continuous (phaseOscillator φ Λ) := by
    unfold phaseOscillator
    fun_prop
  have hv' : Continuous (PlanarFalconer.angularTransport q f) :=
    hv.continuous_deriv (by simp)
  have hi₁ : Integrable (fun x => phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) :=
    (hE.mul hv').integrable_of_hasCompactSupport hvc.deriv.mul_left
  have hE' : Continuous (fun x =>
      Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (hφ.continuous_deriv (by simp)))).mul hE
  have hi₂ : Integrable (fun x =>
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) * v x) :=
    (hE'.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hi₃ : Integrable (fun x => phaseOscillator φ Λ x * v x) :=
    (hE.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := phaseOscillator φ Λ) (v := v) (v' := PlanarFalconer.angularTransport q f)
    (fun x _ => phaseOscillator_hasDerivAt (hφ.differentiable (by simp)) Λ x)
    (fun x _ => (hv.differentiable (by simp)).differentiableAt.hasDerivAt) hi₁ hi₂ hi₃
  change (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q f x) = _ at hh
  rw [hh]
  have he : (fun x =>
      (Complex.I * (Λ : ℂ) * ((deriv φ x : ℝ) : ℂ) * phaseOscillator φ Λ x) * v x) =
      fun x => (Complex.I * (Λ : ℂ)) * (phaseOscillator φ Λ x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · dsimp [v]
      calc
        _ = (Complex.I * (Λ : ℂ)) * phaseOscillator φ Λ x *
            (((deriv φ x : ℝ) : ℂ) * q x) * f x := by ring
        _ = _ := by rw [hrecip x hx]; ring
    · simp [v, image_eq_zero_of_notMem_tsupport hx]
  rw [he, integral_const_mul]
  ring

theorem phase_transport_iterate_integral {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1) (Λ : ℝ) (n : ℕ) :
    (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransportIterate q n f x) =
      (-Complex.I * (Λ : ℂ))^n * ∫ x, phaseOscillator φ Λ x * f x := by
  induction n with
  | zero => simp [PlanarFalconer.angularTransportIterate]
  | succ n ih =>
    have hi := PlanarFalconer.angularTransportIterate_contDiff hq hf n
    have hs := PlanarFalconer.angularTransportIterate_support q f n
    have hc' : HasCompactSupport (PlanarFalconer.angularTransportIterate q n f) :=
      hc.mono' (fun _ hx => hs (subset_closure hx))
    have hh := phase_integration_by_parts hφ hq hi hc'
      (fun x hx => hrecip x (hs hx)) Λ
    change (∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransport q
      (PlanarFalconer.angularTransportIterate q n f) x) = _
    rw [hh, ih, pow_succ]
    ring

/-- Uniform coordinate IBP. The reciprocal derivative has size `U` and
derivative scale `D`; the gain per integration is `U*D/Λ`. -/
theorem phase_nonstationary_scale_bound {φ : ℝ → ℝ} {q f : ℝ → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a ≤ b) (hs : tsupport f ⊆ Icc a b)
    (hrecip : ∀ x ∈ tsupport f, ((deriv φ x : ℝ) : ℂ) * q x = 1)
    (Q : ℕ → ℝ) (hQ : ∀ k, 0 ≤ Q k)
    {C U D Λ : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U) (hD : 0 ≤ D) (hΛ : 0 < Λ)
    (n : ℕ)
    (hbq : ∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k q x‖ ≤ Q k * U * D^k)
    (hbf : ∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C * D^k) :
    ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤
      (PlanarFalconer.scaledAngularTransportCost Q n 0 * C * (b-a)) * (U*D/Λ)^n := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have ht := PlanarFalconer.angularTransportIterate_contDiff hq hf n
  have hts := (PlanarFalconer.angularTransportIterate_support q f n).trans hs
  let A := PlanarFalconer.scaledAngularTransportCost Q n 0
  have hA : 0 ≤ A := PlanarFalconer.scaledAngularTransportCost_nonneg hQ n 0
  have hbound (x : ℝ) : ‖PlanarFalconer.angularTransportIterate q n f x‖ ≤ A*C*U^n*D^n := by
    by_cases hx : x ∈ tsupport f
    · simpa only [iteratedDeriv_zero, Nat.add_zero] using
        PlanarFalconer.angularTransportIterate_scaled_bound hq hf hQ hC hU hD n 0 x
          (fun k hk => hbq k (by simpa using hk) x hx)
          (fun k hk => hbf k (by simpa using hk) x hx)
    · rw [image_eq_zero_of_notMem_tsupport
        (fun hh => hx (PlanarFalconer.angularTransportIterate_support q f n hh)), norm_zero]
      positivity
  obtain ⟨ψ,hψ⟩ := PlanarFalconer.compact_smooth_to_schwartz hts ht
  have hψs : tsupport (ψ : ℝ → ℂ) ⊆ Icc a b := by simpa [hψ] using hts
  have hψb : ∀ x, ‖iteratedDeriv 0 (ψ : ℝ → ℂ) x‖ ≤ A*C*U^n*D^n := by
    simpa [hψ] using hbound
  have hint := PlanarFalconer.compact_derivative_integral_bound ψ hab hψs 0 hψb
  simp only [iteratedDeriv_zero] at hint
  have hψ' : ∀ x, ψ x = PlanarFalconer.angularTransportIterate q n f x := congrFun hψ
  simp only [hψ'] at hint
  have hi : ‖∫ x, phaseOscillator φ Λ x * PlanarFalconer.angularTransportIterate q n f x‖ ≤
      (A*C*U^n*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul, phaseOscillator_norm, one_mul] using hint
  rw [phase_transport_iterate_integral hφ hq hf hc hrecip Λ n, norm_mul,
    norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΛ] at hi
  have hh : ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤ (A*C*U^n*D^n)*(b-a)/Λ^n :=
    (le_div_iff₀ (pow_pos hΛ n)).mpr (by simpa only [mul_comm (Λ^n)] using hi)
  apply hh.trans_eq
  dsimp [A]
  rw [div_pow, mul_pow]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_NonstationaryPhase
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform nonstationary phase in one angular coordinate

A smooth reciprocal of the phase derivative is constructed from a scalar
bump. A lower bound on the phase derivative and normalized bounds
on its higher derivatives give the required power of `D / (Λ * τ)`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem phase_nonstationary_from_derivative_bounds
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (φ : ℝ → ℝ) (f : ℝ → ℂ),
      ContDiff ℝ ∞ φ → ContDiff ℝ ∞ f →
      ∀ (a b C D Λ τ : ℝ), a ≤ b → 0 ≤ C → 0 ≤ D → 0 < Λ → 0 < τ →
      tsupport f ⊆ Icc a b →
      (∀ x ∈ tsupport f, τ ≤ |deriv φ x|) →
      (∀ k, 1 ≤ k → k ≤ n → ∀ x ∈ tsupport f,
        |iteratedDeriv k (deriv φ) x| ≤ B k * τ * D^k) →
      (∀ k ≤ n, ∀ x ∈ tsupport f, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ‖∫ x, phaseOscillator φ Λ x * f x‖ ≤ A*C*(b-a)*(D/(Λ*τ))^n := by
  choose Q hQ hbound using reciprocal_germ_derivatives B hB
  let A := PlanarFalconer.scaledAngularTransportCost Q n 0
  refine ⟨A,PlanarFalconer.scaledAngularTransportCost_nonneg hQ n 0,?_⟩
  intro φ f hφ hf a b C D Λ τ hab hC hD hΛ hτ hs haway hgb hfb
  have hg : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  let q₀ : ℝ → ℝ := fun x => smoothReciprocal (τ/2) (half_pos hτ) (deriv φ x)
  let q : ℝ → ℂ := fun x => (q₀ x : ℂ)
  have hq₀ : ContDiff ℝ ∞ q₀ := (smoothReciprocal_contDiff _ _).comp hg
  have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp hq₀
  have hgerm (x : ℝ) (hx : x ∈ tsupport f) :
      (fun y => q₀ y * deriv φ y) =ᶠ[𝓝 x] (fun _ => 1) :=
    smoothReciprocal_half_germ hg.continuous hτ (haway x hx)
  have hrecip (x : ℝ) (hx : x ∈ tsupport f) : ((deriv φ x : ℝ) : ℂ) * q x = 1 := by
    have hh := (hgerm x hx).eq_of_nhds
    dsimp [q]
    exact_mod_cast (show deriv φ x * q₀ x = 1 by simpa only [mul_comm] using hh)
  have hbq (k : ℕ) (hk : k ≤ n) (x : ℝ) (hx : x ∈ tsupport f) :
      ‖iteratedDeriv k q x‖ ≤ Q k * τ⁻¹ * D^k := by
    change ‖iteratedDeriv k (fun y => (q₀ y : ℂ)) x‖ ≤ _
    rw [PlanarFalconer.iteratedDeriv_ofReal hq₀,Complex.norm_real,Real.norm_eq_abs]
    exact hbound k (deriv φ) q₀ hg hq₀ τ D x hτ hD (haway x hx) (hgerm x hx)
      (fun j hj hjk => hgb j hj (hjk.trans hk) x hx)
  have hh := phase_nonstationary_scale_bound hφ hq hf hab hs hrecip Q hQ hC
    (inv_nonneg.mpr hτ.le) hD hΛ n hbq hfb
  apply hh.trans_eq
  dsimp only [A]
  congr 1
  congr 1
  rw [div_eq_mul_inv,div_eq_mul_inv,mul_inv_rev]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ChartNonstationary
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonstationary integration in the actual normalized chart

The phase is the scalar product with the normalized affine chart, not an
abstract phase supplied as a hypothesis. Its higher derivative constants
come from `tangent_line_phase_derivatives`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_chart_nonstationary (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w y t v : E) (f : ℝ → ℂ),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ContDiff ℝ ∞ f →
      ∀ (C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      ‖v‖ ≤ τ * D → tsupport f ⊆ Icc (-1 : ℝ) 1 →
      (∀ u ∈ tsupport f,
        τ ≤ |deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v) u|) →
      (∀ k ≤ n, ∀ u ∈ tsupport f, ‖iteratedDeriv k f u‖ ≤ C*D^k) →
      ‖∫ u, phaseOscillator (fun x => inner ℝ (normalizedLine (w+y) t x) v) Λ u * f u‖ ≤
        A*C*(D/(Λ*τ))^n := by
  choose B hB hbound using (fun k => tangent_line_phase_derivatives (E := E) (k+1))
  obtain ⟨A,hA,hestimate⟩ := phase_nonstationary_from_derivative_bounds B hB n
  refine ⟨2*A,by positivity,?_⟩
  intro w y t v f hw ht hwy hwt hyt hy hf C D Λ τ hC hD hΛ hτ hv hs hl hb
  have hφ := tangent_line_phase_smooth hw ht hwy hwt hyt v
  have hgb (k : ℕ) (hk : 1 ≤ k) (_hkn : k ≤ n) (u : ℝ) (hu : u ∈ tsupport f) :
      |iteratedDeriv k (deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v)) u| ≤
        B k * τ * D^k := by
    rw [← iteratedDeriv_succ']
    calc
      _ ≤ B k * ‖v‖ := hbound k w y t v hw ht hwy hwt hyt hy u (hs hu)
      _ ≤ B k * (τ*D^k) := by
        apply mul_le_mul_of_nonneg_left _ (hB k)
        exact hv.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hD (by omega)) hτ.le)
      _ = _ := by ring
  have hh := hestimate _ f hφ hf (-1) 1 C D Λ τ (by norm_num) hC
    (zero_le_one.trans hD) hΛ hτ hs hl hgb hb
  convert hh using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_ChartDensityEstimate
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonstationary chart integration with the surface density

The surface Jacobian is included in the differentiated amplitude. Its
derivatives are bounded on the fixed chart, uniformly in the remaining
coordinate parameters.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem density_tangent_chart_nonstationary (d n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w y t v : E) (f : ℝ → ℂ),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ContDiff ℝ ∞ f →
      ∀ (C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      ‖v‖ ≤ τ*D → tsupport f ⊆ Icc (-1 : ℝ) 1 →
      (∀ u ∈ tsupport f,
        τ ≤ |deriv (fun x => inner ℝ (normalizedLine (w+y) t x) v) u|) →
      (∀ k ≤ n, ∀ u ∈ tsupport f, ‖iteratedDeriv k f u‖ ≤ C*D^k) →
      ‖∫ u, phaseOscillator (fun x => inner ℝ (normalizedLine (w+y) t x) v) Λ u *
        ((chartDensityKernel d (‖y‖,u) : ℂ) * f u)‖ ≤ A*C*(D/(Λ*τ))^n := by
  choose P hP hPb using chartDensityKernel_derivatives d
  let Q := ∑ k ∈ Finset.range (n+1), P k
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun k _ => hP k)
  have hPQ (k : ℕ) (hk : k ≤ n) : P k ≤ Q :=
    Finset.single_le_sum (fun i _ => hP i) (Finset.mem_range.mpr (by omega))
  obtain ⟨A,hA,he⟩ := tangent_chart_nonstationary (E := E) n
  refine ⟨A * 2^n * Q,by positivity,?_⟩
  intro w y t v f hw ht hwy hwt hyt hy hf C D Λ τ hC hD hΛ hτ hv hs hl hb
  let g : ℝ → ℂ := fun u => (chartDensityKernel d (‖y‖,u) : ℂ)
  have hg₀ : ContDiff ℝ ∞ (fun u => chartDensityKernel d (‖y‖,u)) :=
    (chartDensityKernel_smooth d).comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp hg₀
  have hsub : tsupport (fun u => g u * f u) ⊆ tsupport f := tsupport_mul_subset_right
  have hgb (k : ℕ) (hk : k ≤ n) (u : ℝ) (hu : u ∈ tsupport f) :
      ‖iteratedDeriv k g u‖ ≤ Q * D^k := by
    change ‖iteratedDeriv k (fun u => (chartDensityKernel d (‖y‖,u) : ℂ)) u‖ ≤ _
    rw [PlanarFalconer.iteratedDeriv_ofReal hg₀,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ P k := hPb k _ ⟨by linarith [norm_nonneg y],hy⟩ _ (hs hu)
      _ ≤ Q := hPQ k hk
      _ ≤ Q * D^k := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (one_le_pow₀ hD) hQ
  have hfb (k : ℕ) (hk : k ≤ n) (u : ℝ) (hu : u ∈ tsupport (fun u => g u*f u)) :
      ‖iteratedDeriv k (fun u => g u * f u) u‖ ≤ (2^n*Q*C)*D^k := by
    have hh := PlanarFalconer.complex_product_derivative_bound hg hf hQ hC
      (zero_le_one.trans hD) k u
      (fun j hj => hgb j (hj.trans hk) u (hsub hu))
      (fun j hj => hb j (hj.trans hk) u (hsub hu))
    apply hh.trans
    gcongr
    norm_num
  have hh := he w y t v (fun u => g u*f u) hw ht hwy hwt hyt hy (hg.mul hf)
    (2^n*Q*C) D Λ τ (by positivity) hD hΛ hτ hv (hsub.trans hs)
    (fun u hu => hl u (hsub hu)) hfb
  convert hh using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNonstationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A nonstationary estimate for the actual sphere measure

The amplitude is supported in one gnomonic cap. Ordinary one-coordinate
regularity and a phase lower bound give arbitrary repeated-integration
decay, with a constant independent of the cap amplitude and frequency.
The density and the remaining-coordinate integration are included.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem sphere_chart_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      Measurable b →
      (∀ w, w ∉ northHemisphere (n+1) → b w = 0) →
      (∀ y : Space n, 1 < ‖y‖ → ∀ u, chartAmplitude b y u = 0) →
      (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (chartAmplitude b y)) →
      (∀ y : Space n, ‖y‖ ≤ 1 → tsupport (chartAmplitude b y) ⊆ Icc (-1 : ℝ) 1) →
      ∀ (M C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      (∀ w, ‖b w‖ ≤ M) → ‖v‖ ≤ τ*D →
      (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (chartAmplitude b y),
        τ ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) v) u|) →
      (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (chartAmplitude b y),
        ‖iteratedDeriv k (chartAmplitude b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
        ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*τ))^m := by
  obtain ⟨A,hA,hestimate⟩ := density_tangent_chart_nonstationary (E := Space (n+2)) (n+2) m
  let K := Metric.closedBall (0 : Space n) 1
  let V : ℝ := (volume : Measure (Space n)).real K
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨A*V,mul_nonneg hA hV,?_⟩
  intro v b hb hs hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ hM hv hl hder
  let F : Sphere (n+2) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
  have hFm : Measurable F := by
    apply Measurable.mul _ hb
    fun_prop
  have hFb (w : Sphere (n+2)) : ‖F w‖ ≤ M := by
    simpa only [F,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,zero_sub,neg_zero,Real.exp_zero,one_mul] using hM w
  have hFi : Integrable F (sphereMeasure (n+2)) :=
    Integrable.of_bound hFm.aestronglyMeasurable M (Filter.Eventually.of_forall hFb)
  let G : Space n → ℂ := fun y => ∫ u : ℝ,
    phaseOscillator (fun x => inner ℝ
      (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) v) Λ u *
      ((chartDensityKernel (n+2) (‖y‖,u) : ℂ) * chartAmplitude b y u)
  have he : (∫ w, F w ∂sphereMeasure (n+2)) = ∫ y, G y := by
    rw [gnomonic_sphere_iterated_integral hpublished hn F hFm hFi (by
      intro w hw
      simp only [F,hs w hw,mul_zero])]
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    filter_upwards with u
    simp only [F,chartAmplitude,gnomonicChart_coordinateJoin,
      gnomonicDensity_coordinateJoin,phaseOscillator,Complex.real_smul]
    ring
  have hGout (y : Space n) (hy : y ∉ K) : G y = 0 := by
    have hn : 1 < ‖y‖ := by
      simpa only [K,Metric.mem_closedBall,dist_zero_right,not_le] using hy
    simp only [G,hout y hn,mul_zero,integral_zero]
  have hGin (y : Space n) (hy : y ∈ K) : ‖G y‖ ≤ A*C*(D/(Λ*τ))^m := by
    have hy' : ‖y‖ ≤ 1 := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hy
    have hh := hestimate (chartPole n) (transverseLift y) (chartAxis n) v (chartAmplitude b y)
      (chartPole_norm n) (chartAxis_norm n) (chartPole_inner_transverse y)
      (chartPole_inner_axis n) (transverseLift_inner_axis y)
      (by simpa only [transverseLift_norm] using hy') (hsmooth y hy')
      C D Λ τ hC hD hΛ hτ hv (hsupport y hy') (hl y hy')
      (fun k hk u hu => hder k hk y hy' u hu)
    simpa only [G,transverseLift_norm] using hh
  change ‖∫ w, F w ∂sphereMeasure (n+2)‖ ≤ _
  rw [he,← setIntegral_eq_integral_of_forall_compl_eq_zero hGout]
  apply (norm_setIntegral_le_of_norm_le_const_ae'
    (isCompact_closedBall (0 : Space n) 1).measure_lt_top
    (Filter.Eventually.of_forall hGin)).trans_eq
  dsimp only [V]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedNonstationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform rotation of the spherical nonstationary estimate

The same constant applies to every cap center and every choice of its
first tangent direction. The displacement is pulled back by the linear
isometry, while the amplitude keeps its original point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem rotated_sphere_chart_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      Measurable b →
      (∀ w, sphereMap e.symm w ∉ northHemisphere (n+1) → b w = 0) →
      (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) →
      (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
      (∀ y : Space n, ‖y‖ ≤ 1 → tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) →
      ∀ (M C D Λ τ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ → 0 < τ →
      (∀ w, ‖b w‖ ≤ M) → ‖v‖ ≤ τ*D →
      (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
        τ ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n + transverseLift y) (chartAxis n) x) (e.symm v)) u|) →
      (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
        ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ)) * b w
        ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*τ))^m := by
  obtain ⟨A,hA,he⟩ := sphere_chart_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro e v b hb hs hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ hM hv hl hder
  have hrot := he (e.symm v) (fun w => b (sphereMap e w))
    (hb.comp (continuous_sphereMap e).measurable) (by
      intro w hw
      apply hs
      have hh : sphereMap e.symm (sphereMap e w) = w := (sphereHomeomorph e).left_inv w
      rw [hh]
      exact hw) hout hsmooth hsupport M C D Λ τ hC hD hΛ hτ
    (fun w => hM (sphereMap e w)) (by simpa only [e.symm.norm_map] using hv) hl hder
  have hI := sphere_integral_rotation e (fun w : Sphere (n+2) =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))*b w)
  rw [← hI]
  convert hrot using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg norm
  apply integral_congr_ae
  filter_upwards with w
  congr 3
  exact congrArg (fun r : ℝ => (r : ℂ)) (inner_isometry_pullback e w v)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_AmbientSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ambient smooth symbols in the adapted spherical chart

The smooth cap partition is constructed in Euclidean space. Its restriction
to every rotated one-coordinate spherical chart is smooth, including at
points where the amplitude vanishes.
-/

namespace Falconer
open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalizedLine_contDiff (a t : E) (hne : ∀ u : ℝ, a+u•t ≠ 0) :
    ContDiff ℝ ∞ (normalizedLine a t) := by
  have hz : ContDiff ℝ ∞ (fun u : ℝ => a+u•t) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact ((hz.norm ℝ hne).inv (fun u => norm_ne_zero_iff.mpr (hne u))).smul hz

theorem ambient_symbol_chart_smooth {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (F : Space (n+2) → ℂ)
    (hF : ContDiff ℝ ∞ F) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => F w) y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  have hc := hF.comp (he.comp hp)
  change ContDiff ℝ ∞ (fun u => F (e (gnomonicChart (coordinateJoin y u))))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BumpDerivatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform derivatives of scaled cap bumps

A single compactly supported bump controls every center and radius. The
scale enters through the curve supplied to that fixed bump, so the k-th
bound loses only the k-th power of the inverse cap radius.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capBump_eq_unit {d : ℕ} (δ : ℝ) (hδ : 0 < δ) (c : Sphere d) (x : Space d) :
    capBump δ hδ c x = unitCapBump d ((δ/2)⁻¹ • (x-(c : Space d))) := by
  have hr : δ/(δ/2) = 2 := by field_simp
  simp only [ContDiffBump.apply,capBump,unitCapBump,hr,div_one,inv_one,one_smul,sub_zero]

/-- This applies to an arbitrary smooth curve and will be specialized to the
rotated normalized line. The constant is independent of its center and scale. -/
theorem capBump_curve_derivatives (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere d) (γ : ℝ → Space d), ContDiff ℝ ∞ γ →
      ∀ (D u : ℝ), 1 ≤ D →
      (∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k γ u‖ ≤ D^k) →
      |iteratedDeriv m (fun t => capBump δ hδ c (γ t)) u| ≤ C*(D/δ)^m := by
  obtain ⟨B,hB,hBb⟩ := (unitCapBump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (unitCapBump d).contDiff m
  refine ⟨(m.factorial : ℝ)*B*2^m,by positivity,?_⟩
  intro δ hδ hδ1 c γ hγ D u hD hγb
  let f : ℝ → Space d := fun t => (δ/2)⁻¹ • (γ t-(c : Space d))
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact (hγ.sub contDiff_const).const_smul _
  have hscale : 1 ≤ (δ/2)⁻¹ := (one_le_inv₀ (half_pos hδ)).mpr (by linarith)
  have hfb (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
      ‖iteratedFDeriv ℝ k f u‖ ≤ ((δ/2)⁻¹*D)^k := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv k (fun t => (δ/2)⁻¹ • (γ t-(c : Space d))) u‖ ≤ _
    rw [iteratedDeriv_fun_const_smul_field,
      iteratedDeriv_fun_sub ((hγ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) contDiffAt_const,
      iteratedDeriv_const,ite_eq_right (by omega : k ≠ 0),sub_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (half_pos hδ))]
    calc
      _ ≤ (δ/2)⁻¹*D^k := mul_le_mul_of_nonneg_left (hγb k hk hkm) (by positivity)
      _ ≤ ((δ/2)⁻¹)^k*D^k := mul_le_mul_of_nonneg_right
        (le_self_pow₀ hscale (by omega)) (pow_nonneg (by linarith) _)
      _ = _ := (mul_pow _ _ _).symm
  have hh := norm_iteratedFDeriv_comp_le (unitCapBump d).contDiff hf
    (show (m : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) u (fun k hk => hBb k hk _) hfb
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hh
  have he : (unitCapBump d) ∘ f = (fun t => capBump δ hδ c (γ t)) := by
    funext t
    exact (capBump_eq_unit δ hδ c (γ t)).symm
  rw [he,Real.norm_eq_abs] at hh
  apply hh.trans_eq
  have hr : (δ/2)⁻¹*D = 2*(D/δ) := by field_simp
  rw [hr,mul_pow]
  ring

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tangent_line_eq {w y t : E} (hw : ‖w‖ = 1) (ht : ‖t‖ = 1)
    (hwy : inner ℝ w y = 0) (hwt : inner ℝ w t = 0)
    (hyt : inner ℝ y t = 0) (u : ℝ) :
    normalizedLine (w+y) t u =
      chartLineKernel (‖y‖,u) • (w+y) + (u*chartLineKernel (‖y‖,u)) • t := by
  have hn : ‖(w+y)+u•t‖ = Real.sqrt (1+‖y‖^2+u^2) := by
    rw [← tangent_line_norm_sq hw ht hwy hwt hyt,Real.sqrt_sq (norm_nonneg _)]
  simp only [normalizedLine,hn,chartLineKernel,smul_add,smul_smul]
  rw [mul_comm]

theorem tangent_line_derivatives (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (normalizedLine (w+y) t) u‖ ≤ B := by
  obtain ⟨C,hC,hCb⟩ := chartLineKernel_derivatives m
  obtain ⟨D,hD,hDb⟩ := chartLineLinearKernel_derivatives m
  refine ⟨2*C+D,by positivity,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu
  have hys : ‖y‖ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [norm_nonneg y],hy⟩
  have hk : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x)) :=
    chartLineKernel_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hl : ContDiff ℝ ∞ (fun x : ℝ => x*chartLineKernel (‖y‖,x)) :=
    contDiff_id.mul hk
  have hwyb : ‖w+y‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hw]; linarith)
  have he : normalizedLine (w+y) t = (fun x =>
      chartLineKernel (‖y‖,x) • (w+y) + (x*chartLineKernel (‖y‖,x)) • t) :=
    funext (tangent_line_eq hw ht hwy hwt hyt)
  have hk' : ContDiff ℝ ∞ (fun x => chartLineKernel (‖y‖,x) • (w+y)) :=
    hk.smul contDiff_const
  have hl' : ContDiff ℝ ∞ (fun x => (x*chartLineKernel (‖y‖,x)) • t) :=
    hl.smul contDiff_const
  rw [he,iteratedDeriv_fun_add
    ((hk'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) ((hl'.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hk.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt),
    iteratedDeriv_smul_const ((hl.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ‖iteratedDeriv m (fun x => chartLineKernel (‖y‖,x)) u • (w+y)‖ +
        ‖iteratedDeriv m (fun x => x*chartLineKernel (‖y‖,x)) u • t‖ := norm_add_le _ _
    _ ≤ C*2+D*1 := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul (hCb _ hys _ hu) hwyb (norm_nonneg _) hC)
        (mul_le_mul (hDb _ hys _ hu) ht.le (norm_nonneg _) hD)
    _ = _ := by ring

/-- One fixed scale controls all positive orders up to a chosen finite order. -/
theorem tangent_line_derivative_scale (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (w y t : E),
      ‖w‖ = 1 → ‖t‖ = 1 → inner ℝ w y = 0 → inner ℝ w t = 0 →
      inner ℝ y t = 0 → ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (normalizedLine (w+y) t) u‖ ≤ D^k := by
  choose B hB hBb using (fun k => tangent_line_derivatives (E := E) k)
  let D := 1+∑ k ∈ Finset.range (m+1), B k
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (m+1)) => hB k)]
  refine ⟨D,hD,?_⟩
  intro w y t hw ht hwy hwt hyt hy u hu k hk hkm
  apply (hBb k w y t hw ht hwy hwt hyt hy u hu).trans
  have hb : B k ≤ D := by
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m+1)) => hB j)
      (Finset.mem_range.mpr (by omega : k < m+1))
    dsimp [D]
    linarith
  exact hb.trans (le_self_pow₀ hD (by omega))

end InnerProduct
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartBumps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap bump derivatives in every rotated spherical chart

The constants depend only on the ambient dimension and derivative order.
The cap center, rotation, radius and transverse chart coordinate remain free.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem rotatedChartCurve_contDiff {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) :
    ContDiff ℝ ∞ (rotatedChartCurve e y) := by
  have hn (u : ℝ) : (chartPole n+transverseLift y)+u•chartAxis n ≠ 0 := by
    rw [add_assoc]
    apply tangent_chart_nonzero (chartPole_norm n)
    simp only [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hp := normalizedLine_contDiff (chartPole n+transverseLift y) (chartAxis n) hn
  have he : ContDiff ℝ ∞ (fun x : Space (n+2) => e x) := e.toContinuousLinearMap.contDiff
  change ContDiff ℝ ∞ (fun u => e (gnomonicChart (coordinateJoin y u)))
  simpa only [Function.comp_def,gnomonicChart_coordinateJoin] using he.comp hp

theorem capBump_rotated_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  obtain ⟨D,hD,hDb⟩ := tangent_line_derivative_scale (E := Space (n+2)) m
  obtain ⟨C,hC,hCb⟩ := capBump_curve_derivatives (n+2) m
  refine ⟨C*D^m,by positivity,?_⟩
  intro δ hδ hδ1 c e y hy u hu
  have hp : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedDeriv k (rotatedChartCurve e y) u‖ ≤ D^k := by
    intro k hk hkm
    have he : rotatedChartCurve e y = e ∘
        normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
      funext t
      simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
    rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hDb _ _ _ (chartPole_norm n) (chartAxis_norm n)
      (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
      (by simpa only [transverseLift_norm] using hy) u hu k hk hkm
  have hh := hCb δ hδ hδ1 c (rotatedChartCurve e y) (rotatedChartCurve_contDiff e y)
    D u hD hp
  apply hh.trans_eq
  simp only [div_eq_mul_inv,mul_pow]
  ring

theorem capBump_rotated_derivative_zero {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
    (y : Space n) (u : ℝ) (hfar : δ < ‖rotatedChartCurve e y u-(c : Space (n+2))‖)
    (m : ℕ) :
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u = 0 := by
  have hn : rotatedChartCurve e y u ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (rotatedChartCurve_contDiff e y).continuous.continuousAt
  have hh := he.iteratedDeriv_eq m
  simpa only [Function.comp_def,Pi.zero_apply,iteratedDeriv_const,ite_self] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapDenominator
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

theorem capDenominator_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capDenominator δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_rotated_derivatives n m
  refine ⟨5^(n+2)*C,by positivity,?_⟩
  intro δ hδ hδ1 S hsep e y hy u hu
  let w : Sphere (n+2) := sphereMap e (gnomonicChart (coordinateJoin y u))
  let T := S.filter (fun c => dist w c ≤ δ)
  let f : Sphere (n+2) → ℝ := fun c =>
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u
  have hdiff (c : Sphere (n+2)) :
      ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hzero (c : Sphere (n+2)) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hdist : δ < dist w c := lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_rotated_derivative_zero hδ c e y u hdist m
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change |iteratedDeriv m (fun t => ∑ c ∈ S, capBump δ hδ c (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_sum (fun c _ => ((hdiff c).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  change |∑ c ∈ S, f c| ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^m := Finset.sum_le_sum (fun c _ => hCb δ hδ hδ1 c e y hy u hu)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^m) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^(n+2)*(C*(δ⁻¹)^m) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapSupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinate support inherited from a geometric sphere cap

The two coordinate bounds are consequences of the actual cap support.
They do not impose additional localization assumptions on the amplitude.
-/

namespace Falconer
open Set

theorem chartPole_inner {n : ℕ} (v : Space (n+2)) :
    inner ℝ (chartPole n) v = v 0 := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [chartPole,coordinateJoin_eq]

theorem transverse_coordinate_bounds {n : ℕ} (y : Space n) (u : ℝ) :
    ‖y‖ ≤ ‖transverseLift y+u•chartAxis n‖ ∧
      |u| ≤ ‖transverseLift y+u•chartAxis n‖ := by
  have he : ‖transverseLift y+u•chartAxis n‖^2 = ‖y‖^2+u^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,transverseLift_inner_axis,
      mul_zero,mul_zero,add_zero,transverseLift_norm,norm_smul,
      chartAxis_norm,mul_one,Real.norm_eq_abs,sq_abs]
  constructor
  · nlinarith [norm_nonneg y,norm_nonneg (transverseLift y+u•chartAxis n),sq_nonneg u]
  · nlinarith [abs_nonneg u,sq_abs u,norm_nonneg (transverseLift y+u•chartAxis n),
      sq_nonneg ‖y‖]

theorem rotated_cap_coordinate_bounds {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ‖(sphereMap e (gnomonicChart (coordinateJoin y u)) : Space (n+2)) -
      e (chartPole n)‖ ≤ δ) :
    ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ ∧ ‖y‖ ≤ 2*δ ∧ |u| ≤ 2*δ := by
  have hc : ‖(gnomonicChart (coordinateJoin y u) : Space (n+2))-chartPole n‖ ≤ δ := by
    change ‖e (gnomonicChart (coordinateJoin y u)) - e (chartPole n)‖ ≤ δ at hcap
    rwa [← e.map_sub,e.norm_map] at hcap
  have ho : inner ℝ (chartPole n) (transverseLift y+u•chartAxis n) = 0 := by
    rw [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hnear : ‖‖chartPole n+(transverseLift y+u•chartAxis n)‖⁻¹ •
      (chartPole n+(transverseLift y+u•chartAxis n))-chartPole n‖ ≤ δ := by
    simpa only [gnomonicChart_coordinateJoin,normalizedLine,add_assoc] using hc
  have hh := small_cap_chart_displacement (chartPole_norm n) ho hδ hsmall hnear
  exact ⟨hh,(transverse_coordinate_bounds y u).1.trans hh,
    (transverse_coordinate_bounds y u).2.trans hh⟩

theorem cap_mem_rotated_north {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (z : Sphere (n+2))
    {δ : ℝ} (hsmall : δ ≤ 1/2)
    (hcap : ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ) :
    sphereMap e.symm z ∈ northHemisphere (n+1) := by
  have hi := abs_real_inner_le_norm (e (chartPole n)) ((z : Space (n+2))-e (chartPole n))
  rw [e.norm_map,chartPole_norm,one_mul,inner_sub_right,
    real_inner_self_eq_norm_sq,e.norm_map,chartPole_norm,one_pow] at hi
  have hp : 0 < inner ℝ (e (chartPole n)) (z : Space (n+2)) := by
    have hh := (neg_le_abs (inner ℝ (e (chartPole n)) (z : Space (n+2))-1)).trans
      (hi.trans hcap)
    linarith
  change 0 < (e.symm (z : Space (n+2))) 0
  rw [← chartPole_inner,← inner_isometry_pullback]
  exact hp

theorem cap_amplitude_chart_support {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ) :
    (∀ z, sphereMap e.symm z ∉ northHemisphere (n+1) → b z = 0) ∧
    (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) ∧
    (∀ y : Space n, tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) := by
  have hcoord (y : Space n) (u : ℝ) (h : rotatedChartAmplitude e b y u ≠ 0) :
      ‖y‖ ≤ 1 ∧ |u| ≤ 1 := by
    have hc := rotated_cap_coordinate_bounds e y u hδ hsmall
      (hcap (sphereMap e (gnomonicChart (coordinateJoin y u))) h)
    exact ⟨hc.2.1.trans (by linarith),hc.2.2.trans (by linarith)⟩
  refine ⟨?_,?_,?_⟩
  · intro z hz
    by_contra h
    exact hz (cap_mem_rotated_north e z hsmall (hcap z h))
  · intro y hy u
    by_contra h
    exact (not_le_of_gt hy) (hcoord y u h).1
  · intro y
    apply closure_minimal _ isClosed_Icc
    intro u hu
    exact abs_le.mp (hcoord y u hu).2

theorem cap_amplitude_chart_radius {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ)
    (y : Space n) :
    ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
      ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ := by
  have hs : tsupport (rotatedChartAmplitude e b y) ⊆
      {u : ℝ | ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ} := by
    apply closure_minimal
    · intro u hu
      exact (rotated_cap_coordinate_bounds e y u hδ hsmall
        (hcap (sphereMap e (gnomonicChart (coordinateJoin y u))) hu)).1
    · exact isClosed_le (by fun_prop) continuous_const
  exact fun u hu => hs hu

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AdaptedFailure
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A single adapted chart for a discarded cell--cap term

The frame is chosen using the cap center and the center displacement.
It works simultaneously for every point displacement allowed by the
cell-replacement error. No choice depends on an individual point pair.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem failed_test_adapted_phase_lower {n : ℕ} {w d : Space (n+2)}
    (hw : ‖w‖ = 1) {τ : ℝ} (hτ : 0 < τ)
    (hbad : τ < ‖perpendicularPart w d‖) :
    ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
      ∀ (y : Space n) (v : Space (n+2)) (u : ℝ),
        ‖transverseLift y+u•chartAxis n‖ ≤ 1 →
        ‖v-d‖+4*‖transverseLift y+u•chartAxis n‖*‖d‖ ≤ τ/2 →
        τ/4 ≤ |deriv (fun x => inner ℝ
          (normalizedLine (chartPole n+transverseLift y) (chartAxis n) x) (e.symm v)) u| := by
  obtain ⟨t,ht,hwt,hl⟩ := perpendicular_failure_chart_nonstationary hw hτ hbad
  obtain ⟨e,he₀,he₁⟩ := exists_adapted_chart_frame hw ht hwt
  refine ⟨e,he₀,?_⟩
  intro y v u hsmall herr
  have hy : inner ℝ w (e (transverseLift y)) = 0 := by
    rw [← he₀,e.inner_map_map]
    exact chartPole_inner_transverse y
  have heq : ‖e (transverseLift y)+u•t‖ = ‖transverseLift y+u•chartAxis n‖ := by
    rw [← he₁,← e.map_smul,← e.map_add,e.norm_map]
  have hsmall' : ‖e (transverseLift y)+u•t‖ ≤ 1 := by rw [heq]; exact hsmall
  have herr' : ‖v-d‖+4*‖e (transverseLift y)+u•t‖*‖d‖ ≤ τ/2 := by
    rw [heq]
    exact herr
  have hh := hl (e (transverseLift y)) v u hy hsmall' herr'
  have hp : (fun x => inner ℝ (normalizedLine (w+e (transverseLift y)) t x) v) =
      (fun x => inner ℝ
        (normalizedLine (chartPole n+transverseLift y) (chartAxis n) x) (e.symm v)) := by
    funext x
    rw [← he₀,← he₁,← e.map_add,normalizedLine_isometry,inner_isometry_pullback]
  rw [hp] at hh
  exact hh

theorem failed_test_sphere_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ : ℝ),
      ‖w‖ = 1 → 0 < τ → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ), Measurable b →
          (∀ z, sphereMap e.symm z ∉ northHemisphere (n+1) → b z = 0) →
          (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) →
          (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
          (∀ y : Space n, ‖y‖ ≤ 1 →
            tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) →
          ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
          (∀ z, ‖b z‖ ≤ M) → ‖v‖ ≤ (τ/4)*D →
          (∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖transverseLift y+u•chartAxis n‖ ≤ 1 ∧
            ‖v-d‖+4*‖transverseLift y+u•chartAxis n‖*‖d‖ ≤ τ/2) →
          (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
          ‖∫ z : Sphere (n+2),
            Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (z : Space (n+2)) v : ℂ))*b z
            ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*(τ/4)))^m := by
  obtain ⟨A,hA,he⟩ := rotated_sphere_chart_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ hw hτ hbad
  obtain ⟨e,hew,hl⟩ := failed_test_adapted_phase_lower hw hτ hbad
  refine ⟨e,hew,?_⟩
  intro v b hb hs hout hsmooth hsupport M C D Λ hC hD hΛ hM hv herr hder
  apply he e v b hb hs hout hsmooth hsupport M C D Λ (τ/4) hC hD hΛ
    (by positivity) hM hv
  · intro y hy u hu
    exact hl y v u (herr y hy u hu).1 (herr y hy u hu).2
  · exact hder

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapLocalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonstationarity on a geometric cap after point replacement

The frame depends only on the cap center and center displacement.
Support and the phase lower bound are proved from the geometric cap and
the original point-replacement error. Only amplitude regularity remains
as local analytic data.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem failed_cap_sphere_nonstationary (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 ≤ δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ), Measurable b →
          (∀ z, b z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
          (∀ y : Space n, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
          ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
          (∀ z, ‖b z‖ ≤ M) → ‖v‖ ≤ (τ/4)*D →
          ‖v-d‖+8*δ*‖d‖ ≤ τ/2 →
          (∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
            ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
          ‖∫ z : Sphere (n+2),
            Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (z : Space (n+2)) v : ℂ))*b z
            ∂sphereMeasure (n+2)‖ ≤ A*C*(D/(Λ*(τ/4)))^m := by
  obtain ⟨A,hA,he⟩ := failed_test_sphere_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ δ hw hτ hδ hδsmall hbad
  obtain ⟨e,hew,hestimate⟩ := he w d τ hw hτ hbad
  refine ⟨e,hew,?_⟩
  intro v b hb hcap hsmooth M C D Λ hC hD hΛ hM hv herr hder
  have hc : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ := by
    simpa only [hew] using hcap
  obtain ⟨hs,hout,hsupport⟩ := cap_amplitude_chart_support e b hδ hδsmall hc
  apply hestimate v b hb hs hout hsmooth (fun y _ => hsupport y)
    M C D Λ hC hD hΛ hM hv
  · intro y _ u hu
    have hr := cap_amplitude_chart_radius e b hδ hδsmall hc y u hu
    refine ⟨hr.trans (by linarith),?_⟩
    have hm := mul_le_mul_of_nonneg_right hr (norm_nonneg d)
    nlinarith
  · exact hder

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapReciprocal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

theorem capReciprocal_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capDenominator_chart_derivatives n k)
  obtain ⟨C,hC,hCb⟩ := reciprocal_germ_derivatives B hB m
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 S hsep hcover e y hy u hu
  let g : ℝ → ℝ := fun t => capDenominator δ hδ S (rotatedChartCurve e y t)
  let q : ℝ → ℝ := fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)
  have hg : ContDiff ℝ ∞ g := (capDenominator_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ q := (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hw (t : ℝ) : rotatedChartCurve e y t ∈ Metric.sphere (0 : Space (n+2)) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,rotatedChartCurve_norm]
  have hg1 (t : ℝ) : 1 ≤ g t := capDenominator_ge_one hδ S hcover ⟨_,hw t⟩
  have he : (fun t => q t*g t) =ᶠ[𝓝 u] (fun _ => 1) := Filter.Eventually.of_forall (by
    intro t
    simpa only [g,q,mul_comm] using capDenominator_mul_reciprocal hδ S hcover ⟨_,hw t⟩)
  have hh := hCb g q hg hq 1 δ⁻¹ u zero_lt_one (inv_nonneg.mpr hδ.le)
    ((hg1 u).trans (le_abs_self _)) he (by
      intro k _hk _hkm
      simpa only [mul_one] using hBb k δ hδ hδ1 S hsep e y hy u hu)
  simpa only [inv_one,mul_one] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_NormalizedCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

theorem normalizedCap_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capBump_rotated_derivatives n k)
  choose Q hQ hQb using (fun k => capReciprocal_chart_derivatives n k)
  let A := ∑ k ∈ Finset.range (m+1), (m.choose k : ℝ)*B k*Q (m-k)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hQ (m-k)))
  refine ⟨A,hA,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  have hb : ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) :=
    (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  change |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)*
    capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_mul ((hb.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) ((hq.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), |(m.choose k : ℝ)*
        iteratedDeriv k (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u*
        iteratedDeriv (m-k) (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m+1), ((m.choose k : ℝ)*B k*Q (m-k))*(δ⁻¹)^m := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (m.choose k : ℝ)*(B k*(δ⁻¹)^k)*(Q (m-k)*(δ⁻¹)^(m-k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hBb k δ hδ hδ1 c e y hy u hu)
            (Nat.cast_nonneg _)) (hQb (m-k) δ hδ hδ1 S hsep hcover e y hy u hu)
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hB k) (pow_nonneg (inv_nonneg.mpr hδ.le) k)))
        _ = _ := by
          have hp : (δ⁻¹)^k*(δ⁻¹)^(m-k) = (δ⁻¹)^m := by
            rw [← pow_add,Nat.add_sub_of_le hkm]
          calc
            _ = ((m.choose k : ℝ)*B k*Q (m-k))*((δ⁻¹)^k*(δ⁻¹)^(m-k)) := by ring
            _ = _ := by rw [hp]
    _ = A*(δ⁻¹)^m := (Finset.sum_mul _ _ _).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_QuantitativeCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative smooth cap partition on the sphere

This supplies the actual partition used in angular localization, with
uniform derivatives, a polynomial global count, and bounded local overlap.
It contains no Fourier or incidence estimate as an assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_complex_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (rotatedChartAmplitude e
        (fun w => (normalizedCap δ hδ S c w : ℂ)) y) u‖ ≤ B*(δ⁻¹)^m := by
  obtain ⟨B,hB,hBb⟩ := normalizedCap_chart_derivatives n m
  refine ⟨B,hB,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  let f : ℝ → ℝ := fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)
  have hf : ContDiff ℝ ∞ f :=
    (normalizedCap_contDiff hδ S c).comp (rotatedChartCurve_contDiff e y)
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.contDiffAt (x := u))
    (show (m : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] at hn
  change ‖iteratedDeriv m (Complex.ofRealLI ∘ f) u‖ ≤ _
  rw [hn]
  exact hBb δ hδ hδ1 S hsep hcover c e y hy u hu

theorem quantitative_smooth_cap_partition (n m : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
        (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
        (∀ w, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^(n+2)) ∧
        (∀ c, Measurable (η c)) ∧
        (∀ w, ∑ c ∈ S, η c w = 1) ∧
        (∀ c ∈ S, ∀ w, 0 ≤ η c w ∧ η c w ≤ 1) ∧
        (∀ c ∈ S, ∀ w, η c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
          ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y)) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
          ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ m,
          ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k) := by
  classical
  choose B hB hBb using (fun k => normalizedCap_complex_chart_derivatives n k)
  let H := ∑ k ∈ Finset.range (m+1), B k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hB k)
  refine ⟨H,hH,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hsep,hcover,hcard,hoverlap⟩ := finite_separated_cap_net (n+2) hδ
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  refine ⟨S,fun c w => normalizedCap δ hδ S c w,hcard,hoverlap,?_,hpart,hbounds,
    (fun c hc w => hsupport c hc w),?_,?_⟩
  · intro c
    exact (normalizedCap_contDiff hδ S c).continuous.measurable.comp continuous_subtype_val.measurable
  · intro c e y
    exact ambient_symbol_chart_smooth e (fun x => (normalizedCap δ hδ S c x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (normalizedCap_contDiff hδ S c)) y
  · intro c e y hy u hu k hkm
    apply (hBb k δ hδ hδ1 S (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
      hcover c e y hy u hu).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereOffPole
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decay away from the two stationary poles

The actual normalized cap partition reduces a full-sphere amplitude to
the proved capwise integration-by-parts estimate. The only published
input is the gnomonic surface formula. Constants depend on the fixed
distance from the poles, dimension, and differentiation order.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

private theorem offPole_center_gap {d : ℕ} (v : Space d) (hv : ‖v‖ = 1)
    (c z : Sphere d) {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ≤ ε/64)
    (hnear : ‖(z : Space d)-(c : Space d)‖ ≤ δ)
    (hgap : ε ≤ ‖perpendicularPart (z : Space d) v‖) :
    ε/4 < ‖perpendicularPart (c : Space d) v‖ := by
  have he := perpendicularPart_test_error (sphere_norm c) (sphere_norm z) v v
  simp only [sub_self,norm_zero,hv,mul_one,zero_add] at he
  rw [norm_sub_rev (c : Space d) (z : Space d)] at he
  have ht : ‖perpendicularPart (z : Space d) v‖ ≤
      ‖perpendicularPart (c : Space d) v‖ +
        ‖perpendicularPart (c : Space d) v-perpendicularPart (z : Space d) v‖ := by
    calc
      _ = ‖perpendicularPart (c : Space d) v -
          (perpendicularPart (c : Space d) v-perpendicularPart (z : Space d) v)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  nlinarith

/-- Uniform full-sphere integration by parts for an amplitude separated
from both poles. Its hypotheses are ordinary chart derivative bounds on
the original amplitude, before cap localization. -/
theorem sphere_offPole_decay (hpublished : PublishedGnomonicSurface)
    (n m : ℕ) (hn : 1 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : Space (n+2)) (b : Sphere (n+2) → ℂ),
      ‖v‖ = 1 → Measurable b →
      (∀ w, b w ≠ 0 → ε ≤ ‖perpendicularPart (w : Space (n+2)) v‖) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
        ContDiff ℝ ∞ (rotatedChartAmplitude e b y)) →
      ∀ (M C D Λ : ℝ), 0 ≤ C → 1 ≤ D → 0 < Λ →
      (∀ w, ‖b w‖ ≤ M) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
        ∀ k ≤ m, ∀ u ∈ Icc (-1 : ℝ) 1,
          ‖iteratedDeriv k (rotatedChartAmplitude e b y) u‖ ≤ C*D^k) →
      ‖∫ w : Sphere (n+2),
        Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))*b w
        ∂sphereMeasure (n+2)‖ ≤ K*C*(D/Λ)^m := by
  classical
  let δ := min (ε/64) (1/4 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε/64 := min_le_left _ _
  have hδsmall : δ ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨H,hH,hpartition⟩ := quantitative_smooth_cap_partition n m
  obtain ⟨S,η,_hcard,_hoverlap,hηmeas,hηsum,hηnorm,hηcap,hηsmooth,hηder⟩ :=
    hpartition δ hδ (hδsmall.trans (by norm_num))
  obtain ⟨A,hA,hestimate⟩ := failed_cap_sphere_nonstationary hpublished n m hn
  let τ := ε/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let q := max 1 (max δ⁻¹ (4/τ))
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hqδ : δ⁻¹ ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqτ : 4/τ ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(S.card : ℝ)*A*(2^m*H)*(q/(τ/4))^m,by positivity,?_⟩
  intro v b hv hb hgap hsmooth M C D Λ hC hD hΛ hM hder
  let bcap : Sphere (n+2) → Sphere (n+2) → ℂ :=
    fun c w => (η c w : ℂ)*b w
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hqD : 1 ≤ q*D := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hD)]
  have hqD0 : 0 ≤ q*D := zero_le_one.trans hqD
  have hDb : D ≤ q*D := le_mul_of_one_le_left hD0 hq
  have hDδ : δ⁻¹ ≤ q*D := hqδ.trans (le_mul_of_one_le_right hq0 hD)
  have hDτ : 1 ≤ (τ/4)*(q*D) := by
    have hbound : 4/τ ≤ q*D := hqτ.trans (le_mul_of_one_le_right hq0 hD)
    have hh := (div_le_iff₀ hτ).mp hbound
    nlinarith
  have hbcMeas (c : Sphere (n+2)) : Measurable (bcap c) :=
    (Complex.measurable_ofReal.comp (hηmeas c)).mul hb
  have hbcCap (c : Sphere (n+2)) (hc : c ∈ S) :
      ∀ w, bcap c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ := by
    intro w hw
    apply hηcap c hc w
    intro hz
    exact hw (by simp [bcap,hz])
  have hbcNorm (c : Sphere (n+2)) (hc : c ∈ S) (w : Sphere (n+2)) :
      ‖bcap c w‖ ≤ M := by
    have he := hηnorm c hc w
    calc
      _ = |η c w| * ‖b w‖ := by simp only [bcap,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ 1*‖b w‖ := mul_le_mul_of_nonneg_right
        (by simpa only [abs_of_nonneg he.1] using he.2) (norm_nonneg _)
      _ ≤ M := by simpa only [one_mul] using hM w
  have hbcSmooth (c : Sphere (n+2))
      (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (hy : ‖y‖ ≤ 1) :
      ContDiff ℝ ∞ (rotatedChartAmplitude e (bcap c) y) :=
    (hηsmooth c e y).mul (hsmooth e y hy)
  let F : Sphere (n+2) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space (n+2)) v : ℂ))
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hFnorm (w : Sphere (n+2)) : ‖F w‖ = 1 := by
    simp only [F,Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
      sub_zero,Real.exp_zero]
  have hbcInt (c : Sphere (n+2)) (hc : c ∈ S) :
      Integrable (fun w => F w*bcap c w) (sphereMeasure (n+2)) :=
    Integrable.of_bound (hFm.mul (hbcMeas c)).aestronglyMeasurable M
      (Filter.Eventually.of_forall (fun w => by
        simpa only [norm_mul,hFnorm,one_mul] using hbcNorm c hc w))
  have hbcEst (c : Sphere (n+2)) (hc : c ∈ S) :
      ‖∫ w, F w*bcap c w ∂sphereMeasure (n+2)‖ ≤
        A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m := by
    by_cases hz : ∀ w, bcap c w = 0
    · simp only [hz,mul_zero,integral_zero,norm_zero]
      positivity
    · obtain ⟨z,hz⟩ := not_forall.mp hz
      have hbz : b z ≠ 0 := by
        intro hh
        exact hz (by simp only [bcap,hh,mul_zero])
      have hbad := offPole_center_gap v hv c z hε hδε (hbcCap c hc z hz) (hgap z hbz)
      obtain ⟨e,he,heEst⟩ := hestimate c v τ δ (sphere_norm c) hτ hδ.le hδsmall hbad
      have hcap : ∀ w, bcap c w ≠ 0 →
          ‖(w : Space (n+2))-e (chartPole n)‖ ≤ δ := by
        simpa only [he] using hbcCap c hc
      have hsupport := (cap_amplitude_chart_support e (bcap c) hδ.le hδsmall hcap).2.2
      apply heEst v (bcap c) (hbcMeas c) (hbcCap c hc) (hbcSmooth c e)
        M (2^m*H*C) (q*D) Λ (by positivity) hqD hΛ (hbcNorm c hc)
        (by simpa only [hv] using hDτ) ?_ ?_
      · simp only [sub_self,norm_zero,hv,mul_one,zero_add]
        dsimp [τ]
        linarith
      · intro k hk y hy u hu
        have hui := hsupport y hu
        have hbound := PlanarFalconer.complex_product_derivative_bound
          (hηsmooth c e y) (hsmooth e y hy) hH hC hqD0 k u
          (fun j hj => (hηder c e y hy u hui j (hj.trans hk)).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hDδ j) hH))
          (fun j hj => (hder e y hy j (hj.trans hk) u hui).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hDb j) hC))
        apply hbound.trans
        change (2 : ℝ)^k*H*C*(q*D)^k ≤ (2^m*H*C)*(q*D)^k
        gcongr
        norm_num
  have hsplit (w : Sphere (n+2)) : F w*b w = ∑ c ∈ S, F w*bcap c w := by
    have hs : (∑ c ∈ S, (η c w : ℂ)) = 1 := by exact_mod_cast hηsum w
    calc
      _ = (F w*(∑ c ∈ S, (η c w : ℂ)))*b w := by rw [hs,mul_one]
      _ = ∑ c ∈ S, F w*((η c w : ℂ)*b w) := by
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := rfl
  change ‖∫ w, F w*b w ∂sphereMeasure (n+2)‖ ≤ _
  simp_rw [hsplit]
  rw [integral_finsetSum S hbcInt]
  calc
    _ ≤ ∑ c ∈ S, ‖∫ w, F w*bcap c w ∂sphereMeasure (n+2)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ S, A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m :=
      Finset.sum_le_sum hbcEst
    _ = (S.card : ℝ)*(A*(2^m*H*C)*((q*D)/(Λ*(τ/4)))^m) := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by
      have hr : (q*D)/(Λ*(τ/4)) = (q/(τ/4))*(D/Λ) := by ring
      rw [hr,mul_pow]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LaplacianIsometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rotation invariance and locality of the actual quadratic jets

These are identities for the Euclidean derivatives in the published input.
They allow the choice of tangent orthonormal coordinates and fixed cutoffs
to be removed from the resulting stationary coefficients.
-/

namespace Falconer
open InnerProductSpace
open scoped Topology

theorem euclidean_iterated_laplacian_congr {n : ℕ} {f g : Space n → ℂ}
    {x : Space n} (h : f =ᶠ[𝓝 x] g) (j : ℕ) :
    ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] f) =ᶠ[𝓝 x]
      ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j] g) := by
  induction j with
  | zero => exact h
  | succ j hj =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact laplacian_congr_nhds hj

theorem quadraticJetCoefficient_congr {n : ℕ} {f g : Space n → ℂ}
    (h : f =ᶠ[𝓝 (0 : Space n)] g) (j : ℕ) :
    quadraticJetCoefficient j f = quadraticJetCoefficient j g := by
  unfold quadraticJetCoefficient
  rw [(euclidean_iterated_laplacian_congr h j).self_of_nhds]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuadraticChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed quadratic chart at a sphere pole

This is the actual chart in `osc:stationary`. Its phase is exactly quadratic,
in every dimension. Surface measure transport and its Jacobian are separate
from the geometric statements here.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem quadraticSpherePoint_norm {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u‖ = 1 := by
  have hu2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have harg : 0 ≤ 1-‖u‖^2/4 := by nlinarith
  have hs := Real.sq_sqrt harg
  have he := coordinateJoin_norm_sq (Real.sqrt (1-‖u‖^2/4) • u) (1-‖u‖^2/2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hs] at he
  change ‖quadraticSpherePoint u‖^2 = _ at he
  nlinarith [norm_nonneg (quadraticSpherePoint u)]

/-- The oscillatory phase at the pole is exactly `1 - ‖u‖²/2`. -/
theorem quadraticSpherePoint_phase {n : ℕ} (u : Space n) :
    inner ℝ (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1) =
      1-‖u‖^2/2 := by
  simp [quadraticSpherePoint, coordinateJoin_inner]

theorem gnomonicChart_quadraticToGnomonic {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (gnomonicChart (quadraticToGnomonic u) : Space (n+1)) = quadraticSpherePoint u := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; nlinarith
  have he : northLift (quadraticToGnomonic u) = a⁻¹ • quadraticSpherePoint u := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [northLift_zero, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_zero_coord]
      change 1 = a⁻¹ * a
      exact (inv_mul_cancel₀ ha.ne').symm
    · simp only [northLift_succ, quadraticToGnomonic, PiLp.smul_apply, smul_eq_mul,
        quadraticSpherePoint_succ_coord]
      dsimp only [a]
      ring
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    rw [he, norm_smul, quadraticSpherePoint_norm (hu.le.trans (by norm_num)),
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_one]
  change ‖northLift (quadraticToGnomonic u)‖⁻¹ • northLift (quadraticToGnomonic u) = _
  rw [hn, he, smul_smul, inv_inv, mul_inv_cancel₀ ha.ne', one_smul]

theorem quadraticToGnomonic_injOn (n : ℕ) :
    Set.InjOn (@quadraticToGnomonic n) (Metric.ball (0 : Space n) 1) := by
  intro u hu v hv heq
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hv' : ‖v‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hp : quadraticSpherePoint u = quadraticSpherePoint v := by
    rw [← gnomonicChart_quadraticToGnomonic hu',
      ← gnomonicChart_quadraticToGnomonic hv', heq]
  have hzero := congrArg (fun z : Space (n+1) => z 0) hp
  simp only [quadraticSpherePoint_zero_coord] at hzero
  have hs : ‖u‖^2 = ‖v‖^2 := by linarith
  have hu2 := (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu'
  have hq : Real.sqrt (1-‖u‖^2/4) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Space (n+1) => z i.succ) hp
  simp only [quadraticSpherePoint_succ_coord, ← hs] at hi
  exact mul_left_cancel₀ hq hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticDifferential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Differential of the quadratic-to-gnomonic coordinate change

The differential is a scalar multiple of the identity plus one radial
rank-one term. These are actual derivatives of the coordinate map, not
assumed Jacobian data.
-/

namespace Falconer

private theorem radial_derivative_algebra (s q a : ℝ) (hq : q ≠ 0)
    (ha : a ≠ 0) (has : a = 1-s/2) (hqs : q^2 = 1-s/4) :
    ((-1/4)/(2*q)*a - q*(-1/2))/a^2 = (6-s)/(16*q*a^2) := by
  field_simp [hq, ha]
  nlinarith

private theorem radial_eigenvalue_algebra (s q a : ℝ) (hq : q ≠ 0)
    (ha : a ≠ 0) (has : a = 1-s/2) (hqs : q^2 = 1-s/4) :
    q/a + 2*s*((6-s)/(16*q*a^2)) = 1/(q*a^2) := by
  field_simp [hq, ha]
  rw [has]
  ring_nf
  rw [hqs]
  ring

theorem quadraticRadialFactor_hasDerivAt {s : ℝ} (hs : s < 1) :
    HasDerivAt quadraticRadialFactor (quadraticRadialDerivative s) s := by
  have hq : 0 < Real.sqrt (1-s/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-s/2 := by linarith
  have hb : HasDerivAt (fun t : ℝ => 1-t/4) (-1/4) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const 4) using 1 <;>
      first | rfl | norm_num
  have hc : HasDerivAt (fun t : ℝ => 1-t/2) (-1/2) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const 2) using 1 <;>
      first | rfl | norm_num
  have hh := (hb.sqrt (by linarith : 1-s/4 ≠ 0)).div hc ha.ne'
  have he := radial_derivative_algebra s (Real.sqrt (1-s/4)) (1-s/2) hq.ne' ha.ne' rfl
    (Real.sq_sqrt (show 0 ≤ 1-s/4 by linarith))
  exact hh.congr_deriv he

theorem quadraticToGnomonic_hasFDerivAt {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    HasFDerivAt quadraticToGnomonic (quadraticCoordinateDifferential u) u := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hφ := (quadraticRadialFactor_hasDerivAt hu2).hasFDerivAt.comp u
    (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hF := hφ.smul (hasFDerivAt_id u)
  apply hF.congr_fderiv
  ext v
  simp [quadraticCoordinateDifferential,
    ContinuousLinearMap.toSpanSingleton_apply, smul_smul, mul_comm, mul_left_comm]

theorem quadratic_radial_eigenvalue {s : ℝ} (hs : s < 1) :
    quadraticRadialFactor s + 2*s*quadraticRadialDerivative s =
      1 / (Real.sqrt (1-s/4) * (1-s/2)^2) := by
  have hq : 0 < Real.sqrt (1-s/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-s/2 := by linarith
  exact radial_eigenvalue_algebra s (Real.sqrt (1-s/4)) (1-s/2) hq.ne' ha.ne' rfl
    (Real.sq_sqrt (show 0 ≤ 1-s/4 by linarith))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticJacobian
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Jacobian of the quadratic-to-gnomonic change of variables

The matrix determinant lemma applies to the actual derivative, a scalar
matrix plus one radial term. This gives the measure Jacobian needed to
transfer the published gnomonic density to the quadratic chart.
-/

namespace Falconer
open Matrix

private theorem radial_matrix_det (n : ℕ) (u : Space n) {a b : ℝ} (ha : a ≠ 0) :
    (a • (1 : Matrix (Fin n) (Fin n) ℝ) +
      b • vecMulVec (fun i => u i) (fun i => u i)).det =
        a^n * (1 + b/a * ‖u‖^2) := by
  have he : a • (1 : Matrix (Fin n) (Fin n) ℝ) +
      b • vecMulVec (fun i => u i) (fun i => u i) =
      a • (1 + vecMulVec (fun i => b/a*u i) (fun i => u i)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    field_simp
  rw [he, Matrix.det_smul, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp only [Fintype.card_fin]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadraticCoordinateDifferential_det {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    (quadraticCoordinateDifferential u).det =
      (quadraticRadialFactor (‖u‖^2))^n *
        (1 + (2 * quadraticRadialDerivative (‖u‖^2)) /
          quadraticRadialFactor (‖u‖^2) * ‖u‖^2) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hφ : quadraticRadialFactor (‖u‖^2) ≠ 0 := by
    unfold quadraticRadialFactor
    exact div_ne_zero (Real.sqrt_pos.mpr (by linarith)).ne' (by linarith)
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change LinearMap.det (quadraticCoordinateDifferential u).toLinearMap = _
  rw [← LinearMap.det_toMatrix B]
  have hmatrix : LinearMap.toMatrix B B (quadraticCoordinateDifferential u).toLinearMap =
      quadraticRadialFactor (‖u‖^2) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        (2 * quadraticRadialDerivative (‖u‖^2)) •
          vecMulVec (fun i => u i) (fun i => u i) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, B, quadraticCoordinateDifferential,
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      OrthonormalBasis.coe_toBasis, map_add, map_smul, smul_eq_mul,
      Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply]
    simp only [EuclideanSpace.basisFun_apply, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      innerSL_apply_apply, EuclideanSpace.inner_single_right,
      PiLp.single_apply, Matrix.one_apply, starRingEnd_apply, star_trivial]
    split_ifs <;> ring
  rw [hmatrix]
  exact radial_matrix_det n u hφ

private theorem radial_det_factor (m : ℕ) {a : ℝ} (ha : a ≠ 0) (b s : ℝ) :
    a^(m+2) * (1+b/a*s) = a^(m+1) * (a+b*s) := by
  rw [show m+2 = (m+1)+1 by omega, pow_succ]
  field_simp

private theorem radial_quotient_factor (m : ℕ) (q a : ℝ)
    (hq : q ≠ 0) (ha : a ≠ 0) :
    (q/a)^(m+1) * (1/(q*a^2)) = q^m/a^(m+3) := by
  rw [div_pow, pow_succ, show m+3 = (m+1)+2 by omega, pow_add]
  field_simp
  rw [show m+1+2 = m+3 by omega, pow_add]

/-- The dimension range in which the published gnomonic formula is used.
The ambient dimension is `m+3` and the sphere dimension is `m+2`. -/
theorem quadraticCoordinateDifferential_det_explicit (m : ℕ) {u : Space (m+2)}
    (hu : ‖u‖ < 1) :
    (quadraticCoordinateDifferential u).det =
      (Real.sqrt (1-‖u‖^2/4))^m / (1-‖u‖^2/2)^(m+3) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hq : 0 < Real.sqrt (1-‖u‖^2/4) := Real.sqrt_pos.mpr (by linarith)
  have ha : 0 < 1-‖u‖^2/2 := by linarith
  have hφ : quadraticRadialFactor (‖u‖^2) ≠ 0 := div_ne_zero hq.ne' ha.ne'
  rw [quadraticCoordinateDifferential_det hu, radial_det_factor m hφ]
  have he : quadraticRadialFactor (‖u‖^2) +
      2 * quadraticRadialDerivative (‖u‖^2) * ‖u‖^2 =
      1 / (Real.sqrt (1-‖u‖^2/4) * (1-‖u‖^2/2)^2) := by
    convert quadratic_radial_eigenvalue hu2 using 1 <;> first | rfl | ring
  rw [he]
  exact radial_quotient_factor m _ _ hq.ne' ha.ne'

theorem quadraticCoordinateDifferential_det_pos (m : ℕ) {u : Space (m+2)}
    (hu : ‖u‖ < 1) : 0 < (quadraticCoordinateDifferential u).det := by
  rw [quadraticCoordinateDifferential_det_explicit m hu]
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (by linarith)) _)
    (pow_pos (by linarith) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual sphere integral in fixed quadratic coordinates

The only measure input is the already recorded gnomonic surface formula.
The quadratic coordinate Jacobian is proved locally. Its product with the
gnomonic density is exactly the manuscript's `(1-‖u‖²/4)^((n-2)/2)`.
-/

namespace Falconer
open Set MeasureTheory

theorem quadratic_gnomonic_density {n : ℕ} {u : Space n} (hu : ‖u‖ < 1) :
    gnomonicDensity (quadraticToGnomonic u) = (1-‖u‖^2/2)^(n+1) := by
  let a : ℝ := 1-‖u‖^2/2
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 0 < a := by dsimp [a]; linarith
  have hp := congrArg (fun x : Space (n+1) => x 0)
    (gnomonicChart_quadraticToGnomonic hu)
  simp only [gnomonicChart_zero, quadraticSpherePoint_zero_coord] at hp
  have hn : ‖northLift (quadraticToGnomonic u)‖ = a⁻¹ := by
    have hi := congrArg Inv.inv hp
    simpa only [inv_inv] using hi
  unfold gnomonicDensity
  rw [← northLift_norm_sq, hn]
  change ((a⁻¹)^2)^(-((n+1 : ℕ) : ℝ)/2) = a^(n+1)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr ha.le),
    Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
  convert Real.rpow_natCast a (n+1) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  push_cast
  ring

theorem quadratic_jacobian_density (m : ℕ) {u : Space (m+2)} (hu : ‖u‖ < 1) :
    |(quadraticCoordinateDifferential u).det| *
      gnomonicDensity (quadraticToGnomonic u) = (Real.sqrt (1-‖u‖^2/4))^m := by
  rw [abs_of_pos (quadraticCoordinateDifferential_det_pos m hu),
    quadraticCoordinateDifferential_det_explicit m hu, quadratic_gnomonic_density hu]
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have ha : 1-‖u‖^2/2 ≠ 0 := by linarith
  have hn : (m+2)+1 = m+3 := by omega
  rw [hn, div_mul_cancel₀ _ (pow_ne_zero _ ha)]

/-- A function supported in this fixed north-pole chart has exactly the
quadratic-coordinate integral, including its surface Jacobian. -/
theorem quadratic_sphere_integral (hpublished : PublishedGnomonicSurface)
    (m : ℕ) (f : Sphere (m+3) → ℂ) (hf : Measurable f)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → f w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        f (gnomonicChart x) = 0) :
    (∫ w, f w ∂sphereMeasure (m+3)) =
      ∫ u in Metric.ball (0 : Space (m+2)) 1,
        (Real.sqrt (1-‖u‖^2/4))^m • f (gnomonicChart (quadraticToGnomonic u)) := by
  rw [gnomonic_sphere_integral hpublished (by omega) f hf hs]
  let U := Metric.ball (0 : Space (m+2)) 1
  let g : Space (m+2) → ℂ := fun x => gnomonicDensity x • f (gnomonicChart x)
  have hg : ∀ x, x ∉ quadraticToGnomonic '' U → g x = 0 := by
    intro x hx
    simp only [g, hchart x hx, smul_zero]
  change (∫ x, g x) = _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (fun u hu => (quadraticToGnomonic_hasFDerivAt (by
      simpa only [U, Metric.mem_ball, dist_zero_right] using hu)).hasFDerivWithinAt)
    (quadraticToGnomonic_injOn (m+2)) g]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (show MeasurableSet U from measurableSet_ball)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [U, Metric.mem_ball, dist_zero_right] using hu
  simp only [g, smul_smul, quadratic_jacobian_density m hu']

/-- The north-pole phase is exactly a constant phase times the negative
quadratic phase. This is the local integral to which quadratic stationary
phase will be applied. -/
theorem quadratic_sphere_oscillatory_integral (hpublished : PublishedGnomonicSurface)
    (m : ℕ) (Λ : ℝ) (b : Sphere (m+3) → ℂ) (hb : Measurable b)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → b w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        b (gnomonicChart x) = 0) :
    (∫ w : Sphere (m+3),
      Complex.exp (Complex.I*(Λ : ℂ)*
        (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
      ∂sphereMeasure (m+3)) =
    Complex.exp (Complex.I*(Λ : ℂ)) *
      ∫ u in Metric.ball (0 : Space (m+2)) 1,
        Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
          ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) * b (gnomonicChart (quadraticToGnomonic u)) := by
  let f : Sphere (m+3) → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*
      (inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) : ℂ)) * b w
  have hf : Measurable f := by
    apply Measurable.mul _ hb
    fun_prop
  have hfs : ∀ w, w ∉ northHemisphere (m+2) → f w = 0 := by
    intro w hw
    simp only [f, hs w hw, mul_zero]
  have hfc : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        f (gnomonicChart x) = 0 := by
    intro x hx
    simp only [f, hchart x hx, mul_zero]
  change (∫ w, f w ∂sphereMeasure (m+3)) = _
  rw [quadratic_sphere_integral hpublished m f hf hfs hfc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_ball :
    MeasurableSet (Metric.ball (0 : Space (m+2)) 1))] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  have hp : inner ℝ (gnomonicChart (quadraticToGnomonic u) : Space (m+3))
      (coordinateJoin (0 : Space (m+2)) 1) = 1-‖u‖^2/2 := by
    rw [gnomonicChart_quadraticToGnomonic hu', quadraticSpherePoint_phase]
  have he : Complex.I*(Λ : ℂ)*((1-‖u‖^2/2 : ℝ) : ℂ) =
      Complex.I*(Λ : ℂ) + -(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ) := by
    push_cast
    ring
  simp only [f, hp, he, Complex.exp_add, Complex.real_smul, Complex.ofReal_pow]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_QuadraticStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the quadratic expansion to the actual sphere integral

The amplitude is the explicitly computed surface density times the spherical
amplitude, extended by zero from the fixed unit chart. Smoothness and its
quantitative derivative bounds are retained as local obligations. The only
published inputs are the gnomonic measure formula and the fixed Euclidean
quadratic stationary-phase theorem.
-/

namespace Falconer
open Set MeasureTheory Metric
open scoped BigOperators ContDiff

theorem quadraticAmplitude_tsupport (m : ℕ) (b : Sphere (m+3) → ℂ) :
    tsupport (quadraticAmplitude m b) ⊆ Metric.closedBall (0 : Space (m+2)) 1 := by
  apply closure_minimal _ isClosed_closedBall
  exact Set.support_indicator_subset.trans Metric.ball_subset_closedBall

/-- A mask that vanishes in the outer half of the fixed chart removes the
boundary issue in extending its chart amplitude by zero. -/
theorem quadraticAmplitude_contDiff (m : ℕ) (b : Sphere (m+3) → ℂ)
    (hb : ContDiffOn ℝ ∞
      (fun u : Space (m+2) => b (gnomonicChart (quadraticToGnomonic u)))
      (Metric.ball (0 : Space (m+2)) 1))
    (hmask : ∀ u : Space (m+2), (1:ℝ)/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (gnomonicChart (quadraticToGnomonic u)) = 0) :
    ContDiff ℝ ∞ (quadraticAmplitude m b) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : ‖u‖ < 1
  · have hum : u ∈ Metric.ball (0 : Space (m+2)) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    have hsq : ‖u‖^2 < 1 := by
      simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
    have hd : ContDiffAt ℝ ∞
        (fun v : Space (m+2) => ((Real.sqrt (1-‖v‖^2/4))^m : ℂ)) u := by
      apply ContDiffAt.pow
      exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
        ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
          (by linarith : 1-‖u‖^2/4 ≠ 0))
    apply (hd.mul ((hb u hum).contDiffAt (isOpen_ball.mem_nhds hum))).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hum] with v hv
    simp only [quadraticAmplitude, indicator_of_mem hv]
  · have hlarge : (1:ℝ)/2 < ‖u‖ := by linarith
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlarge] with v hv
    by_cases hvin : v ∈ Metric.ball (0 : Space (m+2)) 1
    · have hvnorm : ‖v‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hvin
      simp only [quadraticAmplitude, indicator_of_mem hvin,
        hmask v (le_of_lt hv) hvnorm, mul_zero]
    · simp only [quadraticAmplitude, indicator_of_notMem hvin]

theorem quadraticSphereOscillation_eq (hgnomonic : PublishedGnomonicSurface)
    (m : ℕ) (Λ : ℝ) (b : Sphere (m+3) → ℂ) (hb : Measurable b)
    (hs : ∀ w, w ∉ northHemisphere (m+2) → b w = 0)
    (hchart : ∀ x : Space (m+2),
      x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
        b (gnomonicChart x) = 0) :
    quadraticSphereOscillation m Λ b = Complex.exp (Complex.I*(Λ : ℂ)) *
      ∫ u : Space (m+2), Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
        quadraticAmplitude m b u := by
  rw [quadraticSphereOscillation,
    quadratic_sphere_oscillatory_integral hgnomonic m Λ b hb hs hchart]
  congr 1
  have heq : (fun u : Space (m+2) =>
      Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) * quadraticAmplitude m b u) =
      (Metric.ball (0 : Space (m+2)) 1).indicator (fun u =>
        Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖u‖^2 : ℝ)) *
          ((Real.sqrt (1-‖u‖^2/4))^m : ℂ) *
            b (gnomonicChart (quadraticToGnomonic u))) := by
    funext u
    by_cases hu : u ∈ Metric.ball (0 : Space (m+2)) 1
    · simp [quadraticAmplitude, hu, mul_assoc]
    · simp [quadraticAmplitude, hu]
  rw [heq, integral_indicator measurableSet_ball]

/-- The published Euclidean estimate bounds the spherical
oscillation. No spherical coefficient formula is presupposed: the jets on
the right are the actual iterated Euclidean Laplacians of the chart amplitude. -/
theorem quadraticSphereOscillation_remainder
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Sphere (m+3) → ℂ), Measurable b →
      (∀ w, w ∉ northHemisphere (m+2) → b w = 0) →
      (∀ x : Space (m+2),
        x ∉ quadraticToGnomonic '' Metric.ball (0 : Space (m+2)) 1 →
          b (gnomonicChart x) = 0) →
      ContDiff ℝ ∞ (quadraticAmplitude m b) →
      ∀ B : ℝ, 0 ≤ B →
        (∀ k ≤ 2*J+(m+2)+1, ∀ x,
          ‖iteratedFDeriv ℝ k (quadraticAmplitude m b) x‖ ≤ B) →
        ∀ Λ : ℝ, 1 ≤ Λ →
          ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) *
              Complex.exp (-(Complex.I*(Λ : ℂ))) * quadraticSphereOscillation m Λ b -
            ∑ j ∈ Finset.range J,
              ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
                quadraticJetCoefficient j (quadraticAmplitude m b)‖ ≤
            C * Λ ^ (-(J : ℝ)) * B := by
  obtain ⟨C, hC, hrem⟩ := hquadratic (m+2) J (by omega) hJ
  refine ⟨C, hC, ?_⟩
  intro b hb hs hchart ha B hB hder Λ hΛ
  have he := quadraticSphereOscillation_eq hgnomonic m Λ b hb hs hchart
  rw [he]
  have hcancel : Complex.exp (-(Complex.I*(Λ : ℂ))) *
      Complex.exp (Complex.I*(Λ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have halg (s z : ℂ) : s * Complex.exp (-(Complex.I*(Λ : ℂ))) *
      (Complex.exp (Complex.I*(Λ : ℂ)) * z) = s*z := by
    rw [mul_assoc, ← mul_assoc (Complex.exp _), hcancel, one_mul]
  rw [halg]
  exact hrem (quadraticAmplitude m b) ha (quadraticAmplitude_tsupport m b) B hB hder Λ hΛ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_StationaryTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

theorem stationaryPoleRotation_pole {n : ℕ} (e : Sphere (n+1)) :
    stationaryPoleRotation e (gnomonicChart (0 : Space n)) = (e : Space (n+1)) := by
  have h := Submodule.reflection_sub
    (v := (gnomonicChart (0 : Space n) : Space (n+1))) (w := -(e : Space (n+1)))
    (by rw [norm_neg, sphere_norm, sphere_norm])
  rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
  exact neg_injective h

theorem stationaryPoleRotation_apply {n : ℕ} (e : Sphere (n+1)) (x : Space (n+1)) :
    stationaryPoleRotation e x =
      poleRotationFormula (gnomonicChart (0 : Space n)) e x := by
  rw [stationaryPoleRotation, Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

theorem gnomonicChart_zero_pole (n : ℕ) :
    (gnomonicChart (0 : Space n) : Space (n+1)) = coordinateJoin (0 : Space n) 1 := by
  have hn : ‖northLift (0 : Space n)‖ = 1 := by
    have h : ‖northLift (0 : Space n)‖^2 = 1 := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
        northLift_norm_sq (0 : Space n)
    nlinarith [norm_nonneg (northLift (0 : Space n))]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [gnomonicChart_zero, hn]
    simp [coordinateJoin_eq]
  · simp [gnomonicChart_succ, coordinateJoin_eq]

theorem sphereOscillation_rotate (m : ℕ) (Λ : ℝ) (e : Sphere (m+3))
    (b : Sphere (m+3) → ℂ) :
    sphereOscillation Λ e b = quadraticSphereOscillation m Λ
      (fun w => b (sphereMap (stationaryPoleRotation e) w)) := by
  let T := stationaryPoleRotation e
  rw [sphereOscillation, ← sphere_integral_rotation T]
  unfold quadraticSphereOscillation
  apply integral_congr_ae
  filter_upwards with w
  have hp : (e : Space (m+3)) = T (gnomonicChart (0 : Space (m+2))) :=
    (stationaryPoleRotation_pole e).symm
  have hi : inner ℝ (sphereMap T w : Space (m+3)) (e : Space (m+3)) =
      inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) := by
    change inner ℝ (T (w : Space (m+3))) (e : Space (m+3)) = _
    rw [hp, T.inner_map_map, gnomonicChart_zero_pole]
  rw [hi]

theorem sphereOscillation_neg {d : ℕ} (Λ : ℝ) (e : Sphere d) (b : Sphere d → ℂ) :
    sphereOscillation (-Λ) e b =
      star (sphereOscillation Λ e (fun w => star (b w))) := by
  rw [sphereOscillation, sphereOscillation]
  simp only [← starRingEnd_apply]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with w
  simp only [map_mul, Complex.conj_conj, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 2
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartJetOperators
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual stationary operators on a smooth pole patch

The operators are the quadratic Laplacian jets of the explicit chart
amplitude. They depend smoothly on the evaluation direction away from the
opposite pole. Their equality with the coefficients in the local
sphere expansion follows by locality, including the fixed chart cutoff.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem actualStationaryCoefficient_eq (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m j B e =
      quadraticJetCoefficient j (quadraticAmplitude m
        (fun w => B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticJetCoefficient_congr
  filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : Space (m+2)) ∈ ball 0 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hu
  simp only [unmaskedStationaryAmplitude, quadraticAmplitude, indicator_of_mem hu]
  congr 1
  congr 1
  rw [← stationaryPoleRotation_apply, ← gnomonicChart_quadraticToGnomonic hu']
  rfl

@[simp] theorem actualStationaryCoefficient_zero (m : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m 0 B e = sphereStationaryConstant (m+2) * B e := by
  rw [actualStationaryCoefficient_eq, quadraticJetCoefficient_amplitude_zero]
  change _ * B (stationaryPoleRotation e (gnomonicChart (0 : Space (m+2)))) = _
  rw [stationaryPoleRotation_pole]

/-- The actual coefficient depends only on the original amplitude near its
evaluation direction; every cutoff that is constant there is invisible. -/
theorem actualStationaryCoefficient_local (m j : ℕ) {B G : Space (m+3) → ℂ}
    (e : Sphere (m+3)) (hBG : B =ᶠ[𝓝 (e : Space (m+3))] G) :
    actualStationaryCoefficient m j B e = actualStationaryCoefficient m j G e := by
  apply quadraticJetCoefficient_congr
  let γ : Space (m+2) → Space (m+3) :=
    fun u => stationaryPoleRotation e (quadraticSpherePoint u)
  have hq0 : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  have hγ0 : γ 0 = (e : Space (m+3)) := by
    change stationaryPoleRotation e (quadraticSpherePoint 0) = _
    rw [hq0, stationaryPoleRotation_pole]
  have hγ : Filter.Tendsto γ (𝓝 (0 : Space (m+2))) (𝓝 (e : Space (m+3))) := by
    rw [← hγ0]
    exact (stationaryPoleRotation e).continuous.continuousAt.comp
      (quadraticSpherePoint_contDiffAt (u := (0 : Space (m+2))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  filter_upwards [hBG.comp_tendsto hγ] with u hu
  simp only [unmaskedStationaryAmplitude, ← stationaryPoleRotation_apply]
  rw [show B (stationaryPoleRotation e (quadraticSpherePoint u)) =
    G (stationaryPoleRotation e (quadraticSpherePoint u)) from hu]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleCutoffs
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem offPoleCutoff_contDiff {d : ℕ} (e : Sphere d) :
    ContDiff ℝ ∞ (offPoleCutoff e) :=
  (contDiff_const.sub (poleCutoff_contDiff e)).sub (poleCutoff_contDiff _)

theorem poleCutoff_one {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : ‖x-(e : Space d)‖ ≤ 1/8) : poleCutoff e x = 1 := by
  apply (capBump (1/4) (by norm_num) e).one_of_mem_closedBall
  change dist x (e : Space d) ≤ (1/4 : ℝ)/2
  rw [dist_eq_norm]
  convert hx using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

theorem poleCutoff_zero {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : 1/4 ≤ ‖x-(e : Space d)‖) : poleCutoff e x = 0 := by
  apply (capBump (1/4) (by norm_num) e).zero_of_le_dist
  simpa only [dist_eq_norm,capBump] using hx

theorem poleCutoff_support {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : poleCutoff e x ≠ 0) : ‖x-(e : Space d)‖ < 1/4 := by
  by_contra h
  exact hx (poleCutoff_zero e x (le_of_not_gt h))

private theorem pole_distance_sum {d : ℕ} (e w : Sphere d) :
    2 ≤ ‖(w : Space d)-(e : Space d)‖ +
      ‖(w : Space d)-(oppositePole e : Space d)‖ := by
  have htwo : ‖(e : Space d)-(oppositePole e : Space d)‖ = 2 := by
    rw [oppositePole_coe,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm]
    norm_num
  have h := norm_sub_le_norm_sub_add_norm_sub (e : Space d) (w : Space d)
    (oppositePole e : Space d)
  rwa [htwo,norm_sub_rev (e : Space d) (w : Space d)] at h

theorem offPoleCutoff_zero_near {d : ℕ} (e w : Sphere d)
    (hw : ‖(w : Space d)-(e : Space d)‖ ≤ 1/8) : offPoleCutoff e w = 0 := by
  have hs := pole_distance_sum e w
  have ho : poleCutoff (oppositePole e) w = 0 := poleCutoff_zero _ _ (by linarith)
  simp only [offPoleCutoff,poleCutoff_one e w hw,ho,sub_self]

theorem offPoleCutoff_opposite {d : ℕ} (e : Sphere d) :
    offPoleCutoff (oppositePole e) = offPoleCutoff e := by
  funext x
  simp only [offPoleCutoff,oppositePole_opposite]
  ring

theorem offPoleCutoff_gap {d : ℕ} (e w : Sphere d) (hw : offPoleCutoff e w ≠ 0) :
    (1 : ℝ)/16 ≤ ‖perpendicularPart (w : Space d) (e : Space d)‖ := by
  have hp : 1/8 < ‖(w : Space d)-(e : Space d)‖ := by
    by_contra h
    exact hw (offPoleCutoff_zero_near e w (le_of_not_gt h))
  have hm : 1/8 < ‖(w : Space d)-(oppositePole e : Space d)‖ := by
    by_contra h
    have hz := offPoleCutoff_zero_near (oppositePole e) w (le_of_not_gt h)
    rw [offPoleCutoff_opposite] at hz
    exact hw hz
  have hps := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/8) (norm_nonneg _)).mpr hp
  have hms := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/8) (norm_nonneg _)).mpr hm
  simp only [oppositePole_coe] at hms
  have hplus := norm_sub_sq_real (w : Space d) (e : Space d)
  have hminus := norm_sub_sq_real (w : Space d) (oppositePole e : Space d)
  rw [sphere_norm,sphere_norm] at hplus hminus
  rw [oppositePole_coe,inner_neg_right] at hminus
  let t := inner ℝ (w : Space d) (e : Space d)
  have ht₁ : 0 ≤ 127/128-t := by dsimp [t]; nlinarith
  have ht₂ : 0 ≤ 127/128+t := by dsimp [t]; nlinarith
  have ht := mul_nonneg ht₁ ht₂
  have hsq : ‖perpendicularPart (w : Space d) (e : Space d)‖^2 = 1-t^2 := by
    have hh := norm_sub_sq_real (e : Space d) (t • (w : Space d))
    rw [norm_smul,sphere_norm,sphere_norm,Real.norm_eq_abs,mul_one,
      sq_abs,real_inner_smul_right] at hh
    have hi : inner ℝ (e : Space d) (w : Space d) = t := by
      dsimp [t]
      exact real_inner_comm _ _
    rw [hi] at hh
    change ‖perpendicularPart (w : Space d) (e : Space d)‖^2 = _
    dsimp only [perpendicularPart]
    dsimp only [t] at hh ⊢
    nlinarith
  nlinarith [norm_nonneg (perpendicularPart (w : Space d) (e : Space d))]

/-- In quadratic coordinates, Euclidean distance from the pole is exactly
the coordinate radius. This gives the needed interior cutoff support. -/
theorem quadraticSpherePoint_dist_pole {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u-coordinateJoin (0 : Space n) 1‖ = ‖u‖ := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    have h := coordinateJoin_norm_sq (0 : Space n) 1
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),one_pow] at h
    nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]
  have h := norm_sub_sq_real (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1)
  rw [quadraticSpherePoint_norm hu,hp,quadraticSpherePoint_phase] at h
  nlinarith [norm_nonneg (quadraticSpherePoint u-coordinateJoin (0 : Space n) 1),norm_nonneg u]

/-- Only a small fixed part of the coordinate image is needed for the
application. Radial continuity proves its inclusion without imposing a
global inverse chart. -/
theorem quadraticToGnomonic_image_smallBall {n : ℕ} (x : Space n)
    (hx : ‖x‖ ≤ 1/2) :
    x ∈ quadraticToGnomonic '' ball (0 : Space n) 1 := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0,by simp,by simp [quadraticToGnomonic]⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let g : ℝ → ℝ := fun r => Real.sqrt (1-r^2/4)/(1-r^2/2)*r
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul _ continuousOn_id
    apply ContinuousOn.div
    · exact (continuousOn_const.sub ((continuousOn_id.pow 2).div_const 4)).sqrt
    · exact continuousOn_const.sub ((continuousOn_id.pow 2).div_const 2)
    · intro r hr
      have hr2 : r^2 ≤ 1 := by
        simpa using (sq_le_sq₀ hr.1 (by norm_num : (0 : ℝ) ≤ 1)).mpr hr.2
      linarith
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : 1 ≤ g 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/4)
    have hn := Real.sqrt_nonneg (3/4 : ℝ)
    have he : g 1 = 2*Real.sqrt (3/4 : ℝ) := by dsimp [g]; norm_num; ring
    rw [he]
    nlinarith
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hg
    (show ‖x‖ ∈ Icc (g 0) (g 1) from ⟨by rw [hg0]; exact hxn.le,hx.trans (by linarith)⟩)
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hr.2
    intro hrEq
    have he1 : g 1 = ‖x‖ := by simpa only [hrEq] using he
    linarith
  let u : Space n := (r/‖x‖) • x
  have hu : ‖u‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr.1 hxn.le),div_mul_cancel₀ _ hxn.ne']
  refine ⟨u,by simpa only [mem_ball,dist_zero_right,hu] using hr1,?_⟩
  change (Real.sqrt (1-‖u‖^2/4)/(1-‖u‖^2/2)) • u = x
  rw [hu]
  change (Real.sqrt (1-r^2/4)/(1-r^2/2)) • ((r/‖x‖) • x) = x
  rw [smul_smul]
  have hc : (Real.sqrt (1-r^2/4)/(1-r^2/2))*(r/‖x‖) = 1 := by
    apply (mul_right_cancel₀ hxn.ne')
    calc
      _ = (Real.sqrt (1-r^2/4)/(1-r^2/2))*r := by field_simp
      _ = ‖x‖ := he
      _ = 1*‖x‖ := (one_mul _).symm
  rw [hc,one_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PoleStationarySupport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual support conditions for the pole expansion

Geometric support in a radius-1/4 cap implies all support conditions in
the quadratic stationary theorem. The ambient pole bump is invisible to
the actual coefficient jets at its center.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem gnomonic_small_cap_coordinates {n : ℕ} (x : Space n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/2)
    (hcap : ‖(gnomonicChart x : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ δ) :
    ‖x‖ ≤ 2*δ := by
  let p := coordinateJoin (0 : Space n) 1
  let h := coordinateJoin x 0
  have hp : ‖p‖ = 1 := by
    change ‖coordinateJoin (0 : Space n) 1‖ = 1
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have horth : inner ℝ p h = 0 := by simp [p,h,coordinateJoin_inner]
  have hh : ‖h‖ = ‖x‖ := by
    change ‖coordinateJoin x 0‖ = ‖x‖
    have he := coordinateJoin_norm_sq x 0
    simp only [zero_pow (by decide : 2 ≠ 0),zero_add] at he
    nlinarith [norm_nonneg (coordinateJoin x 0),norm_nonneg x]
  have hsplit : northLift x = p+h := by
    apply PiLp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [p,h,northLift,coordinateJoin_eq]
  have hc : ‖‖p+h‖⁻¹ • (p+h)-p‖ ≤ δ := by
    simpa only [gnomonicChart,hsplit] using hcap
  rw [← hh]
  exact small_cap_chart_displacement hp horth hδ hδsmall hc

private theorem fixed_cap_mem_north {n : ℕ} (w : Sphere (n+1))
    (hw : ‖(w : Space (n+1))-coordinateJoin (0 : Space n) 1‖ ≤ 1/4) :
    w ∈ northHemisphere n := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    rw [← gnomonicChart_zero_pole]
    exact sphere_norm _
  have hi : inner ℝ (w : Space (n+1)) (coordinateJoin (0 : Space n) 1) =
      (w : Space (n+1)) 0 := by
    rw [PiLp.inner_apply,Fin.sum_univ_succ]
    simp [coordinateJoin_eq]
  have he := norm_sub_sq_real (w : Space (n+1)) (coordinateJoin (0 : Space n) 1)
  rw [sphere_norm,hp,hi] at he
  change 0 < (w : Space (n+1)) 0
  nlinarith [norm_nonneg ((w : Space (n+1))-coordinateJoin (0 : Space n) 1)]

theorem rotated_cap_quadratic_support (m : ℕ) (e : Sphere (m+3))
    (b : Sphere (m+3) → ℂ)
    (hcap : ∀ w, b w ≠ 0 → ‖(w : Space (m+3))-(e : Space (m+3))‖ ≤ 1/4) :
    let T := stationaryPoleRotation e
    (∀ w, w ∉ northHemisphere (m+2) → b (sphereMap T w) = 0) ∧
    (∀ x : Space (m+2), x ∉ quadraticToGnomonic '' ball (0 : Space (m+2)) 1 →
      b (sphereMap T (gnomonicChart x)) = 0) ∧
    (∀ u : Space (m+2), 1/2 ≤ ‖u‖ → ‖u‖ < 1 →
      b (sphereMap T (gnomonicChart (quadraticToGnomonic u))) = 0) := by
  let T := stationaryPoleRotation e
  have htransport (w : Sphere (m+3)) (hw : b (sphereMap T w) ≠ 0) :
      ‖(w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1‖ ≤ 1/4 := by
    have he : T (coordinateJoin (0 : Space (m+2)) 1) = (e : Space (m+3)) := by
      rw [← gnomonicChart_zero_pole]
      exact stationaryPoleRotation_pole e
    calc
      _ = ‖T ((w : Space (m+3))-coordinateJoin (0 : Space (m+2)) 1)‖ := (T.norm_map _).symm
      _ = ‖(sphereMap T w : Space (m+3))-(e : Space (m+3))‖ := by rw [T.map_sub,he]; rfl
      _ ≤ _ := hcap _ hw
  refine ⟨?_,?_,?_⟩
  · intro w hw
    by_contra hb
    exact hw (fixed_cap_mem_north w (htransport w hb))
  · intro x hx
    by_contra hb
    have hc := gnomonic_small_cap_coordinates x (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1/2) (htransport _ hb)
    exact hx (quadraticToGnomonic_image_smallBall x (by linarith))
  · intro u hu hu1
    by_contra hb
    have hc := htransport _ hb
    rw [gnomonicChart_quadraticToGnomonic hu1,
      quadraticSpherePoint_dist_pole (hu1.le.trans (by norm_num))] at hc
    linarith

theorem poleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (poleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).mul hB

theorem poleLocalizedAmbient_cap {d : ℕ} (e : Sphere d) (B : Space d → ℂ)
    (w : Sphere d) (hw : poleLocalizedAmbient e B w ≠ 0) :
    ‖(w : Space d)-(e : Space d)‖ ≤ 1/4 := by
  apply (poleCutoff_support e w _).le
  intro hz
  exact hw (by simp only [poleLocalizedAmbient,hz,Complex.ofReal_zero,zero_mul])

theorem poleLocalizedAmbient_coefficient (m j : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    actualStationaryCoefficient m j (poleLocalizedAmbient e B) e =
      actualStationaryCoefficient m j B e := by
  apply actualStationaryCoefficient_local m j e
  have he := (capBump (1/4) (by norm_num) e).eventuallyEq_one
  filter_upwards [he] with x hx
  change capBump (1/4) (by norm_num) e x = (1 : ℝ) at hx
  simp only [poleLocalizedAmbient,poleCutoff,hx,Complex.ofReal_one,one_mul]

theorem poleCutoff_opposite_neg {d : ℕ} (e : Sphere d) (x : Space d) :
    poleCutoff (oppositePole e) (-x) = poleCutoff e x := by
  simp only [poleCutoff,ContDiffBump.apply,capBump,oppositePole_coe]
  have he : ((1/4 : ℝ)/2)⁻¹ • (-x-(-(e : Space d))) =
      -(((1/4 : ℝ)/2)⁻¹ • (x-(e : Space d))) := by module
  rw [he,ContDiffBumpBase.symmetric]

/-- The incoming pole uses the same smooth direction patch as the outgoing
pole, applied to the conjugated antipodal amplitude. -/
theorem poleLocalized_opposite_oscillation {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (B : Space d → ℂ) :
    sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w) =
      star (sphereOscillation Λ e
        (fun w => poleLocalizedAmbient e (fun x => star (B (-x))) w)) := by
  have heq : sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w) =
      sphereOscillation (-Λ) e (fun w => poleLocalizedAmbient e (fun x => B (-x)) w) := by
    rw [sphereOscillation,← sphere_integral_rotation (LinearIsometryEquiv.neg ℝ)]
    unfold sphereOscillation
    apply integral_congr_ae
    filter_upwards with w
    change Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (-(w : Space d)) (e : Space d) : ℂ)) *
      ((poleCutoff (oppositePole e) (-(w : Space d)) : ℂ)*B (-(w : Space d))) = _
    rw [poleCutoff_opposite_neg,inner_neg_left]
    have hp : Complex.I*(Λ : ℂ)*((-inner ℝ (w : Space d) (e : Space d) : ℝ) : ℂ) =
        Complex.I*((-Λ : ℝ) : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ) := by
      push_cast
      ring
    rw [hp]
    rfl
  rw [heq,sphereOscillation_neg]
  congr 1
  congr 1
  funext w
  simp [poleLocalizedAmbient]

theorem poleLocalized_quadratic_contDiff (m : ℕ) (e : Sphere (m+3))
    {B : Space (m+3) → ℂ} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticAmplitude_contDiff
  · let T := stationaryPoleRotation e
    have h : ContDiffOn ℝ ∞
        (fun u => poleLocalizedAmbient e B (T (quadraticSpherePoint u)))
        (ball (0 : Space (m+2)) 1) := by
      intro u hu
      have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
      exact ((poleLocalizedAmbient_contDiff e hB).comp
        T.toContinuousLinearMap.contDiff).contDiffAt.comp u
          (quadraticSpherePoint_contDiffAt (hu1.trans (by norm_num))) |>.contDiffWithinAt
    apply h.congr
    intro u hu
    have hu1 : ‖u‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hu
    change poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic u))) = _
    rw [gnomonicChart_quadraticToGnomonic hu1]
  · exact (rotated_cap_quadratic_support m e (fun w => poleLocalizedAmbient e B w)
      (poleLocalizedAmbient_cap e B)).2.2

/-- The local expansion has the original-amplitude coefficients.
All support and smoothness requirements are discharged by the fixed bump.
The remaining derivative bound is the explicit Euclidean jet budget. -/
theorem poleLocalized_stationary_remainder
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ E : ℝ, 0 ≤ E →
      (∀ k ≤ 2*J+(m+2)+1, ∀ u,
        ‖iteratedFDeriv ℝ k (quadraticAmplitude m
          (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) u‖ ≤ E) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(Complex.I*(Λ : ℂ))) *
          sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w) -
        ∑ j ∈ Finset.range J, ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
          actualStationaryCoefficient m j B e‖ ≤ C*Λ^(-(J : ℝ))*E := by
  obtain ⟨C,hC,hrem⟩ := quadraticSphereOscillation_remainder hgnomonic hquadratic m J hJ
  refine ⟨C,hC,?_⟩
  intro e B hB E hE hder Λ hΛ
  let b : Sphere (m+3) → ℂ := fun w => poleLocalizedAmbient e B w
  have hb : Measurable b :=
    (poleLocalizedAmbient_contDiff e hB).continuous.measurable.comp
      continuous_subtype_val.measurable
  obtain ⟨hs,hchart,_⟩ := rotated_cap_quadratic_support m e b (poleLocalizedAmbient_cap e B)
  have hr := hrem (fun w => b (sphereMap (stationaryPoleRotation e) w))
    (hb.comp (continuous_sphereMap _).measurable) hs hchart
    (poleLocalized_quadratic_contDiff m e hB) E hE hder Λ hΛ
  have hj (j : ℕ) : quadraticJetCoefficient j (quadraticAmplitude m
      (fun w => b (sphereMap (stationaryPoleRotation e) w))) =
      actualStationaryCoefficient m j B e := by
    rw [← actualStationaryCoefficient_eq m j (poleLocalizedAmbient e B) e,
      poleLocalizedAmbient_coefficient]
  simpa only [sphereOscillation_rotate,hj] using hr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FixedChartBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform finite derivative bounds for fixed quadratic geometry

Only compact sets inside the smooth chart are used. The chart need not
extend smoothly through its outer singularity.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_iteratedFDeriv_bound_at {f : E → F} {K : Set E}
    (hK : IsCompact K) (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hc (i : ℕ) : ContinuousOn (iteratedFDeriv ℝ i f) K := by
    intro x hx
    exact ((hf x hx).continuousAt_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousWithinAt
  choose A hA using fun i => hK.exists_bound_of_continuousOn (hc i)
  let C := ∑ i ∈ Finset.range (n+1), max 0 (A i)
  refine ⟨C,Finset.sum_nonneg (fun _ _ => le_max_left _ _),?_⟩
  intro i hi x hx
  apply (hA i x hx).trans
  apply (le_max_right 0 (A i)).trans
  exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem norm_iteratedFDeriv_mul_le_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (k-i) g x‖ := by
  obtain ⟨U,hU,hxU,hfU⟩ := hf.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨V,hV,hxV,hgV⟩ := hg.contDiffOn' (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (k : ℕ∞ω) ≤ ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hxW : x ∈ W := ⟨hxU,hxV⟩
  have hfU' : ContDiffOn ℝ k f U := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hfU
  have hgV' : ContDiffOn ℝ k g V := by
    simpa only [insert_eq_of_mem (mem_univ x),univ_inter] using hgV
  have hfW : ContDiffOn ℝ k f W := hfU'.mono inter_subset_left
  have hgW : ContDiffOn ℝ k g W := hgV'.mono inter_subset_right
  have hh := norm_iteratedFDerivWithin_mul_le hfW hgW hW.uniqueDiffOn hxW (le_refl (k : ℕ∞ω))
  have hre (j : ℕ) (a : E → ℂ) : iteratedFDerivWithin ℝ j a W x = iteratedFDeriv ℝ j a x :=
    iteratedFDerivWithin_of_isOpen j hW hxW
  simpa only [hre] using hh

theorem fixed_quadratic_geometry_bounds (n m k : ℕ) :
    ∃ Q C : ℝ, 0 ≤ Q ∧ 0 ≤ C ∧ ∀ j ≤ k, ∀ u : Space n, ‖u‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j quadraticSpherePoint u‖ ≤ Q ∧
      ‖iteratedFDeriv ℝ j (quadraticChartDensity m) u‖ ≤ C := by
  obtain ⟨Q,hQ,hQb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticSpherePoint_contDiffAt (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  obtain ⟨C,hC,hCb⟩ := compact_iteratedFDeriv_bound_at
    (isCompact_closedBall (0 : Space n) 1) (fun u hu =>
      quadraticChartDensity_contDiffAt m (by
        have hh : ‖u‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hu
        linarith)) k
  refine ⟨Q,C,hQ,hC,?_⟩
  intro j hj u hu
  have hum : u ∈ closedBall (0 : Space n) 1 := by
    simpa only [mem_closedBall,dist_zero_right] using hu
  exact ⟨hQb j hj u hum,hCb j hj u hum⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuadraticBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The derivative budget of the actual quadratic amplitude

The fixed pole cutoff and fixed quadratic geometry cost constants depending
only on the dimension and derivative order. The original symbol supplies
the entire scale power.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

theorem mixed_product_uniform_bound_at {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B) (k : ℕ)
    (hfb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgb : ∀ j ≤ k, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖ ≤ 2^k*A*B := by
  apply (norm_iteratedFDeriv_mul_le_at hf hg k).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb j hjk) (Nat.cast_nonneg _))
        (hgb (k-j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = _ := by
      have hs : (∑ j ∈ Finset.range (k+1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
        simpa only [one_pow,mul_one,one_mul,one_add_one_eq_two] using
          (add_pow (1 : ℝ) 1 k).symm
      rw [← Finset.sum_mul,← Finset.sum_mul,hs]

theorem poleLocalizedAmbient_uniform_budget (d K : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ j (poleLocalizedAmbient e B) w‖ ≤ A*C*D^K := by
  choose P hP hPb using fun j => capBump_ambient_derivatives d j
  let Q := ∑ j ∈ Finset.range (K+1), P j*4^j
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hP j) (pow_nonneg (by norm_num) j))
  have hPQ (j : ℕ) (hj : j ≤ K) : P j*4^j ≤ Q := by
    change P j*(4 : ℝ)^j ≤ ∑ i ∈ Finset.range (K+1), P i*4^i
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hP i) (pow_nonneg (by norm_num) i))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨2^K*Q,by positivity,?_⟩
  intro e B hB C D hC hD hb j hj w
  have hCD : 0 ≤ C*D^K := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) K)
  have hcut (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun x => (poleCutoff e x : ℂ)) w‖ ≤ Q := by
    have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      ((poleCutoff_contDiff e).contDiffAt (x := (w : Space d)))
      (show (i : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ i (Complex.ofRealLI ∘ poleCutoff e) w‖ ≤ Q
    rw [hn]
    apply (hPb i (1/4) (by norm_num) e w).trans
    simpa only [one_div,inv_inv] using hPQ i (hi.trans hj)
  have hBb (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i B w‖ ≤ C*D^K :=
    (hb i (hi.trans hj) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD (hi.trans hj)) hC)
  have hh := mixed_product_uniform_bound_at
    ((Complex.ofRealCLM.contDiff.comp (poleCutoff_contDiff e)).contDiffAt)
    hB.contDiffAt hQ hCD j hcut hBb
  apply hh.trans
  calc
    _ ≤ 2^K*Q*(C*D^K) := by gcongr; norm_num
    _ = _ := by ring

theorem quadraticAmplitude_tsupport_half (m : ℕ) (e : Sphere (m+3))
    (B : Space (m+3) → ℂ) :
    tsupport (quadraticAmplitude m
      (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) ⊆
      closedBall (0 : Space (m+2)) (1/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  by_contra hout
  have hlarge : 1/2 < ‖u‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hout
  by_cases hunit : ‖u‖ < 1
  · have hz := (rotated_cap_quadratic_support m e
      (fun w => poleLocalizedAmbient e B w) (poleLocalizedAmbient_cap e B)).2.2 u hlarge.le hunit
    have hum : u ∈ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_mem hum,hz,mul_zero])
  · have hum : u ∉ ball (0 : Space (m+2)) 1 := by
      simpa only [mem_ball,dist_zero_right] using hunit
    exact hu (by simp only [quadraticAmplitude,indicator_of_notMem hum])

theorem quadratic_chart_composition_uniform_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (T : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1))
      (B : Space (n+1) → ℂ), ContDiff ℝ ∞ B → ∀ E : ℝ, 0 ≤ E →
      (∀ j ≤ K, ∀ w : Sphere (n+1), ‖iteratedFDeriv ℝ j B w‖ ≤ E) →
      ∀ j ≤ K, ∀ u : Space n, ‖u‖ ≤ 1 →
        ‖iteratedFDeriv ℝ j (fun y => B (T (quadraticSpherePoint y))) u‖ ≤ H*E := by
  obtain ⟨Q,_C,hQ,_hC,hgeometry⟩ := fixed_quadratic_geometry_bounds n 0 K
  let a : ℕ → ℝ := fun j => mixedCompositionBudget (fun _ => Q) j
  have ha (j : ℕ) : 0 ≤ a j := mixedCompositionBudget_nonneg (fun _ => hQ) j
  let H := ∑ j ∈ Finset.range (K+1), a j
  have hH : 0 ≤ H := Finset.sum_nonneg (fun j _ => ha j)
  have haH (j : ℕ) (hj : j ≤ K) : a j ≤ H :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨H,hH,?_⟩
  intro T B hB E hE hb j hj u hu
  have hu2 : ‖u‖ < 2 := by linarith
  have hQu := quadraticSpherePoint_contDiffAt hu2
  let f : Space n → Space (n+1) := fun y => T (quadraticSpherePoint y)
  have hf : ContDiffAt ℝ ∞ f u := T.toContinuousLinearMap.contDiff.contDiffAt.comp u hQu
  let w : Sphere (n+1) := ⟨f u,by
    rw [mem_sphere,dist_zero_right]
    exact (T.norm_map _).trans (quadraticSpherePoint_norm hu2.le)⟩
  have hinner (i : ℕ) (_hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i f u‖ ≤ Q*(1 : ℝ)^i := by
    have he := T.toLinearIsometry.norm_iteratedFDeriv_comp_left hQu
      (show (i : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change ‖iteratedFDeriv ℝ i (T.toLinearIsometry ∘ quadraticSpherePoint) u‖ ≤ _
    rw [he,one_pow,mul_one]
    exact (hgeometry i (hij.trans hj) u hu).1
  have hh := mixed_composition_derivative_bound hf hB.contDiffAt hE j
    (fun i hi => hb i (hi.trans hj) w) hinner
  change ‖iteratedFDeriv ℝ j (B ∘ f) u‖ ≤ H*E
  apply hh.trans
  simp only [one_pow,mul_one]
  exact mul_le_mul_of_nonneg_right (haH j hj) hE

/-- Uniform global bounds for the actual zero-extended quadratic amplitude.
The scale appears with exactly the highest requested derivative order K. -/
theorem pole_quadratic_amplitude_budget (m K : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ j ≤ K, ∀ u,
        ‖iteratedFDeriv ℝ j (quadraticAmplitude m
          (fun w => poleLocalizedAmbient e B (sphereMap (stationaryPoleRotation e) w))) u‖ ≤
          L*C*D^K := by
  obtain ⟨A,hA,hAb⟩ := poleLocalizedAmbient_uniform_budget (m+3) K
  obtain ⟨H,hH,hHb⟩ := quadratic_chart_composition_uniform_budget (m+2) K
  obtain ⟨_Q,R,_hQ,hR,hgeometry⟩ := fixed_quadratic_geometry_bounds (m+2) m K
  refine ⟨2^K*R*H*A,by positivity,?_⟩
  intro e B hB C D hC hD hder j hj u
  let b := fun w : Sphere (m+3) => poleLocalizedAmbient e B w
  let amp := quadraticAmplitude m (fun w => b (sphereMap (stationaryPoleRotation e) w))
  let T := stationaryPoleRotation e
  let G : Space (m+2) → ℂ := fun y => poleLocalizedAmbient e B (T (quadraticSpherePoint y))
  let F : Space (m+2) → ℂ := fun y => quadraticChartDensity m y * G y
  have hE : 0 ≤ A*C*D^K := by positivity
  have hGb := hHb T (poleLocalizedAmbient e B) (poleLocalizedAmbient_contDiff e hB)
    (A*C*D^K) hE (hAb e B hB C D hC hD hder)
  by_cases hu : ‖u‖ < 1
  · have hu2 : ‖u‖ < 2 := hu.trans (by norm_num)
    have hG : ContDiffAt ℝ ∞ G u :=
      ((poleLocalizedAmbient_contDiff e hB).comp T.toContinuousLinearMap.contDiff).contDiffAt.comp u
        (quadraticSpherePoint_contDiffAt hu2)
    have hbound := mixed_product_uniform_bound_at (quadraticChartDensity_contDiffAt m hu2)
      hG hR (mul_nonneg hH hE) j
      (fun i hi => (hgeometry i (hi.trans hj) u hu.le).2)
      (fun i hi => hGb i (hi.trans hj) u hu.le)
    have he : amp =ᶠ[𝓝 u] F := by
      have hum : u ∈ ball (0 : Space (m+2)) 1 := by simpa only [mem_ball,dist_zero_right] using hu
      filter_upwards [isOpen_ball.mem_nhds hum] with y hy
      have hy1 : ‖y‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hy
      dsimp only [amp,quadraticAmplitude,F,G,b,quadraticChartDensity]
      rw [indicator_of_mem hy]
      change _ * poleLocalizedAmbient e B (T (gnomonicChart (quadraticToGnomonic y))) = _
      rw [gnomonicChart_quadraticToGnomonic hy1]
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
    apply hbound.trans
    calc
      _ ≤ 2^K*R*(H*(A*C*D^K)) := by gcongr; norm_num
      _ = _ := by ring
  · have hn : u ∉ tsupport amp := by
      intro hm
      have hh := quadraticAmplitude_tsupport_half m e B hm
      have huHalf : ‖u‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hh
      linarith
    have he := (notMem_tsupport_iff_eventuallyEq.mp hn).iteratedFDeriv ℝ j
    have hz : iteratedFDeriv ℝ j amp u = 0 := by simpa using he.self_of_nhds
    change ‖iteratedFDeriv ℝ j amp u‖ ≤ _
    rw [hz,norm_zero]
    positivity

/-- Quantitative outgoing stationary phase for the actual ambient symbol.
The Euclidean derivative budget is derived, not assumed. -/
theorem pole_stationary_remainder_of_ambient_bounds
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ ^ (((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) * Complex.exp (-(Complex.I*(Λ : ℂ))) *
          sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w) -
        ∑ j ∈ Finset.range J, ((Λ ^ (-(j : ℝ)) : ℝ) : ℂ) *
          actualStationaryCoefficient m j B e‖ ≤
        A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hrem⟩ := poleLocalized_stationary_remainder hgnomonic hquadratic m J hJ
  obtain ⟨L,hL,hbudget⟩ := pole_quadratic_amplitude_budget m (2*J+(m+2)+1)
  refine ⟨A*L,by positivity,?_⟩
  intro e B hB C D hC hD hder Λ hΛ
  have hh := hrem e B hB (L*C*D^(2*J+(m+2)+1)) (by positivity)
    (hbudget e B hB C D hC hD hder) Λ hΛ
  exact hh.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_AmbientChartBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient symbol bounds imply the ordinary rotated chart bounds

Only derivatives of the original symbol evaluated at sphere points are
used. The one-coordinate curve has a fixed, rotation-independent budget.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

theorem rotatedChartCurve_derivative_scale (n K : ℕ) :
    ∃ q : ℝ, 1 ≤ q ∧ ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ∀ k, 1 ≤ k → k ≤ K →
        ‖iteratedFDeriv ℝ k (rotatedChartCurve e y) u‖ ≤ q^k := by
  obtain ⟨q,hq,hqb⟩ := tangent_line_derivative_scale (E := Space (n+2)) K
  refine ⟨q,hq,?_⟩
  intro e y hy u hu k hk hkK
  have he : rotatedChartCurve e y = e ∘
      normalizedLine (chartPole n+transverseLift y) (chartAxis n) := by
    funext t
    simp only [rotatedChartCurve,Function.comp_def,gnomonicChart_coordinateJoin]
  rw [he,e.norm_iteratedFDeriv_comp_left,norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hqb _ _ _ (chartPole_norm n) (chartAxis_norm n)
    (chartPole_inner_transverse y) (chartPole_inner_axis n) (transverseLift_inner_axis y)
    (by simpa only [transverseLift_norm] using hy) u hu k hk hkK

theorem ambient_symbol_rotated_chart_budget (n K : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ B : Space (n+2) → ℂ,
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ K, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ K,
        ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => B w) y) u‖ ≤ H*C*D^k := by
  obtain ⟨q,hq,hqb⟩ := rotatedChartCurve_derivative_scale n K
  let a : ℕ → ℝ := fun k => mixedCompositionBudget (fun _ => 1) k*q^k
  have ha (k : ℕ) : 0 ≤ a k := mul_nonneg
    (mixedCompositionBudget_nonneg (fun _ => zero_le_one) k)
    (pow_nonneg (zero_le_one.trans hq) k)
  let H := ∑ k ∈ Finset.range (K+1), a k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => ha k)
  refine ⟨H,hH,?_⟩
  intro B hB C D hC hD hb e y hy u hu k hk
  let w : Sphere (n+2) := ⟨rotatedChartCurve e y u,by
    rw [mem_sphere,dist_zero_right,rotatedChartCurve_norm]⟩
  have hCE : 0 ≤ C*D^k := mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) k)
  have hh := mixed_composition_derivative_bound (B := fun _ => 1) (D := q)
    (rotatedChartCurve_contDiff e y).contDiffAt hB.contDiffAt hCE k
    (fun j hj => (hb j (hj.trans hk) w).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hD hj) hC))
    (fun j hj hjk => by simpa only [one_mul] using hqb e y hy u hu j hj (hjk.trans hk))
  have he : rotatedChartAmplitude e (fun w => B w) y = B ∘ rotatedChartCurve e y := rfl
  rw [he,← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  apply hh.trans
  have haH : a k ≤ H := Finset.single_le_sum (fun i _ => ha i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  calc
    _ = a k*C*D^k := by dsimp [a]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right haH hC)
      (pow_nonneg (zero_le_one.trans hD) k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OffPoleAmbient
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The off-pole estimate with the original ambient derivative budget -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem offPoleLocalizedAmbient_contDiff {d : ℕ} (e : Sphere d) {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (offPoleLocalizedAmbient e B) :=
  (Complex.ofRealCLM.contDiff.comp (offPoleCutoff_contDiff e)).mul hB

theorem offPoleLocalizedAmbient_eq {d : ℕ} (e : Sphere d) (B : Space d → ℂ) :
    offPoleLocalizedAmbient e B = B-poleLocalizedAmbient e B-
      poleLocalizedAmbient (oppositePole e) B := by
  funext x
  simp only [offPoleLocalizedAmbient,offPoleCutoff,poleLocalizedAmbient,Pi.sub_apply,
    Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem offPoleLocalizedAmbient_scaled_budget (d r : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : Sphere d) (B : Space d → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ r, ∀ w : Sphere d, ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ k ≤ r, ∀ w : Sphere d,
        ‖iteratedFDeriv ℝ k (offPoleLocalizedAmbient e B) w‖ ≤ L*C*D^k := by
  choose A hA hAb using fun k => poleLocalizedAmbient_uniform_budget d k
  let H := ∑ k ∈ Finset.range (r+1), A k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hA k)
  refine ⟨1+2*H,by positivity,?_⟩
  intro e B hB C D hC hD hb k hk w
  have hp := poleLocalizedAmbient_contDiff e hB
  have hm := poleLocalizedAmbient_contDiff (oppositePole e) hB
  rw [offPoleLocalizedAmbient_eq,
    iteratedFDeriv_sub_apply (i := k) (f := B-poleLocalizedAmbient e B)
      (g := poleLocalizedAmbient (oppositePole e) B) ((hB.sub hp).contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hm.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    iteratedFDeriv_sub_apply (i := k) (f := B) (g := poleLocalizedAmbient e B)
      (hB.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hp.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  have hbp := hAb k e B hB C D hC hD (fun j hj => hb j (hj.trans hk)) k le_rfl w
  have hbm := hAb k (oppositePole e) B hB C D hC hD
    (fun j hj => hb j (hj.trans hk)) k le_rfl w
  have hAH : A k ≤ H := Finset.single_le_sum (fun k _ => hA k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hpow : 0 ≤ D^k := pow_nonneg (zero_le_one.trans hD) k
  calc
    _ ≤ (‖iteratedFDeriv ℝ k B w‖+
        ‖iteratedFDeriv ℝ k (poleLocalizedAmbient e B) w‖)+
        ‖iteratedFDeriv ℝ k (poleLocalizedAmbient (oppositePole e) B) w‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (C*D^k+A k*C*D^k)+A k*C*D^k := by gcongr; exact hb k hk w
    _ ≤ (C*D^k+H*C*D^k)+H*C*D^k := by gcongr
    _ = _ := by ring

theorem sphere_offPole_decay_of_ambient_bounds (hpublished : PublishedGnomonicSurface)
    (n M : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (n+2)) (B : Space (n+2) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ M, ∀ w : Sphere (n+2), ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 0 < Λ →
      ‖sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w)‖ ≤
        A*C*(D/Λ)^M := by
  obtain ⟨A,hA,hdecay⟩ := sphere_offPole_decay hpublished n M hn (ε := 1/16) (by norm_num)
  obtain ⟨L,hL,hLb⟩ := offPoleLocalizedAmbient_scaled_budget (n+2) M
  obtain ⟨H,hH,hHb⟩ := ambient_symbol_rotated_chart_budget n M
  refine ⟨A*H*L,by positivity,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  let F := offPoleLocalizedAmbient e B
  have hF : ContDiff ℝ ∞ F := offPoleLocalizedAmbient_contDiff e hB
  have hder : ∀ j ≤ M, ∀ w : Sphere (n+2),
      ‖iteratedFDeriv ℝ j F w‖ ≤ (L*C)*D^j := by
    intro j hj w
    exact (hLb e B hB C D hC hD hb j hj w).trans_eq (by ring)
  have hFb : ∀ w : Sphere (n+2), ‖F w‖ ≤ L*C := by
    intro w
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hder 0 (Nat.zero_le _) w
  have hh := hdecay e (fun w => F w) (sphere_norm e)
    (hF.continuous.measurable.comp continuous_subtype_val.measurable)
    (fun w hw => offPoleCutoff_gap e w (by
      intro hz
      exact hw (by simp only [F,offPoleLocalizedAmbient,hz,Complex.ofReal_zero,zero_mul])))
    (fun T y _ => ambient_symbol_chart_smooth T F hF y)
    (L*C) (H*(L*C)) D Λ (by positivity) hD hΛ hFb
    (fun T y hy k hk u hu => hHb F hF (L*C) D (by positivity) hD hder T y hy u hu k hk)
  exact hh.trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereStationaryAssembly
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration for the two stationary poles

These identities retain the original sphere measure and the original
ambient amplitude. The antipodal contribution uses the same smooth pole
patch as the outgoing contribution.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem antipodalConjugate_contDiff {d : ℕ} {B : Space d → ℂ}
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (antipodalConjugate B) :=
  Complex.conjCLE.contDiff.comp (hB.comp contDiff_id.neg)

theorem antipodalConjugate_derivative_norm {d : ℕ} (B : Space d → ℂ)
    (k : ℕ) (x : Space d) :
    ‖iteratedFDeriv ℝ k (antipodalConjugate B) x‖ = ‖iteratedFDeriv ℝ k B (-x)‖ := by
  change ‖iteratedFDeriv ℝ k (Complex.conjLIE ∘
    (B ∘ LinearIsometryEquiv.neg ℝ (E := Space d))) x‖ = _
  rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left,
    (LinearIsometryEquiv.neg ℝ (E := Space d)).norm_iteratedFDeriv_comp_right]
  rfl

theorem sphere_phase_norm {d : ℕ} (Λ : ℝ) (e w : Sphere d) :
    ‖Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
    sub_zero,Real.exp_zero]

theorem sphereOscillation_integrable {d : ℕ} (Λ : ℝ) (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    Integrable (fun w : Sphere d =>
      Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))*B w)
        (sphereMeasure d) := by
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : Space d) 1).exists_bound_of_continuousOn
    hB.continuous.continuousOn
  apply Integrable.of_bound (by fun_prop) C
  filter_upwards with w
  simpa only [norm_mul,sphere_phase_norm,one_mul] using hC w w.property

theorem sphereOscillation_pole_partition {d : ℕ} (Λ : ℝ) (e : Sphere d)
    {B : Space d → ℂ} (hB : ContDiff ℝ ∞ B) :
    sphereOscillation Λ e (fun w => B w) =
      (sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w)+
        sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w))+
      sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w) := by
  let F : Sphere d → ℂ := fun w =>
    Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) (e : Space d) : ℂ))
  have hfun : (fun w : Sphere d => F w*B w) = fun w =>
      (F w*poleLocalizedAmbient e B w+F w*poleLocalizedAmbient (oppositePole e) B w)+
        F w*offPoleLocalizedAmbient e B w := by
    funext w
    simp only [poleLocalizedAmbient,offPoleLocalizedAmbient,offPoleCutoff,
      Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have hp := sphereOscillation_integrable Λ e (poleLocalizedAmbient_contDiff e hB)
  have hm := sphereOscillation_integrable Λ e (poleLocalizedAmbient_contDiff (oppositePole e) hB)
  have ho := sphereOscillation_integrable Λ e (offPoleLocalizedAmbient_contDiff e hB)
  change (∫ w, F w*B w ∂sphereMeasure d) = _
  rw [hfun]
  calc
    _ = (∫ w, F w*poleLocalizedAmbient e B w+F w*poleLocalizedAmbient (oppositePole e) B w
          ∂sphereMeasure d)+(∫ w, F w*offPoleLocalizedAmbient e B w ∂sphereMeasure d) :=
      integral_add (hp.add hm) ho
    _ = _ := congrArg (fun z => z+(∫ w, F w*offPoleLocalizedAmbient e B w ∂sphereMeasure d))
      (integral_add hp hm)

theorem sphere_stationary_phase_norm (Λ : ℝ) : ‖Complex.exp (Complex.I*(Λ : ℂ))‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,Real.exp_zero]

theorem remove_outgoing_phase (Λ : ℝ) (p I S : ℂ) :
    ‖p*I-Complex.exp (Complex.I*(Λ : ℂ))*S‖ =
      ‖p*Complex.exp (-(Complex.I*(Λ : ℂ)))*I-S‖ := by
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have he : z*(p*z⁻¹*I-S) = p*I-z*S := by field_simp
  rw [Complex.exp_neg]
  change ‖p*I-z*S‖ = ‖p*z⁻¹*I-S‖
  rw [← he,norm_mul,sphere_stationary_phase_norm,one_mul]

theorem stationary_offPole_scale (m J : ℕ) {D Λ : ℝ} (hD : 1 ≤ D) (hΛ : 1 ≤ Λ) :
    Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1) ≤
      Λ^(-(J : ℝ))*D^(2*J+(m+2)+1) := by
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hpow : Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1) =
      Λ^(((m+2 : ℕ) : ℝ)/2-((J+(m+2)+1 : ℕ) : ℝ))*D^(J+(m+2)+1) := by
    rw [div_pow,div_eq_mul_inv (D^(J+(m+2)+1)) (Λ^(J+(m+2)+1)),
      ← Real.rpow_natCast Λ (J+(m+2)+1),
      ← Real.rpow_neg hΛp.le]
    rw [show Λ^(((m+2 : ℕ) : ℝ)/2)*
        (D^(J+(m+2)+1)*Λ^(-((J+(m+2)+1 : ℕ) : ℝ))) =
      (Λ^(((m+2 : ℕ) : ℝ)/2)*Λ^(-((J+(m+2)+1 : ℕ) : ℝ)))*D^(J+(m+2)+1) by ring,
      ← Real.rpow_add hΛp]
    congr 1
  rw [hpow]
  apply mul_le_mul
  · apply Real.rpow_le_rpow_of_exponent_le hΛ
    push_cast
    linarith
  · exact pow_le_pow_right₀ hD (by omega)
  · exact pow_nonneg hD0 _
  · exact (Real.rpow_pos_of_pos hΛp _).le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereStationary
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full-sphere stationary phase for the actual amplitude

The two pole expansions are combined with the proved off-pole estimate.
The only inputs are the recorded gnomonic surface formula and the precise
quadratic stationary-phase specialization. No spherical estimate is an
assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

/-- Full outgoing/incoming expansion, with the original symbol and
original sphere measure. The derivative budget is `2*J+d`. -/
theorem sphere_stationary_expansion_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*sphereOscillation Λ e (fun w => B w) -
        (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e +
          star (Complex.exp (Complex.I*(Λ : ℂ))*
            directStationarySum m J Λ (antipodalConjugate B) e))‖ ≤
        A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hpole⟩ := pole_stationary_remainder_of_ambient_bounds
    hgnomonic hquadratic m J hJ
  obtain ⟨O,hO,hoff⟩ := sphere_offPole_decay_of_ambient_bounds
    hgnomonic (m+1) (J+(m+2)+1) (by omega)
  refine ⟨2*A+O,by positivity,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  let Ip := sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w)
  let Im := sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w)
  let Io := sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w)
  let Sp := z*directStationarySum m J Λ B e
  let Sm := star (z*directStationarySum m J Λ (antipodalConjugate B) e)
  let T := Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1)
  have hp : ‖p*Ip-Sp‖ ≤ A*T := by
    rw [show A*T = A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) by dsimp [T]; ring]
    simpa only [p,Ip,Sp,z,directStationarySum,remove_outgoing_phase] using
      hpole e B hB C D hC hD hb Λ hΛ
  have hanti : ContDiff ℝ ∞ (antipodalConjugate B) := antipodalConjugate_contDiff hB
  have hab : ∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (antipodalConjugate B) w‖ ≤ C*D^j := by
    intro j hj w
    rw [antipodalConjugate_derivative_norm]
    exact hb j hj (oppositePole w)
  have hpa : ‖p*sphereOscillation Λ e
      (fun w => poleLocalizedAmbient e (antipodalConjugate B) w)-
        z*directStationarySum m J Λ (antipodalConjugate B) e‖ ≤ A*T := by
    rw [show A*T = A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) by dsimp [T]; ring]
    simpa only [p,z,directStationarySum,remove_outgoing_phase] using
      hpole e (antipodalConjugate B) hanti C D hC hD hab Λ hΛ
  have hm : ‖p*Im-Sm‖ ≤ A*T := by
    have hpstar : star p = p := by
      change (starRingEnd ℂ) ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) = _
      exact Complex.conj_ofReal _
    have he : p*Im-Sm = star (p*sphereOscillation Λ e
        (fun w => poleLocalizedAmbient e (antipodalConjugate B) w)-
          z*directStationarySum m J Λ (antipodalConjugate B) e) := by
      dsimp only [Im,Sm]
      simp only [poleLocalized_opposite_oscillation,star_sub,star_mul',hpstar]
      rfl
    rw [he,norm_star]
    exact hpa
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hpr : 0 < Λ^(((m+2 : ℕ) : ℝ)/2) := Real.rpow_pos_of_pos hΛp _
  have ho : ‖p*Io‖ ≤ O*T := by
    have hod := hoff e B hB C D hC hD
      (fun j hj => hb j (by omega)) Λ hΛp
    rw [norm_mul,show ‖p‖ = Λ^(((m+2 : ℕ) : ℝ)/2) by
      simp only [p,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpr]]
    apply (mul_le_mul_of_nonneg_left hod hpr.le).trans
    calc
      _ = O*C*(Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1)) := by ring
      _ ≤ O*C*(Λ^(-(J : ℝ))*D^(2*J+(m+2)+1)) :=
        mul_le_mul_of_nonneg_left (stationary_offPole_scale m J hD hΛ) (mul_nonneg hO hC)
      _ = O*T := by dsimp [T]; ring
  have hsplit : p*sphereOscillation Λ e (fun w => B w)-(Sp+Sm) =
      (p*Ip-Sp)+(p*Im-Sm)+p*Io := by
    rw [sphereOscillation_pole_partition Λ e hB]
    dsimp [Ip,Im,Io]
    ring
  change ‖p*sphereOscillation Λ e (fun w => B w)-(Sp+Sm)‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ (‖p*Ip-Sp‖+‖p*Im-Sm‖)+‖p*Io‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (A*T+A*T)+O*T := add_le_add (add_le_add hp hm) ho
    _ = _ := by dsimp [T]; ring

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.sphere_stationary_expansion_oai := @OAI.Falconer.sphere_stationary_expansion_oai
