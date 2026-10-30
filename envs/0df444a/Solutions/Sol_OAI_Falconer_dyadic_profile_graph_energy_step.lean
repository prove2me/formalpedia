-- Prove2me | solution 1 for OAI.Falconer.dyadic_profile_graph_energy_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:13:31.245527+00:00
-- url     : https://prove2.me/submissions/2d0f555e-e255-439e-9855-93871a82e59c

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

/-- Scalar phase error under point and cap replacement. -/
theorem longitudinal_test_error {w z : E} (hw : ‖w‖ = 1) (u v : E) :
    |inner ℝ w u - inner ℝ z v| ≤ ‖u-v‖ + ‖w-z‖ * ‖v‖ := by
  have he : inner ℝ w u - inner ℝ z v =
      inner ℝ w (u-v) + inner ℝ (w-z) v := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ w (u-v)| + |inner ℝ (w-z) v| := abs_add_le _ _
    _ ≤ ‖w‖ * ‖u-v‖ + ‖w-z‖ * ‖v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = _ := by rw [hw, one_mul]

/-- A perpendicular tube and a longitudinal interval together confine the
unknown point to a ball, regardless of any other direction in the graph. -/
theorem norm_le_longitudinal_add_perpendicular {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖v‖ ≤ |inner ℝ w v| + ‖perpendicularPart w v‖ := by
  have he : v = inner ℝ w v • w + perpendicularPart w v := by
    dsimp [perpendicularPart]
    abel
  calc
    ‖v‖ = ‖inner ℝ w v • w + perpendicularPart w v‖ := congrArg norm he
    _ ≤ ‖inner ℝ w v • w‖ + ‖perpendicularPart w v‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, hw, mul_one]

/-- Difference of two points satisfying the same scalar interval and the same
perpendicular tube belongs to a ball of the expected radius. -/
theorem two_test_diameter {w : E} (hw : ‖w‖ = 1) {u v : E} {a b : ℝ}
    (hlong : |inner ℝ w u - inner ℝ w v| ≤ a)
    (hperp : ‖perpendicularPart w u - perpendicularPart w v‖ ≤ b) :
    ‖u-v‖ ≤ a+b := by
  calc
    ‖u-v‖ ≤ |inner ℝ w (u-v)| + ‖perpendicularPart w (u-v)‖ :=
      norm_le_longitudinal_add_perpendicular hw _
    _ = |inner ℝ w u - inner ℝ w v| +
        ‖perpendicularPart w u - perpendicularPart w v‖ := by
      rw [inner_sub_right, perpendicularPart_sub]
    _ ≤ a+b := add_le_add hlong hperp

/-- When each point lies in a tube of radius τ and its scalar coordinate in
an interval of half-width τ, the full candidate diameter is at most 4τ. -/
theorem retained_candidates_diameter {w : E} (hw : ‖w‖ = 1) {u v : E} {c τ : ℝ}
    (hu : |inner ℝ w u - c| ≤ τ) (hv : |inner ℝ w v - c| ≤ τ)
    (hpu : ‖perpendicularPart w u‖ ≤ τ) (hpv : ‖perpendicularPart w v‖ ≤ τ) :
    ‖u-v‖ ≤ 4*τ := by
  have hlong : |inner ℝ w u - inner ℝ w v| ≤ 2*τ := by
    calc
      _ = |(inner ℝ w u-c) - (inner ℝ w v-c)| := by congr 1; ring
      _ ≤ |inner ℝ w u-c| + |inner ℝ w v-c| := abs_sub _ _
      _ ≤ 2*τ := by linarith
  have hperp : ‖perpendicularPart w u - perpendicularPart w v‖ ≤ 2*τ :=
    (norm_sub_le _ _).trans (by linarith)
  exact (two_test_diameter hw hlong hperp).trans_eq (by ring)

/-- Two centers retained in one cap lie in a slightly wider tube in any
nearby witness direction. This is the geometric input to the parallel test. -/
theorem witness_tube_bound {w w₀ : E} (hw : ‖w‖ = 1) (hw₀ : ‖w₀‖ = 1)
    {u v z : E} {τ δ L : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖perpendicularPart w₀ (u-z)‖ ≤ τ)
    (hv : ‖perpendicularPart w₀ (v-z)‖ ≤ τ)
    (hclose : ‖w-w₀‖ ≤ δ) (hsize : ‖u-v‖ ≤ L) :
    ‖perpendicularPart w (u-v)‖ ≤ 2*τ + 2*δ*L := by
  have he : (u-z) - (v-z) = u-v := by abel
  have hbase : ‖perpendicularPart w₀ (u-v)‖ ≤ 2*τ := by
    rw [← he, perpendicularPart_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have herror := perpendicularPart_direction_error hw hw₀ (u-v)
  have hg : 2 * ‖w-w₀‖ * ‖u-v‖ ≤ 2*δ*L := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hclose (by norm_num)) hsize
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (perpendicularPart w (u-v)) (perpendicularPart w₀ (u-v)) 0
  simp only [sub_zero] at ht
  linarith

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

/-- Failure of the longitudinal center test gives a radial phase
derivative bounded away from zero after the two endpoint replacements. -/
theorem longitudinal_failure_nonstationary {w₁ w₂ z₁ z₂ : E}
    (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (v₁ v₂ d₁ d₂ : E) {τ : ℝ}
    (hbad : τ < |inner ℝ z₁ d₁ + inner ℝ z₂ d₂|)
    (herr : (‖v₁-d₁‖ + ‖w₁-z₁‖ * ‖d₁‖) +
      (‖v₂-d₂‖ + ‖w₂-z₂‖ * ‖d₂‖) ≤ τ/2) :
    τ/2 ≤ |inner ℝ w₁ v₁ + inner ℝ w₂ v₂| := by
  have he₁ := longitudinal_test_error hw₁ v₁ d₁ (z := z₁)
  have he₂ := longitudinal_test_error hw₂ v₂ d₂ (z := z₂)
  have he : |(inner ℝ w₁ v₁ + inner ℝ w₂ v₂) -
      (inner ℝ z₁ d₁ + inner ℝ z₂ d₂)| ≤ τ/2 := by
    calc
      _ = |(inner ℝ w₁ v₁ - inner ℝ z₁ d₁) +
          (inner ℝ w₂ v₂ - inner ℝ z₂ d₂)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add he₁ he₂).trans herr)
  have ht := abs_sub_le (inner ℝ z₁ d₁ + inner ℝ z₂ d₂)
    (inner ℝ w₁ v₁ + inner ℝ w₂ v₂) 0
  rw [sub_zero, sub_zero, abs_sub_comm] at ht
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
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FinsetSchur
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

/-- The same count with an arbitrary common origin for the displacement
tests. The grid itself need not be centered at the origin of the tube. -/
theorem retained_grid_card_translated {d L : ℕ} {s τ c : ℝ}
    (hs : 0 < s) (hL : 4 * τ * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w u : Space d) (hw : ‖w‖ = 1)
    (hlong : ∀ z ∈ S, |inner ℝ w (scaledGridPoint s z - u) - c| ≤ τ)
    (hperp : ∀ z ∈ S, ‖perpendicularPart w (scaledGridPoint s z - u)‖ ≤ τ) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    apply grid_ball_card hs hL S z₀
    intro z hz
    have hh := retained_candidates_diameter hw (hlong z hz) (hlong z₀ hz₀)
      (hperp z hz) (hperp z₀ hz₀)
    simpa only [sub_sub_sub_cancel_right] using hh
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphDegrees
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Degrees of the higher-dimensional retained graph

The vertex sets are the eligible depth-`p` grid cells for a
fixed pair of caps. A parallel test controls the first unknown cell; the
scalar constraint then controls the second, in its own cap direction.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

theorem retainedGridEdge_swap {d : ℕ} (s : ℝ) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : (Fin d → ℤ) × (Fin d → ℤ)) :
    retainedGridEdge s w₁ w₂ τ row col ↔
      retainedGridEdge s w₂ w₁ τ row.swap col.swap := by
  simp only [retainedGridEdge, Prod.fst_swap, Prod.snd_swap, add_comm]
  tauto

/-- Counting a finite set of pairs by its first-coordinate candidates and
the uniformly bounded second-coordinate fibers. -/
theorem pair_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (A : Finset α) (K : ℕ)
    (hA : ∀ z ∈ S, z.1 ∈ A)
    (hK : ∀ a ∈ A, ((S.filter (fun z => z.1 = a)).image Prod.snd).card ≤ K) :
    S.card ≤ K * A.card := by
  apply Finset.card_le_mul_card_image_of_maps_to hA K
  intro a ha
  have hinj : Set.InjOn Prod.snd (↑(S.filter (fun z => z.1 = a)) : Set (α × β)) := by
    intro x hx y hy hxy
    exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
  rw [← Finset.card_image_of_injOn hinj]
  exact hK a ha

/-- Row degree from the first endpoint's parallel-test count. The second
endpoint only uses its unit cap direction and the grid packing bound. -/
theorem retainedGrid_degree_first {d L C : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₂ : ‖w₂‖ = 1)
    (row : (Fin d → ℤ) × (Fin d → ℤ))
    (hparallel : (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)).card ≤ C) :
    ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card ≤
      (2 * L + 1)^d * C := by
  classical
  let S := (A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)
  let T := A.filter (fun z =>
    ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)
  have hcount : S.card ≤ (2 * L + 1)^d * T.card := by
    apply pair_card_le S T
    · intro z hz
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hz).1, he.1⟩
    · intro a _ha
      apply retained_grid_card_translated hs hL _ w₂ (scaledGridPoint s row.2) hw₂
        (c := -inner ℝ w₁ (scaledGridPoint s a - scaledGridPoint s row.1))
      · intro b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨hz, hza⟩ := Finset.mem_filter.mp hz
        obtain ⟨_, he⟩ := Finset.mem_filter.mp hz
        simpa only [sub_neg_eq_add, ← hza, add_comm] using he.2.2
      · intro b hb
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2.2.1
  exact hcount.trans (Nat.mul_le_mul_left _ hparallel)

/-- Both choices of the first unknown are valid, so the smaller parallel
count controls the degree. -/
theorem retainedGrid_degree_min {d L C₁ C₂ : ℕ} {s τ : ℝ} (hs : 0 < s)
    (hL : 4 * τ * s ≤ L) (A B : Finset (Fin d → ℤ))
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    (row : (Fin d → ℤ) × (Fin d → ℤ))
    (h₁ : (A.filter (fun z =>
      ‖perpendicularPart w₁ (scaledGridPoint s z - scaledGridPoint s row.1)‖ ≤ τ)).card ≤ C₁)
    (h₂ : (B.filter (fun z =>
      ‖perpendicularPart w₂ (scaledGridPoint s z - scaledGridPoint s row.2)‖ ≤ τ)).card ≤ C₂) :
    ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card ≤
      (2 * L + 1)^d * min C₁ C₂ := by
  classical
  have hfirst := retainedGrid_degree_first hs hL A B w₁ w₂ hw₂ row h₁
  have hsecond := retainedGrid_degree_first hs hL B A w₂ w₁ hw₁ row.swap h₂
  have heq : ((A ×ˢ B).filter (retainedGridEdge s w₁ w₂ τ row)).card =
      ((B ×ˢ A).filter (retainedGridEdge s w₂ w₁ τ row.swap)).card := by
    apply Finset.card_bij (fun z _ => z.swap)
    · intro z hz
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] using
        (Finset.mem_product.mp hz).symm, (retainedGridEdge_swap _ _ _ _ _ _).mp he⟩
    · intro a _ b _ hab
      exact Prod.swap_injective hab
    · intro z hz
      refine ⟨z.swap, ?_, Prod.swap_swap z⟩
      obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] using
        (Finset.mem_product.mp hz).symm, (retainedGridEdge_swap _ _ _ _ _ _).mpr he⟩
  rw [← heq] at hsecond
  by_cases h : C₁ ≤ C₂
  · simpa only [min_eq_left h] using hfirst
  · simpa only [min_eq_right (le_of_not_ge h)] using hsecond

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphSchur
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive Schur step for the all-dimensional graph estimate

The finite Schur inequality applies to arbitrary index types. The graph
geometry and degrees retain the ambient dimension. A partition of unity
costs no factor equal to the number of caps.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Positive Schur bound for a complex amplitude on a finite graph. -/
theorem finite_graph_schur {ι : Type*} (S : Finset ι)
    (G : ι → ι → Prop) (F : ι → ℂ) (D : ℝ)
    (hrow : ∀ a ∈ S, ((S.filter (G a)).card : ℝ) ≤ D)
    (hcol : ∀ b ∈ S, ((S.filter (fun a => G a b)).card : ℝ) ≤ D) :
    (∑ a ∈ S, ∑ b ∈ S, if G a b then ‖F a * star (F b)‖ else 0) ≤
      D * ∑ a ∈ S, ‖F a‖^2 := by
  have h := PlanarFalconer.finset_bipartite_schur S S G
    (fun a => ‖F a‖) (fun a => ‖F a‖) D hrow hcol
  simp only [norm_mul, norm_star] at ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Summing a nonnegative angular partition of unity preserves the Schur
bound without a cap-count factor. -/
theorem partition_graph_schur {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → ℂ) (weight : κ → ℝ) (D : ℝ)
    (hweight : ∀ k ∈ K, 0 ≤ weight k) (hpartition : ∑ k ∈ K, weight k = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ K, weight k • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a * star (F b) else 0)‖ ≤ D * ∑ a ∈ S, ‖F a‖^2 := by
  calc
    _ ≤ ∑ k ∈ K, ‖weight k • (∑ a ∈ S, ∑ b ∈ S,
        if G k a b then F a * star (F b) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, weight k * (D * ∑ a ∈ S, ‖F a‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight k hk)]
      apply mul_le_mul_of_nonneg_left _ (hweight k hk)
      calc
        _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖if G k a b then F a * star (F b) else 0‖ := by
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
        _ = ∑ a ∈ S, ∑ b ∈ S, if G k a b then ‖F a * star (F b)‖ else 0 := by
          simp only [apply_ite norm, norm_zero]
        _ ≤ _ := finite_graph_schur S (G k) F D (hrow k hk) (hcol k hk)
    _ = _ := by rw [← Finset.sum_mul, hpartition, one_mul]

/-- Integrated retained-edge estimate. The domain can include both angular
variables and the radial variable with its nonnegative cutoff measure. -/
theorem integral_partition_graph_schur {X ι κ : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → X → ℂ) (weight : κ → X → ℝ) (D : ℝ)
    (hF : ∀ a ∈ S, Integrable (fun x => ‖F a x‖^2) μ)
    (hweight : ∀ x k, k ∈ K → 0 ≤ weight k x)
    (hpartition : ∀ x, ∑ k ∈ K, weight k x = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∫ x, ∑ k ∈ K, weight k x • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a x * star (F b x) else 0) ∂μ‖ ≤
      D * ∑ a ∈ S, ∫ x, ‖F a x‖^2 ∂μ := by
  have hbound := norm_integral_le_of_norm_le ((integrable_finsetSum S hF).const_mul D)
    (Filter.Eventually.of_forall (fun x => partition_graph_schur S K G
      (fun a => F a x) (fun k => weight k x) D (hweight x) (hpartition x) hrow hcol))
  simpa only [integral_const_mul, integral_finsetSum S hF] using hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

theorem sourceAngularShellMeasure_real_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    (sourceAngularShellMeasure v Ψ).real univ ≤ 4*B := by
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (sourceAngularShellMeasure_mass_le v Ψ hB hb hs)).trans_eq
  exact ENNReal.toReal_ofReal (by positivity)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SphericalEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sphere_product_square_integral {d : ℕ} (U V : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d, ‖U z.1 * V z.2‖^2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, ‖U w‖^2 ∂sphereMeasure d) * (∫ w, ‖V w‖^2 ∂sphereMeasure d) := by
  simp only [norm_mul, mul_pow]
  exact integral_prod_mul (fun w => ‖U w‖^2) (fun w => ‖V w‖^2)

/-- Bounded measurable endpoint transforms give an integrable square on
the full radial and independent angular product. -/
theorem angular_product_square_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2)
      ((PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
        ((sphereMeasure d).prod (sphereMeasure d))) := by
  have hmU : Measurable (fun z : ℝ × (Sphere d × Sphere d) => U (z.1,z.2.1)) :=
    hU.comp (measurable_fst.prodMk measurable_snd.fst)
  have hmV : Measurable (fun z : ℝ × (Sphere d × Sphere d) => V (z.1,z.2.2)) :=
    hV.comp (measurable_fst.prodMk measurable_snd.snd)
  apply Integrable.of_bound ((hmU.mul hmV).norm.pow_const 2).aestronglyMeasurable ((C*D)^2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hD)).mpr
  change ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖ ≤ C * D
  rw [norm_mul]
  exact mul_le_mul (hbU _) (hbV _) (norm_nonneg _) hC

theorem independentAngularEnergy_product_integral {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V = (2 : ℝ)^((d : ℝ)*(v-a)) *
      ∫ z : ℝ × (Sphere d × Sphere d), ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d)) := by
  have hi := angular_product_square_integrable v Ψ U V hU hV hC hD hbU hbV
  rw [independentAngularEnergy, integral_prod _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  exact (sphere_product_square_integral (fun w => U (r,w)) (fun w => V (r,w))).symm

/-- Schur integration produces precisely the independent child energies
defined with the sphere measure in the original ambient dimension. -/
theorem independentAngularEnergy_graph_schur {d : ℕ} {ι κ : Type*}
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
    (U V : ι → ℝ × Sphere d → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ D i)
    (weight : κ → ℝ × (Sphere d × Sphere d) → ℝ) (degree : ℝ)
    (hweight : ∀ z k, k ∈ K → 0 ≤ weight k z)
    (hpartition : ∀ z, ∑ k ∈ K, weight k z = 1)
    (hrow : ∀ k ∈ K, ∀ i ∈ S, ((S.filter (G k i)).card : ℝ) ≤ degree)
    (hcol : ∀ k ∈ K, ∀ j ∈ S, ((S.filter (fun i => G k i j)).card : ℝ) ≤ degree) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      ‖∫ z : ℝ × (Sphere d × Sphere d), ∑ k ∈ K, weight k z •
        (∑ i ∈ S, ∑ j ∈ S, if G k i j then
          (U i (z.1,z.2.1) * V i (z.1,z.2.2)) *
            star (U j (z.1,z.2.1) * V j (z.1,z.2.2)) else 0)
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d))‖ ≤
      degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
  classical
  let μ := (PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
    ((sphereMeasure d).prod (sphereMeasure d))
  let F := fun i (z : ℝ × (Sphere d × Sphere d)) =>
    U i (z.1,z.2.1) * V i (z.1,z.2.2)
  have hF (i : ι) (hi : i ∈ S) : Integrable (fun z => ‖F i z‖^2) μ :=
    angular_product_square_integrable v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hb := integral_partition_graph_schur μ S K G F weight degree hF
    hweight hpartition hrow hcol
  have he (i : ι) (hi : i ∈ S) : independentAngularEnergy a v Ψ (U i) (V i) =
      (2 : ℝ)^((d : ℝ)*(v-a)) * ∫ z, ‖F i z‖^2 ∂μ :=
    independentAngularEnergy_product_integral a v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) * (degree * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
      have hs : (∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i)) =
          (2 : ℝ)^((d : ℝ)*(v-a)) * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl he
      rw [hs]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two independent angular variables in one graph term

For fixed spatial points, the four-point phase separates into two sphere
integrals. A nonstationary bound in either variable can thus be used without
any angle separation or pointwise truncation of the amplitude.
-/

namespace Falconer
open MeasureTheory

theorem angular_pair_factorization {d : ℕ} (Λ : ℝ) (v₁ v₂ : Space d)
    (b₁ b₂ : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) v₁ : ℂ)+(inner ℝ (z.2 : Space d) v₂ : ℂ))) *
          b₁ z.1 * b₂ z.2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, sphereOscillator Λ v₁ w*b₁ w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ v₂ w*b₂ w ∂sphereMeasure d) := by
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [sphereOscillator]
  rw [mul_add,Complex.exp_add]
  ring

theorem angular_pair_bound {d : ℕ} (Λ : ℝ) (v₁ v₂ : Space d)
    (b₁ b₂ : Sphere d → ℂ) {A B : ℝ} (hA : 0 ≤ A)
    (hfirst : ‖∫ w, sphereOscillator Λ v₁ w*b₁ w ∂sphereMeasure d‖ ≤ A)
    (hsecond : ∀ w, ‖b₂ w‖ ≤ B) :
    ‖∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) v₁ : ℂ)+(inner ℝ (z.2 : Space d) v₂ : ℂ))) *
          b₁ z.1 * b₂ z.2 ∂(sphereMeasure d).prod (sphereMeasure d)‖ ≤
      A*(B*(sphereMeasure d).real Set.univ) := by
  rw [angular_pair_factorization,norm_mul]
  apply mul_le_mul hfirst _ (norm_nonneg _) hA
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simpa only [norm_mul,sphereOscillator_norm,one_mul] using hsecond w

theorem angular_pair_outer_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Λ : ℝ) (v₁ v₂ : X → Space d)
    (b₁ b₂ : X → Sphere d → ℂ) {A B : ℝ} (hA : 0 ≤ A)
    (hfirst : ∀ x, ‖∫ w, sphereOscillator Λ (v₁ x) w*b₁ x w ∂sphereMeasure d‖ ≤ A)
    (hsecond : ∀ x w, ‖b₂ x w‖ ≤ B) :
    ‖∫ x, ∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+(inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) *
          b₁ x z.1 * b₂ x z.2 ∂(sphereMeasure d).prod (sphereMeasure d) ∂μ‖ ≤
      (A*(B*(sphereMeasure d).real Set.univ))*μ.real Set.univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  exact angular_pair_bound Λ (v₁ x) (v₂ x) (b₁ x) (b₂ x) hA (hfirst x) (hsecond x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularPairSwap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fubini for the spatially expanded angular term

Bounded measurable amplitudes on finite original laws are sufficient.
There is no spatial differentiability requirement and no change of the
point labels in the two endpoint factors.
-/

namespace Falconer
open MeasureTheory

theorem angular_pair_spatial_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Λ : ℝ) (v₁ v₂ : X → Space d)
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B C : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ C) :
    (∫ z : Sphere d × Sphere d, ∫ x,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+(inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) *
          b₁ x z.1 * b₂ x z.2 ∂μ ∂(sphereMeasure d).prod (sphereMeasure d)) =
      ∫ x, (∫ w, sphereOscillator Λ (v₁ x) w*b₁ x w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ (v₂ x) w*b₂ x w ∂sphereMeasure d) ∂μ := by
  let F : X × (Sphere d × Sphere d) → ℂ := fun p =>
    Complex.exp (Complex.I*(Λ : ℂ)*
      ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
       (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ))) * b₁ p.1 p.2.1 * b₂ p.1 p.2.2
  have hm : Measurable F := by
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hb₁.comp (measurable_fst.prodMk measurable_snd.fst)
    · exact hb₂.comp (measurable_fst.prodMk measurable_snd.snd)
  have hnorm (p : X × (Sphere d × Sphere d)) : ‖F p‖ ≤ B*C := by
    have hexp : ‖Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
         (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ)))‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [F,norm_mul,hexp,one_mul]
    exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB
  have hi : Integrable F (μ.prod ((sphereMeasure d).prod (sphereMeasure d))) :=
    Integrable.of_bound hm.aestronglyMeasurable (B*C) (Filter.Eventually.of_forall hnorm)
  calc
    _ = ∫ x, ∫ z : Sphere d × Sphere d, F (x,z)
        ∂(sphereMeasure d).prod (sphereMeasure d) ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact angular_pair_factorization Λ (v₁ x) (v₂ x) (b₁ x) (b₂ x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Potential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_Ledger
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_attained (A : ℕ → ℝ) {a t : ℕ} (hat : a ≤ t) :
    ∃ i, a ≤ i ∧ i ≤ t ∧ intervalMin A a t = A i := by
  have hn : (Finset.Icc a t).Nonempty := ⟨a, Finset.mem_Icc.mpr ⟨le_rfl,hat⟩⟩
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hn A
  exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
    by simpa only [intervalMin, finiteMin, dite_eq_left hn] using he⟩

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

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
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EndpointTransform
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

theorem endpoint_integrand_norm {d : ℕ} (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) (x : Space d) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w‖ = ‖b x w‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem measurable_endpointTransform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (M : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ × Sphere d => endpointTransform ρ M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × Sphere d) × Space d =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Space d) z.2 : ℂ)) *
        b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk measurable_fst.snd)
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

theorem endpoint_integrand_integrable {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    Integrable (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * b x w) ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    exact (endpoint_integrand_norm b r w x).trans_le ((hC x w).trans (le_abs_self C))

theorem endpointTransform_norm_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {M C : ℝ} (hM : 0 < M) (b : Space d → Sphere d → ℂ)
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    ‖endpointTransform ρ M b r w‖ ≤ C * ρ.real Set.univ / M := by
  unfold endpointTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_integral_le_of_norm_le_const (μ := ρ)
    (Filter.Eventually.of_forall (fun x => (endpoint_integrand_norm b r w x).trans_le (hC x w)))
  calc
    _ ≤ M⁻¹ * (C * ρ.real Set.univ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

/-- Exact model-mass splitting of one endpoint transform. -/
theorem endpointTransform_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (ρ : ι → Measure (Space d)) [∀ i, IsFiniteMeasure (ρ i)]
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (∑ i ∈ S, ρ i) Ma b r w =
      (Mp / Ma) • ∑ i ∈ S, endpointTransform (ρ i) Mp b r w := by
  simp only [endpointTransform]
  rw [integral_finsetSum_measure (fun i _ => endpoint_integrand_integrable (ρ i) b hb hC r w)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OscillatoryExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oscillatory spatial expansion before absolute values

The product of an endpoint transform and a conjugate transform is written
as the exact two-point integral with displacement phase. The identity uses
the original spatial measures and does not assume spatial smoothness.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem exponential_mul_conj (s t : ℝ) :
    Complex.exp (Complex.I * (s : ℂ)) * star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * ((s-t : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ)) by simp [← Complex.exp_conj]]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem endpointTransform_mul_star {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M P : ℝ) (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M b r w * star (endpointTransform ν P c r w) =
      (M⁻¹ * P⁻¹) • ∫ z : Space d × Space d,
        Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ)) *
          (b z.1 w * star (c z.2 w)) ∂μ.prod ν := by
  have hid (x y : Space d) :
      (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w) *
        star (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) y : ℂ)) * c y w) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (x-y) : ℝ) : ℂ)) *
        (b x w * star (c y w)) := by
    rw [star_mul]
    have he := exponential_mul_conj (r * inner ℝ (w : Space d) x)
      (r * inner ℝ (w : Space d) y)
    push_cast at he
    rw [show r * inner ℝ (w : Space d) (x-y) =
      r * inner ℝ (w : Space d) x - r * inner ℝ (w : Space d) y by
        rw [inner_sub_right, mul_sub]]
    push_cast
    rw [← he]
    ring_nf
  simp only [endpointTransform, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [mul_comm P⁻¹ M⁻¹]
  congr 1
  change _ * conj (∫ x, _ ∂ν) = _
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => hid z.1 z.2)

/-- Equation `graph:phase`, with four possibly different endpoint laws and
with the symbols retained inside the original spatial integral. -/
theorem endpointTransform_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' : ℝ) (b b' c c' : Space d → Sphere d → ℂ)
    (r : ℝ) (w v : Sphere d) :
    (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
    ((M⁻¹ * M'⁻¹) * (P⁻¹ * P'⁻¹)) •
      ∫ z : (Space d × Space d) × (Space d × Space d),
        Complex.exp (Complex.I * ((r *
          (inner ℝ (w : Space d) (z.1.1-z.1.2) +
           inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) *
          ((b z.1.1 w * star (b' z.1.2 w)) * (c z.2.1 v * star (c' z.2.2 v)))
        ∂(μ.prod μ').prod (ν.prod ν') := by
  rw [show (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
      (endpointTransform μ M b r w * star (endpointTransform μ' M' b' r w)) *
      (endpointTransform ν P c r v * star (endpointTransform ν' P' c' r v)) by
        rw [star_mul]; ring]
  rw [endpointTransform_mul_star, endpointTransform_mul_star,
    smul_mul_smul_comm, ← integral_prod_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have he : Complex.exp (Complex.I * ((r *
      (inner ℝ (w : Space d) (z.1.1-z.1.2) +
       inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1.1-z.1.2) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((r * inner ℝ (v : Space d) (z.2.1-z.2.2) : ℝ) : ℂ)) := by
    rw [mul_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [he]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_StationaryOppositePhase
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_iteratedDeriv_conj {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => conj (f x)) = fun x => conj (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt (x := x)
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    change HasDerivAt (fun y => conj (iteratedDeriv n f y))
      (conj (deriv (iteratedDeriv n f) x)) x at hh
    simpa only [iteratedDeriv_succ] using hh.deriv

end PlanarFalconer

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
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ParentRetainedEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_ae_nonzero (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) :
    ∀ᵐ r ∂sourceAngularShellMeasure v Ψ, Ψ (r/(2:ℝ)^v) ≠ 0 := by
  unfold sourceAngularShellMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards with r hr
  intro hz
  apply hr
  simp only [hz, zero_div, ENNReal.ofReal_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialNonstationary
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Arbitrary-power decay for radial discarded terms

After rescaling the radial shell variable, a discarded longitudinal edge
has a Fourier frequency bounded below by a positive power of `R`. The
fixed radial cutoff is Schwartz. Its library Fourier seminorm estimates
therefore supply the arbitrary-power error required by `graph:localization`.
The Fourier convention includes `2π`; a fixed conversion of frequency is
absorbed into the displayed constant.
-/

namespace Falconer
open scoped FourierTransform SchwartzMap

theorem schwartz_fourier_decay (Ψ : 𝓢(ℝ, ℂ)) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ ξ : ℝ, r ≤ |ξ| →
      ‖(𝓕 Ψ) ξ‖ ≤ C * r^(-(M : ℝ)) := by
  let C := max 1 ((SchwartzMap.seminorm ℝ M 0) (𝓕 Ψ))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr ξ hξ
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 Ψ) M ξ
  have hproduct : r^M * ‖(𝓕 Ψ) ξ‖ ≤ C := by
    calc
      _ ≤ |ξ|^M * ‖(𝓕 Ψ) ξ‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hξ M) (norm_nonneg _)
      _ ≤ (SchwartzMap.seminorm ℝ M 0) (𝓕 Ψ) := by
        simpa only [Real.norm_eq_abs] using hdecay
      _ ≤ C := le_max_right _ _
  have hb : ‖(𝓕 Ψ) ξ‖ ≤ C / r^M :=
    (le_div_iff₀ (pow_pos hr M)).mpr (by simpa only [mul_comm] using hproduct)
  simpa only [Real.rpow_neg hr.le, Real.rpow_natCast, div_eq_mul_inv] using hb

/-- A fixed positive gain in rescaled phase frequency gives every requested
power of decay by choosing a finite Schwartz seminorm order. -/
theorem radial_nonstationary_arbitrary_power (Ψ : 𝓢(ℝ, ℂ))
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ ξ : ℝ, R^a ≤ |ξ| →
      ‖(𝓕 Ψ) ξ‖ ≤ C * R^(-T) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (T / a)
  obtain ⟨C, hC, hdecay⟩ := schwartz_fourier_decay Ψ M
  refine ⟨C, hC, ?_⟩
  intro R hR ξ hξ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have horder : T ≤ a * (M : ℝ) := by
    have hh := (div_le_iff₀ ha).mp hM
    nlinarith
  have hh := hdecay (R^a) (Real.rpow_pos_of_pos hR0 _) ξ hξ
  have heq : (R^a)^(-(M : ℝ)) = R^(-a * (M : ℝ)) := by
    rw [← Real.rpow_mul hR0.le]
    congr 1
    ring
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) hC.le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_OriginalShellIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem sourceAngularShellMeasure_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hzero : ∀ t ≤ 0, Ψ t = 0) (f : ℝ → E) :
    (∫ r, f r ∂sourceAngularShellMeasure v Ψ) =
      ((2:ℝ)^v)⁻¹ • ∫ r : ℝ, Ψ (r/(2:ℝ)^v) • f r := by
  have hR : 0 < (2:ℝ)^v := by positivity
  rw [sourceAngularShellMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpos _) hR.le)]
  have he : (fun r => (Ψ (r/(2:ℝ)^v)/(2:ℝ)^v) • f r) =
      fun r => ((2:ℝ)^v)⁻¹ • (Ψ (r/(2:ℝ)^v) • f r) := by
    funext r
    rw [smul_smul]
    congr 1
    ring
  rw [he, integral_smul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : r ∈ Ioi (0:ℝ)
  · exact Set.indicator_of_mem hr _
  · have hz : Ψ (r/(2:ℝ)^v) = 0 := hzero _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) hR.le)
    simp [hr,hz]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialLocalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial localization for the actual shell measure

The normalized radial shell integral is exactly the Fourier transform of
its fixed Schwartz cutoff. This identifies the oscillatory kernel in the
longitudinal discarded terms and gives arbitrary power decay, including
after integration against finite spatial and angular laws.
-/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem radial_shell_oscillator_fourier (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0) (v s : ℝ) :
    (∫ r, Complex.exp (Complex.I * (r*s : ℝ))
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) =
        (𝓕 φ) (-((2 : ℝ)^v)*s/(2*Real.pi)) := by
  let R : ℝ := (2 : ℝ)^v
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  rw [PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero]
  change R⁻¹ • (∫ r, Ψ (r/R) • Complex.exp (Complex.I * (r*s : ℝ))) = _
  have hscale := Measure.integral_comp_div
    (fun u : ℝ => Ψ u • Complex.exp (Complex.I * (R*u*s : ℝ))) R
  have he (r : ℝ) : R*(r/R)*s = r*s := by field_simp
  simp_rw [he] at hscale
  rw [hscale, abs_of_pos hR, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  have hfreq : -2*Real.pi*u*(-R*s/(2*Real.pi)) = R*u*s := by
    field_simp
  change Ψ u • Complex.exp (Complex.I * (R*u*s : ℝ)) =
    Complex.exp ((-2*Real.pi*u*(-R*s/(2*Real.pi)) : ℝ) * Complex.I) • φ u
  rw [hfreq, hφ, Complex.real_smul, smul_eq_mul]
  ring_nf

theorem radial_shell_arbitrary_decay (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ v s : ℝ,
      2*Real.pi*R^α ≤ (2 : ℝ)^v*|s| →
      ‖∫ r, Complex.exp (Complex.I * (r*s : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤ C*R^(-T) := by
  obtain ⟨C,hC,hdecay⟩ := radial_nonstationary_arbitrary_power φ hα T
  refine ⟨C,hC,?_⟩
  intro R hR v s hfreq
  rw [radial_shell_oscillator_fourier φ Ψ hφ hΨ hpos hzero]
  apply hdecay R hR
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2*Real.pi)).mpr (by nlinarith)

/-- Integrating a discarded term loses only its amplitude bound and the
finite mass of the remaining variables. The phase gap is required only
where the amplitude is nonzero. -/
theorem radial_discarded_term_bound_uniform {X : Type*} [MeasurableSpace X]
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure X) [IsFiniteMeasure μ], ∀ R : ℝ, 1 ≤ R → ∀ v : ℝ,
      ∀ (A : X → ℂ) (s : X → ℝ) (B : ℝ), 0 ≤ B →
      (∀ x, ‖A x‖ ≤ B) →
      (∀ x, A x ≠ 0 → 2*Real.pi*R^α ≤ (2 : ℝ)^v*|s x|) →
      ‖∫ x, ∫ r, A x * Complex.exp (Complex.I * (r*s x : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂μ‖ ≤
        (B*C*μ.real Set.univ)*R^(-T) := by
  obtain ⟨C,hC,hdecay⟩ := radial_shell_arbitrary_decay φ Ψ hφ hΨ hpos hzero hα T
  refine ⟨C,hC,?_⟩
  intro μ hμ R hR v A s B hB hAbound hgap
  have hpoint (x : X) :
      ‖∫ r, A x * Complex.exp (Complex.I * (r*s x : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤ B*(C*R^(-T)) := by
    rw [integral_const_mul, norm_mul]
    by_cases hx : A x = 0
    · rw [hx, norm_zero, zero_mul]
      positivity
    · exact mul_le_mul (hAbound x) (hdecay R hR v (s x) (hgap x hx))
        (norm_nonneg _) hB
  have hi := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hpoint)
  exact hi.trans_eq (by ring)


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPairSwap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Radial Fubini for an original-label cap pair

The finite shell law and bounded measurable endpoint factors justify moving
its integral inside both the angles and the original spatial labels. No
spatial regularity or separation of the two angles is required.
-/

namespace Falconer
open MeasureTheory

theorem expandedCapTerm_radial_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    (v₁ v₂ : X → Space d) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B₁) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ B₂) :
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ =
      ∫ p : (Sphere d × Sphere d) × X, ∫ r,
        (b₁ p.2 p.1.1 * b₂ p.2 p.1.2) *
        Complex.exp (Complex.I * (r *
          (inner ℝ (p.1.1 : Space d) (v₁ p.2) +
           inner ℝ (p.1.2 : Space d) (v₂ p.2)) : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ
        ∂((sphereMeasure d).prod (sphereMeasure d)).prod μ := by
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hΨW hz
  let σ := ((sphereMeasure d).prod (sphereMeasure d)).prod μ
  let ρ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  let F : ℝ × ((Sphere d × Sphere d) × X) → ℂ := fun p =>
    (b₁ p.2.2 p.2.1.1 * b₂ p.2.2 p.2.1.2) *
      Complex.exp (Complex.I * (p.1 *
        (inner ℝ (p.2.1.1 : Space d) (v₁ p.2.2) +
         inner ℝ (p.2.1.2 : Space d) (v₂ p.2.2)) : ℝ))
  have hm : Measurable F := by
    apply Measurable.mul
    · exact (hb₁.comp (measurable_snd.snd.prodMk measurable_snd.fst.fst)).mul
        (hb₂.comp (measurable_snd.snd.prodMk measurable_snd.fst.snd))
    · fun_prop
  have hnorm (p : ℝ × ((Sphere d × Sphere d) × X)) : ‖F p‖ ≤ B₁*B₂ := by
    have he : ‖Complex.exp (Complex.I * (p.1 *
        (inner ℝ (p.2.1.1 : Space d) (v₁ p.2.2) +
         inner ℝ (p.2.1.2 : Space d) (v₂ p.2.2)) : ℝ))‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [F,norm_mul,he,mul_one]
    exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB₁
  have hi : Integrable F (ρ.prod σ) :=
    Integrable.of_bound hm.aestronglyMeasurable (B₁*B₂) (Filter.Eventually.of_forall hnorm)
  calc
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ = ∫ r, ∫ p, F (r,p) ∂σ ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with r hr
      rw [integral_prod _ hr]
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      push_cast
      rw [mul_assoc Complex.I]
      ring
    _ = _ := integral_integral_swap hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FourPointCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact cap expansion of an endpoint cross term

Each cap weight stays inside the original four-point amplitude. The only
factor removed from the integral is the product of the four model-mass
normalizations. The measures are the original restricted endpoint laws.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem endpointCapCrossTerm_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) •
        expandedCapTerm ((μ.prod μ').prod (ν.prod ν')) v Ψ
          (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2)
          (fun x w => capPairAmplitude η b b' x.1 w)
          (fun x w => capPairAmplitude θ c c' x.2 w) := by
  unfold endpointCapCrossTerm expandedCapTerm
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [endpointTransform_four_point]
  rw [mul_smul_comm, ← integral_const_mul, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [capPairAmplitude]
  have he : Complex.I * ((r *
      (inner ℝ (z.1 : Space d) (x.1.1-x.1.2) +
       inner ℝ (z.2 : Space d) (x.2.1-x.2.2)) : ℝ) : ℂ) =
      Complex.I*(r : ℂ)*
        ((inner ℝ (z.1 : Space d) (x.1.1-x.1.2) : ℂ)+
         (inner ℝ (z.2 : Space d) (x.2.1-x.2.2) : ℂ)) := by
    push_cast
    ring
  rw [he]
  apply congrArg (fun z : ℂ => ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) • z)
  ring

theorem capPairAmplitude_measurable {d : ℕ} (η : Sphere d → ℝ)
    (hη : Measurable η) (b b' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b')) :
    Measurable (Function.uncurry (capPairAmplitude η b b')) := by
  unfold capPairAmplitude
  exact (Complex.measurable_ofReal.comp (hη.comp measurable_snd)).mul
    ((hb.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hb'.comp (measurable_fst.snd.prodMk measurable_snd))))

theorem capPairAmplitude_norm_le {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) {H B B' : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hη : ∀ w, |η w| ≤ H) (hb : ∀ x w, ‖b x w‖ ≤ B) (hb' : ∀ x w, ‖b' x w‖ ≤ B')
    (x : Space d × Space d) (w : Sphere d) :
    ‖capPairAmplitude η b b' x w‖ ≤ H*(B*B') := by
  simp only [capPairAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_star]
  exact mul_le_mul (hη w) (mul_le_mul (hb _ _) (hb' _ _) (norm_nonneg _) hB)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hH

end Falconer

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapAmplitudeDerivatives
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Derivatives of the actual cap-weighted endpoint pair

Scalar product and conjugation rules control the amplitudes and their
rotated spherical chart in arbitrary ambient dimension at least three.
-/

namespace Falconer
open Set
open scoped ContDiff ComplexConjugate

theorem capPairAmplitude_chart_smooth {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (y : Space n)
    (hη : ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y)) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) :=
  hη.mul (hb.mul (Complex.conjCLE.contDiff.comp hb'))

theorem capPairAmplitude_chart_derivatives {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (y : Space n) (m : ℕ)
    (hη : ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y))
    {H B B' D : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hB' : 0 ≤ B') (hD : 0 ≤ D)
    (u : ℝ)
    (hηbound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η w : ℂ)) y) u‖ ≤ H*D^k)
    (hbbound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b x.1) y) u‖ ≤ B*D^k)
    (hb'bound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b' x.2) y) u‖ ≤ B'*D^k) :
    ∀ k ≤ m, ‖iteratedDeriv k
      (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) u‖ ≤
        (4^m*H*B*B')*D^k := by
  let f := rotatedChartAmplitude e (b x.1) y
  let g := rotatedChartAmplitude e (b' x.2) y
  let h := rotatedChartAmplitude e (fun w => (η w : ℂ)) y
  have hconj : ContDiff ℝ ∞ (fun u => conj (g u)) := Complex.conjCLE.contDiff.comp hb'
  have hconjb (k : ℕ) (hk : k ≤ m) :
      ‖iteratedDeriv k (fun u => conj (g u)) u‖ ≤ B'*D^k := by
    rw [PlanarFalconer.complex_iteratedDeriv_conj hb',Complex.norm_conj]
    exact hb'bound k hk
  have hpair (k : ℕ) (hk : k ≤ m) :
      ‖iteratedDeriv k (fun u => f u*conj (g u)) u‖ ≤ (2^m*B*B')*D^k := by
    apply (PlanarFalconer.complex_product_derivative_bound hb hconj hB hB' hD k u
      (fun j hj => hbbound j (hj.trans hk)) (fun j hj => hconjb j (hj.trans hk))).trans
    gcongr
    norm_num
  intro k hk
  change ‖iteratedDeriv k (fun u => h u*(f u*conj (g u))) u‖ ≤ _
  apply (PlanarFalconer.complex_product_derivative_bound hη (hb.mul hconj)
    hH (by positivity) hD k u (fun j hj => hηbound j (hj.trans hk))
    (fun j hj => hpair j (hj.trans hk))).trans
  calc
    _ ≤ (2^m*H*(2^m*B*B'))*D^k := by gcongr; norm_num
    _ = _ := by rw [show (4 : ℝ)^m = 2^m*2^m by rw [← mul_pow]; norm_num]; ring

theorem capPairAmplitude_cap_support {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) (w₀ : Space d) (δ : ℝ)
    (hη : ∀ w, η w ≠ 0 → ‖(w : Space d)-w₀‖ ≤ δ)
    (x : Space d × Space d) (w : Sphere d)
    (h : capPairAmplitude η b b' x w ≠ 0) : ‖(w : Space d)-w₀‖ ≤ δ := by
  apply hη w
  intro hz
  exact h (by simp [capPairAmplitude,hz])

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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

theorem DyadicCube.cover_descendants {d : ℕ} (Q : DyadicCube d) (n : ℕ) :
    Q.carrier = ⋃ p ∈ cubePaths d n, (Q.descendant p).carrier := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨p, hp, hxp⟩
  · exact iUnion₂_subset fun p _ => Q.descendant_subset p

/-- Exact disjoint measure decomposition; no boundaries or extra spatial
cutoffs are added to the original law. -/
theorem DyadicCube.restrict_descendants {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier = ∑ p ∈ cubePaths d n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.cover_descendants n]
  rw [Measure.restrict_biUnion_finset]
  · simp only [Measure.sum_fintype, Finset.univ_eq_attach]
    exact Finset.sum_attach (cubePaths d n) (fun p => μ.restrict (Q.descendant p).carrier)
  · intro p hp q hq hpq
    exact Q.descendants_disjoint ((mem_cubePaths d n p).mp hp |>.trans
      ((mem_cubePaths d n q).mp hq).symm) hpq
  · intro p
    exact (Q.descendant p).measurable

theorem DyadicCube.restrict_occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier =
      ∑ p ∈ Q.occupiedPaths μ n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.restrict_descendants μ n]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpo
  apply Measure.restrict_eq_zero.mpr
  have hz : ¬ 0 < μ (Q.descendant p).carrier := by
    intro hpos
    exact hpo (Finset.mem_filter.mpr ⟨hp, hpos⟩)
  exact le_antisymm (le_of_not_gt hz) bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DyadicTransforms
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact splitting into occupied dyadic cells

This is the spatial splitting in `graph:splitting`, for the original law
and the same measurable endpoint symbol on every descendant.
-/

namespace Falconer
open MeasureTheory

theorem DyadicCube.endpointTransform_split {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ)
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) Ma b r w =
      (Mp / Ma) • ∑ p ∈ Q.occupiedPaths μ n,
        endpointTransform (μ.restrict (Q.descendant p).carrier) Mp b r w := by
  conv_lhs => rw [Q.restrict_occupiedPaths μ n]
  exact endpointTransform_sum (Q.occupiedPaths μ n)
    (fun p => μ.restrict (Q.descendant p).carrier) Ma Mp hMp b hb hC r w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EnergySplitting
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact independent-energy expansion on the original dyadic cells

The two endpoint laws and their symbols are unchanged when passing to
occupied descendants. The identity keeps every complex cross term inside
the angular--radial integral, where nonstationary localization is applied.
-/

namespace Falconer
open MeasureTheory

theorem complex_sum_square {ι : Type*} (S : Finset ι) (F : ι → ℂ) :
    ((‖∑ i ∈ S, F i‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, F i * star (F j) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem integral_cross_sum_norm {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (F : ι → X → ℂ) :
    ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ‖ =
      ∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ := by
  have he : (∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ) =
      ((∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ : ℝ) : ℂ) := by
    simp_rw [← complex_sum_square]
    exact integral_ofReal
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]

theorem dyadicPairTransform_sum {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (z : ℝ × (Sphere d × Sphere d)) :
    endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2.1 *
      endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2.2 =
    ((Mp₁ / Ma₁) * (Mp₂ / Ma₂)) •
      ∑ p ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c p z := by
  rw [Q₁.endpointTransform_split μ n Ma₁ Mp₁ hMp₁ b hb hbB,
    Q₂.endpointTransform_split ν n Ma₂ Mp₂ hMp₂ c hc hcC,
    smul_mul_smul_comm, Finset.sum_product]
  congr 1
  simp only [dyadicPairTransform, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Exact expansion before any cross term is discarded or replaced by
its absolute value. The child masses are the chosen model masses. -/
theorem independentAngularEnergy_dyadic_expansion {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) =
    (2 : ℝ)^((d : ℝ)*(v-a)) * ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
      ‖∫ z, ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c row z *
            star (dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c col z)
        ∂angularProductMeasure d v Ψ‖ := by
  rw [independentAngularEnergy_product_integral a v Ψ _ _
    (measurable_endpointTransform _ _ b hb) (measurable_endpointTransform _ _ c hc)
    (show 0 ≤ B * (μ.restrict Q₁.carrier).real Set.univ / Ma₁ by positivity)
    (show 0 ≤ C * (ν.restrict Q₂.carrier).real Set.univ / Ma₂ by positivity)
    (fun z => endpointTransform_norm_le _ hMa₁ b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le _ hMa₂ c hcC z.1 z.2)]
  simp_rw [dyadicPairTransform_sum Q₁ Q₂ μ ν n Ma₁ Ma₂ Mp₁ Mp₂ hMp₁ hMp₂ b c hb hc hbB hcC,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_cross_sum_norm]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapCrossIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The original cap cross term as one product-measure integral

This is the bridge between the radial/angular nonstationary estimates
and the finite graph expansion. Its integrability follows from bounded
endpoint symbols and the finite radial shell law.
-/

namespace Falconer
open Set MeasureTheory

theorem weighted_endpoint_cross_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (η θ : Sphere d → ℝ) (U U' V V' : ℝ × Sphere d → ℂ)
    (hη : Measurable η) (hθ : Measurable θ)
    (hU : Measurable U) (hU' : Measurable U') (hV : Measurable V) (hV' : Measurable V')
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B₁ B₂ B₃ B₄ : ℝ} (hB₁ : ∀ z, ‖U z‖ ≤ B₁) (hB₂ : ∀ z, ‖U' z‖ ≤ B₂)
    (hB₃ : ∀ z, ‖V z‖ ≤ B₃) (hB₄ : ∀ z, ‖V' z‖ ≤ B₄) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2))))
      (angularProductMeasure d v Ψ) := by
  have hp₁ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hp₂ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hUV := (hU.comp hp₁).mul (hV.comp hp₂)
  have hUV' := (hU'.comp hp₁).mul (hV'.comp hp₂)
  have hweight : Measurable (fun z : ℝ × (Sphere d × Sphere d) =>
      (η z.2.1 : ℂ)*(θ z.2.2 : ℂ)) :=
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd.fst)).mul
      (Complex.measurable_ofReal.comp (hθ.comp measurable_snd.snd))
  apply Integrable.of_bound (hweight.mul
    (hUV.mul (Complex.continuous_conj.measurable.comp hUV'))).aestronglyMeasurable
    ((B₁*B₃)*(B₂*B₄))
  filter_upwards with z
  change ‖((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
    ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2)))‖ ≤ _
  have hw : |η z.2.1| * |θ z.2.2| ≤ 1 :=
    (mul_le_mul (hηnorm _) (hθnorm _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hp : ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖ ≤ B₁*B₃ :=
    mul_le_mul (hB₁ (z.1,z.2.1)) (hB₃ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U (z.1,z.2.1))).trans (hB₁ (z.1,z.2.1)))
  have hp' : ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖ ≤ B₂*B₄ :=
    mul_le_mul (hB₂ (z.1,z.2.1)) (hB₄ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U' (z.1,z.2.1))).trans (hB₂ (z.1,z.2.1)))
  have hpp := mul_le_mul hp hp' (by positivity : 0 ≤ ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖)
    ((by positivity : 0 ≤ ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖).trans hp)
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul hw hpp (by positivity) zero_le_one).trans_eq (one_mul _)

theorem endpointCapCrossTerm_integrable {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) => ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
) (angularProductMeasure d v Ψ) := by
  exact weighted_endpoint_cross_integrable v Ψ η θ
    (fun z => endpointTransform μ M b z.1 z.2)
    (fun z => endpointTransform μ' M' b' z.1 z.2)
    (fun z => endpointTransform ν P c z.1 z.2)
    (fun z => endpointTransform ν' P' c' z.1 z.2)
    hη hθ (measurable_endpointTransform μ M b hb)
    (measurable_endpointTransform μ' M' b' hb')
    (measurable_endpointTransform ν P c hc)
    (measurable_endpointTransform ν' P' c' hc') hηnorm hθnorm
    (fun z => endpointTransform_norm_le μ hM b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le μ' hM' b' hb'B z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP c hcB z.1 z.2)
    (fun z => endpointTransform_norm_le ν' hP' c' hc'B z.1 z.2)

theorem endpointCapCrossTerm_product_integral {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ∫ z, ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
        ∂angularProductMeasure d v Ψ := by
  exact (integral_prod _ (endpointCapCrossTerm_integrable μ μ' ν ν' M M' P P' v Ψ
    hM hM' hP hP' b b' c c' hb hb' hc hc' η θ hη hθ hηnorm hθnorm
    hB hbB hb'B hcB hc'B)).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapEnergyExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inserting the actual cap partition before localization

The complex cross terms remain inside the angular and radial integrals.
The cap insertion is an exact identity; no positivity or pointwise
truncation is used to discard an oscillatory term.
-/

namespace Falconer
open MeasureTheory

theorem cap_pair_partition {d : ℕ} {κ : Type*} (K : Finset κ)
    (η : κ → Sphere d → ℝ) (hpart : ∀ w, ∑ k ∈ K, η k w = 1)
    (w₁ w₂ : Sphere d) : ∑ k ∈ K ×ˢ K, η k.1 w₁*η k.2 w₂ = 1 := by
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,hpart,hpart,one_mul]

theorem cap_partition_cross_sum {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (K : Finset κ) (η : κ → Sphere d → ℝ)
    (hpart : ∀ w, ∑ k ∈ K, η k w = 1) (F : ι → ℂ) (w₁ w₂ : Sphere d) :
    (∑ i ∈ S, ∑ j ∈ S, F i*star (F j)) =
      ∑ k ∈ K ×ˢ K, ∑ i ∈ S, ∑ j ∈ S,
        (η k.1 w₁*η k.2 w₂) • (F i*star (F j)) := by
  simp_rw [← Finset.smul_sum]
  rw [← Finset.sum_smul,cap_pair_partition K η hpart,one_smul]

theorem integrated_cap_cross_expansion {d : ℕ} {ι κ : Type*}
    (S : Finset ι) (K : Finset κ) (η : κ → Sphere d → ℝ)
    (hpart : ∀ w, ∑ k ∈ K, η k w = 1)
    (F : ι → (ℝ × (Sphere d × Sphere d)) → ℂ) (v : ℝ) (Ψ : ℝ → ℝ) :
    (∫ z, ∑ i ∈ S, ∑ j ∈ S, F i z*star (F j z) ∂angularProductMeasure d v Ψ) =
      ∫ z, ∑ k ∈ K ×ˢ K, ∑ i ∈ S, ∑ j ∈ S,
        (η k.1 z.2.1*η k.2 z.2.2) • (F i z*star (F j z))
        ∂angularProductMeasure d v Ψ := by
  apply integral_congr_ae
  filter_upwards with z
  exact cap_partition_cross_sum S K η hpart (fun i => F i z) z.2.1 z.2.2

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapPairSymmetry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interchanging the two independent angular variables

This allows the same nonstationary estimate to remove a failed perpendicular
test at either endpoint, with the original spatial law unchanged.
-/

namespace Falconer
open MeasureTheory


theorem endpointCapCrossTerm_swap {d : ℕ}
    (μ μ' ν ν' : Measure (Space d)) (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      endpointCapCrossTerm ν ν' μ μ' P P' M M' v Ψ c c' b b' θ η := by
  unfold endpointCapCrossTerm
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [Prod.swap]
  simp only [star_mul]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapSymbolBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The derivative budget of an actual localized endpoint pair

The cap cutoff has scale delta, while each endpoint symbol has scale D.
When D dominates the inverse radius, the full amplitude satisfies the
budget required by the proved nonstationary sphere estimate. The compact
chart interval is deduced from cap support.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capPairAmplitude_supported_derivatives {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (m : ℕ)
    {δ H B B' D : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/2)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hB' : 0 ≤ B') (hD : 0 ≤ D) (hscale : δ⁻¹ ≤ D)
    (hcap : ∀ z, η z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ)
    (hη : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y))
    (hηb : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η w : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k)
    (hbb : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b x.1) y) u‖ ≤ B*D^k)
    (hb'b : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b' x.2) y) u‖ ≤ B'*D^k) :
    ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 →
      ∀ u ∈ tsupport (rotatedChartAmplitude e (capPairAmplitude η b b' x) y),
      ‖iteratedDeriv k (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) u‖ ≤
        (4^m*H*B*B')*D^k := by
  have hpcap := capPairAmplitude_cap_support η b b' (e (chartPole n)) δ hcap x
  have hs := (cap_amplitude_chart_support e (capPairAmplitude η b b' x) hδ.le hsmall hpcap).2.2
  intro k hk y hy u hu
  have hui := hs y hu
  apply capPairAmplitude_chart_derivatives e η b b' x y m (hη y) (hb y) (hb' y)
    hH hB hB' hD u (fun j hj => ?_) (fun j hj => hbb j hj y hy u hui)
    (fun j hj => hb'b j hj y hy u hui) k hk
  exact (hηb j hj y hy u hui).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hscale j) hH)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellNonstationary
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrating angular nonstationarity over the actual radial shell

The frequency lower bound follows from the support of the fixed cutoff.
No frequency assumption is added to the endpoint symbols.
-/

namespace Falconer
open Set MeasureTheory

theorem shell_ae_radius_lower (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) :
    ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ, (2 : ℝ)^v/4 < r := by
  filter_upwards [PlanarFalconer.sourceAngularShellMeasure_ae_nonzero v Ψ hΨ] with r hr
  have hh := (hs _ hr).1
  have hp : 0 < (2 : ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have h := (lt_div_iff₀ hp).mp hh
  linarith

theorem shell_nonstationary_integral_bound (v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (F : ℝ → ℂ) (m : ℕ) {C D τ : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hτ : 0 < τ)
    (hF : ∀ r, (2 : ℝ)^v/4 < r → ‖F r‖ ≤ C*(D/(r*τ))^m) :
    ‖∫ r, F r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤
      (C*(4*D/((2 : ℝ)^v*τ))^m)*(4*W) := by
  have hu : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hn
    exact (not_lt_of_ge (hs t hn).2.le) ht
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hw hu
  have hp : 0 < (2 : ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r‖ ≤ C*(4*D/((2 : ℝ)^v*τ))^m := by
    filter_upwards [shell_ae_radius_lower v Ψ hΨ hs] with r hr
    have hr0 : 0 < r := lt_trans (by positivity) hr
    apply (hF r hr).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_of_nonneg_left hD
      (mul_pos (div_pos hp (by norm_num)) hτ)
      (mul_le_mul_of_nonneg_right hr.le hτ.le)).trans_eq
    field_simp
  apply (norm_integral_le_of_norm_le_const hbound).trans
  apply mul_le_mul_of_nonneg_left
    (PlanarFalconer.sourceAngularShellMeasure_real_mass_le v Ψ hW hw hu)
    (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DiscardedCapTerm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The complete angular–radial error for one discarded cap term

Spatial labels remain in their original finite measure. The adapted frame
is fixed before these labels are integrated. The phase is the four-point
phase after the two displacements have been formed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem discarded_cap_term_bound {X : Type*} [MeasurableSpace X]
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 ≤ δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (μ : Measure X) [IsFiniteMeasure μ] (v₁ v₂ : X → Space (n+2)),
          Measurable v₁ → Measurable v₂ →
          ∀ (b₁ b₂ : X → Sphere (n+2) → ℂ),
          Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
          (∀ x z, b₁ x z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
          (∀ x y, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e (b₁ x) y)) →
          ∀ (B₁ B₂ C D v : ℝ) (Ψ : ℝ → ℝ),
          0 ≤ B₁ → 0 ≤ B₂ → 0 ≤ C → 1 ≤ D →
          (∀ x z, ‖b₁ x z‖ ≤ B₁) → (∀ x z, ‖b₂ x z‖ ≤ B₂) →
          (∀ x, (∃ z, b₁ x z ≠ 0) → ‖v₁ x‖ ≤ (τ/4)*D) →
          (∀ x, (∃ z, b₁ x z ≠ 0) → ‖v₁ x-d‖+8*δ*‖d‖ ≤ τ/2) →
          (∀ k ≤ m, ∀ x y, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e (b₁ x) y),
            ‖iteratedDeriv k (rotatedChartAmplitude e (b₁ x) y) u‖ ≤ C*D^k) →
          Measurable Ψ → (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
          ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
          ‖∫ r, ∫ z : Sphere (n+2) × Sphere (n+2), ∫ x,
            Complex.exp (Complex.I*(r : ℂ)*
              ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
               (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
            ∂μ ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2))
            ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤
          (A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ) *
            (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  obtain ⟨A,hA,he⟩ := failed_cap_sphere_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ δ hw hτ hδ hsmall hbad
  obtain ⟨e,hew,hest⟩ := he w d τ δ hw hτ hδ hsmall hbad
  refine ⟨e,hew,?_⟩
  intro μ hμ v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂ hcap hsmooth B₁ B₂ C D v Ψ
    hB₁ hB₂ hC hD hbound₁ hbound₂ hv herr hder hΨ hs W hW hΨW
  let F : ℝ → ℂ := fun r => ∫ z : Sphere (n+2) × Sphere (n+2), ∫ x,
    Complex.exp (Complex.I*(r : ℂ)*
      ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
       (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
    ∂μ ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2))
  have hfirst (r : ℝ) (hr : 0 < r) (x : X) :
      ‖∫ z, sphereOscillator r (v₁ x) z*b₁ x z ∂sphereMeasure (n+2)‖ ≤
        A*C*(D/(r*(τ/4)))^m := by
    by_cases hactive : ∃ z, b₁ x z ≠ 0
    · exact hest (v₁ x) (b₁ x) (hb₁.comp (measurable_const.prodMk measurable_id))
        (hcap x) (hsmooth x) B₁ C D r hC hD hr (hbound₁ x) (hv x hactive) (herr x hactive)
        (fun k hk y hy u hu => hder k hk x y hy u hu)
    · have hz : ∀ z, b₁ x z = 0 := by simpa only [not_exists,not_not] using hactive
      simp only [hz,mul_zero,integral_zero,norm_zero]
      positivity
  have hF (r : ℝ) (hr : (2 : ℝ)^v/4 < r) : ‖F r‖ ≤
      (A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ)*(D/(r*(τ/4)))^m := by
    have hr0 : 0 < r := lt_trans (by positivity) hr
    have hswap := angular_pair_spatial_swap μ r v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂
      hB₁ hB₂ hbound₁ hbound₂
    have heq : F r = ∫ x, ∫ z : Sphere (n+2) × Sphere (n+2),
        Complex.exp (Complex.I*(r : ℂ)*
          ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
           (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
        ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2)) ∂μ := by
      rw [show F r = _ from hswap]
      apply integral_congr_ae
      filter_upwards with x
      exact (angular_pair_factorization r (v₁ x) (v₂ x) (b₁ x) (b₂ x)).symm
    rw [heq]
    apply (angular_pair_outer_bound μ r v₁ v₂ b₁ b₂ (by positivity)
      (hfirst r hr0) hbound₂).trans_eq
    ring
  have hh := shell_nonstationary_integral_bound v Ψ hΨ hs hW hΨW F m
    (show 0 ≤ A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ by positivity)
    (zero_le_one.trans hD) (show 0 < τ/4 by positivity) hF
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  congr 1
  field_simp
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DyadicCapTerms
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap terms on the original dyadic descendants

The finite graph expansion and the analytic endpoint cross terms use the
same restricted laws and model masses. These identities connect them
without changing the spatial labels or taking an absolute value early.
-/

namespace Falconer
open Set MeasureTheory

theorem dyadicCapIntegrand_integrable {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    Integrable (dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col)
      (angularProductMeasure d v Ψ) := by
  unfold dyadicCapIntegrand
  simpa only [dyadicCapIntegrand,dyadicPairTransform,Complex.real_smul,Complex.ofReal_mul] using
    endpointCapCrossTerm_integrable (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ
      hM₁ hM₁ hM₂ hM₂ b b c c hb hb hc hc η θ hη hθ hηnorm hθnorm hB hbB hbB hcB hcB

theorem integral_dyadicCapIntegrand {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    (∫ z, dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col z
      ∂angularProductMeasure d v Ψ) =
    endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ := by
  simpa only [dyadicCapIntegrand,dyadicPairTransform,Complex.real_smul,Complex.ofReal_mul] using
    (endpointCapCrossTerm_product_integral (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ
      hM₁ hM₁ hM₂ hM₂ b b c c hb hb hc hc η θ hη hθ hηnorm hθnorm hB hbB hbB hcB hcB).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_LongitudinalCapTerm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The longitudinal discarded cap term

The failed test is imposed on the two fixed cap centers and cell-center
displacements. Cap support and point-replacement errors transfer it to the
actual phase. Radial Fubini then applies Schwartz decay before any absolute
values are taken in the cell expansion.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem longitudinal_discarded_cap_term_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (μ : Measure X) [IsFiniteMeasure μ], ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ,
      0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (w₁ w₂ d₁ d₂ : Space d),
      τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂| →
      ∀ (v₁ v₂ : X → Space d), Measurable v₁ → Measurable v₂ →
      ∀ (b₁ b₂ : X → Sphere d → ℂ),
      Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
      (∀ x z, b₁ x z ≠ 0 → ‖(z : Space d)-w₁‖ ≤ δ) →
      (∀ x z, b₂ x z ≠ 0 → ‖(z : Space d)-w₂‖ ≤ δ) →
      (∀ x, (∃ z, b₁ x z ≠ 0) → (∃ z, b₂ x z ≠ 0) →
        (‖v₁ x-d₁‖+δ*‖d₁‖)+(‖v₂ x-d₂‖+δ*‖d₂‖) ≤ τ/2) →
      ∀ B₁ B₂ : ℝ, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ x z, ‖b₁ x z‖ ≤ B₁) → (∀ x z, ‖b₂ x z‖ ≤ B₂) →
      ‖expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂‖ ≤
        B₁*B₂*A*((sphereMeasure d).real univ)^2*μ.real univ*R^(-T) := by
  obtain ⟨A,hA,hdecay⟩ := radial_discarded_term_bound_uniform
    (X := (Sphere d × Sphere d) × X) φ Ψ hφ hΨ hpos hzero hα T
  refine ⟨A,hA,?_⟩
  intro μ hμ R hR v τ δ _hδ hfreq w₁ w₂ d₁ d₂ hbad v₁ v₂ hv₁ hv₂
    b₁ b₂ hb₁ hb₂ hcap₁ hcap₂ herr B₁ B₂ hB₁ hB₂ hbound₁ hbound₂
  rw [expandedCapTerm_radial_swap μ v Ψ hW hΨW hz v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂
    hB₁ hbound₁ hbound₂]
  let σ := ((sphereMeasure d).prod (sphereMeasure d)).prod μ
  have hh := hdecay σ R hR v
    (fun p : (Sphere d × Sphere d) × X => b₁ p.2 p.1.1*b₂ p.2 p.1.2)
    (fun p => inner ℝ (p.1.1 : Space d) (v₁ p.2)+inner ℝ (p.1.2 : Space d) (v₂ p.2))
    (B₁*B₂) (mul_nonneg hB₁ hB₂) (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB₁) (by
      intro p hp
      obtain ⟨hp₁,hp₂⟩ := mul_ne_zero_iff.mp hp
      have he₁ := hcap₁ p.2 p.1.1 hp₁
      have he₂ := hcap₂ p.2 p.1.2 hp₂
      have he : (‖v₁ p.2-d₁‖+‖(p.1.1 : Space d)-w₁‖*‖d₁‖)+
          (‖v₂ p.2-d₂‖+‖(p.1.2 : Space d)-w₂‖*‖d₂‖) ≤ τ/2 := by
        apply le_trans _ (herr p.2 ⟨p.1.1,hp₁⟩ ⟨p.1.2,hp₂⟩)
        gcongr
      have hl := longitudinal_failure_nonstationary
        (sphere_norm p.1.1) (sphere_norm p.1.2) (v₁ p.2) (v₂ p.2) d₁ d₂ hbad he
      have ht : (2 : ℝ)^v*τ/2 ≤ (2 : ℝ)^v*
          |inner ℝ (p.1.1 : Space d) (v₁ p.2)+inner ℝ (p.1.2 : Space d) (v₂ p.2)| := by
        nlinarith [mul_le_mul_of_nonneg_left hl
          (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) v))]
      linarith)
  apply hh.trans_eq
  dsimp only [σ]
  rw [show (univ : Set ((Sphere d × Sphere d) × X)) = univ ×ˢ univ by simp,
    measureReal_prod_prod]
  rw [show (univ : Set (Sphere d × Sphere d)) = univ ×ˢ univ by simp,
    measureReal_prod_prod]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_LongitudinalCrossTerm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The longitudinal error for the original four endpoint transforms

The radial estimate is applied before absolute values or spatial summation.
The endpoint symbols may be merely measurable in the spatial labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem longitudinal_endpoint_cross_term {d : ℕ}
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (μ μ' ν ν' : Measure (Space d))
        [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
      ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ, 0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (w₁ w₂ d₁ d₂ : Space d), τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂| →
      ∀ (η θ : Sphere d → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space d)-w₁‖ ≤ δ) →
      (∀ z, θ z ≠ 0 → ‖(z : Space d)-w₂‖ ≤ δ) →
      ∀ (b b' c c' : Space d → Sphere d → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry b') →
      Measurable (Function.uncurry c) → Measurable (Function.uncurry c') →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖b' x z‖ ≤ B) →
      (∀ x z, ‖c x z‖ ≤ B) → (∀ x z, ‖c' x z‖ ≤ B) →
      (∀ x : (Space d × Space d) × (Space d × Space d),
        (∃ z, capPairAmplitude η b b' x.1 z ≠ 0) →
        (∃ z, capPairAmplitude θ c c' x.2 z ≠ 0) →
        (‖(x.1.1-x.1.2)-d₁‖+δ*‖d₁‖)+(‖(x.2.1-x.2.2)-d₂‖+δ*‖d₂‖) ≤ τ/2) →
      ∀ M M' P P' : ℝ,
      ‖endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ‖ ≤
        |(M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)| *
          ((B*B)*(B*B)*A*((sphereMeasure d).real univ)^2*
            ((μ.prod μ').prod (ν.prod ν')).real univ*R^(-T)) := by
  let X := (Space d × Space d) × (Space d × Space d)
  obtain ⟨A,hA,hmain⟩ := longitudinal_discarded_cap_term_bound (X := X)
    φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,hA,?_⟩
  intro μ μ' ν ν' _ _ _ _ R hR v τ δ hδ hfreq w₁ w₂ d₁ d₂ hbad
    η θ hη hθ hηnorm hθnorm hcap₁ hcap₂ b b' c c' hb hb' hc hc'
    B hB hbB hb'B hcB hc'B herr M M' P P'
  let μ₄ := (μ.prod μ').prod (ν.prod ν')
  let a₁ : X → Sphere d → ℂ := fun x z => capPairAmplitude η b b' x.1 z
  let a₂ : X → Sphere d → ℂ := fun x z => capPairAmplitude θ c c' x.2 z
  have ha₁ : Measurable (Function.uncurry a₁) :=
    (capPairAmplitude_measurable η hη b b' hb hb').comp
      (measurable_fst.fst.prodMk measurable_snd)
  have ha₂ : Measurable (Function.uncurry a₂) :=
    (capPairAmplitude_measurable θ hθ c c' hc hc').comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hb₁ (x : X) (z : Sphere d) : ‖a₁ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le η b b' zero_le_one hB hηnorm hbB hb'B x.1 z
  have hb₂ (x : X) (z : Sphere d) : ‖a₂ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le θ c c' zero_le_one hB hθnorm hcB hc'B x.2 z
  have hh := hmain μ₄ R hR v τ δ hδ hfreq w₁ w₂ d₁ d₂ hbad
    (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2) (by fun_prop) (by fun_prop)
    a₁ a₂ ha₁ ha₂
    (fun x z hz => capPairAmplitude_cap_support η b b' w₁ δ hcap₁ x.1 z hz)
    (fun x z hz => capPairAmplitude_cap_support θ c c' w₂ δ hcap₂ x.2 z hz)
    herr (B*B) (B*B) (mul_nonneg hB hB) (mul_nonneg hB hB) hb₁ hb₂
  rw [endpointCapCrossTerm_four_point,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicDisplacements
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Point replacement errors in the original dyadic cubes

The two points of an internal displacement belong to different descendants
of the same parent. No separation between the two endpoint parents enters
these estimates.
-/

namespace Falconer

theorem DyadicCube.descendant_displacement_error {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n) {x x' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hx' : x' ∈ (Q.descendant q).carrier) :
    ‖(x-x')-((Q.descendant p).center-(Q.descendant q).center)‖ ≤
      2*Real.sqrt d*(Q.side/(2 : ℝ)^n) := by
  have h₁ := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hx
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
  have h₂ := (Q.descendant q).dist_le (Q.descendant_side_pos hQ q).le hx'
    ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q))
  rw [Q.descendant_side,hp,dist_eq_norm] at h₁
  rw [Q.descendant_side,hq,dist_eq_norm] at h₂
  have he : (x-x')-((Q.descendant p).center-(Q.descendant q).center) =
      (x-(Q.descendant p).center)-(x'-(Q.descendant q).center) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem DyadicCube.descendant_displacement_bound {d : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    {x x' : Space d} (hx : x ∈ (Q.descendant p).carrier)
    (hx' : x' ∈ (Q.descendant q).carrier) :
    ‖x-x'‖ ≤ Real.sqrt d*Q.side := by
  simpa only [dist_eq_norm] using Q.dist_le hQ.le
    (Q.descendant_subset p hx) (Q.descendant_subset q hx')

theorem DyadicCube.descendant_center_displacement_bound {d : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool)) :
    ‖(Q.descendant p).center-(Q.descendant q).center‖ ≤ Real.sqrt d*Q.side :=
  Q.descendant_displacement_bound hQ p q
    ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
    ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q))

theorem DyadicCube.descendant_cap_error {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n) {x x' : Space d}
    (hx : x ∈ (Q.descendant p).carrier) (hx' : x' ∈ (Q.descendant q).carrier)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖(x-x')-((Q.descendant p).center-(Q.descendant q).center)‖ +
        8*δ*‖(Q.descendant p).center-(Q.descendant q).center‖ ≤
      2*Real.sqrt d*(Q.side/(2 : ℝ)^n)+8*δ*(Real.sqrt d*Q.side) :=
  add_le_add (Q.descendant_displacement_error hQ p q hp hq hx hx')
    (mul_le_mul_of_nonneg_left (Q.descendant_center_displacement_bound hQ p q) (by positivity))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_CellSymbols
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cell restrictions inside original endpoint symbols

An indicator in the spatial variable leaves the restricted transform
unchanged and requires no spatial derivative. It makes all nonstationary
geometry hypotheses conditional on genuinely active point labels.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
attribute [local instance] Classical.propDecidable

theorem cellSymbol_measurable {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (cellSymbol Q b)) := by
  exact hb.ite (Q.measurable.preimage measurable_fst) measurable_const

theorem cellSymbol_active {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) {x : Space d} {w : Sphere d}
    (h : cellSymbol Q b x w ≠ 0) : x ∈ Q.carrier := by
  by_contra hn
  exact h (by simp [cellSymbol,hn])

theorem cellSymbol_bound {d : ℕ} (Q : DyadicCube d)
    (b : Space d → Sphere d → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (x : Space d) (w : Sphere d) :
    ‖cellSymbol Q b x w‖ ≤ B := by
  by_cases hx : x ∈ Q.carrier
  · simpa [cellSymbol,hx] using hb x w
  · simpa [cellSymbol,hx] using hB

theorem endpointTransform_cellSymbol {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (M : ℝ) (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) M (cellSymbol Q b) r w =
      endpointTransform (μ.restrict Q.carrier) M b r w := by
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem Q.measurable] with x hx
  simp [cellSymbol,hx]

theorem cellSymbol_chart_smooth {n : ℕ} (Q : DyadicCube (n+2))
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
    (b : Space (n+2) → Sphere (n+2) → ℂ) (x : Space (n+2)) (y : Space n)
    (hb : x ∈ Q.carrier → ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (cellSymbol Q b x) y) := by
  by_cases hx : x ∈ Q.carrier
  · have he : cellSymbol Q b x = b x := by funext w; simp [cellSymbol,hx]
    rw [he]
    exact hb hx
  · have he : cellSymbol Q b x = fun _ => 0 := by funext w; simp [cellSymbol,hx]
    rw [he]
    exact contDiff_const

theorem capPair_cell_active {d : ℕ} (Q Q' : DyadicCube d) (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) {x : Space d × Space d} {w : Sphere d}
    (h : capPairAmplitude η (cellSymbol Q b) (cellSymbol Q' b') x w ≠ 0) :
    x.1 ∈ Q.carrier ∧ x.2 ∈ Q'.carrier := by
  have hpair := (mul_ne_zero_iff.mp h).2
  exact ⟨cellSymbol_active Q b (mul_ne_zero_iff.mp hpair).1,
    cellSymbol_active Q' b' (by simpa only [star_ne_zero] using (mul_ne_zero_iff.mp hpair).2)⟩

/-- The phase bounds refer to the actual descendant cubes whenever
there is a nonzero cap amplitude. -/
theorem cellCapPair_displacement_bounds {d n : ℕ}
    (Q : DyadicCube d) (hQ : 0 < Q.side) (p q : List (Fin d → Bool))
    (hp : p.length = n) (hq : q.length = n)
    (η : Sphere d → ℝ) (b b' : Space d → Sphere d → ℂ)
    (x : Space d × Space d) {δ : ℝ} (hδ : 0 ≤ δ)
    (hactive : ∃ w, capPairAmplitude η (cellSymbol (Q.descendant p) b)
      (cellSymbol (Q.descendant q) b') x w ≠ 0) :
    ‖x.1-x.2‖ ≤ Real.sqrt d*Q.side ∧
    ‖(x.1-x.2)-((Q.descendant p).center-(Q.descendant q).center)‖ +
      8*δ*‖(Q.descendant p).center-(Q.descendant q).center‖ ≤
        2*Real.sqrt d*(Q.side/(2 : ℝ)^n)+8*δ*(Real.sqrt d*Q.side) := by
  obtain ⟨w,hw⟩ := hactive
  obtain ⟨hx,hx'⟩ := capPair_cell_active _ _ η b b' hw
  exact ⟨Q.descendant_displacement_bound hQ p q hx hx',
    Q.descendant_cap_error hQ p q hp hq hx hx' hδ⟩

theorem endpointCapCrossTerm_cellSymbols {d : ℕ}
    (Q Q' S S' : DyadicCube d) (μ μ' ν ν' : Measure (Space d))
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm (μ.restrict Q.carrier) (μ'.restrict Q'.carrier)
      (ν.restrict S.carrier) (ν'.restrict S'.carrier) M M' P P' v Ψ b b' c c' η θ =
    endpointCapCrossTerm (μ.restrict Q.carrier) (μ'.restrict Q'.carrier)
      (ν.restrict S.carrier) (ν'.restrict S'.carrier) M M' P P' v Ψ
      (cellSymbol Q b) (cellSymbol Q' b') (cellSymbol S c) (cellSymbol S' c') η θ := by
  unfold endpointCapCrossTerm
  simp_rw [endpointTransform_cellSymbol]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ChartSymbolControl
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite derivative data for the graph localization

These records express cap and endpoint regularity bounds. They contain no oscillatory estimate or incidence conclusion.
Spatial cell indicators preserve all the required angular derivative bounds.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem ChartSymbolControl.cell {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (Q : DyadicCube (n+2)) : ChartSymbolControl m (cellSymbol Q b) B D := by
  classical
  refine ⟨cellSymbol_measurable Q b h.measurable,
    cellSymbol_bound Q b hB h.bound,?_,?_⟩
  · intro x e y
    exact cellSymbol_chart_smooth Q e b x y (fun _ => h.smooth x e y)
  · intro e k hk x y hy u hu
    by_cases hx : x ∈ Q.carrier
    · have he : cellSymbol Q b x = b x := by funext w; simp [cellSymbol,hx]
      rw [he]
      exact h.derivative e k hk x y hy u hu
    · have he : cellSymbol Q b x = fun _ => 0 := by funext w; simp [cellSymbol,hx]
      rw [he]
      have hzero : rotatedChartAmplitude e (fun _ => (0 : ℂ)) y = fun _ => 0 := rfl
      rw [hzero]
      simp only [iteratedDeriv_const,ite_self,norm_zero]
      exact mul_nonneg hB (pow_nonneg hD k)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DyadicLongitudinal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Longitudinal localization on the original descendant cubes

The original spatial labels give the point-to-center error. Both cap
errors are controlled before the radial Fourier decay is used.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_longitudinal_cross_term {d : ℕ}
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q₁ Q₂ : DyadicCube d), 0 < Q₁.side → 0 < Q₂.side →
      ∀ (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin d → Bool) × List (Fin d → Bool)),
      row.1.length = j → col.1.length = j → row.2.length = j → col.2.length = j →
      ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ, 0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      (2*Real.sqrt d*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt d*Q₁.side))+
        (2*Real.sqrt d*(Q₂.side/(2 : ℝ)^j)+8*δ*(Real.sqrt d*Q₂.side)) ≤ τ/2 →
      ∀ (w₁ w₂ : Sphere d),
      τ < |inner ℝ (w₁ : Space d) ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)+
        inner ℝ (w₂ : Space d) ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)| →
      ∀ (η θ : Sphere d → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space d)-(w₁ : Space d)‖ ≤ δ) →
      (∀ z, θ z ≠ 0 → ‖(z : Space d)-(w₂ : Space d)‖ ≤ δ) →
      ∀ (b c : Space d → Sphere d → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      ∀ B : ℝ, 0 ≤ B → (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖c x z‖ ≤ B) →
      ∀ M₁ M₂ : ℝ,
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        ((B*B)*(B*B)*A*((sphereMeasure d).real univ)^2*
          (((μ.restrict (Q₁.descendant row.1).carrier).prod
            (μ.restrict (Q₁.descendant col.1).carrier)).prod
            ((ν.restrict (Q₂.descendant row.2).carrier).prod
              (ν.restrict (Q₂.descendant col.2).carrier))).real univ*R^(-T)) := by
  obtain ⟨A,hA,hmain⟩ := longitudinal_endpoint_cross_term φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,hA,?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ j row col hr₁ hc₁ hr₂ hc₂ R hR v τ δ hδ hfreq
    herr w₁ w₂ hbad η θ hη hθ hηbound hθbound hηcap hθcap b c hb hc B hB hbB hcB M₁ M₂
  rw [endpointCapCrossTerm_cellSymbols]
  apply hmain _ _ _ _ R hR v τ δ hδ hfreq w₁ w₂
    ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)
    ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center) hbad
    η θ hη hθ hηbound hθbound hηcap hθcap
    _ _ _ _ (cellSymbol_measurable _ b hb) (cellSymbol_measurable _ b hb)
    (cellSymbol_measurable _ c hc) (cellSymbol_measurable _ c hc) B hB
    (cellSymbol_bound _ b hB hbB) (cellSymbol_bound _ b hB hbB)
    (cellSymbol_bound _ c hB hcB) (cellSymbol_bound _ c hB hcB)
  intro x hx₁ hx₂
  have he₁ := (cellCapPair_displacement_bounds Q₁ hQ₁ row.1 col.1 hr₁ hc₁ η b b x.1 hδ hx₁).2
  have he₂ := (cellCapPair_displacement_bounds Q₂ hQ₂ row.2 col.2 hr₂ hc₂ θ c c x.2 hδ hx₂).2
  have hδ₁ : 0 ≤ δ*‖(Q₁.descendant row.1).center-(Q₁.descendant col.1).center‖ := by positivity
  have hδ₂ : 0 ≤ δ*‖(Q₂.descendant row.2).center-(Q₂.descendant col.2).center‖ := by positivity
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_PerpendicularCrossTerm
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular-test error for the original four endpoint transforms

The cap-weighted endpoint products satisfy the analytic localization
hypotheses. All four original spatial laws and all four model-mass
normalizations are retained in the resulting estimate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem perpendicular_endpoint_cross_term
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d₀ : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 < δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d₀‖ →
      ∀ (μ μ' ν ν' : Measure (Space (n+2)))
        [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν'],
      ∀ (η θ : Sphere (n+2) → ℝ), Measurable η → Measurable θ →
      (∀ z, |η z| ≤ 1) → (∀ z, |θ z| ≤ 1) →
      (∀ z, η z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
      ∀ (b b' c c' : Space (n+2) → Sphere (n+2) → ℂ),
      Measurable (Function.uncurry b) → Measurable (Function.uncurry b') →
      Measurable (Function.uncurry c) → Measurable (Function.uncurry c') →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (fun z => (η z : ℂ)) y)) →
      (∀ x, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)) →
      (∀ x, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
        ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x) y)) →
      ∀ (H B D : ℝ), 0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      (∀ x z, ‖b x z‖ ≤ B) → (∀ x z, ‖b' x z‖ ≤ B) →
      (∀ x z, ‖c x z‖ ≤ B) → (∀ x z, ‖c' x z‖ ≤ B) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (fun z => (η z : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ x, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (b x) y) u‖ ≤ B*D^k) →
      (∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ k ≤ m,
        ∀ x, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
        ‖iteratedDeriv k (rotatedChartAmplitude e (b' x) y) u‖ ≤ B*D^k) →
      (∀ x : Space (n+2) × Space (n+2), (∃ z, capPairAmplitude η b b' x z ≠ 0) →
        ‖x.1-x.2‖ ≤ (τ/4)*D) →
      (∀ x : Space (n+2) × Space (n+2), (∃ z, capPairAmplitude η b b' x z ≠ 0) →
        ‖(x.1-x.2)-d₀‖+8*δ*‖d₀‖ ≤ τ/2) →
      ∀ (M M' P P' v : ℝ) (Ψ : ℝ → ℝ), Measurable Ψ →
      (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) → ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
      ‖endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ‖ ≤
        |(M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)| *
          (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ*
            ((μ.prod μ').prod (ν.prod ν')).real univ) *
          (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  let X := (Space (n+2) × Space (n+2)) × (Space (n+2) × Space (n+2))
  obtain ⟨A,hA,hmain⟩ := discarded_cap_term_bound (X := X) hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d₀ τ δ hw hτ hδ hsmall hbad
  obtain ⟨e,hew,he⟩ := hmain w d₀ τ δ hw hτ hδ.le hsmall hbad
  intro μ μ' ν ν' _ _ _ _ η θ hη hθ hηnorm hθnorm hcap
    b b' c c' hb hb' hc hc' hηsmooth hbsmooth hb'smooth
    H B D hH hB hD hscale hbB hb'B hcB hc'B hηder hbder hb'der hv herr
    M M' P P' v Ψ hΨ hs W hW hΨW
  let μ₄ := (μ.prod μ').prod (ν.prod ν')
  let a₁ : X → Sphere (n+2) → ℂ := fun x z => capPairAmplitude η b b' x.1 z
  let a₂ : X → Sphere (n+2) → ℂ := fun x z => capPairAmplitude θ c c' x.2 z
  have ha₁ : Measurable (Function.uncurry a₁) :=
    (capPairAmplitude_measurable η hη b b' hb hb').comp
      (measurable_fst.fst.prodMk measurable_snd)
  have ha₂ : Measurable (Function.uncurry a₂) :=
    (capPairAmplitude_measurable θ hθ c c' hc hc').comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hcap₁ (x : X) (z : Sphere (n+2)) (hz : a₁ x z ≠ 0) :
      ‖(z : Space (n+2))-w‖ ≤ δ := capPairAmplitude_cap_support η b b' w δ hcap x.1 z hz
  have hb₁ (x : X) (z : Sphere (n+2)) : ‖a₁ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le η b b' zero_le_one hB hηnorm hbB hb'B x.1 z
  have hb₂ (x : X) (z : Sphere (n+2)) : ‖a₂ x z‖ ≤ B*B := by
    simpa only [one_mul] using capPairAmplitude_norm_le θ c c' zero_le_one hB hθnorm hcB hc'B x.2 z
  have hpairSmooth (x : X) (y : Space n) (_hy : ‖y‖ ≤ 1) :
      ContDiff ℝ ∞ (rotatedChartAmplitude e (a₁ x) y) :=
    capPairAmplitude_chart_smooth e η b b' x.1 y (hηsmooth e y)
      (hbsmooth x.1.1 e y) (hb'smooth x.1.2 e y)
  have hpairDer (k : ℕ) (hk : k ≤ m) (x : X) (y : Space n) (hy : ‖y‖ ≤ 1)
      (u : ℝ) (hu : u ∈ tsupport (rotatedChartAmplitude e (a₁ x) y)) :
      ‖iteratedDeriv k (rotatedChartAmplitude e (a₁ x) y) u‖ ≤ (4^m*H*B*B)*D^k := by
    apply capPairAmplitude_supported_derivatives e η b b' x.1 m hδ hsmall
      hH hB hB (zero_le_one.trans hD) hscale
      (fun z hz => by simpa only [hew] using hcap z hz)
      (hηsmooth e) (hbsmooth x.1.1 e) (hb'smooth x.1.2 e)
      (hηder e) (fun j hj => hbder e j hj x.1.1)
      (fun j hj => hb'der e j hj x.1.2) k hk y hy u hu
  have hh := he μ₄ (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2)
    (by fun_prop) (by fun_prop) a₁ a₂ ha₁ ha₂ hcap₁ hpairSmooth
    (B*B) (B*B) (4^m*H*B*B) D v Ψ (by positivity) (by positivity) (by positivity) hD
    hb₁ hb₂ (fun x hx => hv x.1 hx) (fun x hx => herr x.1 hx) hpairDer hΨ hs W hW hΨW
  rw [endpointCapCrossTerm_four_point,norm_smul,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DyadicPerpendicular
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Perpendicular localization on actual descendant cubes

The small point-to-center error and derivative hypotheses are verified
for the original cell-restricted symbols before applying the cap estimate.
-/

namespace Falconer
open Set MeasureTheory

theorem dyadic_perpendicular_cross_term
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)),
      row.1.length = j → col.1.length = j →
      ∀ (w : Sphere (n+2)) (τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/2 →
      τ < ‖perpendicularPart (w : Space (n+2))
        ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)‖ →
      ∀ (η θ : Sphere (n+2) → ℝ), ChartCapControl m η (w : Space (n+2)) δ H →
      Measurable θ → (∀ z, |θ z| ≤ 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → Measurable (Function.uncurry c) → (∀ x z, ‖c x z‖ ≤ B) →
      ∀ (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ), 0 < M₁ → 0 < M₂ →
      Measurable Ψ → (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
      ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ*
          (((μ.restrict (Q₁.descendant row.1).carrier).prod
            (μ.restrict (Q₁.descendant col.1).carrier)).prod
            ((ν.restrict (Q₂.descendant row.2).carrier).prod
              (ν.restrict (Q₂.descendant col.2).carrier))).real univ) *
        (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  obtain ⟨A,hA,hmain⟩ := perpendicular_endpoint_cross_term hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro Q₁ Q₂ hQ μ ν _ _ j row col hrow hcol w τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hbad η θ hη hθ hθbound b c hb hc hcB
    M₁ M₂ v Ψ _hM₁ _hM₂ hΨ hΨsupp W hW hΨW
  have hbrow := hb.cell hB (zero_le_one.trans hD) (Q₁.descendant row.1)
  have hbcol := hb.cell hB (zero_le_one.trans hD) (Q₁.descendant col.1)
  have hcRow := cellSymbol_measurable (Q₂.descendant row.2) c hc
  have hcCol := cellSymbol_measurable (Q₂.descendant col.2) c hc
  rw [endpointCapCrossTerm_cellSymbols]
  apply hmain w ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)
    τ δ (sphere_norm w) hτ hδ hδsmall hbad
    _ _ _ _ η θ hη.measurable hθ hη.bound hθbound hη.support
    _ _ _ _ hbrow.measurable hbcol.measurable hcRow hcCol
    hη.smooth hbrow.smooth hbcol.smooth H B D hH hB hD hδD
    hbrow.bound hbcol.bound
    (cellSymbol_bound _ c hB hcB) (cellSymbol_bound _ c hB hcB)
    hη.derivative hbrow.derivative hbcol.derivative
  · intro x hx
    exact ((cellCapPair_displacement_bounds Q₁ hQ row.1 col.1 hrow hcol η b b
      x hδ.le hx).1).trans hnorm
  · intro x hx
    exact ((cellCapPair_displacement_bounds Q₁ hQ row.1 col.1 hrow hcol η b b
      x hδ.le hx).2).trans herr
  · exact hΨ
  · exact hΨsupp
  · exact hW
  · exact hΨW

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Eligibility
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Eligible cell--cap incidences

Positive incidence supplies one point--angle witness. Zero incidence
annihilates the endpoint transform on almost every angle in the cap,
simultaneously for every radial frequency. The symbols need only be
measurable in the spatial variable.
-/

namespace Falconer
open Set MeasureTheory

theorem capIncidence_witness {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ)
    (hη : ∀ w, 0 ≤ η w) (P : Space d → Prop)
    (hP : ∀ᵐ x ∂ρ, P x) (hinc : 0 < capIncidence ρ η b) :
    ∃ x w, P x ∧ 0 < η w ∧ b x w ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_ne_zero_of_integral_ne_zero hinc.ne'
  have hηne : η w ≠ 0 := left_ne_zero_of_mul hw
  have hxne : (∫ x, ‖b x w‖^2 ∂ρ) ≠ 0 := right_ne_zero_of_mul hw
  obtain ⟨x, hx, hPx⟩ :=
    ((frequently_ae_ne_zero_of_integral_ne_zero hxne).and_eventually hP).exists
  refine ⟨x,w,hPx,lt_of_le_of_ne (hη w) (Ne.symm hηne),?_⟩
  intro hb
  exact hx (by simp [hb])

theorem endpoint_square_integrable {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x w, ‖b x w‖ ≤ C) (w : Sphere d) :
    Integrable (fun x => ‖b x w‖^2) ρ := by
  apply Integrable.of_bound
    ((hb.comp (measurable_id.prodMk measurable_const)).norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound x w)

theorem endpoint_square_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x w, ‖b x w‖ ≤ C) (w : Sphere d) :
    (∫ x, ‖b x w‖^2 ∂ρ) ≤ C^2 * ρ.real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound x w)

/-- A null cell--cap incidence is removed as an integrated whole. There is
no frequency-dependent exceptional set of angles. -/
theorem capIncidence_zero_transform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hηB : ∀ w, η w ≤ B) (hbound : ∀ x w, ‖b x w‖ ≤ C)
    (hzero : capIncidence ρ η b = 0) (M : ℝ) :
    ∀ᵐ w ∂sphereMeasure d, 0 < η w → ∀ r, endpointTransform ρ M b r w = 0 := by
  have hinner (w : Sphere d) : 0 ≤ ∫ x, ‖b x w‖^2 ∂ρ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hnonneg (w : Sphere d) : 0 ≤ η w * (∫ x, ‖b x w‖^2 ∂ρ) :=
    mul_nonneg (hη w) (hinner w)
  have hm : Measurable (fun w => η w * (∫ x, ‖b x w‖^2 ∂ρ)) :=
    hηm.mul ((hb.norm.pow_const 2).stronglyMeasurable.integral_prod_left.measurable)
  have hi : Integrable (fun w => η w * (∫ x, ‖b x w‖^2 ∂ρ)) (sphereMeasure d) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (B * (C^2 * ρ.real univ))
    filter_upwards with w
    change ‖η w * (∫ x, ‖b x w‖^2 ∂ρ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg w)]
    exact mul_le_mul (hηB w) (endpoint_square_le ρ b hC hbound w) (hinner w) hB
  have hnull := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hzero
  filter_upwards [hnull] with w hw
  intro hwpos
  have hsq : (∫ x, ‖b x w‖^2 ∂ρ) = 0 := (mul_eq_zero.mp hw).resolve_left hwpos.ne'
  have hbx := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖b x w‖)
    (endpoint_square_integrable ρ b hb hC hbound w)).mp hsq
  intro r
  unfold endpointTransform
  suffices hh : (∫ x, Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * b x w ∂ρ) = 0 by rw [hh, smul_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [hbx] with x hx
  change ‖b x w‖^2 = 0 at hx
  have hz : b x w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (b x w)])
  simp [hz]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parallel tests and the first unknown cell

A cap incidence supplies a witness direction. Grouping eligible cells by
their testing ancestor lets one witness control each group. The direction
perturbation is handled in the original ambient space.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The geometric counting step in `graph:degrees`. The hypotheses are the
literal parallel test at each eligible witness and the diameter of a common
ancestor. In applications there are at most `G` testing ancestors. -/
theorem parallel_count_from_witnesses {E α β : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (center : α → E) (ancestor : α → β)
    (w₀ base : E) (hw₀ : ‖w₀‖ = 1) {τ δ L W : ℝ} (hδ : 0 ≤ δ)
    {C G : ℕ} (hgroups : (A.image ancestor).card ≤ G)
    (hwidth : 2 * τ + 2 * δ * L ≤ W)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ancestor x = ancestor y →
      ‖center x - center y‖ ≤ L)
    (hwitness : ∀ a ∈ A, ∃ w : E, ‖w‖ = 1 ∧ ‖w - w₀‖ ≤ δ ∧
      (A.filter (fun z => ancestor z = ancestor a ∧
        ‖center z - center a‖ ≤ L ∧
        ‖perpendicularPart w (center z - center a)‖ ≤ W)).card ≤ C) :
    (A.filter (fun z => ‖perpendicularPart w₀ (center z - base)‖ ≤ τ)).card ≤ C * G := by
  classical
  let S := A.filter (fun z => ‖perpendicularPart w₀ (center z - base)‖ ≤ τ)
  have hfiber (b : β) (hb : b ∈ S.image ancestor) :
      (S.filter (fun z => ancestor z = b)).card ≤ C := by
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
    obtain ⟨haA, haTube⟩ := Finset.mem_filter.mp ha
    obtain ⟨w, hw, hclose, htest⟩ := hwitness a haA
    apply le_trans (Finset.card_le_card (t := A.filter (fun z =>
      ancestor z = ancestor a ∧ ‖center z - center a‖ ≤ L ∧
        ‖perpendicularPart w (center z - center a)‖ ≤ W)) ?_) htest
    intro z hz
    obtain ⟨hzS, hzb⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzA, hzTube⟩ := Finset.mem_filter.mp hzS
    have hza : ancestor z = ancestor a := hzb.trans hab.symm
    have hsize := hdiam z hzA a haA hza
    exact Finset.mem_filter.mpr ⟨hzA, hza, hsize,
      (witness_tube_bound hw hw₀ hδ hzTube haTube hclose hsize).trans hwidth⟩
  have hcount := Finset.card_le_mul_card_image S C hfiber
  have hsub : S.image ancestor ⊆ A.image ancestor :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  exact hcount.trans (Nat.mul_le_mul_left C ((Finset.card_le_card hsub).trans hgroups))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicAncestors
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ancestor groups for the retained graph witnesses

There are at most `2^(d*g)` ancestor groups at relative depth `g`.
All centers within one group lie in the same original dyadic cube, giving
the diameter used in the parallel-test witness argument.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem dyadic_ancestor_count {d n g : ℕ} (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hg : g ≤ n) :
    (A.image (List.take g)).card ≤ 2^(d*g) := by
  rw [← card_cubePaths]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  simp only [mem_cubePaths, List.length_take, hA q hq, min_eq_left hg]

/-- One eligible point--angle witness per cell supplies the literal
parallel test; the candidate count then costs only the number of actual
dyadic ancestors, independently of their occupied masses. -/
theorem DyadicCube.parallel_count {d n g C : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hg : g ≤ n)
    (w₀ base : Space d) (hw₀ : ‖w₀‖ = 1) {τ δ W : ℝ} (hδ : 0 ≤ δ)
    (hwidth : 2*τ + 2*δ*(Real.sqrt d * (Q.side/(2 : ℝ)^g)) ≤ W)
    (hwitness : ∀ a ∈ A, ∃ w : Space d, ‖w‖ = 1 ∧ ‖w-w₀‖ ≤ δ ∧
      (A.filter (fun z => z.take g = a.take g ∧
        ‖(Q.descendant z).center - (Q.descendant a).center‖ ≤
          Real.sqrt d * (Q.side/(2 : ℝ)^g) ∧
        ‖perpendicularPart w ((Q.descendant z).center - (Q.descendant a).center)‖ ≤ W)).card ≤ C) :
    (A.filter (fun z => ‖perpendicularPart w₀
      ((Q.descendant z).center - base)‖ ≤ τ)).card ≤ C*2^(d*g) := by
  apply parallel_count_from_witnesses A (fun p => (Q.descendant p).center)
    (List.take g) w₀ base hw₀ hδ (dyadic_ancestor_count A hA hg) hwidth
  · intro x hx y _ hxy
    simpa only [dist_eq_norm] using Q.same_ancestor_center_dist hQ x y (hA x hx) hg hxy
  · exact hwitness

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_DyadicGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Retained graph on the actual dyadic cells

The grid degree estimate is transported to arbitrary finite collections
of equal-depth descendants. Their original cube centers define every
test. The final Schur bound can therefore be applied directly to the
endpoint transforms restricted to those cells.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

theorem retainedDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col ↔ retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ col row := by
  have hn (x y : Space d) : x-y = -(y-x) := by abel
  simp only [retainedDyadicEdge, hn (Q₁.descendant row.1).center,
    hn (Q₂.descendant row.2).center, perpendicularPart_neg, norm_neg,
    inner_neg_right, ← neg_add, abs_neg]

theorem retainedDyadicEdge_iff_grid {d n : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hside : Q₂.side = Q₁.side) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hr₁ : row.1.length = n) (hr₂ : row.2.length = n)
    (hc₁ : col.1.length = n) (hc₂ : col.2.length = n) :
    retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col ↔
      retainedGridEdge ((2 : ℝ)^n/Q₁.side) w₁ w₂ τ
        (dyadicCode row.1, dyadicCode row.2) (dyadicCode col.1, dyadicCode col.2) := by
  unfold retainedDyadicEdge retainedGridEdge
  rw [Q₁.center_sub_eq_grid_sub col.1 row.1 hc₁ hr₁,
    Q₂.center_sub_eq_grid_sub col.2 row.2 hc₂ hr₂, hside]

private theorem dyadic_candidate_grid_bound {d n C : ℕ} (Q : DyadicCube d)
    (A : Finset (List (Fin d → Bool))) (hA : ∀ p ∈ A, p.length = n)
    (w : Space d) (τ : ℝ) (a : List (Fin d → Bool)) (ha : a.length = n)
    (hb : (A.filter (fun p => ‖perpendicularPart w
      ((Q.descendant p).center - (Q.descendant a).center)‖ ≤ τ)).card ≤ C) :
    ((A.image dyadicCode).filter (fun z => ‖perpendicularPart w
      (scaledGridPoint ((2 : ℝ)^n/Q.side) z -
        scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode a))‖ ≤ τ)).card ≤ C := by
  classical
  rw [Finset.filter_image]
  apply Finset.card_image_le.trans
  have heq : A.filter (fun p => ‖perpendicularPart w
      (scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode p) -
        scaledGridPoint ((2 : ℝ)^n/Q.side) (dyadicCode a))‖ ≤ τ) =
      A.filter (fun p => ‖perpendicularPart w
        ((Q.descendant p).center - (Q.descendant a).center)‖ ≤ τ) := by
    apply Finset.filter_congr
    intro p hp
    rw [Q.center_sub_eq_grid_sub p a (hA p hp) ha]
  rwa [heq]

theorem retainedDyadic_degree {d n L C₁ C₂ : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1) (τ : ℝ)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ A ×ˢ B)
    (h₁ : (A.filter (fun p => ‖perpendicularPart w₁
      ((Q₁.descendant p).center - (Q₁.descendant row.1).center)‖ ≤ τ)).card ≤ C₁)
    (h₂ : (B.filter (fun p => ‖perpendicularPart w₂
      ((Q₂.descendant p).center - (Q₂.descendant row.2).center)‖ ≤ τ)).card ≤ C₂) :
    ((A ×ˢ B).filter (retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row)).card ≤
      (2*L+1)^d * min C₁ C₂ := by
  classical
  let s := (2 : ℝ)^n/Q₁.side
  let code := fun a : List (Fin d → Bool) × List (Fin d → Bool) =>
    (dyadicCode a.1, dyadicCode a.2)
  have hrA := (Finset.mem_product.mp hr).1
  have hrB := (Finset.mem_product.mp hr).2
  have hc₁ := dyadic_candidate_grid_bound Q₁ A hA w₁ τ row.1 (hA _ hrA) h₁
  have hc₂ := dyadic_candidate_grid_bound Q₂ B hB w₂ τ row.2 (hB _ hrB) h₂
  rw [hside] at hc₂
  have hgrid := retainedGrid_degree_min (show 0 < s by dsimp [s]; positivity) hL
    (A.image dyadicCode) (B.image dyadicCode) w₁ w₂ hw₁ hw₂ (code row) hc₁ hc₂
  apply le_trans _ hgrid
  apply Finset.card_le_card_of_injOn code
  · intro col hcol
    obtain ⟨hcol, hedge⟩ := Finset.mem_filter.mp hcol
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hcol
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨col.1,ha,rfl⟩,
      Finset.mem_image.mpr ⟨col.2,hb,rfl⟩⟩, ?_⟩
    exact (retainedDyadicEdge_iff_grid Q₁ Q₂ hside w₁ w₂ τ row col
      (hA _ hrA) (hB _ hrB) (hA _ ha) (hB _ hb)).mp hedge
  · intro col hcol col' hcol' heq
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hcol).1
    obtain ⟨ha',hb'⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hcol').1
    exact Prod.ext
      (dyadicCode_injective_at_depth (hA _ ha) (hA _ ha') (congrArg Prod.fst heq))
      (dyadicCode_injective_at_depth (hB _ hb) (hB _ hb') (congrArg Prod.snd heq))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_EligibleDyadicGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph of eligible original cell--cap incidences

Support of an endpoint symbol in a literal parallel test supplies the
witnesses used by the degree estimate. Eligibility only filters the finite
cell list; no angular support is cut by a pointwise edge decision.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.eligiblePaths_subset {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) :
    Q.eligiblePaths μ n η b ⊆ Q.occupiedPaths μ n := Finset.filter_subset _ _

theorem DyadicParallelTest.mono {d g C : ℕ} (Q : DyadicCube d)
    {A B : Finset (List (Fin d → Bool))} (hAB : A ⊆ B)
    (p : List (Fin d → Bool)) (w : Space d) (W : ℝ)
    (h : DyadicParallelTest Q B g p w W C) : DyadicParallelTest Q A g p w W C :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hAB)).trans h

theorem DyadicCube.eligiblePaths_witnesses {d n g C : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (η : Sphere d → ℝ)
    (b : Space d → Sphere d → ℂ) (w₀ : Space d) (δ W : ℝ)
    (hη : ∀ w, 0 ≤ η w)
    (hcap : ∀ w, 0 < η w → ‖(w : Space d)-w₀‖ ≤ δ)
    (hsupport : ∀ p ∈ Q.occupiedPaths μ n,
      ∀ᵐ x ∂μ.restrict (Q.descendant p).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q (Q.occupiedPaths μ n) g p (w : Space d) W C) :
    DyadicCapWitnesses Q (Q.eligiblePaths μ n η b) g w₀ δ W C := by
  intro p hp
  obtain ⟨hpocc,hpinc⟩ := Finset.mem_filter.mp hp
  obtain ⟨x,w,hx,hw,hbw⟩ := capIncidence_witness
    (μ.restrict (Q.descendant p).carrier) η b hη _ (hsupport p hpocc) hpinc
  exact ⟨w, sphere_norm w, hcap w hw,
    DyadicParallelTest.mono Q (Q.eligiblePaths_subset μ n η b) p w W (hx w hbw)⟩

theorem eligibleDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (A B : Finset (List (Fin d → Bool))) (w₁ w₂ : Space d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row col ↔
      eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ col row := by
  simp only [eligibleDyadicEdge, retainedDyadicEdge_symm Q₁ Q₂ w₁ w₂ τ row col]
  tauto

/-- The degree bound holds inside any larger row list. Ineligible rows
have degree zero; eligible rows are bounded using their original witnesses. -/
theorem eligibleDyadic_degree {d n g₁ g₂ L C₁ C₂ : ℕ}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    (hg₁ : g₁ ≤ n) (hg₂ : g₂ ≤ n)
    (w₁ w₂ : Space d) (hw₁ : ‖w₁‖ = 1) (hw₂ : ‖w₂‖ = 1)
    {τ δ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (htest₁ : DyadicCapWitnesses Q₁ A g₁ w₁ δ W₁ C₁)
    (htest₂ : DyadicCapWitnesses Q₂ B g₂ w₂ δ W₂ C₂)
    (S : Finset (List (Fin d → Bool) × List (Fin d → Bool)))
    (row : List (Fin d → Bool) × List (Fin d → Bool)) :
    (S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row)).card ≤
      (2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) := by
  by_cases hr : row ∈ A ×ˢ B
  · have hsub : S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row) ⊆
        (A ×ˢ B).filter (retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row) := by
      intro col hcol
      obtain ⟨_,hcol,hedge⟩ := (Finset.mem_filter.mp hcol).2
      exact Finset.mem_filter.mpr ⟨hcol,hedge⟩
    apply (Finset.card_le_card hsub).trans
    apply retainedDyadic_degree Q₁ Q₂ hQ hside A B hA hB w₁ w₂ hw₁ hw₂ τ hL row hr
    · exact Q₁.parallel_count hQ A hA hg₁ w₁ (Q₁.descendant row.1).center
        hw₁ hδ hwidth₁ htest₁
    · exact Q₂.parallel_count (hside.symm ▸ hQ) B hB hg₂ w₂ (Q₂.descendant row.2).center
        hw₂ hδ hwidth₂ htest₂
  · have hz : S.filter (eligibleDyadicEdge Q₁ Q₂ A B w₁ w₂ τ row) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro col _ h
      exact hr h.1
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EligibilityExcision
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing all ineligible cell terms from the exact expansion

The exceptional angular sets are chosen before the radial frequency.
Consequently the finite whole-cell decision is valid in the full product
integral and never truncates an angular support by a nonsmooth test.
-/

namespace Falconer
open Set MeasureTheory MeasureTheory.Measure
attribute [local instance] Classical.propDecidable

theorem capIncidence_nonneg {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ) (hη : ∀ w, 0 ≤ η w) :
    0 ≤ capIncidence ρ η b :=
  integral_nonneg (fun w => mul_nonneg (hη w) (integral_nonneg (fun _ => sq_nonneg _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_IneligibleCapTerms
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing of individual ineligible original cap terms

One null set is chosen before frequency. This permits arbitrary whole-cell
edge decisions in the finite graph without introducing angular cutoffs.
-/

namespace Falconer
open Set MeasureTheory MeasureTheory.Measure

theorem DyadicCube.ineligible_transform_ae_zero {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (j : ℕ) (M : ℝ)
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B : ℝ} (hB : 0 ≤ B) (hηB : ∀ w, η w ≤ 1) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (p : List (Fin d → Bool)) (hp : p ∈ Q.occupiedPaths μ j)
    (he : p ∉ Q.eligiblePaths μ j η b) :
    ∀ᵐ w ∂sphereMeasure d, ∀ r, η w ≠ 0 →
      endpointTransform (μ.restrict (Q.descendant p).carrier) M b r w = 0 := by
  have hz : capIncidence (μ.restrict (Q.descendant p).carrier) η b = 0 := by
    apply le_antisymm _ (capIncidence_nonneg _ η b hη)
    apply le_of_not_gt
    intro hpos
    exact he (Finset.mem_filter.mpr ⟨hp,hpos⟩)
  have hzero := capIncidence_zero_transform (μ.restrict (Q.descendant p).carrier)
    η hηm hη b hb zero_le_one hB hηB hbB hz M
  filter_upwards [hzero] with w hw
  intro r hne
  exact hw (lt_of_le_of_ne (hη w) (Ne.symm hne)) r

theorem angularProduct_ae_first {d : ℕ} {v : ℝ} {Ψ : ℝ → ℝ}
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {p : Sphere d → Prop} (hp : ∀ᵐ w ∂sphereMeasure d, p w) :
    ∀ᵐ z ∂angularProductMeasure d v Ψ, p z.2.1 :=
  quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_fst.ae hp)

theorem angularProduct_ae_second {d : ℕ} {v : ℝ} {Ψ : ℝ → ℝ}
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {p : Sphere d → Prop} (hp : ∀ᵐ w ∂sphereMeasure d, p w) :
    ∀ᵐ z ∂angularProductMeasure d v Ψ, p z.2.2 :=
  quasiMeasurePreserving_snd.ae (quasiMeasurePreserving_snd.ae hp)

theorem dyadicCapIntegrand_star {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ) (b c : Space d → Sphere d → ℂ)
    (η θ : Sphere d → ℝ) (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (z : ℝ × (Sphere d × Sphere d)) :
    star (dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col z) =
      dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ col row z := by
  simp only [dyadicCapIntegrand,star_smul,star_mul,star_star]
  congr 1
  exact mul_comm _ _

theorem dyadicCapIntegrand_row_ineligible {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (j : ℕ) (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hηm : Measurable η) (hθm : Measurable θ)
    (hη : ∀ w, 0 ≤ η w) (hθ : ∀ w, 0 ≤ θ w)
    (hηB : ∀ w, η w ≤ 1) (hθB : ∀ w, θ w ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hrow : row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j)
    (he : row ∉ Q₁.eligiblePaths μ j η b ×ˢ Q₂.eligiblePaths ν j θ c) :
    dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col =ᵐ[angularProductMeasure d v Ψ] 0 := by
  classical
  rw [Finset.mem_product,not_and_or] at he
  rcases he with hfirst | hsecond
  · have hz := angularProduct_ae_first (v := v) (Ψ := Ψ)
      (Q₁.ineligible_transform_ae_zero μ j M₁ η hηm hη b hb hB hηB hbB row.1
        (Finset.mem_product.mp hrow).1 hfirst)
    filter_upwards [hz] with z hz
    by_cases hzero : η z.2.1 = 0
    · simp [dyadicCapIntegrand,hzero]
    · simp [dyadicCapIntegrand,dyadicPairTransform,hz z.1 hzero]
  · have hz := angularProduct_ae_second (v := v) (Ψ := Ψ)
      (Q₂.ineligible_transform_ae_zero ν j M₂ θ hθm hθ c hc hB hθB hcB row.2
        (Finset.mem_product.mp hrow).2 hsecond)
    filter_upwards [hz] with z hz
    by_cases hzero : θ z.2.2 = 0
    · simp [dyadicCapIntegrand,hzero]
    · simp [dyadicCapIntegrand,dyadicPairTransform,hz z.1 hzero]

theorem dyadicCapIntegrand_col_ineligible {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (j : ℕ) (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hηm : Measurable η) (hθm : Measurable θ)
    (hη : ∀ w, 0 ≤ η w) (hθ : ∀ w, 0 ≤ θ w)
    (hηB : ∀ w, η w ≤ 1) (hθB : ∀ w, θ w ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hcol : col ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j)
    (he : col ∉ Q₁.eligiblePaths μ j η b ×ˢ Q₂.eligiblePaths ν j θ c) :
    dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col =ᵐ[angularProductMeasure d v Ψ] 0 := by
  have hz := dyadicCapIntegrand_row_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c hb hc
    η θ hηm hθm hη hθ hηB hθB hB hbB hcB col row hcol he
  filter_upwards [hz] with z hz
  rw [← dyadicCapIntegrand_star,hz]
  exact star_zero _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrated estimate for the actual retained dyadic graph

This is the positive Schur step after localization. It uses the two
original restricted laws and retains their endpoint symbols on every
child. Summing the angular partition introduces no cap-count factor.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem retained_dyadic_energy_bound {d n g₁ g₂ L C₁ C₂ : ℕ} {κ : Type*}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (K : Finset κ) (η : κ → Sphere d → ℝ) (center : κ → Sphere d)
    (hη : ∀ k ∈ K, ∀ w, 0 ≤ η k w)
    (hpartition : ∀ w, ∑ k ∈ K, η k w = 1)
    {δ τ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ k ∈ K, ∀ w, 0 < η k w → ‖(w : Space d)-center k‖ ≤ δ)
    (hg₁ : g₁ ≤ n) (hg₂ : g₂ ≤ n)
    (hL : 4*τ*((2 : ℝ)^n/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (hsupport₁ : ∀ p ∈ Q₁.occupiedPaths μ n,
      ∀ᵐ x ∂μ.restrict (Q₁.descendant p).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ n) g₁ p (w : Space d) W₁ C₁)
    (hsupport₂ : ∀ p ∈ Q₂.occupiedPaths ν n,
      ∀ᵐ x ∂ν.restrict (Q₂.descendant p).carrier,
        ∀ w : Sphere d, c x w ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν n) g₂ p (w : Space d) W₂ C₂)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      ‖∫ z, ∑ k ∈ K ×ˢ K, (η k.1 z.2.1 * η k.2 z.2.2) •
        (∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          if eligibleDyadicEdge Q₁ Q₂
              (Q₁.eligiblePaths μ n (η k.1) b) (Q₂.eligiblePaths ν n (η k.2) c)
              (center k.1) (center k.2) τ row col then
            dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
              star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z) else 0)
        ∂angularProductMeasure d v Ψ‖ ≤
    (2 : ℝ)^((d : ℝ)*(p-a)) *
      ((2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) : ℕ) *
      ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2)
          (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2) := by
  let S := Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ n (η k.1) b) (Q₂.eligiblePaths ν n (η k.2) c)
    (center k.1) (center k.2) τ
  let D : ℕ := (2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂))
  have hlen₁ : ∀ q ∈ Q₁.occupiedPaths μ n, q.length = n := by
    intro q hq
    exact (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1
  have hlen₂ : ∀ q ∈ Q₂.occupiedPaths ν n, q.length = n := by
    intro q hq
    exact (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1
  have hdegree (k : κ × κ) (hk : k ∈ K ×ˢ K)
      (row : List (Fin d → Bool) × List (Fin d → Bool)) :
      (S.filter (G k row)).card ≤ D := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    apply eligibleDyadic_degree Q₁ Q₂ hQ hside _ _
      (fun q hq => hlen₁ q (Q₁.eligiblePaths_subset μ n (η k.1) b hq))
      (fun q hq => hlen₂ q (Q₂.eligiblePaths_subset ν n (η k.2) c hq))
      hg₁ hg₂ _ _ (sphere_norm _) (sphere_norm _) hδ hL hwidth₁ hwidth₂
    · exact Q₁.eligiblePaths_witnesses μ (η k.1) b (center k.1) δ W₁
        (hη k.1 hk₁) (hcap k.1 hk₁) hsupport₁
    · exact Q₂.eligiblePaths_witnesses ν (η k.2) c (center k.2) δ W₂
        (hη k.2 hk₂) (hcap k.2 hk₂) hsupport₂
  have hcolumn (k : κ × κ) (hk : k ∈ K ×ˢ K)
      (col : List (Fin d → Bool) × List (Fin d → Bool)) :
      (S.filter (fun row => G k row col)).card ≤ D := by
    have he : S.filter (fun row => G k row col) = S.filter (G k col) := by
      apply Finset.filter_congr
      intro row _
      exact eligibleDyadicEdge_symm Q₁ Q₂ _ _ _ _ τ row col
    rw [he]
    exact hdegree k hk col
  let U := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    fun z : ℝ × Sphere d =>
      endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2
  let V := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    fun z : ℝ × Sphere d =>
      endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2
  let bound₁ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    B * (μ.restrict (Q₁.descendant row.1).carrier).real Set.univ / M₁
  let bound₂ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    C * (ν.restrict (Q₂.descendant row.2).carrier).real Set.univ / M₂
  have hs := independentAngularEnergy_graph_schur p v Ψ S (K ×ˢ K) G U V
    (fun _ _ => measurable_endpointTransform _ _ _ hb)
    (fun _ _ => measurable_endpointTransform _ _ _ hc)
    bound₁ bound₂ (fun _ _ => by dsimp [bound₁]; positivity)
    (fun _ _ => by dsimp [bound₂]; positivity)
    (fun _ _ z => endpointTransform_norm_le _ hM₁ b hbB z.1 z.2)
    (fun _ _ z => endpointTransform_norm_le _ hM₂ c hcC z.1 z.2)
    (fun k z => η k.1 z.2.1 * η k.2 z.2.2) D
    (fun z k hk => mul_nonneg (hη k.1 (Finset.mem_product.mp hk).1 z.2.1)
      (hη k.2 (Finset.mem_product.mp hk).2 z.2.2))
    (fun z => by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, hpartition, hpartition, one_mul])
    (fun k hk row _ => by exact_mod_cast hdegree k hk row)
    (fun k hk col _ => by exact_mod_cast hcolumn k hk col)
  have hexp : (2 : ℝ)^((d : ℝ)*(v-a)) =
      (2 : ℝ)^((d : ℝ)*(p-a)) * (2 : ℝ)^((d : ℝ)*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hexp]
  simpa only [mul_assoc, S, G, U, V, D, dyadicPairTransform, angularProductMeasure] using
    mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by norm_num) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicEnergyStep
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From integrated localization to the original independent energy

This is the algebraic assembly step: exact original-law splitting, the
actual cap partition, integrated localization, and the proved Schur bound.
The localization premise is supplied by `dyadic_localization_error`.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem independentAngularEnergy_of_localization
    {d j g₁ g₂ L C₁ C₂ : ℕ} {κ : Type*}
    (Q₁ Q₂ : DyadicCube d) (hQ : 0 < Q₁.side) (hside : Q₂.side = Q₁.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (K : Finset κ) (η : κ → Sphere d → ℝ) (center : κ → Sphere d)
    (hη : ∀ k ∈ K, ∀ w, 0 ≤ η k w)
    (hpartition : ∀ w, ∑ k ∈ K, η k w = 1)
    {δ τ W₁ W₂ : ℝ} (hδ : 0 ≤ δ)
    (hcap : ∀ k ∈ K, ∀ w, 0 < η k w → ‖(w : Space d)-center k‖ ≤ δ)
    (hg₁ : g₁ ≤ j) (hg₂ : g₂ ≤ j)
    (hL : 4*τ*((2 : ℝ)^j/Q₁.side) ≤ L)
    (hwidth₁ : 2*τ+2*δ*(Real.sqrt d*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁)
    (hwidth₂ : 2*τ+2*δ*(Real.sqrt d*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂)
    (hsupport₁ : ∀ q ∈ Q₁.occupiedPaths μ j,
      ∀ᵐ x ∂μ.restrict (Q₁.descendant q).carrier,
        ∀ w : Sphere d, b x w ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ j) g₁ q (w : Space d) W₁ C₁)
    (hsupport₂ : ∀ q ∈ Q₂.occupiedPaths ν j,
      ∀ᵐ x ∂ν.restrict (Q₂.descendant q).carrier,
        ∀ w : Sphere d, c x w ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν j) g₂ q (w : Space d) W₂ C₂)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {ε : ℝ}
    (herror :
      let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
      let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
        (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
        (center k.1) (center k.2) τ
      let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν Mp₁ Mp₂ b c (η k.1) (η k.2)
      ‖(∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z ∂angularProductMeasure d v Ψ) -
        (∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
          if G k row col then F k row col z else 0 ∂angularProductMeasure d v Ψ)‖ ≤ ε) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) ≤
    ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
      ((2 : ℝ)^((d : ℝ)*(p-a)) *
        ((2*L+1)^d * min (C₁*2^(d*g₁)) (C₂*2^(d*g₂)) : ℕ) *
        ∑ row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j,
          independentAngularEnergy p v Ψ
            (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) Mp₁ b z.1 z.2)
            (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) Mp₂ c z.1 z.2)) +
      (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*ε := by
  let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
    (center k.1) (center k.2) τ
  let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν Mp₁ Mp₂ b c (η k.1) (η k.2)
  let full := ∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z
    ∂angularProductMeasure d v Ψ
  let kept := ∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
    if G k row col then F k row col z else 0 ∂angularProductMeasure d v Ψ
  have hfull : independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) =
      (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*‖full‖ := by
    rw [independentAngularEnergy_dyadic_expansion Q₁ Q₂ μ ν j a v Ψ
      Ma₁ Ma₂ Mp₁ Mp₂ hMa₁ hMa₂ hMp₁.ne' hMp₂.ne' b c hb hc hB hB hbB hcB]
    rw [integrated_cap_cross_expansion S K η hpartition]
    rfl
  have hkept : kept = ∫ z, ∑ k ∈ K ×ˢ K, (η k.1 z.2.1*η k.2 z.2.2) •
      (∑ row ∈ S, ∑ col ∈ S, if G k row col then
        dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c row z *
        star (dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c col z) else 0)
      ∂angularProductMeasure d v Ψ := by
    apply integral_congr_ae
    filter_upwards with z
    simp only [F,dyadicCapIntegrand,Finset.smul_sum,smul_ite,smul_zero]
  have hret := retained_dyadic_energy_bound Q₁ Q₂ hQ hside μ ν Mp₁ Mp₂ hMp₁ hMp₂
    b c hb hc hB hB hbB hcB K η center hη hpartition hδ hcap hg₁ hg₂ hL
    hwidth₁ hwidth₂ hsupport₁ hsupport₂ a p v Ψ
  change (2 : ℝ)^((d : ℝ)*(v-a))*‖_‖ ≤ _ at hret
  rw [← hkept] at hret
  have he : ‖full-kept‖ ≤ ε := herror
  have hnorm : ‖full‖ ≤ ‖kept‖+ε := by
    calc
      _ = ‖kept+(full-kept)‖ := by congr 1; abel
      _ ≤ ‖kept‖+‖full-kept‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl he
  rw [hfull]
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*(‖kept‖+ε) := by gcongr
    _ = ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*((2 : ℝ)^((d : ℝ)*(v-a))*‖kept‖) +
        (2 : ℝ)^((d : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2*ε := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hret (sq_nonneg _)) le_rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicFailedTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All failed geometric tests for an original cell pair

For probability starting laws the four restricted masses are at most one.
Each discarded edge fails one of the two perpendicular tests or the
longitudinal test. The estimate below is derived from those three cases.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem four_restrictions_mass_le_one {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s₁ s₂ : Set X) (t₁ t₂ : Set Y) :
    (((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂))).real univ ≤ 1 := by
  have hle : ((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂)) ≤ (μ.prod μ).prod (ν.prod ν) :=
    Measure.prod_mono (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
  have ht : (((μ.restrict s₁).prod (μ.restrict s₂)).prod
      ((ν.restrict t₁).prod (ν.restrict t₂))) univ ≤ 1 := by
    simpa using hle univ
  exact (ENNReal.toReal_mono (by simp) ht).trans_eq (by simp)

theorem dyadic_failed_tests_bound
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (row col : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)),
      row.1.length = j → col.1.length = j → row.2.length = j → col.2.length = j →
      ∀ R : ℝ, 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (M₁ M₂ : ℝ), 0 < M₁ → 0 < M₂ →
      ∀ (w₁ w₂ : Sphere (n+2)) (η θ : Sphere (n+2) → ℝ),
      ChartCapControl m η (w₁ : Space (n+2)) δ H →
      ChartCapControl m θ (w₂ : Space (n+2)) δ H →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ¬retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ row col →
      ‖endpointCapCrossTerm (μ.restrict (Q₁.descendant row.1).carrier)
        (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
        (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ b b c c η θ‖ ≤
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
          (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
      |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
        ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T)) := by
  obtain ⟨A,hA,hperp⟩ := dyadic_perpendicular_cross_term hpublished n m hn
  have hz : ∀ t, 4 < t → Ψ t = 0 := by
    intro t ht
    by_contra hne
    exact (not_lt_of_ge (hsupp t hne).2.le) ht
  obtain ⟨C,hC,hlong⟩ := dyadic_longitudinal_cross_term φ Ψ hφ hΨ hpos hzero hW hΨW hz hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j row col hr₁ hc₁ hr₂ hc₂ R hR v τ δ H B D
    hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq M₁ M₂ hM₁ hM₂ w₁ w₂ η θ hη hθ b c hb hc hbad
  let EP := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
      (16*D/((2 : ℝ)^v*τ))^m*(4*W)
  let EL := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))
  have hEP : 0 ≤ EP := by dsimp [EP]; positivity
  have hEL : 0 ≤ EL := by dsimp [EL]; positivity
  have herr' : 2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+
      8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/2 := by linarith
  have hbad' : ¬retainedDyadicEdge Q₁ Q₂ w₁ w₂ τ col row :=
    fun he => hbad ((retainedDyadicEdge_symm Q₁ Q₂ w₁ w₂ τ row col).mpr he)
  by_cases hfirst : ‖perpendicularPart (w₁ : Space (n+2))
      ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)‖ ≤ τ
  · by_cases hsecond : ‖perpendicularPart (w₂ : Space (n+2))
        ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)‖ ≤ τ
    · have hthird : τ < |inner ℝ (w₁ : Space (n+2))
          ((Q₁.descendant row.1).center-(Q₁.descendant col.1).center)+
          inner ℝ (w₂ : Space (n+2))
          ((Q₂.descendant row.2).center-(Q₂.descendant col.2).center)| := by
        apply lt_of_not_ge
        intro hle
        exact hbad' ⟨hfirst,hsecond,hle⟩
      have he := hlong Q₁ Q₂ hQ (hside.symm ▸ hQ) μ ν j row col hr₁ hc₁ hr₂ hc₂
        R hR v τ δ hδ.le hfreq (by rw [hside]; linarith) w₁ w₂ hthird
        η θ hη.measurable hθ.measurable hη.bound hθ.bound hη.support hθ.support
        b c hb.measurable hc.measurable B hB hb.bound hc.bound M₁ M₂
      have hmass := four_restrictions_mass_le_one μ ν
        (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
        (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
      apply he.trans
      calc
        _ = EL * (((μ.restrict (Q₁.descendant row.1).carrier).prod
          (μ.restrict (Q₁.descendant col.1).carrier)).prod
          ((ν.restrict (Q₂.descendant row.2).carrier).prod
          (ν.restrict (Q₂.descendant col.2).carrier))).real univ := by dsimp [EL]; ring
        _ ≤ EL := mul_le_of_le_one_right hEL hmass
        _ ≤ EP+EL := le_add_of_nonneg_left hEP
    · have he := hperp Q₂ Q₁ (hside.symm ▸ hQ) ν μ j (row.2,row.1) (col.2,col.1)
        hr₂ hc₂ w₂ τ δ H B D hτ hδ hδsmall hH hB hD hδD
        (by simpa only [hside] using hnorm) (by simpa only [hside] using herr')
        (lt_of_not_ge hsecond) θ η hθ hη.measurable hη.bound c b hc hb.measurable hb.bound
        M₂ M₁ v Ψ hM₂ hM₁ hΨ hsupp W hW hΨW
      have hmass := four_restrictions_mass_le_one ν μ
        (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
        (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
      rw [endpointCapCrossTerm_swap]
      apply he.trans
      calc
        _ = EP * (((ν.restrict (Q₂.descendant row.2).carrier).prod
          (ν.restrict (Q₂.descendant col.2).carrier)).prod
          ((μ.restrict (Q₁.descendant row.1).carrier).prod
          (μ.restrict (Q₁.descendant col.1).carrier))).real univ := by
            dsimp [EP]
            rw [mul_comm (M₂⁻¹*M₂⁻¹) (M₁⁻¹*M₁⁻¹)]
            ring
        _ ≤ EP := mul_le_of_le_one_right hEP hmass
        _ ≤ EP+EL := le_add_of_nonneg_right hEL
  · have he := hperp Q₁ Q₂ hQ μ ν j row col hr₁ hc₁ w₁ τ δ H B D
      hτ hδ hδsmall hH hB hD hδD hnorm herr' (lt_of_not_ge hfirst) η θ
      hη hθ.measurable hθ.bound b c hb hc.measurable hc.bound M₁ M₂ v Ψ hM₁ hM₂ hΨ hsupp W hW hΨW
    have hmass := four_restrictions_mass_le_one μ ν
      (Q₁.descendant row.1).carrier (Q₁.descendant col.1).carrier
      (Q₂.descendant row.2).carrier (Q₂.descendant col.2).carrier
    apply he.trans
    calc
      _ = EP * (((μ.restrict (Q₁.descendant row.1).carrier).prod
        (μ.restrict (Q₁.descendant col.1).carrier)).prod
        ((ν.restrict (Q₂.descendant row.2).carrier).prod
        (ν.restrict (Q₂.descendant col.2).carrier))).real univ := by dsimp [EP]; ring
      _ ≤ EP := mul_le_of_le_one_right hEP hmass
      _ ≤ EP+EL := le_add_of_nonneg_right hEL

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalizationSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summing integrated nonstationary errors

An edge is removed only after its whole oscillatory integral has been
estimated. The cardinality loss is explicit and can be absorbed by the
arbitrary power gain. No pointwise angular truncation is introduced.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem integrated_discarded_sum_bound {X ι κ : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
    (T : κ → ι → ι → X → ℂ)
    (hT : ∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, Integrable (T k i j) μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ k ∈ K, ∀ i ∈ S, ∀ j ∈ S, ¬G k i j → ‖∫ x, T k i j x ∂μ‖ ≤ ε) :
    ‖(∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, T k i j x ∂μ) -
      (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S,
        if G k i j then T k i j x else 0 ∂μ)‖ ≤ (K.card : ℝ)*S.card*S.card*ε := by
  classical
  have hfull : (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, T k i j x ∂μ) =
      ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, ∫ x, T k i j x ∂μ := by
    rw [integral_finsetSum _ (fun k hk =>
      integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (hT k hk i hi)))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hT k hk i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ (hT k hk i hi)
  have hpart (k : κ) (hk : k ∈ K) (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      Integrable (fun x => if G k i j then T k i j x else 0) μ := by
    by_cases h : G k i j
    · simpa only [ite_eq_left h] using hT k hk i hi j hj
    · simp only [ite_eq_right h]
      exact integrable_zero _ _ _
  have hkept : (∫ x, ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S,
        if G k i j then T k i j x else 0 ∂μ) =
      ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, if G k i j then (∫ x, T k i j x ∂μ) else 0 := by
    rw [integral_finsetSum _ (fun k hk =>
      integrable_finsetSum _ (fun i hi => integrable_finsetSum _ (hpart k hk i hi)))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hpart k hk i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (hpart k hk i hi)]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hfull,hkept,← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ K, ∑ i ∈ S, ∑ j ∈ S, ε := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : G k i j
      · simpa only [ite_eq_left h,sub_self,norm_zero] using hε
      · simpa only [ite_eq_right h,sub_zero] using herr k hk i hi j hj h
    _ = _ := by simp [mul_assoc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLocalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization of the full original dyadic graph expansion

The discarded-term estimate is derived from the actual three geometric
tests. Ineligible original cell--cap terms vanish. Every remaining error
is estimated only after its complete angular and radial integration.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
attribute [local instance] Classical.propDecidable

theorem dyadic_localization_error
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (R : ℝ), 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (M₁ M₂ : ℝ), 0 < M₁ → 0 < M₂ →
      ∀ {κ : Type*} (K : Finset κ) (w : κ → Sphere (n+2)) (η : κ → Sphere (n+2) → ℝ),
      (∀ k ∈ K, ChartCapControl m (η k) (w k : Space (n+2)) δ H) →
      (∀ k ∈ K, ∀ z, 0 ≤ η k z) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
      let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
        (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
        (w k.1) (w k.2) τ
      let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c (η k.1) (η k.2)
      ‖(∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S, F k row col z ∂angularProductMeasure (n+2) v Ψ) -
        (∫ z, ∑ k ∈ K ×ˢ K, ∑ row ∈ S, ∑ col ∈ S,
          if G k row col then F k row col z else 0 ∂angularProductMeasure (n+2) v Ψ)‖ ≤
        (K.card : ℝ)^2*(S.card : ℝ)^2 *
        (|(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
          (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
            (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
        |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
          ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))) := by
  obtain ⟨A,C,hA,hC,hfailed⟩ := dyadic_failed_tests_bound hpublished n m hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq M₁ M₂ hM₁ hM₂ κ K w η hcap hη b c hb hc _
  dsimp only
  let S := Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j
  let G := fun k : κ × κ => eligibleDyadicEdge Q₁ Q₂
    (Q₁.eligiblePaths μ j (η k.1) b) (Q₂.eligiblePaths ν j (η k.2) c)
    (w k.1) (w k.2) τ
  let F := fun k : κ × κ => dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c (η k.1) (η k.2)
  let ε := |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
    (A*(4^m*H*B*B)*(B*B)*(sphereMeasure (n+2)).real univ) *
      (16*D/((2 : ℝ)^v*τ))^m*(4*W) +
    |(M₁⁻¹*M₁⁻¹)*(M₂⁻¹*M₂⁻¹)| *
      ((B*B)*(B*B)*C*((sphereMeasure (n+2)).real univ)^2*R^(-T))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hi (k : κ × κ) (hk : k ∈ K ×ˢ K) (row : _) (_hr : row ∈ S)
      (col : _) (_hc : col ∈ S) : Integrable (F k row col) (angularProductMeasure (n+2) v Ψ) := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    exact dyadicCapIntegrand_integrable Q₁ Q₂ μ ν M₁ M₂ v Ψ hM₁ hM₂ b c
      hb.measurable hc.measurable (η k.1) (η k.2) (hcap k.1 hk₁).measurable
      (hcap k.2 hk₂).measurable (hcap k.1 hk₁).bound (hcap k.2 hk₂).bound
      hB hb.bound hc.bound row col
  have he (k : κ × κ) (hk : k ∈ K ×ˢ K) (row : _) (hr : row ∈ S)
      (col : _) (hcol : col ∈ S) (hbad : ¬G k row col) :
      ‖∫ z, F k row col z ∂angularProductMeasure (n+2) v Ψ‖ ≤ ε := by
    obtain ⟨hk₁,hk₂⟩ := Finset.mem_product.mp hk
    have hη₁ := hcap k.1 hk₁
    have hη₂ := hcap k.2 hk₂
    have hηB₁ : ∀ z, η k.1 z ≤ 1 := fun z => (le_abs_self _).trans (hη₁.bound z)
    have hηB₂ : ∀ z, η k.2 z ≤ 1 := fun z => (le_abs_self _).trans (hη₂.bound z)
    by_cases hrow : row ∈ Q₁.eligiblePaths μ j (η k.1) b ×ˢ Q₂.eligiblePaths ν j (η k.2) c
    · by_cases hcol' : col ∈ Q₁.eligiblePaths μ j (η k.1) b ×ˢ Q₂.eligiblePaths ν j (η k.2) c
      · have hg : ¬retainedDyadicEdge Q₁ Q₂ (w k.1) (w k.2) τ row col :=
          fun h => hbad ⟨hrow,hcol',h⟩
        have hlen₁ (p : _) (hp : p ∈ Q₁.occupiedPaths μ j) : p.length = j :=
          (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
        have hlen₂ (p : _) (hp : p ∈ Q₂.occupiedPaths ν j) : p.length = j :=
          (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
        dsimp only [F]
        rw [integral_dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ v Ψ hM₁ hM₂ b c
          hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
          hη₁.bound hη₂.bound hB hb.bound hc.bound]
        exact hfailed Q₁ Q₂ hQ hside μ ν j row col
          (hlen₁ _ (Finset.mem_product.mp hr).1) (hlen₁ _ (Finset.mem_product.mp hcol).1)
          (hlen₂ _ (Finset.mem_product.mp hr).2) (hlen₂ _ (Finset.mem_product.mp hcol).2)
          R hR v τ δ H B D hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq
          M₁ M₂ hM₁ hM₂ (w k.1) (w k.2) (η k.1) (η k.2) hη₁ hη₂ b c hb hc hg
      · have hz := dyadicCapIntegrand_col_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c
          hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
          (hη k.1 hk₁) (hη k.2 hk₂) hηB₁ hηB₂ hB hb.bound hc.bound row col hcol hcol'
        rw [integral_congr_ae hz]
        simpa only [Pi.zero_apply,integral_zero,norm_zero] using hε
    · have hz := dyadicCapIntegrand_row_ineligible Q₁ Q₂ μ ν j M₁ M₂ v Ψ b c
        hb.measurable hc.measurable (η k.1) (η k.2) hη₁.measurable hη₂.measurable
        (hη k.1 hk₁) (hη k.2 hk₂) hηB₁ hηB₂ hB hb.bound hc.bound row col hr hrow
      rw [integral_congr_ae hz]
      simpa only [Pi.zero_apply,integral_zero,norm_zero] using hε
  have hmain := integrated_discarded_sum_bound (angularProductMeasure (n+2) v Ψ)
    S (K ×ˢ K) G F hi hε he
  dsimp only [S,ε] at hmain
  convert hmain using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.card_product,Nat.cast_mul]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizedCellCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

theorem RegularizedProfileData.descendant_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X : CellPath d) (hX : X.length = a) :
    (((Q.descendant X).occupiedPaths ρ (p-a)).card : ℝ) ≤
      ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) := by
  let := h.probability
  let R := (2:ℝ)^N
  let ℓ := ((d:ℝ)+1)*lam
  let lo := R^(-ℓ-m ((p:ℝ)/N))
  let S := (Q.descendant X).occupiedPaths ρ (p-a)
  have hlo : 0 < lo := by dsimp [lo,R]; positivity
  have hmass (z : CellPath d) (hz : z ∈ S) :
      lo ≤ (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    have hz' : z ∈ cubePaths d (p-a) ∧
        0 < ρ ((Q.descendant X).descendant z).carrier := by
      simpa only [S,DyadicCube.occupiedPaths,Finset.mem_filter] using hz
    obtain ⟨hz,hpos⟩ := hz'
    have hlen : (X++z).length = p := by
      simp only [List.length_append,hX,(mem_cubePaths _ _ _).mp hz]
      omega
    have hh := (h.cells p hp (X++z) hlen
      (by simpa only [Q.descendant_append] using hpos)).1
    simpa only [Q.descendant_append,lo,R,ℓ,sub_eq_add_neg,neg_mul,
      Real.rpow_add (by positivity : 0 < (2:ℝ)^N)] using hh
  have he : ρ (Q.descendant X).carrier =
      ∑ z ∈ S, ρ ((Q.descendant X).descendant z).carrier := by
    have hh := congrArg (fun ν : Measure (Space d) => ν univ)
      ((Q.descendant X).restrict_occupiedPaths ρ (p-a))
    simpa only [Measure.restrict_apply_univ,Measure.finsetSum_apply,S] using hh
  have hr : (ρ (Q.descendant X).carrier).toReal =
      ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    rw [he,ENNReal.toReal_sum]
    intro z _
    exact measure_ne_top ρ _
  have hc : (S.card:ℝ)*lo ≤ R^(ℓ-m ((a:ℝ)/N)) := by
    calc
      _ = ∑ _z ∈ S, lo := by simp
      _ ≤ ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal :=
        Finset.sum_le_sum hmass
      _ = (ρ (Q.descendant X).carrier).toReal := hr.symm
      _ ≤ _ := h.cell_mass_upper (hap.trans hp) X hX
  apply (le_div_iff₀ hlo).mpr at hc
  apply hc.trans_eq
  dsimp only [lo,R,ℓ]
  rw [← Real.rpow_sub (by positivity)]
  congr 1
  ring

theorem RegularizedProfileData.pair_count_two {Q₁ Q₂ : DyadicCube d}
    {ρ₁ ρ₂ : Measure (Space d)} {N : ℕ} {s₁ s₂ lam : ℝ} {m₁ m₂ : ℝ → ℝ}
    (h₁ : RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁)
    (h₂ : RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : CellPath d) (hX : X.length = a) (hY : Y.length = a) :
    ((((Q₁.descendant X).occupiedPaths ρ₁ (p-a)) ×ˢ
      ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))).card : ℝ) ≤
      ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+
        (m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ ((2:ℝ)^N)^(m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) *
        ((2:ℝ)^N)^(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) :=
      mul_le_mul (h₁.descendant_count hap hp X hX) (h₂.descendant_count hap hp Y hY)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphEnergyEstimate
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph energy estimate before profile normalization

This assembles the exact splitting, proved localization and retained
Schur bound. All endpoint symbols, including reached anchor masks, remain
unchanged on children. The numerical error is explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_graph_energy_step
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), 0 < Q₁.side → Q₂.side = Q₁.side →
      ∀ (μ ν : Measure (Space (n+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (j : ℕ) (R : ℝ), 1 ≤ R → ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*Q₁.side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^j)+8*δ*(Real.sqrt (n+2 : ℕ)*Q₁.side) ≤ τ/4 →
      4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (Ma₁ Ma₂ Mp₁ Mp₂ a p : ℝ), 0 < Ma₁ → 0 < Ma₂ → 0 < Mp₁ → 0 < Mp₂ →
      ∀ {κ : Type*} (K : Finset κ) (w : κ → Sphere (n+2)) (η : κ → Sphere (n+2) → ℝ),
      (∀ k ∈ K, ChartCapControl m (η k) (w k : Space (n+2)) δ H) →
      (∀ k ∈ K, ∀ z, 0 ≤ η k z) → (∀ z, ∑ k ∈ K, η k z = 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl m b B D → ChartSymbolControl m c B D →
      ∀ (g₁ g₂ L C₁ C₂ : ℕ), g₁ ≤ j → g₂ ≤ j →
      4*τ*((2 : ℝ)^j/Q₁.side) ≤ L →
      ∀ W₁ W₂ : ℝ,
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.side/(2 : ℝ)^g₁)) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*(Q₂.side/(2 : ℝ)^g₂)) ≤ W₂ →
      (∀ q ∈ Q₁.occupiedPaths μ j, ∀ᵐ x ∂μ.restrict (Q₁.descendant q).carrier,
        ∀ z : Sphere (n+2), b x z ≠ 0 →
          DyadicParallelTest Q₁ (Q₁.occupiedPaths μ j) g₁ q (z : Space (n+2)) W₁ C₁) →
      (∀ q ∈ Q₂.occupiedPaths ν j, ∀ᵐ x ∂ν.restrict (Q₂.descendant q).carrier,
        ∀ z : Sphere (n+2), c x z ≠ 0 →
          DyadicParallelTest Q₂ (Q₂.occupiedPaths ν j) g₂ q (z : Space (n+2)) W₂ C₂) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
        (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) ≤
      ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
        ((2 : ℝ)^(((n+2 : ℕ) : ℝ)*(p-a)) *
          ((2*L+1)^(n+2) * min (C₁*2^((n+2)*g₁)) (C₂*2^((n+2)*g₂)) : ℕ) *
          ∑ row ∈ Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j,
            independentAngularEnergy p v Ψ
              (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) Mp₁ b z.1 z.2)
              (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) Mp₂ c z.1 z.2)) +
        (2 : ℝ)^(((n+2 : ℕ) : ℝ)*(v-a))*((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
          capGraphError (n+2) m A C W R T Mp₁ Mp₂ H B D v τ K.card
            (Q₁.occupiedPaths μ j ×ˢ Q₂.occupiedPaths ν j).card := by
  obtain ⟨A,C,hA,hC,hloc⟩ := dyadic_localization_error hpublished n m hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ hside μ ν _ _ j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq Ma₁ Ma₂ Mp₁ Mp₂ a p hMa₁ hMa₂ hMp₁ hMp₂
    κ K w η hcap hη hpart b c hb hc g₁ g₂ L C₁ C₂ hg₁ hg₂ hL W₁ W₂ hw₁ hw₂ hs₁ hs₂ _
  apply independentAngularEnergy_of_localization Q₁ Q₂ hQ hside μ ν Ma₁ Ma₂ Mp₁ Mp₂
    hMa₁ hMa₂ hMp₁ hMp₂ b c hb.measurable hc.measurable hB hb.bound hc.bound K η w
    hη hpart hδ.le (fun k hk z hz => (hcap k hk).support z (ne_of_gt hz))
    hg₁ hg₂ hL hw₁ hw₂ hs₁ hs₂ a p v Ψ
  exact hloc Q₁ Q₂ hQ hside μ ν j R hR v τ δ H B D hτ hδ hδsmall
    hH hB hD hδD hnorm herr hfreq Mp₁ Mp₂ hMp₁ hMp₂ K w η hcap hη b c hb hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraphDegree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual graph degree, with its profile cost and dimensional loss -/

namespace Falconer

theorem height_mono_start (A : ℕ → ℝ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p) :
    PlanarFalconer.height A g p ≤ PlanarFalconer.height A a p := by
  obtain ⟨j,hgj,hjp,hj⟩ := PlanarFalconer.intervalMin_attained A hgp
  have hmin := PlanarFalconer.intervalMin_le A (hag.trans hgj) hjp
  unfold PlanarFalconer.height
  rw [hj]
  linarith

theorem profile_graph_degree (d : ℕ) (A : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : 0 ≤ σ) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (hgap : (g:ℝ)-(a:ℝ) ≤ 2*σ*N) :
    (((2*⌈4*((2:ℝ)^N)^(30*σ)⌉₊+1)^d *
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g-a))) : ℕ) : ℝ) ≤
      2*11^d*((2:ℝ)^N)^(PlanarFalconer.height A a p+
        (1000*((d:ℝ)+1)+32*d)*σ) := by
  let R := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hX : 1 ≤ R^(30*σ) := Real.one_le_rpow hR (by positivity)
  have hL : ((2*⌈4*R^(30*σ)⌉₊+1:ℕ):ℝ) ≤ 11*R^(30*σ) := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*R^(30*σ))).le
    push_cast
    linarith
  have hH := height_mono_start A hag hgp
  have hT : 1 ≤ R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ) :=
    Real.one_le_rpow hR (add_nonneg (PlanarFalconer.height_nonneg A hgp) (by positivity))
  have hC : (⌈R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ)⌉₊:ℝ) ≤
      2*R^(PlanarFalconer.height A a p+1000*((d:ℝ)+1)*σ) := by
    calc
      _ ≤ 2*R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ) := by
        have hh := (Nat.ceil_lt_add_one
          (by positivity : 0 ≤ R^(PlanarFalconer.height A g p+1000*((d:ℝ)+1)*σ))).le
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (by norm_num)
  have hg : ((2^(d*(g-a)):ℕ):ℝ) ≤ R^(2*(d:ℝ)*σ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat]
    have he : ((d*(g-a):ℕ):ℝ) = (d:ℝ)*((g:ℝ)-a) := by
      rw [Nat.cast_mul,Nat.cast_sub hag]
    rw [← Real.rpow_natCast,he,← dyadic_rpow_change_base hN]
    apply Real.rpow_le_rpow_of_exponent_le hR
    apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) d)
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_mul]
  apply (mul_le_mul
    (pow_le_pow_left₀ (by positivity) hL d)
    (mul_le_mul hC hg (Nat.cast_nonneg _) (by positivity))
    (by positivity) (by positivity)).trans_eq
  rw [mul_pow]
  have hp : (R^(30*σ))^d = R^(30*(d:ℝ)*σ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hRpos.le]
    congr 1
    ring
  rw [hp]
  calc
    _ = 2*11^d*(R^(30*(d:ℝ)*σ)*
        R^(PlanarFalconer.height A a p+1000*((d:ℝ)+1)*σ)*R^(2*(d:ℝ)*σ)) := by ring
    _ = _ := by rw [← Real.rpow_add hRpos,← Real.rpow_add hRpos]; congr 2; ring

theorem profile_graph_degree_two (d : ℕ) (A₁ A₂ : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {σ : ℝ} (hσ : 0 ≤ σ) {a g₁ g₂ p : ℕ}
    (hag₁ : a ≤ g₁) (hgp₁ : g₁ ≤ p) (hgap₁ : (g₁:ℝ)-(a:ℝ) ≤ 2*σ*N)
    (hag₂ : a ≤ g₂) (hgp₂ : g₂ ≤ p) (hgap₂ : (g₂:ℝ)-(a:ℝ) ≤ 2*σ*N) :
    (((2*⌈4*((2:ℝ)^N)^(30*σ)⌉₊+1)^d * min
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A₁ g₁ p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g₁-a)))
      (⌈((2:ℝ)^N)^(PlanarFalconer.height A₂ g₂ p+1000*((d:ℝ)+1)*σ)⌉₊ *
        2^(d*(g₂-a))) : ℕ) : ℝ) ≤
      2*11^d*((2:ℝ)^N)^(min (PlanarFalconer.height A₁ a p)
        (PlanarFalconer.height A₂ a p)+(1000*((d:ℝ)+1)+32*d)*σ) := by
  by_cases h : PlanarFalconer.height A₁ a p ≤ PlanarFalconer.height A₂ a p
  · rw [min_eq_left h]
    exact (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (min_le_left _ _))).trans
      (profile_graph_degree d A₁ hN hσ hag₁ hgp₁ hgap₁)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (min_le_right _ _))).trans
      (profile_graph_degree d A₂ hN hσ hag₂ hgp₂ hgap₂)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Profile normalization of the retained graph contribution

The sum is over the actual occupied descendants and retains both endpoint
symbols. The degree is the integer degree used in the graph energy estimate.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem two_profile_graph_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℕ) (lam : ℝ) :
    ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
      (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
      ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+
        (m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-((m₁ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m₁ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))-
      ((m₂ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m₂ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hr (m : ℝ → ℝ) : profileModelMass m N p/profileModelMass m N a =
      ((2:ℝ)^N)^(-(m ((p:ℝ)/N)-m ((a:ℝ)/N))) := by
    unfold profileModelMass
    rw [← Real.rpow_sub hR]
    congr 1
    ring
  rw [hr m₁,hr m₂,← Real.rpow_add hR,← Real.rpow_natCast,← Real.rpow_mul hR.le,
    ← dyadic_rpow_change_base hN ((d:ℝ)*((p:ℝ)-a)),
    ← Real.rpow_add hR,← Real.rpow_add hR]
  congr 1
  ring

theorem two_profile_graph_contribution_bound (Q₁ Q₂ : DyadicCube d)
    (ρ₁ ρ₂ : Measure (Space d)) {m₁ m₂ : ℝ → ℝ} {N : ℕ} {s₁ s₂ lam : ℝ}
    (hreg₁ : Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁)
    (hreg₂ : Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂) (hN : 0 < N)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) (b c : Space d → Sphere d → ℂ)
    (degree : ℕ) {K H E : ℝ} (_hK : 0 ≤ K) (hE : 0 ≤ E)
    (hdegree : (degree:ℝ) ≤ K*((2:ℝ)^N)^H)
    (hchild : ∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
        (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
      independentAngularEnergy p v Ψ
        (fun z => endpointTransform
          (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
          (profileModelMass m₁ N p) b z.1 z.2)
        (fun z => endpointTransform
          (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
          (profileModelMass m₂ N p) c z.1 z.2) ≤ E) :
    twoProfileGraphContribution (Q₁.descendant X) (Q₂.descendant Y)
      ρ₁ ρ₂ m₁ m₂ N a p v Ψ b c degree ≤
      K*((2:ℝ)^N)^(-((m₁ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m₁ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))-
        ((m₂ ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m₂ ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+H+4*((d:ℝ)+1)*lam)*E := by
  have hs := Finset.sum_le_sum hchild
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hrows := hreg₁.pair_count_two hreg₂ hap hp X Y hX hY
  have hsum := hs.trans (mul_le_mul_of_nonneg_right hrows hE)
  have hboth : (degree:ℝ) *
      (∑ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
        (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform
            (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform
            (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2)) ≤
      (K*((2:ℝ)^N)^H) *
        (((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E) :=
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg degree)).trans
      (mul_le_mul_of_nonneg_right hdegree (by positivity))
  unfold twoProfileGraphContribution
  calc
    _ = (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a))) * _ := by ring
    _ ≤ (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a))) *
        ((K*((2:ℝ)^N)^H) *
          (((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E)) :=
      mul_le_mul_of_nonneg_left hboth (by positivity)
    _ = K * (((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
        ((2:ℝ)^N)^((m₁ ((p:ℝ)/N)-m₁ ((a:ℝ)/N))+(m₂ ((p:ℝ)/N)-m₂ ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)) *
        ((2:ℝ)^N)^H * E := by ring
    _ = _ := by
      rw [two_profile_graph_prefactor hN,mul_assoc K,← Real.rpow_add (by positivity)]
      congr 2
      ring_nf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraphEstimate
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph estimate with the two actual regularized profiles

This applies the proved oscillatory localization and graph bound, then
inserts the actual occupied-cell counts and integer parallel-test degrees.
The analytic error remains explicit for the separate arbitrary-power budget.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_profile_graph_energy_step_oai
    (hpublished : PublishedGnomonicSurface) (n k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (n+2))) (N : ℕ) (s₁ s₂ lam : ℝ)
        (m₁ m₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂ → 0 < N →
      ∀ (a p g₁ g₂ : ℕ) (σ : ℝ), a ≤ p → p ≤ N → 0 ≤ σ →
      a ≤ g₁ → g₁ ≤ p → (g₁:ℝ)-a ≤ 2*σ*N →
      a ≤ g₂ → g₂ ≤ p → (g₂:ℝ)-a ≤ 2*σ*N →
      ∀ (X Y : List (Fin (n+2) → Bool)), X.length = a → Y.length = a →
      ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(p-a))+
        8*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side) ≤ τ/4 →
      4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ →
      4*τ*((2:ℝ)^(p-a)/(Q₁.descendant X).side) ≤
        (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ) →
      ∀ {ι : Type*} (K : Finset ι) (w : ι → Sphere (n+2))
        (η : ι → Sphere (n+2) → ℝ),
      (∀ j ∈ K, ChartCapControl k (η j) (w j : Space (n+2)) δ H) →
      (∀ j ∈ K, ∀ z, 0 ≤ η j z) → (∀ z, ∑ j ∈ K, η j z = 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl k b B D → ChartSymbolControl k c B D →
      ∀ (W₁ W₂ : ℝ),
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(g₁-a))) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₂.descendant Y).side/(2:ℝ)^(g₂-a))) ≤ W₂ →
      (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
        ∀ᵐ x ∂ρ₁.restrict ((Q₁.descendant X).descendant q).carrier,
        ∀ z : Sphere (n+2), b x z ≠ 0 →
          DyadicParallelTest (Q₁.descendant X) ((Q₁.descendant X).occupiedPaths ρ₁ (p-a))
            (g₁-a) q z W₁
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₁ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        ∀ᵐ x ∂ρ₂.restrict ((Q₂.descendant Y).descendant q).carrier,
        ∀ z : Sphere (n+2), c x z ≠ 0 →
          DyadicParallelTest (Q₂.descendant Y) ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))
            (g₂-a) q z W₂
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₂ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      ∀ E : ℝ, 0 ≤ E →
      (∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
          (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform
            (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform
            (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2) ≤ E) →
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant X).carrier)
          (profileModelMass m₁ N a) b z.1 z.2)
        (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant Y).carrier)
          (profileModelMass m₂ N a) c z.1 z.2) ≤
      2*11^(n+2)*((2:ℝ)^N)^(
        -((m₁ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₁ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))-
        ((m₂ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₂ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))+
        (min (PlanarFalconer.height (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)
          (PlanarFalconer.height (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)+
        (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*σ)+4*(((n+2:ℕ):ℝ)+1)*lam)*E +
      (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError (n+2) k A C W ((2:ℝ)^N) T
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
          ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
            (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card := by
  obtain ⟨A,C,hA,hC,hloc⟩ := dyadic_graph_energy_step hpublished n k hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ N s₁ s₂ lam m₁ m₂ hreg₁ hreg₂ hN
    a p g₁ g₂ σ hap hp hσ hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂ X Y hX hY
    v τ δ H B D hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq hL
    ι K w η hcap hη hpart b c hb hc W₁ W₂ hw₁ hw₂ hs₁ hs₂ _ E hE hchild
  let := hreg₁.probability
  let := hreg₂.probability
  have hside : (Q₂.descendant Y).side = (Q₁.descendant X).side := by
    rw [Q₁.descendant_side,Q₂.descendant_side,hX,hY,hQ₁,hQ₂]
  have hQ : 0 < (Q₁.descendant X).side :=
    Q₁.descendant_side_pos (by rw [hQ₁]; norm_num) X
  have hmass (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  let F₁ : ℕ → ℝ := fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N
  let F₂ : ℕ → ℝ := fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N
  let C₁ := ⌈((2:ℝ)^N)^(PlanarFalconer.height F₁ g₁ p+1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊
  let C₂ := ⌈((2:ℝ)^N)^(PlanarFalconer.height F₂ g₂ p+1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊
  let L := ⌈4*((2:ℝ)^N)^(30*σ)⌉₊
  let degree := (2*L+1)^(n+2) * min (C₁*2^((n+2)*(g₁-a))) (C₂*2^((n+2)*(g₂-a)))
  have hd := profile_graph_degree_two (n+2) F₁ F₂ hN hσ
    hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂
  have hbound := two_profile_graph_contribution_bound Q₁ Q₂ ρ₁ ρ₂ hreg₁ hreg₂ hN
    hap hp X Y hX hY v Ψ b c degree (by positivity) hE hd hchild
  have hraw := hloc (Q₁.descendant X) (Q₂.descendant Y) hQ hside ρ₁ ρ₂
    (p-a) ((2:ℝ)^N) (one_le_pow₀ (by norm_num)) v τ δ H B D
    hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq
    (profileModelMass m₁ N a) (profileModelMass m₂ N a)
    (profileModelMass m₁ N p) (profileModelMass m₂ N p) a p
    (hmass m₁ a) (hmass m₂ a) (hmass m₁ p) (hmass m₂ p)
    K w η hcap hη hpart b c hb hc (g₁-a) (g₂-a) L C₁ C₂
    (Nat.sub_le_sub_right hgp₁ a) (Nat.sub_le_sub_right hgp₂ a)
    hL W₁ W₂ hw₁ hw₂ hs₁ hs₂
  have hadd := add_le_add hbound (le_refl
    ((2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
      ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
      capGraphError (n+2) k A C W ((2:ℝ)^N) T
        (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
        ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
          (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card))
  exact hraw.trans (by simpa only [twoProfileGraphContribution,mul_assoc] using hadd)

end Falconer

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Falconer.dyadic_profile_graph_energy_step_oai.{u_1} := @OAI.Falconer.dyadic_profile_graph_energy_step_oai.{u_1}
