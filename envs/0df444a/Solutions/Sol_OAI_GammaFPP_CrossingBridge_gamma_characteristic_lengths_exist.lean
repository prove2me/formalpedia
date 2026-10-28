-- Prove2me | solution 1 for OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:43.792223+00:00
-- url     : https://prove2.me/submissions/95ddbd69-85d7-4572-9c27-a528338573fb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000
import Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_goodSiteEvent_failure
import Theorems.Thm_OAI_GammaFPP_GammaEnvironment_uniform_shape

section
-- module Solutions.OAIW2_GammaFPP.Compat
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Supports
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem support_le_of_positive_halfspace (μ : E → ℝ) (x f : E →ₗ[ℝ] ℝ) (u : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hfu : f u = μ u)
    (hhalf : ∀ z, 0 < x z → f z ≤ μ z) : ∀ z, f z ≤ μ z := by
  intro z
  let t : ℝ := |x z| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 < x (z + t • u) := by
    simp only [map_add, map_smul, hxu, smul_eq_mul, mul_one]
    dsimp [t]
    linarith [neg_le_abs (x z)]
  have hh := hhalf (z + t • u) hz
  have ha := hadd z (t • u)
  rw [hhom t ht u] at ha
  simp only [map_add, map_smul, smul_eq_mul, hfu] at hh
  linarith

theorem support_from_transverse_subgradient (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ)
    (u e : E) (a : ℝ)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hsub : ∀ t : ℝ, μ u + a * t ≤ μ (u + t • e)) :
    (∀ z, coordinateSupport x r (μ u) a z ≤ μ z) ∧
      coordinateSupport x r (μ u) a u = μ u := by
  have hcontact : coordinateSupport x r (μ u) a u = μ u := by
    simp [hxu, hru]
  refine ⟨support_le_of_positive_halfspace μ x _ u hadd hhom hxu hcontact ?_, hcontact⟩
  intro z hz
  have hrepr : z = x z • (u + (r z / x z) • e) := by
    rw [smul_add, smul_smul]
    have heq : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
    rw [heq]
    exact hcoords z
  have hbound := mul_le_mul_of_nonneg_left (hsub (r z / x z)) (le_of_lt hz)
  have hμ : μ z = x z * μ (u + (r z / x z) • e) := by
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  rw [coordinateSupport_apply, hμ]
  calc
    μ u * x z + a * r z = x z * (μ u + a * (r z / x z)) := by
      field_simp [ne_of_gt hz]
    _ ≤ x z * μ (u + (r z / x z) • e) := hbound

end
end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

theorem extreme_slopes_ordered (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    leftSlope φ ≤ rightSlope φ :=
  hφ.leftDeriv_le_rightDeriv_of_mem_interior (by simp)

theorem subgradient_of_between_slopes (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ)
    (a : ℝ) (hleft : leftSlope φ ≤ a) (hright : a ≤ rightSlope φ) :
    ∀ t, φ 0 + a * t ≤ φ t := by
  intro t
  rcases lt_trichotomy 0 t with ht | rfl | ht
  · have hbound := hφ.rightDeriv_le_slope_of_mem_interior (by simp) (by simp) ht
    have ha : a ≤ (φ t - φ 0) / t := by
      exact le_trans hright (by simpa [rightSlope, slope_def_field] using hbound)
    have := (le_div_iff₀ ht).mp ha
    linarith
  · simp
  · have hbound := hφ.slope_le_leftDeriv_of_mem_interior (by simp) (by simp) ht
    have ha : (φ 0 - φ t) / (0 - t) ≤ a := by
      exact le_trans (by simpa [leftSlope, slope_def_field] using hbound) hleft
    have := (div_le_iff₀ (show 0 < 0 - t by linarith)).mp ha
    linarith

theorem extreme_subgradients (φ : ℝ → ℝ) (hφ : ConvexOn ℝ univ φ) :
    (∀ t, φ 0 + leftSlope φ * t ≤ φ t) ∧
    (∀ t, φ 0 + rightSlope φ * t ≤ φ t) := by
  have horder := extreme_slopes_ordered φ hφ
  exact ⟨subgradient_of_between_slopes φ hφ _ le_rfl horder,
    subgradient_of_between_slopes φ hφ _ horder le_rfl⟩

theorem convex_transverse_profile {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z) :
    ConvexOn ℝ univ (fun t : ℝ => μ (u + t • e)) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  simp only [smul_eq_mul]
  have heq : u + (a * v + b * w) • e = a • (u + v • e) + b • (u + w • e) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm,
      ← add_smul, hab, one_smul, ← add_smul]
  rw [heq]
  exact (hadd _ _).trans_eq (by rw [hhom a ha, hhom b hb])

theorem extreme_supports {E : Type*} [AddCommGroup E] [Module ℝ E]
    (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ) (u e : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e) :
    let φ := fun t : ℝ => μ (u + t • e)
    (∀ z, coordinateSupport x r (μ u) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport x r (μ u) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport x r (μ u) (leftSlope φ) u = μ u ∧
    coordinateSupport x r (μ u) (rightSlope φ) u = μ u := by
  dsimp only
  obtain ⟨hl, hr⟩ := extreme_subgradients _ (convex_transverse_profile μ u e hadd hhom)
  have hls := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hl)
  have hrs := support_from_transverse_subgradient μ x r u e _ hadd hhom hxu hru hcoords
    (by simpa using hr)
  exact ⟨hls.1, hrs.1, hls.2, hrs.2⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem defect_append (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds es : List Step) :
    defect τ b m a p (ds ++ es) =
      defect τ b m a p ds + defect τ b m a (p + displacement ds) es := by
  simp [defect, pathCost_append]; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem plane_reconstruction (b : ℝ) (z : Plane) :
    z = xCoord z • direction b + rCoord b z • transverseUnit := by
  ext i
  fin_cases i <;> simp [direction, transverseUnit, PiLp.add_apply, PiLp.smul_apply]
  ring

theorem norm_positive_homogeneous (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z := by
  intro t ht z
  rw [hμ.homogeneous, abs_of_nonneg ht]

theorem planar_extreme_supports (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    let φ := fun t : ℝ => μ (direction b + t • transverseUnit)
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) z ≤ μ z) ∧
    (∀ z, coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) z ≤ μ z) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (leftSlope φ) (direction b) = μ (direction b) ∧
    coordinateSupport xCoord.toLinearMap (rCoord b).toLinearMap
      (μ (direction b)) (rightSlope φ) (direction b) = μ (direction b) := by
  exact extreme_supports μ xCoord.toLinearMap (rCoord b).toLinearMap (direction b)
    transverseUnit hμ.triangle (norm_positive_homogeneous μ hμ)
    (xCoord_direction b) (rCoord_direction b) (plane_reconstruction b)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem measurableSet_strict_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds < bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_lt (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

theorem measurableSet_bounded_path_event (hτ : ∀ e, Measurable (τ e))
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet {ω | ∃ p ds, family p ds ∧
      pathCost (fun e => τ e ω) p ds ≤ bound p ds} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  apply MeasurableSet.iUnion
  intro ds
  by_cases hf : family p ds
  · simpa only [hf, true_and] using
      measurableSet_le (measurable_pathCost hτ p ds) measurable_const
  · simp [hf]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_TiltPath
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

theorem pathCost_scale (τ : Edge → ℝ) (α : ℝ) (p : Vertex) (ds : List Step) :
    pathCost (fun e => α * τ e) p ds = α * pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, mul_add]

theorem tilt_crossing_defect (τ : Edge → ℝ) (b m a K lam s n : ℝ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam * s < n) (hgain : K + 16 * |a| + 1 < lam * m)
    (p : Vertex) (ds : List Step)
    (hx : ((displacement ds).1 : ℝ) = n)
    (hr : |transverse b (displacement ds)| ≤ 16 * s)
    (hcheap : pathCost τ p ds < m * n + K * s) :
    defect (fun e => (1 - lam * s / n) * τ e) b m a p ds < -s := by
  have hα : 0 < 1 - lam * s / n := by
    have := (div_lt_one hn).mpr hsmall
    linarith
  have hc := mul_lt_mul_of_pos_left hcheap hα
  have habs : -(a * transverse b (displacement ds)) ≤ 16 * |a| * s := by
    calc
      -(a * transverse b (displacement ds)) ≤ |a * transverse b (displacement ds)| :=
        neg_le_abs _
      _ = |a| * |transverse b (displacement ds)| := abs_mul _ _
      _ ≤ |a| * (16 * s) := mul_le_mul_of_nonneg_left hr (abs_nonneg a)
      _ = 16 * |a| * s := by ring
  have halg : (1 - lam * s / n) * (m * n + K * s) - m * n =
      (K - lam * m) * s - lam * K * s ^ 2 / n := by
    field_simp [ne_of_gt hn]
    ring
  have hnonneg : 0 ≤ lam * K * s ^ 2 / n := by positivity
  have hgain' := mul_lt_mul_of_pos_right hgain hs
  unfold defect support
  rw [pathCost_scale, hx]
  nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BoundaryGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uncancelled, counterclockwise square sides in
crossings.tex:cr:oriented-paths. A dual vertex `p` represents the actual
point `p - (1/2,1/2)`, so the square at the primal site `q` has lower-left
corner `q` in these integer coordinates. -/
namespace PlanarFPP
open Finset

theorem boundaryNext_tail (S : Finset Vertex) (e : SquareSide) :
    (boundaryNext S e).tail = e.head := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;> simp [SquareSide.tail, SquareSide.head, Step.corner,
      Step.left, Step.delta, Prod.mk_add_mk]
  · split <;> cases d <;>
      simp [SquareSide.tail, SquareSide.head, Step.corner, Step.left,
        Step.right, Step.outward, Step.delta, Prod.mk_add_mk]

@[simp] theorem boundaryPerm_tail (S : Finset Vertex) (e : BoundarySide S) :
    (boundaryPerm S e).val.tail = e.val.head := boundaryNext_tail S e.val

theorem boundaryPerm_ne_self (S : Finset Vertex) (e : BoundarySide S) :
    boundaryPerm S e ≠ e := by
  intro h
  have hh := boundaryPerm_tail S e
  rw [h] at hh
  have hz : e.val.2.delta = 0 := by
    have : e.val.tail + e.val.2.delta = e.val.tail + 0 := by
      simpa [SquareSide.head] using hh.symm
    exact add_left_cancel this
  cases hd : e.val.2 <;> simp [hd, Step.delta] at hz

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BoundaryWinding
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

theorem SquareSide.opposite_ne_self (e : SquareSide) : e.opposite ≠ e := by
  intro h
  have hh := congrArg Prod.snd h
  cases hd : e.2 <;> simp [opposite, hd, Step.reverse] at hh

theorem square_rayCross_sum (q : Vertex) :
    ∑ d : Step, SquareSide.rayCross (q,d) = if q = 0 then 1 else 0 := by
  have hu : (univ : Finset Step) = {Step.east,Step.west,Step.north,Step.south} := rfl
  rw [hu]
  rcases q with ⟨x,y⟩
  simp [SquareSide.rayCross, Prod.ext_iff]
  split_ifs <;> omega

theorem internalSides_opposite (S : Finset Vertex) (e : SquareSide)
    (he : e ∈ internalSides S) : e.opposite ∈ internalSides S := by
  simp only [internalSides, mem_filter, mem_product, mem_univ, and_true] at he ⊢
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [SquareSide.opposite, Step.outward,
    Step.right, Step.reverse, Step.delta, Prod.mk_add_mk, add_assoc]

theorem internalSides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ internalSides S, e.rayCross = 0 := by
  refine sum_involution (fun e _ => e.opposite) ?_ ?_ (internalSides_opposite S) ?_
  · intro e he
    simp
  · intro e he hh
    exact e.opposite_ne_self
  · intro e he
    exact e.opposite_opposite

/-- Before cancellation, only the square centered at zero crosses the ray
with net signed count one. Shared sides have opposite counts and cancel. -/
theorem boundarySides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ boundarySides S, e.rayCross = if (0 : Vertex) ∈ S then 1 else 0 := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (S ×ˢ (univ : Finset Step))
    (fun e : SquareSide => e.1 + e.2.outward ∈ S) SquareSide.rayCross
  change (∑ e ∈ internalSides S, e.rayCross) +
    (∑ e ∈ boundarySides S, e.rayCross) = _ at hsplit
  rw [internalSides_rayCross_sum, zero_add] at hsplit
  rw [hsplit, sum_product]
  change (∑ q ∈ S, ∑ d : Step, SquareSide.rayCross (q,d)) = _
  simp_rw [square_rayCross_sum]
  by_cases h0 : (0 : Vertex) ∈ S
  · rw [ite_eq_left h0]
    calc
      _ = (if (0 : Vertex) = 0 then (1 : ℤ) else 0) := by
        apply sum_eq_single 0
        · intro b hb hne
          exact ite_eq_right hne
        · exact fun hh => False.elim (hh h0)
      _ = 1 := ite_eq_left rfl
  · rw [ite_eq_right h0]
    apply sum_eq_zero
    intro q hq
    apply ite_eq_right
    intro hh
    exact h0 (hh ▸ hq)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BoundaryCycles
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Directed boundary cycles with nonzero signed ray-crossing count. -/
namespace PlanarFPP
open Finset Equiv

/-- A nonzero total weight on a fixed-point-free finite permutation has a
cycle of nonzero weight. -/
theorem exists_cycle_nonzero_sum {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (w : α → ℤ)
    (hw : ∑ x, w x ≠ 0) :
    ∃ x, ∑ y ∈ (p.toList x).toFinset, w y ≠ 0 := by
  classical
  let := Equiv.Perm.SameCycle.setoid p
  let Q := Quotient (Equiv.Perm.SameCycle.setoid p)
  let : Fintype Q := Fintype.ofFinite Q
  let c : α → Q := Quotient.mk (Equiv.Perm.SameCycle.setoid p)
  have hs := sum_fiberwise (univ : Finset α) c w
  by_contra hn
  push Not at hn
  have hz (q : Q) : ∑ y ∈ univ.filter (fun y => c y = q), w y = 0 := by
    induction q using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ univ.filter (fun y => c y = c x), w y) = 0
      have he : univ.filter (fun y => c y = c x) = (p.toList x).toFinset := by
        ext y
        simp only [mem_filter, mem_univ, true_and, List.mem_toFinset,
          Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_support]
        constructor
        · intro hy
          exact ⟨(Quotient.exact hy : p.SameCycle y x).symm, hp x⟩
        · intro hy
          exact Quotient.sound hy.1.symm
      rw [he]
      exact hn x
  simp_rw [hz] at hs
  exact hw (by simpa using hs.symm)

/-- The source's enclosing boundary walk, with "nonzero winding" represented
by its exact signed intersections with the positive horizontal ray. -/
theorem exists_boundary_cycle (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ x : BoundarySide S,
      let es := (boundaryPerm S).toList x
      es.Nodup ∧ 0 < es.length ∧
      (∀ e ∈ es, ((boundaryPerm S) e).val.tail = e.val.head) ∧
      (∀ e (he : e ∈ es), (es.next e he).val.tail = e.val.head) ∧
      (∑ e ∈ es.toFinset, e.val.rayCross) ≠ 0 := by
  classical
  have hw : ∑ e : BoundarySide S, e.val.rayCross ≠ 0 := by
    have hh := boundarySides_rayCross_sum S
    rw [ite_eq_left h0] at hh
    rw [Finset.sum_coe_sort]
    omega
  obtain ⟨x,hx⟩ := exists_cycle_nonzero_sum (boundaryPerm S)
    (boundaryPerm_ne_self S) (fun e => e.val.rayCross) hw
  refine ⟨x, Equiv.Perm.nodup_toList _ _, ?_, ?_, ?_, hx⟩
  · exact Equiv.Perm.length_toList_pos_of_mem_support _ _
      (Equiv.Perm.mem_support.mpr (boundaryPerm_ne_self S x))
  · intro e he
    exact boundaryPerm_tail S e
  · intro e he
    rw [Equiv.Perm.next_toList_eq_apply]
    exact boundaryPerm_tail S e

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Environment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- The joint law on a finite set of edges, including the empty set. -/
theorem IidEnvironment.finiteJointLaw (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) :
    P.map (fun ω (e : S) => τ e ω) = Measure.pi (fun _ : S => ν) := by
  have hi := h.independent.precomp
    (Subtype.val_injective : Function.Injective (fun e : S => (e : PlanarFPP.Edge)))
  rw [iIndepFun.map_fun_eq_pi_map (fun e : S => (h.measurable e).aemeasurable) hi]
  simp only [h.marginal]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

/-- Exponential functions are integrable under the Gamma law for `theta < rate`. -/
theorem gamma_integrable_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    Integrable (fun x : ℝ => exp (theta * x)) (gammaMeasure shape rate) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le)).mp
  rw [gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.ofReal_ne_top

/-- Gamma exponential moments, as in paper 210, Lemma `df:ga:moment`. -/
theorem gamma_integral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫ x : ℝ, exp (theta * x) ∂gammaMeasure shape rate) =
      (rate / (rate - theta)) ^ shape := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le) (by fun_prop),
    gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.toReal_ofReal
    (Real.rpow_pos_of_pos (div_pos hrate (sub_pos.mpr htheta)) shape).le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

variable {shape rate theta : ℝ}

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPath
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

attribute [local instance] OAI.GammaFPP.cheapStepFintype
private lemma cheapStep_card : Fintype.card Step = 4 := by decide

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PassageLowerBound
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Filter

/-- Each original nearest-neighbor step contributes at most one L1 unit. -/
lemma displacement_natAbs_sum_le_length (ds : List Step) :
    (displacement ds).1.natAbs + (displacement ds).2.natAbs ≤ ds.length := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
      have h₁ := Int.natAbs_add_le d.delta.1 (displacement ds).1
      have h₂ := Int.natAbs_add_le d.delta.2 (displacement ds).2
      have hd : d.delta.1.natAbs + d.delta.2.natAbs = 1 := by
        cases d <;> norm_num [Step.delta]
      simp only [displacement_cons, List.length_cons]
      change (d.delta.1 + (displacement ds).1).natAbs +
        (d.delta.2 + (displacement ds).2).natAbs ≤ ds.length + 1
      omega

/-- Literal latticeDistance, not the product max norm. -/
lemma latticeDistance_endpoint_le_length (p : Vertex) (ds : List Step) :
    latticeDistance p (p + displacement ds) ≤ ds.length := by
  simpa only [latticeDistance, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] using
    displacement_natAbs_sum_le_length ds

/-- Erasure preserves the endpoint, so every sufficiently distant arbitrary
path inherits the long-trail lower bound, even if it repeats edges. -/
lemma pathCost_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) (ds : List Step)
    (hend : p + displacement ds = q) :
    c * (latticeDistance p q : ℝ) < pathCost w p ds := by
  obtain ⟨es, he, hn, hcost⟩ := LoopErase.erase_path_loops w hw p ds
  have hend' : p + displacement es = q := by rw [he, hend]
  have hdist : latticeDistance p q ≤ es.length := by
    simpa only [hend'] using latticeDistance_endpoint_le_length p es
  have hdistR : (latticeDistance p q : ℝ) ≤ (es.length : ℝ) := by
    exact_mod_cast hdist
  exact (mul_le_mul_of_nonneg_left hdistR hc).trans_lt
    ((hN es (hq.trans hdist) hn).trans_le hcost)

/-- Taking the infimum of path costs preserves the non-strict lower bound,
without requiring the existence of a minimizing path. -/
lemma passageTime_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) :
    c * (latticeDistance p q : ℝ) ≤ passageTime w p q := by
  apply le_csInf (path_costs_nonempty w p q)
  rintro t ⟨ds, hend, rfl⟩
  exact (pathCost_lower_of_long_trails w hw c hc p N hN q hq ds hend).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- On one probability-one event, every lattice start has an eventual metric
lower bound for all distant endpoints. The cutoff may depend on start/sample. -/
theorem GammaEnvironment.ae_all_starts_passageTime_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ q : Vertex,
      N ≤ latticeDistance p q →
        cheapSlope shape rate * (latticeDistance p q : ℝ) ≤
          passageTime (fun e => τ e ω) p q := by
  filter_upwards [h.ae_positive, h.ae_all_starts_long_trails_cost hs hr] with ω hpos hlong
  intro p
  obtain ⟨N, hN⟩ := hlong p
  refine ⟨N, ?_⟩
  intro q hq
  exact passageTime_lower_of_long_trails (fun e => τ e ω) (fun e => (hpos e).le)
    (cheapSlope shape rate) (cheapSlope_pos hs hr).le p N hN q hq

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPositive
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fatou needs only eventual lower bounds, not samplewise convergence. -/
lemma lower_le_limit_integral_of_ae_eventually [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a m : ℝ)
    (hX : ∀ n, Measurable (X n)) (hI : ∀ n, Integrable (X n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, a ≤ X n ω)
    (hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) (hm : 0 ≤ m) :
    a ≤ m := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X n ω)
  have hmeas : ∀ n, Measurable (F n) := fun n => (hX n).ennreal_ofReal
  have hpoint : ∀ᵐ ω ∂P, ENNReal.ofReal a ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hlower] with ω hω
    exact le_liminf_of_le (h := hω.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  have hlow : ENNReal.ofReal a ≤ ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
    simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hpoint
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop) hmeas
  have hint (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, X n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hI n) (hpos n)).symm
  have ht : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 (ENNReal.ofReal m)) := by
    simpa only [hint] using ENNReal.tendsto_ofReal hlimit
  have hb : ENNReal.ofReal a ≤ ENNReal.ofReal m := by
    simpa only [ht.liminf_eq] using hlow.trans hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hm).mp hb

/-- Literal lattice L1 distance scales under natural multiplication. -/
lemma latticeDistance_zero_nsmul (z : Vertex) (n : ℕ) :
    latticeDistance 0 (n • z) = n * latticeDistance 0 z := by
  simp [latticeDistance, nsmul_eq_mul, Int.natAbs_mul, Nat.mul_add]

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The actual Fekete mean limit has the same positive linear lower bound as
the eventual path metric. The zero direction is treated before division. -/
theorem GammaEnvironment.directionalMeanConstant_linear_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ directionalMeanConstant h hs hr z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeDistance, h.directionalMeanConstant_zero hs hr]
  let : IsProbabilityMeasure P := h.probability
  have hd : 0 < latticeDistance 0 z := by
    by_contra hn
    have hd0 : latticeDistance 0 z = 0 := Nat.eq_zero_of_not_pos hn
    have hxy : z.1 = 0 ∧ z.2 = 0 := by simpa [latticeDistance] using hd0
    exact hz (Prod.ext hxy.1 hxy.2)
  let X : ℕ → Ω → ℝ := fun n ω => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
  have hX : ∀ n, Measurable (X n) := fun n =>
    (h.measurable_passageTime 0 (n • z)).div_const (n : ℝ)
  have hI : ∀ n, Integrable (X n) P := fun n =>
    (h.integrable_passageTime hs hr 0 (n • z)).div_const (n : ℝ)
  have hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω := by
    intro n
    filter_upwards [h.ae_positive] with ω hω
    exact div_nonneg (passageTime_nonneg _ (fun e => (hω e).le) 0 (n • z))
      (Nat.cast_nonneg n)
  have hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ X n ω := by
    filter_upwards [h.ae_all_starts_passageTime_lower hs hr] with ω hω
    obtain ⟨N, hN⟩ := hω 0
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hnd : N ≤ latticeDistance 0 (n • z) := by
      rw [latticeDistance_zero_nsmul]
      nlinarith
    have hb := hN (n • z) hnd
    rw [latticeDistance_zero_nsmul, Nat.cast_mul] at hb
    change cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤
      passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop
      (𝓝 (directionalMeanConstant h hs hr z)) := by
    simpa only [X, integral_div, meanPassageSequence] using h.meanPassageSequence_tendsto hs hr z
  exact lower_le_limit_integral_of_ae_eventually X _ _ hX hI hpos hlower hlimit
    (h.directionalMeanConstant_nonneg hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

/-- Positive denominators transport a lattice coercivity bound to rationals. -/
lemma rationalMean_lower (m : Vertex → ℝ) (c : ℝ)
    (hm : ∀ x, c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|) ≤ m x)
    (q : ℚ × ℚ) :
    c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ rationalMean m q := by
  let x := rationalNumerator q
  let n := rationalDenominator q
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (rationalDenominator_pos q)
  have he := rationalLatticePoint_numerator_denominator q
  have h₁ : (x.1 : ℝ) / (n : ℝ) = (q.1 : ℝ) := by
    have hq : (x.1 : ℚ) / (n : ℚ) = q.1 := by
      simpa only [rationalLatticePoint] using congrArg Prod.fst he
    exact_mod_cast hq
  have h₂ : (x.2 : ℝ) / (n : ℝ) = (q.2 : ℝ) := by
    have hq : (x.2 : ℚ) / (n : ℚ) = q.2 := by
      simpa only [rationalLatticePoint] using congrArg Prod.snd he
    exact_mod_cast hq
  change _ ≤ m x / (n : ℝ)
  rw [← h₁, ← h₂, abs_div, abs_div, abs_of_pos hn]
  simpa only [← add_div, ← mul_div_assoc] using
    div_le_div_of_nonneg_right (hm x) hn.le

/-- A closed inequality on the rational image holds on its real closure. -/
lemma realMeanExtension_lower {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (c : ℝ) (hl : ∀ q, c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ f q)
    (v : ℝ × ℝ) : c * (|v.1| + |v.2|) ≤ realMeanExtension f v := by
  apply isClosed_property rationalPairCast_dense
    (p := fun v => c * (|v.1| + |v.2|) ≤ realMeanExtension f v) ?_ ?_ v
  · exact isClosed_le
      (continuous_const.mul (continuous_fst.abs.add continuous_snd.abs))
      (realMeanExtension_uniformContinuous hf).continuous
  · intro q
    rw [realMeanExtension_on_rat hf]
    exact hl q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : ℝ × ℝ) :
    cheapSlope shape rate * (|v.1| + |v.2|) ≤ gammaMeanPairSeminorm h hs hr v := by
  change _ ≤ realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_lower
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  apply rationalMean_lower
  intro z
  simpa [latticeDistance] using h.directionalMeanConstant_linear_lower hs hr z

lemma gammaMeanNorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * (|v 0| + |v 1|) ≤ gammaMeanNorm h hs hr v :=
  gammaMeanPairSeminorm_lower h hs hr (v 0, v 1)

/-- The real extension of the Gamma directional mean constants is a norm. -/
theorem gammaMeanNorm_laws
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    TimeConstantNorm (gammaMeanNorm h hs hr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact apply_nonneg (gammaMeanPairSeminorm h hs hr) (v 0, v 1)
  · intro v
    constructor
    · intro hv
      have hb := gammaMeanNorm_lower h hs hr v
      have hc := cheapSlope_pos hs hr
      rw [hv] at hb
      have h₀ : v 0 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      have h₁ : v 1 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      ext i
      fin_cases i
      · exact h₀
      · exact h₁
    · rintro rfl
      change gammaMeanPairSeminorm h hs hr 0 = 0
      exact map_zero _
  · intro v w
    change gammaMeanPairSeminorm h hs hr ((v 0, v 1) + (w 0, w 1)) ≤ _
    exact map_add_le_add (gammaMeanPairSeminorm h hs hr) _ _
  · intro a v
    change gammaMeanPairSeminorm h hs hr (a • (v 0, v 1)) = _
    simpa only [Real.norm_eq_abs, gammaMeanNorm] using map_smul_eq_mul (gammaMeanPairSeminorm h hs hr) a (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

end GammaFPP.RealDirectionBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltDensity
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

lemma gammaScaleLikelihood_pos (shape rate : ℝ) {alpha : ℝ}
    (halpha : 0 < alpha) (x : ℝ) : 0 < gammaScaleLikelihood shape rate alpha x := by
  exact mul_pos (Real.rpow_pos_of_pos halpha (-shape)) (exp_pos _)

/-- The likelihood identity includes the real-power convention at `x = 0`. -/
lemma gamma_scale_likelihood_density {shape rate alpha : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (halpha : 0 < alpha) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (gammaScaleLikelihood shape rate alpha x) =
      gammaPDF shape (rate / alpha) x := by
  have hcoeff : rate ^ shape * alpha ^ (-shape) = (rate / alpha) ^ shape := by
    rw [Real.div_rpow hrate.le halpha.le, Real.rpow_neg halpha.le, div_eq_mul_inv]
  have hexp : exp (-(rate * x)) * exp (-(rate * (alpha⁻¹ - 1)) * x) =
      exp (-((rate / alpha) * x)) := by
    rw [← exp_add]
    congr 1
    field_simp [halpha.ne']; ring
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold gammaScaleLikelihood
    calc
      (rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x))) *
          (alpha ^ (-shape) * exp (-(rate * (alpha⁻¹ - 1)) * x)) =
          (rate ^ shape * alpha ^ (-shape)) / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (-(rate * (alpha⁻¹ - 1)) * x)) := by ring
      _ = (rate / alpha) ^ shape / Gamma shape * x ^ (shape - 1) *
          exp (-((rate / alpha) * x)) := by rw [hcoeff, hexp]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- Weighting the Gamma measure by the scaling likelihood changes its rate. -/
theorem gammaMeasure_withDensity_scaleLikelihood {shape rate alpha : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (halpha : 0 < alpha) :
    (gammaMeasure shape rate).withDensity
        (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate alpha x)) =
      gammaMeasure shape (rate / alpha) := by
  change (volume.withDensity (gammaPDF shape rate)).withDensity _ =
    volume.withDensity (gammaPDF shape (rate / alpha))
  rw [← withDensity_mul volume (by unfold gammaPDF; fun_prop)
    (by unfold gammaScaleLikelihood; fun_prop)]
  congr 1
  funext x
  exact gamma_scale_likelihood_density hshape hrate halpha x

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ScalingLaw
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Scalar change of variables for a measurable nonnegative density. -/
lemma map_mul_withDensity_real {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measure.map (fun x : ℝ => a * x) (volume.withDensity f) =
      volume.withDensity (fun y => ENNReal.ofReal a⁻¹ * f (y / a)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul volume hf
      (g := fun x : ℝ => g (a * x)) (hg.comp (by fun_prop)),
    lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hg]
  have hchange :
      (∫⁻ y : ℝ, f (y / a) * g y ∂Measure.map (fun x : ℝ => a * x) volume) =
        ∫⁻ x : ℝ, f x * g (a * x) := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    simp only [mul_div_cancel_left₀ _ ha.ne']
  rw [Real.map_volume_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha),
    lintegral_smul_measure, smul_eq_mul] at hchange
  calc
    (∫⁻ x : ℝ, (f * fun x => g (a * x)) x) =
        ENNReal.ofReal a⁻¹ * ∫⁻ y : ℝ, f (y / a) * g y := hchange.symm
    _ = ∫⁻ y : ℝ, (fun y => ENNReal.ofReal a⁻¹ * f (y / a)) y * g y := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_congr
      intro y
      exact (mul_assoc _ _ _).symm

/-- The Gamma density satisfies the scaling Jacobian identity, including at the origin. -/
lemma gammaPDF_scaling {shape rate a : ℝ} (hshape : 0 < shape) (hrate : 0 < rate)
    (ha : 0 < a) (y : ℝ) :
    ENNReal.ofReal a⁻¹ * gammaPDF shape rate (y / a) =
      gammaPDF shape (rate / a) y := by
  by_cases hy : 0 ≤ y
  · rw [gammaPDF_of_nonneg (div_nonneg hy ha.le), gammaPDF_of_nonneg hy,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
    congr 1
    rw [Real.div_rpow hy ha.le, Real.div_rpow hrate.le ha.le,
      Real.rpow_sub ha shape 1, Real.rpow_one]
    have he : -(rate * (y / a)) = -((rate / a) * y) := by ring
    rw [he]
    field_simp [ha.ne', (Real.rpow_pos_of_pos ha shape).ne',
      (Real.Gamma_pos_of_pos hshape).ne']
  · rw [gammaPDF_of_neg (div_neg_of_neg_of_pos (lt_of_not_ge hy) ha),
      gammaPDF_of_neg (lt_of_not_ge hy), mul_zero]

/-- Scaling a Gamma random variable by a positive constant divides its rate. -/
theorem map_mul_gammaMeasure {shape rate a : ℝ} (hshape : 0 < shape)
    (hrate : 0 < rate) (ha : 0 < a) :
    Measure.map (fun x : ℝ => a * x) (gammaMeasure shape rate) =
      gammaMeasure shape (rate / a) := by
  change Measure.map _ (volume.withDensity (gammaPDF shape rate)) =
    volume.withDensity (gammaPDF shape (rate / a))
  rw [map_mul_withDensity_real ha (by unfold gammaPDF; fun_prop)]
  congr 1
  funext y
  exact gammaPDF_scaling hshape hrate ha y

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltMoment
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

private lemma shrink_likelihood_sq (shape rate delta x : ℝ) :
    gammaShrinkLikelihood shape rate delta x ^ 2 =
      ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x) := by
  unfold gammaShrinkLikelihood gammaScaleLikelihood squareTheta
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1
  congr 1
  ring

private lemma square_shifted_rate (rate : ℝ) {delta : ℝ} (hdelta : delta < 1) :
    rate - squareTheta rate delta = rate * (1 + delta) / (1 - delta) := by
  unfold squareTheta
  field_simp [(sub_pos.mpr hdelta).ne']; ring

private lemma squareTheta_lt_rate {rate delta : ℝ}
    (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    squareTheta rate delta < rate := by
  apply sub_pos.mp
  rw [square_shifted_rate rate hhi]
  exact div_pos (mul_pos hrate (by linarith)) (sub_pos.mpr hhi)

private lemma square_moment_coefficient {shape rate delta : ℝ}
    (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    ((1 - delta) ^ (-shape)) ^ 2 *
        (rate / (rate - squareTheta rate delta)) ^ shape =
      (1 - delta ^ 2) ^ (-shape) := by
  have ha : 0 < 1 - delta := sub_pos.mpr hhi
  have hb : 0 < 1 + delta := by linarith
  have hd : 0 < 1 - delta ^ 2 := by
    have he : 1 - delta ^ 2 = (1 - delta) * (1 + delta) := by ring
    rw [he]
    exact mul_pos ha hb
  have hratio : rate / (rate - squareTheta rate delta) = (1 - delta) / (1 + delta) := by
    rw [square_shifted_rate rate hhi]
    field_simp [hrate.ne', ha.ne', hb.ne']
  have hbase : ((1 - delta)⁻¹) ^ 2 * ((1 - delta) / (1 + delta)) =
      (1 - delta ^ 2)⁻¹ := by
    field_simp [ha.ne', hb.ne', hd.ne']; ring
  rw [hratio]
  calc
    ((1 - delta) ^ (-shape)) ^ 2 * ((1 - delta) / (1 + delta)) ^ shape =
        (((1 - delta)⁻¹) ^ 2) ^ shape * ((1 - delta) / (1 + delta)) ^ shape := by
      rw [Real.rpow_neg_eq_inv_rpow,
        Real.rpow_pow_comm (inv_nonneg.mpr ha.le) shape 2]
    _ = (((1 - delta)⁻¹) ^ 2 * ((1 - delta) / (1 + delta))) ^ shape :=
      (Real.mul_rpow (sq_nonneg _) (div_nonneg ha.le hb.le)).symm
    _ = ((1 - delta ^ 2)⁻¹) ^ shape := by rw [hbase]
    _ = (1 - delta ^ 2) ^ (-shape) :=
      (Real.rpow_neg_eq_inv_rpow (1 - delta ^ 2) shape).symm

/-- The square of the shrinking likelihood is integrable under the Gamma law. -/
theorem gamma_shrink_likelihood_sq_integrable {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    Integrable (fun x : ℝ => gammaShrinkLikelihood shape rate delta x ^ 2)
      (gammaMeasure shape rate) := by
  have he : (fun x : ℝ => gammaShrinkLikelihood shape rate delta x ^ 2) =
      (fun x : ℝ => ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x)) :=
    funext (shrink_likelihood_sq shape rate delta)
  rw [he]
  exact (gamma_integrable_exp hshape hrate (squareTheta_lt_rate hrate hlo hhi)).const_mul _

/-- The second moment of the likelihood for one coordinate. -/
theorem gamma_shrink_likelihood_second_moment {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2 ∂gammaMeasure shape rate) =
      (1 - delta ^ 2) ^ (-shape) := by
  calc
    (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2 ∂gammaMeasure shape rate) =
        ∫ x : ℝ, ((1 - delta) ^ (-shape)) ^ 2 * exp (squareTheta rate delta * x)
          ∂gammaMeasure shape rate :=
      integral_congr_ae (Filter.Eventually.of_forall (shrink_likelihood_sq shape rate delta))
    _ = ((1 - delta) ^ (-shape)) ^ 2 *
        (∫ x : ℝ, exp (squareTheta rate delta * x) ∂gammaMeasure shape rate) :=
      integral_const_mul _ _
    _ = ((1 - delta) ^ (-shape)) ^ 2 *
        (rate / (rate - squareTheta rate delta)) ^ shape := by
      rw [gamma_integral_exp hshape hrate (squareTheta_lt_rate hrate hlo hhi)]
    _ = (1 - delta ^ 2) ^ (-shape) := square_moment_coefficient hrate hlo hhi

/-- The nonnegative second moment used in finite-product likelihood arguments. -/
theorem gamma_shrink_likelihood_second_lintegral {shape rate delta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x : ℝ, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
        ∂gammaMeasure shape rate) = ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape)) := by
  calc
    (∫⁻ x : ℝ, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
        ∂gammaMeasure shape rate) =
        ∫⁻ x : ℝ, ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x ^ 2)
          ∂gammaMeasure shape rate := by
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_pow
        (gammaScaleLikelihood_pos shape rate (sub_pos.mpr hhi) x).le 2).symm
    _ = ENNReal.ofReal (∫ x : ℝ, gammaShrinkLikelihood shape rate delta x ^ 2
        ∂gammaMeasure shape rate) :=
      (ofReal_integral_eq_lintegral_ofReal
        (gamma_shrink_likelihood_sq_integrable hshape hrate hlo hhi)
        (Filter.Eventually.of_forall fun x => sq_nonneg (gammaShrinkLikelihood shape rate delta x))).symm
    _ = ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape)) := by
      rw [gamma_shrink_likelihood_second_moment hshape hrate hlo hhi]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTilt
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

lemma measurable_finiteGammaScaleLikelihood (shape rate a : ℝ) :
    Measurable (finiteGammaScaleLikelihood (ι := ι) shape rate a) := by
  unfold finiteGammaScaleLikelihood gammaScaleLikelihood
  fun_prop

/-- Factorization of nonnegative integrals under a finite product of probability measures. -/
private theorem probability_pi_lintegral_prod (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂μ i := by
  have hi : iIndepFun (fun i (x : ι → ℝ) => f i (x i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]

private theorem indicator_pi_prod (s : ι → Set ℝ) (f : ι → ℝ → ℝ≥0∞)
    (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · have hh : x ∈ Set.univ.pi s := by simpa using hx
    rw [Set.indicator_of_mem hh]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hx i)]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hh : x ∉ Set.univ.pi s := by simpa using (not_forall.mpr ⟨i, hi⟩)
    rw [Set.indicator_of_notMem hh]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Coordinatewise Gamma likelihoods change the rate in the product measure. -/
theorem finite_gamma_withDensity_scale {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).withDensity
        (finiteGammaScaleLikelihood shape rate a) =
      finiteGammaMeasure shape (rate / a) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  let : IsProbabilityMeasure (gammaMeasure shape (rate / a)) :=
    isProbabilityMeasure_gammaMeasure hs (div_pos hr ha)
  unfold finiteGammaMeasure
  symm
  apply Measure.pi_eq
  intro s hsmeas
  rw [withDensity_apply _ (MeasurableSet.univ_pi hsmeas),
    ← lintegral_indicator (MeasurableSet.univ_pi hsmeas)]
  change (∫⁻ x, (Set.univ.pi s).indicator
    (fun y => ∏ i, ENNReal.ofReal (gammaScaleLikelihood shape rate a (y i))) x
    ∂Measure.pi (fun _ : ι => gammaMeasure shape rate)) = _
  simp_rw [indicator_pi_prod s (fun _ x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x))]
  rw [probability_pi_lintegral_prod _
    (fun i => (s i).indicator (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x)))
    (fun i => (by unfold gammaScaleLikelihood; fun_prop :
      Measurable (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x))).indicator (hsmeas i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hsmeas i), ← withDensity_apply _ (hsmeas i),
    gammaMeasure_withDensity_scaleLikelihood hs hr ha]

/-- The pushforward of a finite Gamma law under coordinatewise scaling. -/
theorem finite_gamma_map_scale {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).map (fun x i => a * x i) =
      finiteGammaMeasure shape (rate / a) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  let : ∀ _ : ι, IsProbabilityMeasure
      ((gammaMeasure shape rate).map (fun x : ℝ => a * x)) :=
    fun _ => Measure.isProbabilityMeasure_map
      (by fun_prop : Measurable (fun x : ℝ => a * x)).aemeasurable
  unfold finiteGammaMeasure
  rw [Measure.pi_map_pi
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => a * x)).aemeasurable)]
  simp only [map_mul_gammaMeasure hs hr ha]

/-- The scaling pushforward equals the measure weighted by the product likelihood. -/
theorem finite_gamma_map_scale_eq_withDensity {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).map (fun x i => a * x i) =
      (finiteGammaMeasure shape rate).withDensity
        (finiteGammaScaleLikelihood shape rate a) := by
  rw [finite_gamma_map_scale hs hr ha, finite_gamma_withDensity_scale hs hr ha]

/-- The second moment of the product likelihood factors over the coordinates. -/
theorem finite_gamma_shrink_second_moment_pow {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x, (finiteGammaScaleLikelihood (ι := ι) shape rate (1 - delta) x) ^ 2
      ∂finiteGammaMeasure shape rate) =
      (ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape))) ^ Fintype.card ι := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  simp only [finiteGammaMeasure, finiteGammaScaleLikelihood, ← Finset.prod_pow]
  rw [probability_pi_lintegral_prod _
    (fun _ x => (ENNReal.ofReal (gammaScaleLikelihood shape rate (1 - delta) x)) ^ 2)
    (fun _ => by unfold gammaScaleLikelihood; fun_prop)]
  change (∏ _ : ι, ∫⁻ x, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
    ∂gammaMeasure shape rate) = _
  simp only [gamma_shrink_likelihood_second_lintegral hs hr hlo hhi,
    Finset.prod_const, Finset.card_univ]

/-- The second moment is `(1 - delta²)^(-shape * N)` for `-1 < delta < 1`, including `N = 0`. -/
theorem finite_gamma_shrink_second_moment {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x, (finiteGammaScaleLikelihood (ι := ι) shape rate (1 - delta) x) ^ 2
      ∂finiteGammaMeasure shape rate) =
      ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape * (Fintype.card ι : ℝ))) := by
  have hb : 0 < 1 - delta ^ 2 := by
    have hprod : 0 < (1 - delta) * (1 + delta) :=
      mul_pos (sub_pos.mpr hhi) (by linarith)
    nlinarith
  rw [finite_gamma_shrink_second_moment_pow hs hr hlo hhi,
    Real.rpow_mul_natCast hb.le (-shape) (Fintype.card ι)]
  exact (ENNReal.ofReal_pow (Real.rpow_nonneg hb.le (-shape)) (Fintype.card ι)).symm

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridIndependence
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint independence for finite families of tests on disjoint edge sets. -/
namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset

theorem measurable_extendEdgeWeights (S : Finset Edge) : Measurable (extendEdgeWeights S) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ S
  · simpa only [extendEdgeWeights,dite_eq_left he] using (measurable_pi_apply (⟨e,he⟩ : S))
  · simp only [extendEdgeWeights,dite_eq_right he]
    exact measurable_const

theorem DependsOnEdges.restriction_iff {A : Set (Edge → ℝ)} {S : Finset Edge}
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    extendEdgeWeights S (fun e : S => w e) ∈ A ↔ w ∈ A := by
  apply hA
  intro e he
  simp [extendEdgeWeights,he]

theorem dependsOnEdges_biInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, DependsOnEdges (A i) (S i)) :
    DependsOnEdges (⋂ i ∈ t, A i) (t.biUnion S) := by
  classical
  intro w w' hh
  simp only [mem_iInter]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hA i hi w w' (fun e he => hh e (mem_biUnion.mpr ⟨i,hi,he⟩))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem disjoint_edge_events_independent (h : GammaEnvironment shape rate P τ)
    (A B : Set (Edge → ℝ)) (S T : Finset Edge)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : DependsOnEdges A S) (hBT : DependsOnEdges B T) (hST : Disjoint S T) :
    IndepSet {ω | (fun e => τ e ω) ∈ A} {ω | (fun e => τ e ω) ∈ B} P := by
  let _ := h.probability
  have hf := h.independent.indepFun_finset S T hST h.measurable
  have hs : Measurable (fun ω (e : S) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have ht : Measurable (fun ω (e : T) => τ e ω) := Measurable.of_eval (fun e => h.measurable e)
  have hi := (indepFun_iff_indepSet_preimage hs ht).mp hf
    ((extendEdgeWeights S) ⁻¹' A) ((extendEdgeWeights T) ⁻¹' B)
    (hA.preimage (measurable_extendEdgeWeights S)) (hB.preimage (measurable_extendEdgeWeights T))
  have heA : (fun ω (e : S) => τ e ω) ⁻¹' ((extendEdgeWeights S) ⁻¹' A) =
      {ω | (fun e => τ e ω) ∈ A} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hAS.restriction_iff (fun e => τ e ω)
  have heB : (fun ω (e : T) => τ e ω) ⁻¹' ((extendEdgeWeights T) ⁻¹' B) =
      {ω | (fun e => τ e ω) ∈ B} := by
    ext ω
    simpa only [Set.mem_preimage,mem_ofPred_eq] using hBT.restriction_iff (fun e => τ e ω)
  simpa only [heA,heB] using hi

theorem disjoint_edge_events_inter_probability (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (t : Finset ι) (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i ∈ t, MeasurableSet (A i))
    (hAS : ∀ i ∈ t, DependsOnEdges (A i) (S i))
    (hdis : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j))) :
    P {ω | ∀ i ∈ t, (fun e => τ e ω) ∈ A i} =
      ∏ i ∈ t, P {ω | (fun e => τ e ω) ∈ A i} := by
  classical
  let _ := h.probability
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have hAt : ∀ i ∈ t, MeasurableSet (A i) := fun i hi => hA i (mem_insert_of_mem hi)
    have hSt : ∀ i ∈ t, DependsOnEdges (A i) (S i) := fun i hi => hAS i (mem_insert_of_mem hi)
    have hd : Set.Pairwise (↑t : Set ι) (fun i j => Disjoint (S i) (S j)) := by
      intro i hi j hj hij
      exact hdis (mem_insert_of_mem hi) (mem_insert_of_mem hj) hij
    have hdunion : Disjoint (S a) (t.biUnion S) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hi) (by intro he; exact ha (he ▸ hi))
    have hm : MeasurableSet (⋂ i ∈ t, A i) := MeasurableSet.biInter (t.countable_toSet) hAt
    have hi := disjoint_edge_events_independent h (A a) (⋂ i ∈ t, A i) (S a) (t.biUnion S)
      (hA a (mem_insert_self _ _)) hm (hAS a (mem_insert_self _ _))
      (dependsOnEdges_biInter t A S hSt) hdunion
    have hprob := hi.measure_inter_eq_mul
    have he : {ω | ∀ i ∈ insert a t, (fun e => τ e ω) ∈ A i} =
        {ω | (fun e => τ e ω) ∈ A a} ∩ {ω | (fun e => τ e ω) ∈ ⋂ i ∈ t, A i} := by
      ext ω; simp
    rw [he,hprob,Finset.prod_insert ha]
    congr 1
    simpa only [mem_iInter] using ih hAt hSt hd

theorem disjoint_edge_events_iIndepSet (h : GammaEnvironment shape rate P τ)
    {ι : Type*} (A : ι → Set (Edge → ℝ)) (S : ι → Finset Edge)
    (hA : ∀ i, MeasurableSet (A i)) (hAS : ∀ i, DependsOnEdges (A i) (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepSet (fun i => {ω | (fun e => τ e ω) ∈ A i}) P := by
  apply (iIndepSet_iff_meas_biInter (fun i => (hA i).preimage
    (Measurable.of_eval h.measurable))).mpr
  intro t
  simpa only [ofPred_forall,Set.preimage] using disjoint_edge_events_inter_probability h t A S
    (fun i _ => hA i) (fun i _ => hAS i) (fun i _ j _ hij => hdis hij)

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingLocalized
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem internalEdges_card_le (V : Finset Vertex) : (internalEdges V).card ≤ 2*V.card := by
  have h := Finset.card_filter_le (s := V ×ˢ (Finset.univ : Finset Bool)) (fun e => edgeEnd e ∈ V)
  simpa [internalEdges,Nat.mul_comm] using h

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem measurableSet_boundedLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (boundedLocalizedEvent V family bound) := by
  simpa only [boundedLocalizedEvent,and_assoc] using
    measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem boundedLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (boundedLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge
open GammaFPP.IntervalTravelBridge Set MeasureTheory Filter
open scoped Topology

theorem mem_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) (w : Edge → ℝ) :
    w ∈ allPairsRegionEvent V I J bound ↔
      ∀ p ∈ I, ∀ q ∈ J, ∃ ds, p+displacement ds=q ∧
        PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p q := by
  simp [allPairsRegionEvent,boundedLocalizedEvent]

theorem measurableSet_allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : MeasurableSet (allPairsRegionEvent V I J bound) := by
  simp only [allPairsRegionEvent,ofPred_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
      measurableSet_boundedLocalizedEvent V _ _))))

theorem allPairsRegionEvent_depends (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) :
    DependsOnEdges (allPairsRegionEvent V I J bound) (internalEdges V) := by
  intro w w' hh
  simp only [allPairsRegionEvent,mem_ofPred_eq]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  apply forall_congr'
  intro q
  apply forall_congr'
  intro hq
  exact boundedLocalizedEvent_depends V _ _ w w' hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RareFastEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

theorem rareFastEvent_depends (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (rareFastEvent b m a A R ε s n t)
      (internalEdges (rareFastVertices b A R s n t)) :=
  strictLocalizedEvent_depends _ _ _

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceConnector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology

theorem trialWindow_scale_bounds (M : ℕ) (hM : 0 < M) (R s : ℝ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    s ≤ trialWindow M R s ∧ trialWindow M R s ≤ (200*M*(R+1))*s := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Nat.le_ceil s
  have hc' := Nat.ceil_lt_add_one (by linarith : 0 ≤ s)
  have hbase : s ≤ (R+1)*(⌈s⌉₊ : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hM' (by positivity : 0 ≤ (R+1)*(⌈s⌉₊ : ℝ))
  have hupper := mul_le_mul_of_nonneg_left (show (⌈s⌉₊ : ℝ) ≤ 2*s by linarith)
    (show 0 ≤ 100*(M : ℝ)*(R+1) by positivity)
  unfold trialWindow trialSpacing
  constructor <;> nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltComparison
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Cauchy–Schwarz for an extended nonnegative density and a measurable event. -/
theorem withDensity_sq_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (L : Ω → ℝ≥0∞) (hL : Measurable L)
    (A : Set Ω) (hA : MeasurableSet A) :
    ((P.withDensity L) A)^2 ≤ (∫⁻ x, (L x)^2 ∂P)*P A := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hL.aemeasurable (measurable_const.aemeasurable :
      AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) (P.restrict A))
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_one,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hh
  have hsqrt (x : ℝ≥0∞) : (x^(1/(2 : ℝ)))^2 = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have hh2 := pow_le_pow_left' hh 2
  rw [mul_pow, hsqrt, hsqrt] at hh2
  rw [withDensity_apply L hA]
  exact hh2.trans (mul_le_mul'
    (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl)

/-- A second-moment bound for scaled finite Gamma event probabilities when `-1 < delta < 1`. -/
theorem finite_gamma_scaled_probability_sq_bound
    {ι : Type*} [Fintype ι] {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1)
    (A : Set (ι → ℝ)) (hA : MeasurableSet A) :
    ((finiteGammaMeasure (ι := ι) shape rate).map
      (fun x i => (1-delta)*x i)).real A ^ 2 ≤
    (1-delta^2)^(-shape * (Fintype.card ι : ℝ)) *
      (finiteGammaMeasure (ι := ι) shape rate).real A := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  have hmeasure : (finiteGammaMeasure (ι := ι) shape rate) A ≠ ∞ := by
    unfold finiteGammaMeasure
    exact measure_ne_top _ _
  have hb : 0 < 1-delta^2 := by
    have hp : 0 < (1-delta)*(1+delta) :=
      mul_pos (sub_pos.mpr hhi) (by linarith)
    nlinarith
  have hc : 0 ≤ (1-delta^2)^(-shape * (Fintype.card ι : ℝ)) :=
    Real.rpow_nonneg hb.le _
  have hh := withDensity_sq_le_second_moment
    (finiteGammaMeasure (ι := ι) shape rate)
    (finiteGammaScaleLikelihood shape rate (1-delta))
    (measurable_finiteGammaScaleLikelihood shape rate (1-delta)) A hA
  rw [← finite_gamma_map_scale_eq_withDensity hs hr (sub_pos.mpr hhi),
    finite_gamma_shrink_second_moment hs hr hlo hhi] at hh
  have hfin : ENNReal.ofReal ((1-delta^2)^(-shape * (Fintype.card ι : ℝ))) *
      (finiteGammaMeasure (ι := ι) shape rate) A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmeasure
  have hhReal := ENNReal.toReal_mono hfin hh
  simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] using hhReal

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteEdgeTilt
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Tilt
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

open GammaFPP.Grid

theorem scaleFiniteEdges_event_iff (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ))
    (hA : DependsOnEdges A S) (w : Edge → ℝ) :
    scaleFiniteEdges S α w ∈ A ↔ (fun e => α*w e) ∈ A := by
  apply hA
  intro e he
  simp [scaleFiniteEdges,he]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- Exact reduction of a supported configuration event to its finite law. -/
theorem finite_support_event_probability (h : GammaEnvironment shape rate P τ)
    (S : Finset Edge) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | (fun e => τ e ω) ∈ A}=
      (Measure.pi (fun _ : S => gammaMeasure shape rate)) ((extendEdgeWeights S) ⁻¹' A) := by
  rw [← h.finiteJointLaw S,Measure.map_apply (Measurable.of_eval (fun e : S => h.measurable e))
    (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  exact (hS.restriction_iff (fun e => τ e ω)).symm

theorem finite_support_scaled_event_probability (h : GammaEnvironment shape rate P τ)
    (S : Finset Edge) (α : ℝ) (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
      ((Measure.pi (fun _ : S => gammaMeasure shape rate)).map (fun x e => α*x e))
        ((extendEdgeWeights S) ⁻¹' A) := by
  have hm : Measurable (fun ω (e : S) => α*τ e ω) :=
    Measurable.of_eval (fun e => measurable_const.mul (h.measurable e))
  rw [← h.finiteJointLaw S,Measure.map_map (by fun_prop)
    (Measurable.of_eval (fun e : S => h.measurable e))]
  change P {ω | scaleFiniteEdges S α (fun e => τ e ω) ∈ A}=
    (P.map (fun ω (e : S) => α*τ e ω)) ((extendEdgeWeights S) ⁻¹' A)
  rw [Measure.map_apply hm (hA.preimage (measurable_extendEdgeWeights S))]
  congr 1
  ext ω
  rw [mem_ofPred_eq,scaleFiniteEdges_event_iff S α A hS]
  exact (hS.restriction_iff (fun e => α*τ e ω)).symm

/-- Exact Gamma cost: the shape factor is retained for every positive shape. -/
theorem finite_edge_tilt_probability_sq_bound
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (δ : ℝ) (hlo : -1 < δ) (hhi : δ < 1)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      (1-δ^2)^(-shape * (S.card : ℝ)) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  have hh := finite_gamma_scaled_probability_sq_bound hs hr hlo hhi
    ((extendEdgeWeights S) ⁻¹' A) (hA.preimage (measurable_extendEdgeWeights S))
  unfold Measure.real at *
  rw [finite_support_scaled_event_probability h S (1-δ) A hA hS,
    finite_support_event_probability h S A hA hS]
  simpa only [finiteGammaMeasure, Fintype.card_coe] using hh

end GammaFPP.Tilt

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Tilt
open Real MeasureTheory ProbabilityTheory PlanarFPP GammaFPP.Grid

/-- A shape-dependent exponential envelope for the Gamma likelihood moment. -/
lemma gamma_likelihood_envelope {shape : ℝ} (hs : 0 < shape)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) (M : ℕ) :
    (1-δ^2)^(-shape*(M : ℝ)) ≤ exp (2*shape*M*δ^2) := by
  have hden : 0 < 1-δ^2 := by nlinarith
  have hsmall : 0 ≤ 1-2*δ^2 := by nlinarith
  have hrat : 1/(1-δ^2) ≤ 2*δ^2+1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg δ) hsmall]
  have he := hrat.trans (add_one_le_exp (2*δ^2))
  have hl := Real.log_le_log (by positivity : 0 < 1/(1-δ^2)) he
  rw [one_div, Real.log_inv, Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl
    (mul_nonneg hs.le (Nat.cast_nonneg M))
  rw [Real.rpow_def_of_pos hden]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem finite_edge_tilt_probability_sq_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
    {shape rate : ℝ} (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      exp (2*shape*S.card*δ^2) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  exact (finite_edge_tilt_probability_sq_bound h hs hr S δ (by linarith) (by linarith)
    A hA hS).trans (mul_le_mul_of_nonneg_right
      (gamma_likelihood_envelope hs δ hδ hδ' S.card) measureReal_nonneg)

end GammaFPP.Tilt

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltRegionCount
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset

theorem int_interval_card_real_le (l u : ℝ) (h : l ≤ u) :
    ((Finset.Icc ⌈l⌉ ⌊u⌋).card : ℝ) ≤ u-l+1 := by
  rw [Int.card_Icc]
  by_cases hh : 0 ≤ ⌊u⌋+1-⌈l⌉
  · have he : ((⌊u⌋+1-⌈l⌉).toNat : ℝ)=((⌊u⌋+1-⌈l⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hh
    rw [he]
    push_cast
    linarith [Int.floor_le u,Int.le_ceil l]
  · have hz : (⌊u⌋+1-⌈l⌉).toNat=0 := Int.toNat_eq_zero.mpr (le_of_not_ge hh)
    rw [hz]
    simp only [Nat.cast_zero]
    linarith

theorem tiltColumn_card (b s : ℝ) (hs : 0 ≤ s) (x : ℤ) :
    ((tiltColumn b s x).card : ℝ) ≤ 16*s+2 := by
  have hh := int_interval_card_real_le (b*x-8*s) (b*x+8*s) (by linarith)
  simpa only [tiltColumn,Finset.card_product,Finset.card_singleton,one_mul] using
    hh.trans (by linarith)

theorem rareFast_tilt_vertices_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((rareFastVertices b 1 8 s n 0).card : ℝ) ≤ (3*(n : ℝ)+1)*(16*s+2) := by
  have hsub : rareFastVertices b 1 8 s n 0 ⊆
      (Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s) := by
    intro p hp
    have hh := (mem_rareFastVertices ..).mp hp
    have hx : -n ≤ p.1 ∧ p.1 ≤ 2*n := by
      constructor
      · have ht : -(n : ℝ) ≤ (p.1 : ℝ) := by simpa using hh.1
        exact_mod_cast ht
      · have := hh.2.1; norm_num only [sub_zero,one_add_one_eq_two] at this
        exact_mod_cast this
    have hy := abs_le.mp hh.2.2
    simp only [sub_zero,transverse] at hy
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,Finset.mem_Icc.mpr hx,?_⟩
    simp only [tiltColumn,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,true_and]
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)
  have hcount : ((Finset.Icc (-n) (2*n)).card : ℝ)=3*(n : ℝ)+1 := by
    rw [Int.card_Icc]
    have he : ((2*n+1-(-n)).toNat : ℝ)=((2*n+1-(-n) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ 2*n+1-(-n))
    rw [he]
    push_cast
    ring
  calc
    _ ≤ (((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (∑ x ∈ Finset.Icc (-n) (2*n), ((tiltColumn b s x).card : ℝ)) := by
      exact_mod_cast (Finset.card_biUnion_le :
        ((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card ≤ _)
    _ ≤ ∑ _x ∈ Finset.Icc (-n) (2*n), (16*s+2) :=
      Finset.sum_le_sum (fun x _ => tiltColumn_card b s (by linarith) x)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hcount]

/-- The internal-edge count is at most `144 * n * s`, for every lattice phase. -/
theorem rareFast_tilt_edges_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤ 144*(n : ℝ)*s := by
  have hv := rareFast_tilt_vertices_card b s n hs hn
  have he : ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤
      2*((rareFastVertices b 1 8 s n 0).card : ℝ) := by
    exact_mod_cast internalEdges_card_le (rareFastVertices b 1 8 s n 0)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul (show 3*(n : ℝ)+1 ≤ 4*n by linarith)
    (show 16*s+2 ≤ 18*s by linarith) (by linarith : 0 ≤ 16*s+2)
    (by linarith : 0 ≤ 4*(n : ℝ))
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingTilt
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.Tilt Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem crossingEvent_tilt_implication (b m a K lam s : ℝ) (n : ℤ)
    (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hs : 0 < s) (hn : 0 < n)
    (hsmall : lam*s < n) (hgain : K+16*|a|+1 < lam*m)
    (w : Edge → ℝ) (hw : w ∈ crossingEvent b m K s n 0) :
    scaleFiniteEdges (internalEdges (rareFastVertices b 1 8 s n 0)) (1-lam*s/n) w ∈
      rareFastEvent b m a 1 8 1 s n 0 := by
  rw [scaleFiniteEdges_event_iff _ _ _ (rareFastEvent_depends b m a 1 8 1 s n 0)]
  obtain ⟨p,ds,⟨hp,hq⟩,hin,hcost⟩ := hw
  have hx : ((displacement ds).1 : ℝ)=(n : ℝ) := by
    have he : (displacement ds).1=n := by simpa [Prod.fst_add,hp] using hq
    exact_mod_cast he
  have hstart : p ∈ rareFastRegion b 1 8 s n 0 := by
    have hh := hin 0 (by omega)
    simpa using hh
  have hend : p+displacement ds ∈ rareFastRegion b 1 8 s n 0 := by
    exact (mem_rareFastVertices ..).mp (pathIn_endpoint _ _ _ hin)
  have hr : |transverse b (displacement ds)| ≤ 16*s := by
    have ht := abs_sub_le (transverse b (p+displacement ds)) 0 (transverse b p)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    simp only [transverse_add,add_sub_cancel_left] at ht
    have h1 := hstart.2.2
    have h2 := hend.2.2
    simp only [sub_zero,transverse_add] at h1 h2
    linarith
  have hd := tilt_crossing_defect w b m a K lam s n hK hlam hs
    (by exact_mod_cast hn) hsmall hgain p ds hx hr hcost
  apply (mem_rareFastEvent ..).mpr
  refine ⟨p,ds,hp,hq,?_,?_⟩
  · intro i hi
    exact (mem_rareFastVertices ..).mp (hin i hi)
  · simpa using hd

theorem source_tilt_exponent_bound (N : ℕ) (lam s n : ℝ)
    (_hs : 0 ≤ s) (hn : 0 < n) (hN : (N : ℝ) ≤ 144*n*s) (hn3 : s^3 ≤ n) :
    2*N*(lam*s/n)^2 ≤ 288*lam^2 := by
  calc
    _ ≤ (2*(144*n*s))*(lam*s/n)^2 := by gcongr
    _ = (288*lam^2)*(s^3/n) := by field_simp; ring
    _ ≤ (288*lam^2)*1 := mul_le_mul_of_nonneg_left ((div_le_one hn).mpr hn3) (by positivity)
    _ = _ := mul_one _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Squared change-of-measure estimate, with a constant independent of `s`
and `n` whenever `n ≥ s^3`. -/
theorem gamma_crossing_tilt_bound {shape rate : ℝ}
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (b m a K lam s : ℝ) (n : ℤ) (hK : 0 ≤ K) (hlam : 0 ≤ lam)
    (hs : 1 ≤ s) (hn : 1 ≤ n) (hn3 : s^3 ≤ n)
    (hsmall : lam*s/n ≤ 1/2) (hgain : K+16*|a|+1 < lam*m) :
    P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ^ 2 ≤
      Real.exp (288*shape*lam^2) *
        P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a 1 8 1 s n 0} := by
  let _ := h.probability
  let S := internalEdges (rareFastVertices b 1 8 s n 0)
  let F := rareFastEvent b m a 1 8 1 s n 0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hδ : 0 ≤ lam*s/n := by positivity
  have hlt : lam*s < n := by
    have hh := (div_le_iff₀ hn0).mp hsmall
    linarith
  have himp : {ω | (fun e => τ e ω) ∈ crossingEvent b m K s n 0} ⊆
      {ω | scaleFiniteEdges S (1-lam*s/n) (fun e => τ e ω) ∈ F} := by
    intro ω hω
    exact crossingEvent_tilt_implication b m a K lam s n hK hlam (by linarith) (by omega) hlt hgain _ hω
  have hprob := measureReal_mono (μ := P) himp
  have hcomp := finite_edge_tilt_probability_sq_exp_bound h hshape hrate S (lam*s/n) hδ hsmall F
    (measurableSet_rareFastEvent ..) (rareFastEvent_depends b m a 1 8 1 s n 0)
  have hexp : Real.exp (2*shape*S.card*(lam*s/n)^2) ≤ Real.exp (288*shape*lam^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left
      (source_tilt_exponent_bound S.card lam s n (by linarith) hn0
        (rareFast_tilt_edges_card b s n hs hn) hn3) hshape.le
    nlinarith
  exact (pow_le_pow_left₀ measureReal_nonneg hprob 2).trans
    (hcomp.trans (mul_le_mul_of_nonneg_right hexp measureReal_nonneg))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedSelection
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy extraction of separated sites from square-lattice contours. -/
namespace PlanarFPP
open Finset Set

theorem orientedSelectionBox_card (n : ℕ) : (orientedSelectionBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [orientedSelectionBox, hi, pow_two]

/-- Greedy selection in a finite symmetric neighborhood system. -/
theorem separated_selection {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ a, R a a) (hsymm : ∀ a b, R a b → R b a)
    (S : Finset α) (d : ℕ)
    (hdegree : ∀ a ∈ S, (S.filter (R a)).card ≤ d) :
    ∃ T : Finset α, T ⊆ S ∧
      Set.Pairwise (↑T : Set α) (fun a b => ¬R a b) ∧ S.card ≤ d*T.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S.Nonempty
    · obtain ⟨a,ha⟩ := hs
      let U := S.filter (fun b => ¬R a b)
      have hu : U ⊆ S := filter_subset _ _
      have hau : a ∉ U := by simp [U,hrefl]
      have hlt : U ⊂ S := ⟨hu,by intro hh; exact hau (hh ha)⟩
      have hdu : ∀ b ∈ U, (U.filter (R b)).card ≤ d := by
        intro b hb
        exact (Finset.card_le_card (filter_subset_filter _ hu)).trans (hdegree b (hu hb))
      obtain ⟨T,hT,hpair,hcard⟩ := ih U hlt hdu
      have hat : a ∉ T := fun hh => hau (hT hh)
      refine ⟨insert a T,?_,?_,?_⟩
      · intro b hb
        rcases mem_insert.mp hb with rfl | hb
        · exact ha
        · exact hu (hT hb)
      · intro b hb c hc hbc
        rcases mem_insert.mp hb with rfl | hbT
        · rcases mem_insert.mp hc with rfl | hcT
          · exact False.elim (hbc rfl)
          · exact (mem_filter.mp (hT hcT)).2
        · rcases mem_insert.mp hc with rfl | hcT
          · intro hr
            exact (mem_filter.mp (hT hbT)).2 (hsymm _ _ hr)
          · exact hpair hbT hcT hbc
      · have hsplit : (S.filter (R a)).card+U.card=S.card := by
          exact card_filter_add_card_filter_not (R a)
        rw [card_insert_of_notMem hat]
        have hd := hdegree a ha
        nlinarith
    · have he : S=∅ := not_nonempty_iff_eq_empty.mp hs
      subst S
      exact ⟨∅,Finset.Subset.rfl,by simp,by simp⟩

theorem latticeNear_refl (k : ℕ) (p : Vertex) : latticeNear k p p := by
  simp [latticeNear]

theorem latticeNear_symm (k : ℕ) (p q : Vertex) : latticeNear k p q ↔ latticeNear k q p := by
  have h0 : p.1-q.1 = -(q.1-p.1) := by omega
  have h1 : p.2-q.2 = -(q.2-p.2) := by omega
  simp only [latticeNear,h0,h1,Int.natAbs_neg]

theorem near_filter_card_le (S : Finset Vertex) (k : ℕ) (p : Vertex) :
    (S.filter (latticeNear k p)).card ≤ (2*k+1)^2 := by
  classical
  have hs : S.filter (latticeNear k p) ⊆ (orientedSelectionBox k).image (fun q => p+q) := by
    intro q hq
    obtain ⟨hq0,hq1⟩ := (mem_filter.mp hq).2
    have hmem : q-p ∈ orientedSelectionBox k := by
      simp only [orientedSelectionBox,mem_product,Finset.mem_Icc,Prod.fst_sub,Prod.snd_sub]
      constructor <;> omega
    exact mem_image.mpr ⟨q-p,hmem,by abel⟩
  exact (Finset.card_le_card hs).trans ((card_image_le).trans_eq (orientedSelectionBox_card k))

/-- From N sites, retain a pairwise k-separated subfamily of size at least
N/(2k+1)^2, expressed without integer division or rounding loss. -/
theorem lattice_separated_selection (S : Finset Vertex) (k : ℕ) :
    ∃ T : Finset Vertex, T ⊆ S ∧
      Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
      S.card ≤ (2*k+1)^2*T.card := by
  exact separated_selection (latticeNear k) (latticeNear_refl k)
    (fun p q => (latticeNear_symm k p q).mp) S ((2*k+1)^2)
    (fun p _ => near_filter_card_le S k p)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SquareLoops
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed square-lattice loops, their closedness count, and bad-site count. -/
namespace PlanarFPP
open Finset

namespace SquareLoop
variable {m : ℕ}

theorem sum_delta (c : SquareLoop m) : ∑ i, (c.side i).2.delta = 0 := by
  have h := congrArg (fun f : Fin m → Vertex => ∑ i, f i) (funext c.follows)
  simp only [SquareSide.head, sum_add_distrib] at h
  rw [Equiv.sum_comp (finRotate m) (fun i => (c.side i).tail)] at h
  exact add_left_cancel (show (∑ i, (c.side i).tail) + (∑ i, (c.side i).2.delta) =
      (∑ i, (c.side i).tail) + 0 by simpa using h.symm)

theorem upLeft_count (c : SquareLoop m) : m = 2 * c.upLeftIndices.card := by
  have hx := congrArg Prod.fst c.sum_delta
  have hy := congrArg Prod.snd c.sum_delta
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at hx hy
  have hd (i : Fin m) : (1 : ℤ) =
      2 * (if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then 1 else 0) -
        ((c.side i).2.delta.2 - (c.side i).2.delta.1) := by
    cases h : (c.side i).2 <;> simp [Step.delta]
  have hs := sum_congr (s₁ := (univ : Finset (Fin m))) rfl (fun i _ => hd i)
  simp only [sum_sub_distrib, hx, hy, sub_zero, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hc : (∑ i : Fin m,
      if (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west then (1 : ℤ) else 0) =
      c.upLeftIndices.card := by
    simp [upLeftIndices, sum_boole]
  rw [← mul_sum, hc] at hs
  exact_mod_cast hs

/-- The source's m/8 lower bound, without rounding conventions. -/
theorem length_le_eight_badSites (c : SquareLoop m) (hc : c.NoRepeatedSides) :
    m ≤ 8*c.badSites.card := by
  have hs : c.upLeftIndices.image c.side ⊆ c.badSites ×ˢ (univ : Finset Step) := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_product.mpr ⟨mem_image.mpr ⟨i,hi,rfl⟩, mem_univ _⟩
  have hn : (c.upLeftIndices.image c.side).card = c.upLeftIndices.card :=
    card_image_of_injective _ hc
  have hcard := card_le_card hs
  rw [hn, card_product] at hcard
  have hfour : (univ : Finset Step).card = 4 := by decide
  rw [hfour] at hcard
  have hh := c.upLeft_count
  omega

end SquareLoop

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ContourEnumeration
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit C(m+1)^2 4^m encoding bound from cr:oriented-paths. -/
namespace PlanarFPP
open Finset

/-- At most 9(m+1)^2 4^m enclosing loops of length m = n+1, with indexed
starting side; counting these also bounds unrooted contours. -/
theorem enclosingLoop_card (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*(n+2)^2*4^(n+1) := by
  have hh := Fintype.card_le_of_injective _ (enclosingLoopCode_injective n)
  have hf : Fintype.card Step = 4 := by decide
  simp only [Fintype.card_prod, Fintype.card_coe, orientedSelectionBox_card,
    Fintype.card_fun, Fintype.card_fin, hf] at hh
  have hsq : (2*(n+2)+1)^2 ≤ 9*(n+2)^2 := by
    calc
      _ ≤ (3*(n+2))^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  exact hh.trans (Nat.mul_le_mul_right _ hsq)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedCompactness
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite branching for oriented square-lattice paths. -/
namespace PlanarFPP
open Set Finset MeasureTheory

theorem orientedSurvival_pred (G : Vertex → Prop) (p : Vertex) (n : ℕ)
    (h : orientedSurvival G p (n+1)) : orientedSurvival G p n := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    refine ⟨h.1,?_⟩
    rcases h.2 with he | hn
    · exact Or.inl (ih _ he)
    · exact Or.inr (ih _ hn)

theorem orientedSurvival_mono (G : Vertex → Prop) (p : Vertex) {m n : ℕ}
    (hmn : m ≤ n) (h : orientedSurvival G p n) : orientedSurvival G p m := by
  induction n,hmn using Nat.le_induction with
  | base => exact h
  | succ n hmn ih => exact ih (orientedSurvival_pred G p n h)

theorem oriented_surviving_successor (G : Vertex → Prop) (p : Vertex)
    (h : ∀ n, orientedSurvival G p n) :
    (∀ n, orientedSurvival G (p+(1,0)) n) ∨ (∀ n, orientedSurvival G (p+(0,1)) n) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨⟨m,hm⟩,⟨n,hn⟩⟩ := hn
  rcases (h (max m n+1)).2 with he | he
  · exact hm (orientedSurvival_mono G _ (le_max_left _ _) he)
  · exact hn (orientedSurvival_mono G _ (le_max_right _ _) he)

theorem infiniteOrientedPath_iff (G : Vertex → Prop) (p : Vertex) :
    infiniteOrientedPath G p ↔ ∀ n, orientedSurvival G p n := by
  classical
  constructor
  · rintro ⟨z,hz,hstep,hG⟩
    have hh (n m : ℕ) : orientedSurvival G (z m) n := by
      induction n generalizing m with
      | zero => trivial
      | succ n ih =>
        refine ⟨hG m,?_⟩
        have ht := ih (m+1)
        rcases hstep m with he | he
        · exact Or.inl (he ▸ ht)
        · exact Or.inr (he ▸ ht)
    intro n
    simpa [hz] using hh n 0
  · intro h
    let V := {q : Vertex // ∀ n, orientedSurvival G q n}
    have next (q : V) : ∃ r : V, r.val=q.val+(1,0) ∨ r.val=q.val+(0,1) := by
      rcases oriented_surviving_successor G q.val q.property with he | hn
      · exact ⟨⟨q.val+(1,0),he⟩,Or.inl rfl⟩
      · exact ⟨⟨q.val+(0,1),hn⟩,Or.inr rfl⟩
    let step (q : V) : V := (next q).choose
    let z : ℕ → V := Nat.rec ⟨p,h⟩ (fun _ q => step q)
    refine ⟨fun n => (z n).val,rfl,?_,?_⟩
    · intro n
      exact (next (z n)).choose_spec
    · intro n
      exact ((z n).property 1).1

theorem orientedEndpoints_nonempty_iff (G : Vertex → Prop) (p : Vertex) (n : ℕ) :
    (orientedEndpoints G p n).Nonempty ↔ orientedSurvival G p n := by
  classical
  induction n generalizing p with
  | zero => simp [orientedEndpoints,orientedSurvival]
  | succ n ih =>
    by_cases hg : G p <;> simp [orientedEndpoints,orientedSurvival,hg,Finset.union_nonempty,ih]

theorem orientedReachable_finite_of_no_infinite_path (G : Vertex → Prop) (p : Vertex)
    (h : ¬infiniteOrientedPath G p) : (orientedReachable G p).Finite := by
  classical
  rw [infiniteOrientedPath_iff] at h
  push Not at h
  obtain ⟨N,hN⟩ := h
  have hs : orientedReachable G p ⊆ ((Finset.range N).biUnion (orientedEndpoints G p) : Set Vertex) := by
    intro q hq
    obtain ⟨n,hn⟩ := mem_iUnion.mp hq
    have hsurv := (orientedEndpoints_nonempty_iff G p n).mp ⟨q,hn⟩
    have hnN : n < N := by
      by_contra hnN
      exact hN (orientedSurvival_mono G p (by omega) hsurv)
    exact mem_biUnion.mpr ⟨n,mem_range.mpr hnN,hn⟩
  exact (Finset.finite_toSet _).subset hs

theorem orientedReachable_origin (G : Vertex → Prop) (p : Vertex) : p ∈ orientedReachable G p := by
  exact mem_iUnion.mpr ⟨0,by simp [orientedEndpoints]⟩

/-- Extend a reachable finite path by a forward step from a good terminal site. -/
theorem orientedEndpoints_extend (G : Vertex → Prop) (p q : Vertex) (n : ℕ)
    (hq : q ∈ orientedEndpoints G p n) (hg : G q) :
    q+(1,0) ∈ orientedEndpoints G p (n+1) ∧ q+(0,1) ∈ orientedEndpoints G p (n+1) := by
  classical
  induction n generalizing p with
  | zero =>
    have he : q=p := by simpa [orientedEndpoints] using hq
    subst q
    simp [orientedEndpoints,hg]
  | succ n ih =>
    by_cases hp : G p
    · simp only [orientedEndpoints,ite_eq_left hp,Finset.mem_union] at hq ⊢
      rcases hq with he | hn
      · obtain ⟨h1,h2⟩ := ih _ he
        exact ⟨Or.inl h1,Or.inl h2⟩
      · obtain ⟨h1,h2⟩ := ih _ hn
        exact ⟨Or.inr h1,Or.inr h2⟩
    · simp [orientedEndpoints,hp] at hq

/-- The forward neighbors of a good reachable site are reachable. -/
theorem orientedReachable_forward (G : Vertex → Prop) (p q : Vertex)
    (hq : q ∈ orientedReachable G p) (hg : G q) :
    q+(1,0) ∈ orientedReachable G p ∧ q+(0,1) ∈ orientedReachable G p := by
  obtain ⟨n,hn⟩ := mem_iUnion.mp hq
  obtain ⟨h1,h2⟩ := orientedEndpoints_extend G p q n hn hg
  exact ⟨mem_iUnion.mpr ⟨n+1,h1⟩,mem_iUnion.mpr ⟨n+1,h2⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurableSet_orientedSurvival (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) (n : ℕ) : MeasurableSet {ω | orientedSurvival (fun v => ω ∈ G v) p n} := by
  induction n generalizing p with
  | zero => simp [orientedSurvival]
  | succ n ih =>
    exact (hG p).inter ((ih (p+(1,0))).union (ih (p+(0,1))))

theorem measurableSet_infiniteOrientedPath (G : Vertex → Set Ω) (hG : ∀ p, MeasurableSet (G p))
    (p : Vertex) : MeasurableSet {ω | infiniteOrientedPath (fun v => ω ∈ G v) p} := by
  simp only [infiniteOrientedPath_iff,ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_orientedSurvival G hG p n)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EnclosingContour
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The enclosing contour of the finite reachable set in cr:oriented-paths. -/
namespace PlanarFPP
open Finset

theorem exists_enclosing_squareLoop (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧ ∀ i, IsBoundarySide S (c.side i) := by
  classical
  obtain ⟨x,hn,hpos,_,hnext,hw⟩ := exists_boundary_cycle S h0
  let es := (boundaryPerm S).toList x
  have hlen : 0 < es.length := hpos
  have : NeZero es.length := ⟨Nat.ne_of_gt hlen⟩
  let c : SquareLoop es.length :=
    { side := fun i => (es.get i).val
      follows := by
        intro i
        have hh := hnext (es.get i) (List.get_mem es i)
        change (es.next es[i.val] (List.get_mem es i)).val.tail = es[i.val].val.head at hh
        rw [List.next_getElem es hn i.val i.isLt] at hh
        simpa only [List.get_eq_getElem, finRotate_apply, Fin.val_add,
          Fin.val_one', Nat.add_mod_mod] using hh }
  refine ⟨es.length,hlen,c,?_,?_,?_⟩
  · exact Subtype.val_injective.comp hn.injective_get
  · change (∑ i : Fin es.length, (es.get i).val.rayCross) ≠ 0
    have hh : (∑ i : Fin es.length, (es.get i).val.rayCross) =
        ∑ e ∈ es.toFinset, e.val.rayCross := by
      rw [List.sum_toFinset _ hn, ← Fin.sum_ofFn]
      have hmap : List.map (fun e : BoundarySide S => e.val.rayCross) (List.ofFn es.get) =
          List.ofFn (fun i => (es.get i).val.rayCross) := List.map_ofFn
      simpa only [List.ofFn_get] using congrArg List.sum hmap.symm
    rw [hh]
    exact hw
  · intro i
    exact (mem_boundarySides S _).mp (es.get i).property

/-- The upward and leftward sides force bad sites using exactly the source's
forward-closure condition, with no probabilistic assumption. -/
theorem SquareLoop.badSites_bad {m : ℕ} (c : SquareLoop m)
    (S : Finset Vertex) (G : Vertex → Prop)
    (hb : ∀ i, IsBoundarySide S (c.side i))
    (hforward : ∀ q ∈ S, G q → q+(1,0) ∈ S ∧ q+(0,1) ∈ S) :
    ∀ q ∈ c.badSites, ¬G q := by
  intro q hq hg
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
  have hf := hforward _ (hb i).1 hg
  have hout := (hb i).2
  rcases (mem_filter.mp hi).2 with hd | hd
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.1)
  · exact hout (by simpa [hd,Step.outward,Step.right,Step.delta] using hf.2)

/-- In the absence of an infinite good oriented path, there is an enclosing
loop with a separated family of forced-bad sites. -/
theorem no_infinite_path_enclosing_contour (G : Vertex → Prop) (k : ℕ)
    (h : ¬infiniteOrientedPath G 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : SquareLoop m,
      c.NoRepeatedSides ∧ c.winding ≠ 0 ∧
      (∀ q ∈ c.badSites, ¬G q) ∧
      ∃ T : Finset Vertex, T ⊆ c.badSites ∧
        Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) ∧
        m ≤ 8*(2*k+1)^2*T.card := by
  classical
  let hf := orientedReachable_finite_of_no_infinite_path G 0 h
  let S := hf.toFinset
  have hS (q : Vertex) : q ∈ S ↔ q ∈ orientedReachable G 0 := hf.mem_toFinset
  have h0 : (0 : Vertex) ∈ S := (hS 0).mpr (orientedReachable_origin G 0)
  obtain ⟨m,hm,c,hc,hw,hb⟩ := exists_enclosing_squareLoop S h0
  refine ⟨m,hm,c,hc,hw,?_,?_⟩
  · apply c.badSites_bad S G hb
    intro q hq hg
    have hh := orientedReachable_forward G 0 q ((hS q).mp hq) hg
    exact ⟨(hS _).mpr hh.1,(hS _).mpr hh.2⟩
  · obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
    refine ⟨T,hT,hpair,?_⟩
    have hh := c.length_le_eight_badSites hc
    nlinarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedProbability
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dependent high-density bound in crossings.tex:cr:oriented-paths.
The tests need not be stationary. -/
namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem independent_complement_inter {ι : Type*} [Fintype ι]
    (A : ι → Set Ω) (hi : iIndepSet A P) :
    P {ω | ∀ i, ω ∉ A i} = ∏ i, P (A i)ᶜ := by
  have hh := (iIndepSet_iff_iIndep A P).mp hi
  have hm (i : ι) : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i)ᶜ :=
    (MeasurableSpace.measurableSet_generateFrom (mem_singleton (A i))).compl
  have he := hh.meas_iInter hm
  have heq : {ω | ∀ i, ω ∉ A i} = ⋂ i, (A i)ᶜ := by ext ω; simp
  rw [heq]
  exact he

/-- Probability of all forced-bad sites on one fixed loop. The exponent
uses an integer threshold, avoiding a rounding loss in m/[8(2k+1)^2]. -/
theorem contour_bad_probability {m : ℕ} (c : SquareLoop m)
    (hc : c.NoRepeatedSides) (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (q : ℝ≥0∞) (hq : q ≤ 1)
    (hbad : ∀ v, P (G v)ᶜ ≤ q^(8*(2*k+1)^2)) :
    P {ω | ∀ v ∈ c.badSites, ω ∉ G v} ≤ q^m := by
  classical
  obtain ⟨T,hT,hpair,hcard⟩ := lattice_separated_selection c.badSites k
  have hlen : m ≤ (8*(2*k+1)^2)*T.card := by
    have hh := c.length_le_eight_badSites hc
    nlinarith
  calc
    _ ≤ P {ω | ∀ v : T, ω ∉ G v.val} := by
      apply measure_mono
      intro ω hω v
      exact hω v.val (hT v.property)
    _ = ∏ v : T, P (G v.val)ᶜ := independent_complement_inter _ (hind T hpair)
    _ ≤ ∏ _v : T, q^(8*(2*k+1)^2) := by
      apply Finset.prod_le_prod'
      intro v hv
      exact hbad v.val
    _ = q^((8*(2*k+1)^2)*T.card) := by simp [← pow_mul]
    _ ≤ q^m := pow_le_pow_right_of_le_one' hq hlen

theorem enclosingLoop_card_geometric (n : ℕ) :
    Fintype.card (EnclosingLoop n) ≤ 9*16^(n+1) := by
  have hp (n : ℕ) : n+2 ≤ 2^(n+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      omega
  have hsq : (n+2)^2 ≤ 4^(n+1) := by
    calc
      _ ≤ (2^(n+1))^2 := Nat.pow_le_pow_left (hp n) 2
      _ = (2^2)^(n+1) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm (n+1) 2]
      _ = _ := by norm_num
  calc
    _ ≤ 9*(n+2)^2*4^(n+1) := enclosingLoop_card n
    _ ≤ 9*(4^(n+1))*4^(n+1) := by gcongr
    _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_HighDensityOriented
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full high-density oriented-path lemma, crossings.tex:cr:oriented-paths. -/
namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
theorem no_infinite_path_subset_contours (G : Vertex → Set Ω) :
    {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ⊆
      ⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c := by
  intro ω hω
  obtain ⟨m,hm,c,hn,hw,hbad,_⟩ :=
    no_infinite_path_enclosing_contour (fun v => ω ∈ G v) 0 hω
  cases m with
  | zero => omega
  | succ n =>
    exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨⟨c,hw,hn⟩,hbad⟩⟩

omit [IsProbabilityMeasure P] in
theorem bad_contours_fixed_length (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) (n : ℕ) :
    P (⋃ c : EnclosingLoop n, badContourEvent G c) ≤
      9*(1/64 : ℝ≥0∞)^(n+1) := by
  classical
  have hc (c : EnclosingLoop n) : P (badContourEvent G c) ≤ (1/1024 : ℝ≥0∞)^(n+1) :=
    contour_bad_probability c.val c.property.2 G k hind _ (by norm_num) hbad
  have hcard : (Fintype.card (EnclosingLoop n) : ℝ≥0∞) ≤ 9*16^(n+1) := by
    exact_mod_cast enclosingLoop_card_geometric n
  calc
    _ ≤ ∑' c : EnclosingLoop n, P (badContourEvent G c) := measure_iUnion_le _
    _ = ∑ c : EnclosingLoop n, P (badContourEvent G c) := tsum_fintype _
    _ ≤ ∑ _c : EnclosingLoop n, (1/1024 : ℝ≥0∞)^(n+1) := sum_le_sum (fun c _ => hc c)
    _ = (Fintype.card (EnclosingLoop n) : ℝ≥0∞)*(1/1024)^(n+1) := by simp [nsmul_eq_mul]
    _ ≤ (9*16^(n+1))*(1/1024 : ℝ≥0∞)^(n+1) := by simpa only [mul_comm] using mul_le_mul_right hcard ((1/1024 : ℝ≥0∞)^(n+1))
    _ = _ := by
      rw [mul_assoc, ← mul_pow]
      have he : (16 : ℝ≥0∞)*(1/1024) = 1/64 := by
        apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (by norm_num)) (by simp)).mp
        norm_num
      rw [he]

omit [IsProbabilityMeasure P] in

theorem no_infinite_path_probability (G : Vertex → Set Ω) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    P {ω | ¬infiniteOrientedPath (fun v => ω ∈ G v) 0} ≤ (1/7 : ℝ≥0∞) := by
  calc
    _ ≤ P (⋃ n : ℕ, ⋃ c : EnclosingLoop n, badContourEvent G c) :=
      measure_mono (no_infinite_path_subset_contours G)
    _ ≤ ∑' n : ℕ, P (⋃ c : EnclosingLoop n, badContourEvent G c) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, 9*(1/64 : ℝ≥0∞)^(n+1) :=
      ENNReal.tsum_le_tsum (bad_contours_fixed_length G k hind hbad)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
      have hlt : (1/64 : ℝ≥0∞) < 1 := by norm_num
      have hsub : (1 - 1/64 : ℝ≥0∞) ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hlt)
      apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by norm_num) (by simpa using hsub))) (by simp)).mp
      norm_num [ENNReal.toReal_sub_of_le hlt.le]

theorem high_density_oriented_paths (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (k : ℕ)
    (hind : SeparatedGoodIndependent P G k)
    (hbad : ∀ v, P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2)) :
    0 < P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb := no_infinite_path_probability G k hind hbad
  have hm := measurableSet_infiniteOrientedPath G hG 0
  by_contra hn
  have hz : P {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  change P ({ω | infiniteOrientedPath (fun v => ω ∈ G v) 0}ᶜ) ≤ _ at hb
  rw [measure_compl hm (measure_ne_top P _), measure_univ, hz] at hb
  norm_num at hb

/-- A threshold depending only on k, with real-valued probabilities. -/
theorem high_density_oriented_paths_real_bound (k : ℕ) (G : Vertex → Set Ω)
    (hG : ∀ v, MeasurableSet (G v)) (hi : SeparatedGoodIndependent P G k)
    (hb : ∀ v, P.real (G v)ᶜ ≤ (1/1024 : ℝ)^(8*(2*k+1)^2)) :
    0 < P.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  have hb' (v : Vertex) : P (G v)ᶜ ≤ (1/1024 : ℝ≥0∞)^(8*(2*k+1)^2) := by
    have hh := ENNReal.ofReal_le_ofReal (hb v)
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)] at hh
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/1024),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1024),
      ENNReal.ofReal_one, ENNReal.ofReal_natCast] using hh
  have hp := high_density_oriented_paths G hG k hi hb'
  exact ENNReal.toReal_pos (ne_of_gt hp) (measure_ne_top P _)

/-- The same positive threshold works for every probability space and field;
the existential is outside both quantifiers, exactly as in the source. -/
theorem high_density_oriented_paths_uniform (k : ℕ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ (Ω' : Type*) [MeasurableSpace Ω']
      (P' : Measure Ω') [IsProbabilityMeasure P'] (G : Vertex → Set Ω'),
      (∀ v, MeasurableSet (G v)) → SeparatedGoodIndependent P' G k →
      (∀ v, P'.real (G v)ᶜ ≤ ζ) →
      0 < P'.real {ω | infiniteOrientedPath (fun v => ω ∈ G v) 0} := by
  refine ⟨(1/1024 : ℝ)^(8*(2*k+1)^2),pow_pos (by norm_num) _,?_⟩
  intro Ω' _ P' _ G hG hi hb
  exact high_density_oriented_paths_real_bound k G hG hi hb

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ShapeDeficit
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

/-- A supporting functional cannot be beaten by a linear amount along a
linearly bounded escaping sequence of endpoints, even if that sequence was
chosen after seeing the weights. -/
theorem UniformShape.no_linear_deficit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ f : Plane → ℝ) (hu : UniformShape w μ) (hf : ∀ v, f v ≤ μ v)
    (z : ℕ → Vertex) (ds : ℕ → List Step) (C a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1))
    (hend : ∀ n, displacement (ds n)=z n)
    (hcost : ∀ n, pathCost w 0 (ds n) ≤ f (latticeEmbed (z n))+C-a*n) : False := by
  obtain ⟨R,hR,hr⟩ := hu (a/(2*B)) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*C/a+2 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨n,hnR,hn⟩ := ((hescape.eventually (eventually_ge_atTop R)).and hlarge).exists
  have he := hr (z n) hnR
  have hlow := (abs_le.mp he).1
  have hpass := passageTime_le_cost w hw 0 (z n) (ds n) (by simpa using hend n)
  have hprod := mul_le_mul_of_nonneg_left (hbound n) (show 0 ≤ a/(2*B) by positivity)
  have hid : a/(2*B)*(B*((n : ℝ)+1))=a/2*((n : ℝ)+1) := by field_simp
  rw [hid] at hprod
  have hn' := (div_lt_iff₀ ha).mp (show 2*C/a < (n : ℝ)-2 by linarith)
  have hs := hf (latticeEmbed (z n))
  have hc := hcost n
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem crossingChain_endpoint (initialPath : List Step) (trial connector : ℕ → List Step)
    (a z : ℕ → Vertex) (hp : displacement initialPath = a 0)
    (ht : ∀ n, a n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=a (n+1)) (n : ℕ) :
    displacement (crossingChain initialPath trial connector n)=z n := by
  induction n with
  | zero => simpa only [crossingChain,displacement_append,hp] using ht 0
  | succ n ih =>
    simp only [crossingChain,displacement_append,ih,← add_assoc,hc,ht]

theorem crossingChain_defect (w : Edge → ℝ) (b m a e : ℝ)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2) (n : ℕ) :
    defect w b m a 0 (crossingChain initialPath trial connector n) ≤
      defect w b m a 0 initialPath-((n : ℝ)+1)*e+(n : ℝ)*e/2 := by
  induction n with
  | zero =>
    simp only [crossingChain,defect_append,zero_add,hp]
    have hh := htrial 0
    norm_num
    linarith
  | succ n ih =>
    rw [crossingChain,defect_append,crossingChain_endpoint initialPath trial connector p z hp ht hc,
      zero_add,defect_append,hc]
    have h1 := htrial (n+1)
    have h2 := hconnector n
    push_cast
    linarith

/-- A forward path from zero lies in its indexed layer, with nonnegative
coordinates bounded by the layer index. -/
theorem oriented_path_coordinates (v : ℕ → Vertex) (h0 : v 0=0)
    (hs : ∀ n, v (n+1)=v n+(1,0) ∨ v (n+1)=v n+(0,1)) (n : ℕ) :
    (v n).1+(v n).2=(n : ℤ) ∧ 0 ≤ (v n).1 ∧ 0 ≤ (v n).2 ∧ (v n).2 ≤ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rcases hs n with he | he <;> rw [he] <;> simp only [Prod.fst_add,Prod.snd_add] <;>
      push_cast <;> omega

/-- A crossing chain with a linear deficit contradicts the uniform shape
law when its endpoints escape with at most linear growth. -/
theorem UniformShape.no_crossing_chain (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ : Plane → ℝ) (hu : UniformShape w μ) (b m a e B : ℝ) (he : 0 < e) (hB : 0 < B)
    (hf : ∀ v, m*v 0+a*(v 1-b*v 0) ≤ μ v)
    (initialPath : List Step) (trial connector : ℕ → List Step) (p z : ℕ → Vertex)
    (hp : displacement initialPath=p 0)
    (ht : ∀ n, p n+displacement (trial n)=z n)
    (hc : ∀ n, z n+displacement (connector n)=p (n+1))
    (htrial : ∀ n, defect w b m a (p n) (trial n) ≤ -e)
    (hconnector : ∀ n, defect w b m a (z n) (connector n) ≤ e/2)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1)) : False := by
  apply hu.no_linear_deficit w hw μ (fun v => m*v 0+a*(v 1-b*v 0)) hf z
    (crossingChain initialPath trial connector) (defect w b m a 0 initialPath) (e/2) B
    (by linarith) hB hescape hbound
    (crossingChain_endpoint initialPath trial connector p z hp ht hc)
  intro n
  have hh := crossingChain_defect w b m a e initialPath trial connector p z hp ht hc htrial hconnector n
  rw [defect,crossingChain_endpoint initialPath trial connector p z hp ht hc] at hh
  simp only [support,transverse] at hh
  change pathCost w 0 (crossingChain initialPath trial connector n) ≤
    m*(z n).1+a*((z n).2-b*(z n).1)+defect w b m a 0 initialPath-e/2*n
  linarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem centers_close_of_point (a b t R : ℝ)
    (ha : |t-a| ≤ R) (hb : |t-b| ≤ R) : |a-b| ≤ 2*R := by
  have hh := abs_sub_le (t-b) 0 (t-a)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have he : (t-b)-(t-a)=a-b := by ring
  rw [he] at hh
  linarith

/-- Sharing one support vertex bounds both transformed lattice indices.
Crucially these bounds contain neither M nor D0. -/
theorem blockRegion_common_indices (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) :
    |((blockLayer v-blockLayer w : ℤ) : ℝ)| ≤ 2*(A+3) ∧
    |((blockLevel v-blockLevel w : ℤ) : ℝ)| ≤ 8 := by
  have hx := centers_close_of_point _ _ _ _ hv.1 hw.1
  have hy := centers_close_of_point _ _ _ _ hv.2 hw.2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hxx : |(blockX n d v : ℝ)-(blockX n d w : ℝ)| =
      |((blockLayer v-blockLayer w : ℤ) : ℝ)| *((n : ℝ)+d) := by
    simp only [blockX, Int.cast_mul, Int.cast_add, Int.cast_sub]
    rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+d)]
  have hyy : |blockY σ S v-blockY σ S w| =
      |((blockLevel v-blockLevel w : ℤ) : ℝ)| *S := by
    have he : blockY σ S v-blockY σ S w =
        σ*((blockLevel v : ℝ)-(blockLevel w : ℝ))*S := by unfold blockY; ring
    rw [he,abs_mul,abs_mul,hσ,one_mul,abs_of_pos hS,Int.cast_sub]
  rw [hxx] at hx
  rw [hyy] at hy
  constructor
  · nlinarith [mul_nonneg (abs_nonneg (((blockLayer v-blockLayer w : ℤ) : ℝ))) hd']
  · nlinarith

theorem blockRegion_common_near (b A : ℝ) (n d : ℤ) (σ S : ℝ) (k : ℕ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S)
    (hA : 0 ≤ A+3) (hk : 4*(A+3)+8 ≤ k)
    (v w p : Vertex) (hv : p ∈ blockRegion b A n d σ S v)
    (hw : p ∈ blockRegion b A n d σ S w) : latticeNear k v w := by
  obtain ⟨hi,hj⟩ := blockRegion_common_indices b A n d σ S hn hd hσ hS v w p hv hw
  have he1 : ((v.1-w.1 : ℤ) : ℝ) =
      2*((blockLayer v-blockLayer w : ℤ) : ℝ)-((blockLevel v-blockLevel w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have he2 : ((v.2-w.2 : ℤ) : ℝ) =
      ((blockLevel v-blockLevel w : ℤ) : ℝ)-((blockLayer v-blockLayer w : ℤ) : ℝ) := by
    simp [blockLayer,blockLevel]; ring
  have hx : |((v.1-w.1 : ℤ) : ℝ)| ≤ k := by
    rw [he1]
    have hh := abs_sub_le (2*((blockLayer v-blockLayer w : ℤ) : ℝ)) 0
      (((blockLevel v-blockLevel w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hh
    linarith
  have hy : |((v.2-w.2 : ℤ) : ℝ)| ≤ k := by
    rw [he2]
    have hh := abs_sub_le (((blockLevel v-blockLevel w : ℤ) : ℝ)) 0
      (((blockLayer v-blockLayer w : ℤ) : ℝ))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith
  have hx' : -(k : ℤ) ≤ v.1-w.1 ∧ v.1-w.1 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hx).1
    · exact_mod_cast (abs_le.mp hx).2
  have hy' : -(k : ℤ) ≤ v.2-w.2 ∧ v.2-w.2 ≤ k := by
    constructor
    · exact_mod_cast (abs_le.mp hy).1
    · exact_mod_cast (abs_le.mp hy).2
  dsimp [latticeNear]
  omega

/-- A radius uniform in the connector gap works at every positive scale. -/
theorem blockRegion_disjoint (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (v w : Vertex) (hvw : ¬latticeNear (⌈4*(A+3)+8⌉₊+1) v w) :
    Disjoint (blockRegion b A n d σ S v) (blockRegion b A n d σ S w) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  apply hvw
  apply blockRegion_common_near b A n d σ S _ hn hd hσ hS (by linarith) _ v w p hp hq
  have hh := Nat.le_ceil (4*(A+3)+8)
  push_cast
  linarith

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Tests supported on sufficiently separated finite block regions are
jointly independent, as required by Lemma `cr:oriented-paths`. -/
theorem block_supported_tests_independent (h : GammaEnvironment shape rate P τ)
    (b A : ℝ) (n d : ℤ) (σ S : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hσ : |σ|=1) (hS : 0 < S) (hA : 0 < A)
    (E : Vertex → Set (Edge → ℝ)) (hE : ∀ v, MeasurableSet (E v))
    (hsupport : ∀ v, DependsOnEdges (E v) (internalEdges (blockVertices b A n d σ S v))) :
    SeparatedGoodIndependent P (fun v => {ω | (fun e => τ e ω) ∈ E v})
      (⌈4*(A+3)+8⌉₊+1) := by
  intro T hT
  apply Grid.disjoint_edge_events_iIndepSet h (fun v : T => E v.val)
    (fun v : T => internalEdges (blockVertices b A n d σ S v.val))
    (fun v => hE v.val) (fun v => hsupport v.val)
  intro v w hvw
  apply internalEdges_disjoint
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hsep := hT v.property w.property (fun hh => hvw (Subtype.ext hh))
  exact Set.disjoint_left.mp (blockRegion_disjoint b A n d σ S hn hd hσ hS hA v.val w.val hsep)
    ((mem_blockVertices ..).mp hp) ((mem_blockVertices ..).mp hq)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingEndpointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem crossing_endpoints_escape_linear (b σ S : ℝ) (n d : ℤ)
    (hb : |b| ≤ 1) (hσ : |σ|=1) (hS : 0 < S) (hn : 0 < n) (hd : 0 ≤ d)
    (v z : ℕ → Vertex) (hv0 : v 0=0)
    (hstep : ∀ t, v (t+1)=v t+(1,0) ∨ v (t+1)=v t+(0,1))
    (hx : ∀ t, (z t).1=blockX n d (v t)+n)
    (hr : ∀ t, |transverse b (z t)-blockY σ S (v t)| ≤ S/4) :
    Tendsto (fun t => ‖latticeEmbed (z t)‖) atTop atTop ∧
    ∀ t, ‖latticeEmbed (z t)‖ ≤ (2*((n : ℝ)+d)+3*S)*((t : ℝ)+1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hcoords (t : ℕ) := oriented_path_coordinates v hv0 hstep t
  have hxt (t : ℕ) : ((z t).1 : ℝ) = (t : ℝ)*((n : ℝ)+d)+n := by
    rw [hx]
    simp only [blockX,blockLayer,Int.cast_add,Int.cast_mul]
    have hh := congrArg (fun a : ℤ => (a : ℝ)) (hcoords t).1
    push_cast at hh
    rw [hh]
  have hxpos (t : ℕ) : (t : ℝ)+1 ≤ ((z t).1 : ℝ) := by
    rw [hxt]
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have hnlow (t : ℕ) : (t : ℝ) ≤ ‖latticeEmbed (z t)‖ := by
    have hh := plane_coordinate_le_norm (latticeEmbed (z t)) 0
    change |((z t).1 : ℝ)| ≤ _ at hh
    have hp : (0 : ℝ) ≤ (z t).1 := by linarith [Nat.cast_nonneg (α := ℝ) t,hxpos t]
    rw [abs_of_nonneg hp] at hh
    linarith [hxpos t]
  refine ⟨tendsto_atTop_mono hnlow tendsto_natCast_atTop_atTop,?_⟩
  intro t
  have hlevel : (0 : ℝ) ≤ blockLevel (v t) ∧ (blockLevel (v t) : ℝ) ≤ 2*t := by
    have hh := hcoords t
    constructor <;> dsimp [blockLevel] <;> exact_mod_cast (by omega : _)
  have hy : |blockY σ S (v t)| ≤ 2*(t : ℝ)*S := by
    unfold blockY
    rw [abs_mul,abs_mul,hσ,one_mul,abs_of_nonneg hlevel.1,abs_of_pos hS]
    exact mul_le_mul_of_nonneg_right hlevel.2 hS.le
  have hrbound : |transverse b (z t)| ≤ 2*(t : ℝ)*S+S/4 := by
    have hh := abs_add_le (transverse b (z t)-blockY σ S (v t)) (blockY σ S (v t))
    rw [sub_add_cancel] at hh
    linarith [hr t]
  have hpos : (0 : ℝ) ≤ (z t).1 := by linarith [hxpos t,Nat.cast_nonneg (α := ℝ) t]
  have hyy : |((z t).2 : ℝ)| ≤ |transverse b (z t)|+((z t).1 : ℝ) := by
    have hh := abs_add_le (transverse b (z t)) (b*((z t).1 : ℝ))
    have he : transverse b (z t)+b*((z t).1 : ℝ)=((z t).2 : ℝ) := by unfold transverse; ring
    rw [he,abs_mul,abs_of_nonneg hpos] at hh
    have hm := mul_le_mul_of_nonneg_right hb hpos
    linarith
  have hnorm := plane_norm_le_coordinates (latticeEmbed (z t))
  change ‖latticeEmbed (z t)‖ ≤ |((z t).1 : ℝ)|+|((z t).2 : ℝ)| at hnorm
  rw [abs_of_nonneg hpos] at hnorm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  rw [hxt] at hyy hnorm
  nlinarith

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem nearest_integer_error (t : ℝ) : |(⌊t+1/2⌋ : ℝ)-t| ≤ 1/2 := by
  have hlo := Int.floor_le (t+1/2)
  have hhi := Int.lt_floor_add_one (t+1/2)
  apply abs_le.mpr
  constructor <;> linarith

theorem trialTranslate_error (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) :
    |transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)| ≤ 1/2 := by
  have hh := nearest_integer_error (b*X+Y+trialOffset M R s j)
  convert hh using 1
  simp [trialTranslate,transverse]
  congr 1
  ring

theorem trialSpacing_bounds (R s : ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    1 ≤ trialSpacing R s ∧ R*s ≤ trialSpacing R s := by
  have hc := Nat.le_ceil s
  have hn : (1 : ℝ) ≤ (⌈s⌉₊ : ℝ) := by linarith
  unfold trialSpacing
  constructor
  · nlinarith
  · nlinarith

theorem trialOffset_bound (M : ℕ) (R s : ℝ) (j : Fin M)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    |trialOffset M R s j| ≤ 3*M*trialSpacing R s := by
  have hB := (trialSpacing_bounds R s hR hs).1
  have hj : (j.val : ℝ)+1 ≤ M := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha : |2*((j.val : ℝ)+1)-(M : ℝ)-1| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith
  unfold trialOffset
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<3),abs_of_nonneg (show 0 ≤ trialSpacing R s by linarith)]
  nlinarith

/-- Every translated strip of half-width `R*s` lies inside its `S₀/4`
window, including the half-unit lattice-phase error. -/
theorem trial_strip_in_window (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (p : Vertex) (hp : |transverse b p-transverse b (trialTranslate b X Y M R s j)| ≤ R*s) :
    |transverse b p-Y| ≤ trialWindow M R s/4 := by
  have he := trialTranslate_error b X Y M R s j
  have ho := trialOffset_bound M R s j hR hs
  have hB := trialSpacing_bounds R s hR hs
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast j.pos
  have hh := abs_add_le
    (transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j))
    (trialOffset M R s j)
  have heq : transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)+
      trialOffset M R s j = transverse b (trialTranslate b X Y M R s j)-Y := by ring
  rw [heq] at hh
  have ht := abs_add_le (transverse b p-transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s j)-Y)
  rw [sub_add_sub_cancel] at ht
  unfold trialWindow
  nlinarith [mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ trialSpacing R s)]

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem internalEdges_mono {V W : Finset Vertex} (h : V ⊆ W) :
    internalEdges V ⊆ internalEdges W := by
  intro e he
  obtain ⟨hp,hq⟩ := (mem_internalEdges e V).mp he
  exact (mem_internalEdges e W).mpr ⟨h hp,h hq⟩

theorem DependsOnEdges.mono {E : Set (Edge → ℝ)} {S T : Finset Edge}
    (h : DependsOnEdges E S) (hst : S ⊆ T) : DependsOnEdges E T := by
  intro w w' hh
  exact h w w' (fun e he => hh e (hst he))

theorem rareFastVertices_subset_block (b A R s σ : ℝ) (n d : ℤ) (v : Vertex)
    (M : ℕ) (j : Fin M) (_hA : 0 ≤ A) (hn : 0 ≤ n) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    rareFastVertices b A R s n
      (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) ⊆
      blockVertices b A n d σ (trialWindow M R s) v := by
  intro p hp
  have hh := (mem_rareFastVertices ..).mp hp
  have htrans : transverse b (p-trialTranslate b (blockX n d v)
      (blockY σ (trialWindow M R s) v) M R s j)=transverse b p-
      transverse b (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) := by
    simp [transverse]; ring
  have hw := trial_strip_in_window b (blockX n d v) (blockY σ (trialWindow M R s) v)
    M R s j hR hs p (by rw [← htrans]; exact hh.2.2)
  have hS : 0 ≤ trialWindow M R s := by
    have := (trialWindow_scale_bounds M j.pos R s hR hs).1
    linarith
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,by linarith⟩
  · have hl := hh.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hl
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  · have hu := hh.2.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hu
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

theorem connectorVertices_subset_block (b A s σ S : ℝ) (n d : ℤ) (v : Vertex)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (_hs : 0 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    connectorVertices b (blockX n d v+n) d (blockY σ S v) S s ⊆
      blockVertices b A n d σ S v := by
  intro p hp
  have hh := (mem_connectorVertices ..).mp hp
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,hh.2.2⟩
  all_goals
    have hl := hh.1
    have hu := hh.2.1
    simp only [Int.cast_add] at hl hu
    have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (0 : ℝ) ≤ n := by linarith
    nlinarith

theorem measurableSet_goodSiteEvent (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) :
    MeasurableSet (goodSiteEvent μ b A R ε s plus n d M v) := by
  change MeasurableSet ({w | ∃ j : Fin M, w ∈ siteTrial μ b A R ε s plus n d M v j} ∩
    (siteConnector μ b R ε s plus n d M v 1 ∩ siteConnector μ b R ε s plus n d M v 2))
  apply MeasurableSet.inter
  · simp only [ofPred_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_rareFastEvent ..)
  · exact (measurableSet_allPairsRegionEvent ..).inter (measurableSet_allPairsRegionEvent ..)

theorem goodSiteEvent_depends (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    DependsOnEdges (goodSiteEvent μ b A R ε s plus n d M v)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) := by
  have hn0 : 0 ≤ n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have ht (j : Fin M) : DependsOnEdges (siteTrial μ b A R ε s plus n d M v j)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (rareFastEvent_depends b (μ (direction b)) (extremeSlope μ b plus) A R ε s n _).mono
      (internalEdges_mono (rareFastVertices_subset_block b A R s (contactSign plus) n d v M j hA hn0 hR hs))
  have hc (a : ℝ) : DependsOnEdges (siteConnector μ b R ε s plus n d M v a)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (allPairsRegionEvent_depends _ _ _ _).mono
      (internalEdges_mono (connectorVertices_subset_block b A s (contactSign plus)
        (trialWindow M R s) n d v hA hd (by linarith) hn))
  intro w w' hh
  change ((∃ j, w ∈ siteTrial μ b A R ε s plus n d M v j) ∧ _ ∧ _) ↔ _
  exact and_congr (exists_congr (fun j => ht j w w' hh))
    (and_congr (hc 1 w w' hh) (hc 2 w w' hh))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_independent (h : GammaEnvironment shape rate P τ)
    (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hM : 0 < M) (hA : 0 < A) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    SeparatedGoodIndependent P
      (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent μ b A R ε s plus n d M v})
      (⌈4*(A+3)+8⌉₊+1) := by
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  exact block_supported_tests_independent h b A n d (contactSign plus) (trialWindow M R s)
    hn0 hd (abs_contactSign plus) hS hA _ (fun v => measurableSet_goodSiteEvent ..)
    (fun v => goodSiteEvent_depends μ b A R ε s plus n d M v hA.le hd hR hs hn)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSitePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem goodSite_trial_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (w : Edge → ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v) :
    ∃ p ds,
      p ∈ connectorWindow b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v)
        (trialWindow M R s) ∧
      p+displacement ds ∈ connectorWindow b (blockX n d v+n)
        (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s) ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds < -ε*s := by
  obtain ⟨j,hj⟩ := hg.1
  obtain ⟨p,ds,hp,hq,hin,hcost⟩ := (mem_rareFastEvent ..).mp hj
  have hw (q : Vertex) (hq : q ∈ rareFastRegion b A R s n
      (trialTranslate b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v) M R s j)) :
      |transverse b q-blockY (contactSign plus) (trialWindow M R s) v| ≤ trialWindow M R s/4 := by
    apply trial_strip_in_window b (blockX n d v)
      (blockY (contactSign plus) (trialWindow M R s) v) M R s j hR hs q
    convert hq.2.2 using 1
    simp [transverse]
    congr 1
    ring
  refine ⟨p,ds,⟨hp,hw p ?_⟩,⟨hq,hw _ (pathIn_endpoint _ _ _ hin)⟩,hcost⟩
  simpa using hin 0 (by omega)

theorem sourceSupportCost_of_endpoint (μ : Plane → ℝ) (b ε s : ℝ) (plus : Bool)
    (p q : Vertex) (ds : List Step) (hd : p+displacement ds=q) :
    sourceSupportCost μ b plus ε s p q =
      support b (μ (direction b)) (extremeSlope μ b plus) (displacement ds)+ε*s/2 := by
  have he : q-p=displacement ds := by rw [← hd]; abel
  simp [sourceSupportCost,he,support,transverse,latticeEmbed]

/-- Both forward neighbors are exactly the two tested endpoint windows. -/
theorem goodSite_connector_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v v' : Vertex) (w : Edge → ℝ)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v)
    (hstep : v'=v+(1,0) ∨ v'=v+(0,1))
    (p q : Vertex)
    (hp : p ∈ connectorWindow b (blockX n d v+n)
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s))
    (hq : q ∈ connectorWindow b (blockX n d v')
      (blockY (contactSign plus) (trialWindow M R s) v') (trialWindow M R s)) :
    ∃ ds, p+displacement ds=q ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
  have htest (a : ℝ) (hc : w ∈ siteConnector μ b R ε s plus n d M v a)
      (hX : blockX n d v'=blockX n d v+n+d)
      (hY : blockY (contactSign plus) (trialWindow M R s) v'=
        blockY (contactSign plus) (trialWindow M R s) v+contactSign plus*a*trialWindow M R s) :
      ∃ ds, p+displacement ds=q ∧
        defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
    have hq' := hq
    rw [hX,hY] at hq'
    obtain ⟨ds,hd,_,hcost⟩ := (mem_allPairsRegionEvent _ _ _ _ w).mp hc p hp q hq'
    refine ⟨ds,hd,?_⟩
    rw [sourceSupportCost_of_endpoint μ b ε s plus p q ds hd] at hcost
    unfold defect
    linarith
  rcases hstep with rfl | rfl
  · apply htest 1 hg.2.1
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring
  · apply htest 2 hg.2.2
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring

/-- At every fixed admissible scale, an infinite path of actual good sites is
incompatible with the origin shape law. Adaptive endpoint choices are allowed. -/
theorem UniformShape.no_goodSite_path (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (hu : UniformShape w μ) :
    ¬infiniteOrientedPath (fun v => w ∈ goodSiteEvent μ b A R ε s plus n d M v) 0 := by
  rintro ⟨v,hv0,hstep,hgood⟩
  choose p trial hp hz ht using (fun t =>
    goodSite_trial_witness μ b A R ε s plus n d M (v t) w hR hs (hgood t))
  let z := fun t => p t+displacement (trial t)
  choose connector hc hcost using (fun t =>
    goodSite_connector_witness μ b A R ε s plus n d M (v t) (v (t+1)) w
      (hgood t) (hstep t) (z t) (p (t+1)) (hz t) (hp (t+1)))
  obtain ⟨initialPath,hinit⟩ := exists_path 0 (p 0)
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  obtain ⟨hescape,hbound⟩ := crossing_endpoints_escape_linear b (contactSign plus)
    (trialWindow M R s) n d hb (abs_contactSign plus) hS hn hd v z hv0 hstep
    (fun t => (hz t).1) (fun t => (hz t).2)
  have hf : ∀ u : Plane, μ (direction b)*u 0+extremeSlope μ b plus*(u 1-b*u 0) ≤ μ u := by
    have hh := planar_extreme_supports μ hμ b
    cases plus
    · exact hh.1
    · exact hh.2.1
  apply hu.no_crossing_chain w hw μ b (μ (direction b)) (extremeSlope μ b plus) (ε*s)
    (2*((n : ℝ)+d)+3*trialWindow M R s) (by positivity) (by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
      positivity) hf initialPath trial connector p z (by simpa using hinit)
    (fun _ => rfl) hc (fun t => by have := (ht t).le; linarith) hcost hescape hbound

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- The almost-sure uniform Gamma shape theorem gives probability zero for
an infinite good-site path. -/
theorem gamma_goodSite_path_probability_zero (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M) :
    P {ω | infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n d M v) 0}=0 := by
  have hh : ∀ᵐ ω ∂P, ¬infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n d M v) 0 := by
    filter_upwards [h.ae_positive,h.uniform_shape hshape hrate] with ω hw hu
    exact UniformShape.no_goodSite_path (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b A R ε s plus n d M hb hR hε hs hn hd hM
      (fun e => τ e ω) (fun e => (hw e).le) hu
  simpa only [ae_iff,not_not] using hh

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RareFast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Quantitative rare-fast bound in terms of an integer ceiling. -/
theorem gamma_rareFast_eventually (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 ≤ 1) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ᶠ s : ℝ in atTop, ∀ n : ℤ,
      (⌈D0*s⌉ : ℝ)+s ≤ n →
      P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} < p0 := by
  let _ := h.probability
  let k : ℕ := ⌈4*(A+3)+8⌉₊+1
  obtain ⟨ζ,hζ,hpaths⟩ := high_density_oriented_paths_uniform k
  have htM := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1-p0)
    (by linarith : 1-p0 < 1)
  obtain ⟨M,hpow,hM⟩ := ((htM.eventually (gt_mem_nhds (by linarith : 0 < ζ/2))).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hM0 : 0 < M := by omega
  obtain ⟨D0,hD0,hbad⟩ := gamma_goodSiteEvent_failure h hshape hrate b A R ε hb plus M hM0 hR hε
  refine ⟨D0,hD0,?_⟩
  filter_upwards [hbad (ζ/2) (by linarith),eventually_ge_atTop (1 : ℝ)] with s hbs hs
  intro n hn
  have hd0 : (0 : ℝ) ≤ (⌈D0*s⌉ : ℤ) := by
    have := Int.le_ceil (D0*s)
    nlinarith
  have hd : 0 ≤ (⌈D0*s⌉ : ℤ) := by exact_mod_cast hd0
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  by_contra hlow
  have hl : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} := le_of_not_gt hlow
  have hg (v : Vertex) : P.real {ω | (fun e => τ e ω) ∉
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} ≤ ζ := by
    have := hbs n v p0 hl
    linarith
  have hi := goodSiteEvent_independent h (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M hM0 hA hd hR hs hn
  have hp := hpaths Ω P
    (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v})
    (fun v => (measurableSet_goodSiteEvent ..).preimage (Measurable.of_eval h.measurable)) hi hg
  have hz := gamma_goodSite_path_probability_zero h hshape hrate b A R ε s plus n ⌈D0*s⌉ M
    hb hR hε hs hn0 hd hM0
  unfold Measure.real at hp
  simp only [mem_ofPred_eq] at hp
  rw [hz] at hp
  simp at hp

/-- Exact two-parameter epsilon formulation: once s and n/s are large,
the probability of the manuscript's strict localized event is small. -/
theorem gamma_rareFast_bound (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S K : ℝ, 1 ≤ S ∧ 0 < K ∧ ∀ s : ℝ, S ≤ s → ∀ n : ℤ,
      K*s ≤ n → P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} < κ := by
  let p0 := min κ 1
  have hp0 : 0 < p0 := lt_min hκ (by norm_num)
  obtain ⟨D0,hD0,hh⟩ := gamma_rareFast_eventually h hshape hrate b A R ε hb hA hR hε plus p0 hp0
    (min_le_right _ _)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hh
  refine ⟨max S 1,D0+2,le_max_right _ _,by linarith,?_⟩
  intro s hs n hn
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hc : (⌈D0*s⌉ : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
  exact (hS s ((le_max_left _ _).trans hs) n (by nlinarith)).trans_le (min_le_left _ _)

/-- Rare-fast joint limit along arbitrary filters with `s → ∞` and
`n/s → ∞`, where `n` is integer-valued and eventually positive. -/
theorem gamma_rareFast_tendsto {ι : Type*} {l : Filter ι}
    (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (s : ι → ℝ) (n : ι → ℤ)
    (hs : Tendsto s l atTop) (hn : Tendsto (fun i => (n i : ℝ)/s i) l atTop) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε (s i) (n i) 0}) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro κ hκ
    obtain ⟨S,K,hS,_,hh⟩ := gamma_rareFast_bound h hshape hrate b A R ε hb hA hR hε plus κ hκ
    filter_upwards [hs.eventually (eventually_ge_atTop S),hn.eventually (eventually_ge_atTop K)] with i hsi hni
    apply hh (s i) hsi (n i)
    exact (le_div_iff₀ (by linarith : 0 < s i)).mp hni

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

/-- A stronger form of gr:tilt: any integer n >= s^3 works. In particular,
no dyadic-grid property is used in the measure-change argument. -/
theorem gamma_crossing_cubic_tendsto {ι : Type*} {l : Filter ι}
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate) (b K : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (s : ι → ℝ) (n : ι → ℤ) (hs : Tendsto s l atTop)
    (hn3 : ∀ᶠ i in l, (s i)^3 ≤ n i) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K (s i) (n i) 0}) l (𝓝 0) := by
  let m := (gammaMeanNorm h hshape hrate) (direction b)
  let a := extremeSlope (gammaMeanNorm h hshape hrate) b true
  let lam := (K+16*|a|+2)/m
  have hm : 0 < m := norm_direction_pos (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hgain : K+16*|a|+1 < lam*m := by
    dsimp [lam]
    rw [div_mul_cancel₀ _ (ne_of_gt hm)]
    linarith
  have hratio : Tendsto (fun i => (n i : ℝ)/s i) l atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 B)),hn3] with i hsi hni
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hsB : B ≤ s i := (le_max_right _ _).trans hsi
    apply (le_div_iff₀ (by linarith : 0 < s i)).mpr
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    nlinarith [mul_le_mul_of_nonneg_right hsB (by linarith : 0 ≤ s i)]
  have hrare := gamma_rareFast_tendsto h hshape hrate b 1 8 1 hb (by norm_num) (by norm_num)
    (by norm_num) true s n hs hratio
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le measureReal_nonneg)
  · intro κ hκ
    have hC : 0 < Real.exp (288*shape*lam^2) := Real.exp_pos _
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 (2*lam))),hn3,
      (tendsto_order.1 hrare).2 (κ^2/Real.exp (288*shape*lam^2)) (by positivity)] with i hsi hni hpi
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hslam : 2*lam ≤ s i := (le_max_right _ _).trans hsi
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    have hn1 : (1 : ℝ) ≤ n i := by nlinarith
    have hn1' : 1 ≤ n i := by exact_mod_cast hn1
    have hsmall : lam*s i/(n i : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n i)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hslam (by linarith : 0 ≤ s i)]
    have hh := gamma_crossing_tilt_bound h hshape hrate b m a K lam (s i) (n i) hK hlam.le hs1 hn1' hni hsmall hgain
    have hh' := (lt_div_iff₀ hC).mp hpi
    nlinarith [measureReal_nonneg (μ := P) (s := {ω | (fun e => τ e ω) ∈ crossingEvent b m K (s i) (n i) 0})]

/-- Dyadic tilt limit with a Gamma geometric and coordinate allowance. -/
theorem gamma_source_tilt (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b : ℝ) (hb : |b| ≤ 1) :
    Tendsto (fun k : ℕ => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) ((2 : ℝ)^k) ((2 : ℤ)^(3*k)) 0})
      atTop (𝓝 0) := by
  apply gamma_crossing_cubic_tendsto h hshape hrate b (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) hb
    (by unfold sourceCrossingK; positivity) (fun k : ℕ => (2 : ℝ)^k) (fun k => (2 : ℤ)^(3*k))
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  apply Eventually.of_forall
  intro k
  norm_num only [Int.cast_pow,Int.cast_ofNat]
  rw [← pow_mul,Nat.mul_comm k 3]

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CharacteristicLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem firstDyadicExponent_spec (p : ℕ → ℝ) (q : ℝ) (h : ∃ j, p j ≤ q) :
    p (firstDyadicExponent p q) ≤ q := by
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_spec h

theorem firstDyadicExponent_le (p : ℕ → ℝ) (q : ℝ) (j : ℕ) (hj : p j ≤ q) :
    firstDyadicExponent p q ≤ j := by
  have h : ∃ j, p j ≤ q := ⟨j,hj⟩
  simpa only [firstDyadicExponent,dite_eq_left h] using Nat.find_min' h hj

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

/-- The first dyadic crossing threshold exists and occurs by `2^(3*k)`. -/
theorem gamma_characteristic_lengths_exist_oai (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop,
      characteristicExponent P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ 3*k ∧
      P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b)
        ((2 : ℝ)^k) (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k) 0} ≤ q := by
  filter_upwards [(gamma_source_tilt h hshape hrate b hb).eventually (gt_mem_nhds hq)] with k hk
  have hh : sourceDyadicCrossingProbability P τ shape rate (gammaMeanNorm h hshape hrate) b k (3*k) ≤ q := hk.le
  exact ⟨firstDyadicExponent_le _ _ _ hh,firstDyadicExponent_spec _ _ ⟨3*k,hh⟩⟩

end GammaFPP.CrossingBridge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist_oai.{u_1} := @OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist_oai.{u_1}
