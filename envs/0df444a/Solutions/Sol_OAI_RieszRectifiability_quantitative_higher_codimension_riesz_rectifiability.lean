-- Prove2me | solution 1 for OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:32.864205+00:00
-- url     : https://prove2.me/submissions/c2f8b64e-6dcd-4162-8f4e-b58122894475

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic
import Mathlib.Topology.Defs.Basic
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_activeRegionSurface_charts
import Theorems.Thm_OAI_RieszRectifiability_active_region_positive_stopping_scale_local_ball_area_ge
import Theorems.Thm_OAI_RieszRectifiability_quantitative_selected_restart_uniform_deficit
import Theorems.Thm_OAI_RieszRectifiability_quantitative_uniform_restart_surface_pieces

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_EuclideanPackingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal Function

theorem euclidean_separated_card_mul_radius_pow_le {k : ℕ}
    (s : Finset (Ambient k)) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * r ≤ dist x y) :
    (s.card : ℝ) * r ^ k ≤ (R + r) ^ k := by
  let μ : Measure (Ambient k) := volume
  let A := ⋃ x ∈ s, ball x r
  have hd : Set.Pairwise (s : Set (Ambient k)) (Disjoint on fun x => ball x r) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    simpa only [two_mul] using! hsep x hx y hy hxy
  have hsub : A ⊆ ball (0 : Ambient k) (R + r) := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs x hx]
  have hRp : 0 < R + r := add_pos_of_nonneg_of_pos hR hr
  have hi :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ k) * μ (ball 0 1) ≤
        ENNReal.ofReal ((R + r) ^ k) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ x ∈ s, ball x r from rfl,
          measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hr, finrank_euclideanSpace_fin,
          Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : Ambient k) (R + r)) := measure_mono hsub
      _ = _ := by
        simp only [μ.addHaar_ball_of_pos _ hRp, finrank_euclideanSpace_fin]
  have hj : (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ k) ≤
      ENNReal.ofReal ((R + r) ^ k) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hi
  have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hRp.le k) hj
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hr.le k)] using! h

theorem euclidean_separated_card_le {k : ℕ}
    (s : Finset (Ambient k)) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r) / r) ^ k := by
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hr k)).mpr
    (euclidean_separated_card_mul_radius_pow_le s R r hR hr hs hsep)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineTubeCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covering tubes around affine planes

Affine orthogonal projection is distance nonincreasing. Combining this estimate with
Euclidean ball nets gives finite covers of bounded tubes, with a cardinality estimate
in the dimension of the plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem affine_projection_difference {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (x y : Ambient d) :
    (orthogonalProjection S x : Ambient d) - (orthogonalProjection S y : Ambient d) =
      S.direction.starProjection (x - y) := by
  rw [orthogonalProjection_apply', orthogonalProjection_apply']
  simp only [Submodule.coe_orthogonalProjectionOnto_apply, vsub_eq_sub, vadd_eq_add]
  rw [add_sub_add_right_eq_sub, ← map_sub, sub_sub_sub_cancel_right]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem directedBallDeviation_bddAbove {d : ℕ} (s t : Set (Ambient d)) (ht : t.Nonempty)
    (a : Ambient d) (r : ℝ) : BddAbove ((fun x => infDist x t) '' (ball a r ∩ s)) := by
  obtain ⟨y, hy⟩ := ht
  refine ⟨r + dist a y, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have hx' : dist x a ≤ r := hx.1.le
  exact (infDist_le_dist_of_mem hy).trans ((dist_triangle x a y).trans (by linarith))

theorem directedBallDeviation_nonneg {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r : ℝ) : 0 ≤ directedBallDeviation s t a r := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact infDist_nonneg

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BilateralBetaWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem bilateralPlaneError_lt_pointwise {n d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (a : Ambient d)
    (r ε : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (he : bilateralPlaneError μ a r S < ε) :
    (∀ x ∈ ball a r, x ∈ μ.support → infDist x (S : Set (Ambient d)) < ε * r) ∧
    (∀ x ∈ ball a r, x ∈ S → infDist x μ.support < ε * r) := by
  have he' : directedBallDeviation μ.support (S : Set (Ambient d)) a r +
      directedBallDeviation (S : Set (Ambient d)) μ.support a r < ε * r :=
    (div_lt_iff₀ hr).mp he
  have h1 := directedBallDeviation_nonneg μ.support (S : Set (Ambient d)) a r
  have h2 := directedBallDeviation_nonneg (S : Set (Ambient d)) μ.support a r
  constructor
  · intro x hx hxs
    have hv : infDist x (S : Set (Ambient d)) ≤
        directedBallDeviation μ.support (S : Set (Ambient d)) a r :=
      le_csSup (directedBallDeviation_bddAbove μ.support (S : Set (Ambient d)) hS.1 a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith
  · intro x hx hxs
    have hv : infDist x μ.support ≤ directedBallDeviation (S : Set (Ambient d)) μ.support a r :=
      le_csSup (directedBallDeviation_bddAbove (S : Set (Ambient d)) μ.support hμ a r)
        ⟨x, ⟨hx, hxs⟩, rfl⟩
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_LocalPlaneDirectionComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing nearby plane directions

Distances to affine planes control normal projections of differences. Directional
projection bounds can then be composed through an intermediate linear subspace.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem normal_projection_bound_by_plane_distances {d : ℕ}
    (W : AffineSubspace ℝ (Ambient d)) [Nonempty W] (x y : Ambient d) :
    ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      infDist x (W : Set (Ambient d)) + infDist y (W : Set (Ambient d)) := by
  have hid : (x - y) - W.direction.starProjection (x - y) =
      (x - (orthogonalProjection W x : Ambient d)) -
        (y - (orthogonalProjection W y : Ambient d)) := by
    rw [← affine_projection_difference W x y]
    abel
  rw [W.direction.starProjection_orthogonal_val, hid]
  calc
    _ ≤ ‖x - (orthogonalProjection W x : Ambient d)‖ +
        ‖y - (orthogonalProjection W y : Ambient d)‖ := norm_sub_le _ _
    _ = _ := by
      rw [← dist_eq_norm, ← dist_eq_norm]
      exact congrArg₂ (· + ·) (dist_orthogonalProjection_eq_infDist W x)
        (dist_orthogonalProjection_eq_infDist W y)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneDiskHausdorffMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem planeUnitHausdorffMeasure_lt_top (n : ℕ) :
    planeUnitHausdorffMeasure n < ⊤ := by
  have h := (isCompact_closedBall (0 : Ambient n) 1).measure_lt_top
    (μ := (μH[(Module.finrank ℝ (Ambient n) : ℝ)] : Measure (Ambient n)))
  simpa only [finrank_euclideanSpace_fin, planeUnitHausdorffMeasure] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADHoleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
AD lower bounds and global upper growth quantify the density lost to a ball-shaped hole.
Persistent holes at vanishing scales force a measurable set to have zero measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem ballHoleDensityDefect_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < ballHoleDensityDefect n C G := by
  unfold ballHoleDensityDefect
  positivity

theorem ad_ball_hole_density_bound {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (x z : Ambient d) (r : ℝ) (hr : 0 < r)
    (hz : z ∈ μ.support) (hnear : dist x z ≤ r) (hcore : AdmissibleRadius μ (r / 4))
    (hhole : Disjoint A (ball z (r / 4))) :
    0 < μ.real (closedBall x (2 * r)) ∧
      μ.real (A ∩ closedBall x (2 * r)) / μ.real (closedBall x (2 * r)) ≤
        1 - ballHoleDensityDefect n C G := by
  have hsub : ball z (r / 4) ⊆ closedBall x (2 * r) := by
    intro y hy
    change dist y x ≤ 2 * r
    have ht := dist_triangle y z x
    rw [dist_comm z x] at ht
    change dist y z < r / 4 at hy
    linarith
  have hbig : μ (closedBall x (2 * r)) ≤ ENNReal.ofReal (G * (3 * r) ^ n) :=
    (measure_mono (closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans
      (hg.2 x (3 * r) (by positivity))
  have hfin : μ (closedBall x (2 * r)) ≠ ∞ := (hbig.trans_lt ENNReal.ofReal_lt_top).ne
  have hholefin := measure_ne_top_of_subset hsub hfin
  have hsmall : (r / 4) ^ n / C ≤ μ.real (ball z (r / 4)) := by
    have h := ENNReal.toReal_mono hholefin (hlower z hz (r / 4) hcore)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), Measure.real] using! h
  have hpos : 0 < μ.real (closedBall x (2 * r)) :=
    (by positivity : 0 < (r / 4) ^ n / C).trans_le
      (hsmall.trans (measureReal_mono hsub hfin))
  refine ⟨hpos, ?_⟩
  have hsum : μ.real (A ∩ closedBall x (2 * r)) + μ.real (ball z (r / 4)) ≤
      μ.real (closedBall x (2 * r)) := by
    rw [← measureReal_union (hhole.mono_left inter_subset_left) measurableSet_ball
      (measure_ne_top_of_subset inter_subset_right hfin) hholefin]
    exact measureReal_mono (union_subset inter_subset_right hsub) hfin
  have hupper : μ.real (closedBall x (2 * r)) ≤ G * (3 * r) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
  have hidentity : ballHoleDensityDefect n C G * (G * (3 * r) ^ n) = (r / 4) ^ n / C := by
    unfold ballHoleDensityDefect
    simp only [mul_pow, div_pow]
    field_simp
  have hdef : ballHoleDensityDefect n C G * μ.real (closedBall x (2 * r)) ≤
      μ.real (ball z (r / 4)) := by
    calc
      _ ≤ ballHoleDensityDefect n C G * (G * (3 * r) ^ n) :=
        mul_le_mul_of_nonneg_left hupper (ballHoleDensityDefect_pos n C G hC hG).le
      _ = _ := hidentity
      _ ≤ _ := hsmall
  apply (div_le_iff₀ hpos).mpr
  linarith

theorem measurable_set_null_of_uniform_ball_holes {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (hA : MeasurableSet A)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (ht : Tendsto r atTop (𝓝 0))
    (hcore : ∀ k, AdmissibleRadius μ (r k / 4))
    (hhole : ∀ x ∈ A, ∀ k, ∃ z ∈ μ.support, dist x z ≤ r k ∧ Disjoint A (ball z (r k / 4))) :
    μ A = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hrt : Tendsto (fun k => 2 * r k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using! ht.const_mul 2
    · change 0 < 2 * r k
      exact mul_pos (by norm_num) (hr k)
  have hzero : ∀ᵐ x ∂μ.restrict A, False := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ A, ae_restrict_mem hA] with x hx hxA
    have hd := hx.comp hrt
    have hdreal : Tendsto (fun k => μ.real (A ∩ closedBall x (2 * r k)) /
        μ.real (closedBall x (2 * r k))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, Measure.real] using!
        (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hd
    have hb : (1 : ℝ) ≤ 1 - ballHoleDensityDefect n C G := by
      apply le_of_tendsto hdreal
      apply Filter.Eventually.of_forall
      intro k
      obtain ⟨z, hz, hnear, hh⟩ := hhole x hxA k
      exact (ad_ball_hole_density_bound μ C G hC hG hg hlower A x z (r k) (hr k)
        hz hnear (hcore k) hh).2
    have hp := ballHoleDensityDefect_pos n C G hC hG
    linarith
  simpa using! (ae_iff.mp hzero)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BallLipschitzExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite-dimensional Lipschitz extension turns partial parameterizations into maps on entire balls
while retaining their images and controlling the Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_ball_lipschitz_extension {n d : ℕ} (r : ℝ) (A : Set (Ambient n))
    (hA : A ⊆ ball (0 : Ambient n) r) (f : Ambient n → Ambient d) (M : ℝ≥0)
    (hf : LipschitzOnWith M f A) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) g ∧ f '' A ⊆ range g := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_finite_dimension
  refine ⟨(ball (0 : Ambient n) r).domRestrict F, hF.restrict _, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨⟨x, hA hx⟩, (hEq hx).symm⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedSupportNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem separated_set_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : N.Countable := by
  have hd : N.PairwiseDisjoint (fun x => ball x (r / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    linarith [hsep hx hy hxy]
  exact hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by positivity)⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDescendantCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netDescendants_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : netDescendants N k z ⊆ E := by
  rintro x ⟨t, hx, _, _⟩
  exact hx

theorem closedNetCell_isClosed {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : IsClosed (closedNetCell N k z) :=
  isClosed_closure

theorem closedNetCell_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hE : IsClosed E) (k : ℕ) (z : E) :
    closedNetCell N k z ⊆ E :=
  hE.closure_subset_iff.mpr (netDescendants_subset N k z)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ClosedNetCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Covering by closed net cells

The geometric decay of lattice radii lets fine net points approximate every point of the
underlying set. Ancestor forcing places relative balls inside their closed cells, while
properness reduces nearby ancestors to finitely many choices and yields a closed-cell cover.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem exists_closedNetCell_containing {X : Type*} [MetricSpace X] [ProperSpace X]
    {E : Set X} (R : ℝ) (hR : 0 < R)
    (N : (k : ℕ) → SeparatedCover E (latticeRadius R k)) (k : ℕ) (y : E) :
    ∃ z : E, (z : X) ∈ (N k).points ∧ (y : X) ∈ closedNetCell N k z := by
  classical
  let S := (N k).points ∩ closedBall (y : X) (3 * latticeRadius R k)
  have hS : S.Finite := separated_set_finite_inter_compact _ _ (latticeRadius R k)
    (latticeRadius_pos R hR k) (N k).separated (isCompact_closedBall _ _)
  let : Fintype S := hS.fintype
  let center : S → E := fun z => ⟨z, (N k).subset z.property.1⟩
  have hclosure : (y : X) ∈ closure (⋃ z : S, netDescendants N k (center z)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨t, ht⟩ := exists_latticeRadius_tail_lt R hR k ε hε
    obtain ⟨x, hxN, hyx⟩ := (N (k + t + 1)).covers y y.property
    have hxE := (N (k + t + 1)).subset hxN
    let z := netAncestor N k (t + 1) ⟨x, hxE⟩
    have hzN : (z : X) ∈ (N k).points := netAncestor_mem N k t _
    have hzy : dist (z : X) (y : X) ≤ 3 * latticeRadius R k := by
      have hd := dist_triangle (z : X) x (y : X)
      rw [dist_comm (z : X) x, dist_comm x (y : X)] at hd
      have ha := netAncestor_dist_le_latticeRadius R hR N k (t + 1) ⟨x, hxE⟩
      have hs := latticeRadius_antitone R hR.le (show k ≤ k + t + 1 by omega)
      change dist x (z : X) ≤ _ at ha
      linarith
    let w : S := ⟨z, ⟨hzN, hzy⟩⟩
    refine ⟨x, mem_iUnion.mpr ⟨w, ?_⟩, hyx.trans ht⟩
    refine ⟨t + 1, hxE, ?_, ?_⟩
    · simpa only [Nat.add_succ] using! hxN
    · rfl
  rw [closure_iUnion_of_finite] at hclosure
  obtain ⟨z, hz⟩ := mem_iUnion.mp hclosure
  exact ⟨center z, z.property.1, hz⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ConstructedSupportCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem supportLatticeNets_countable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : (supportLatticeNets μ R hR k).points.Countable :=
  separated_set_countable _ _ (latticeRadius_pos R hR k) (supportLatticeNets μ R hR k).separated

theorem supportLatticeCell_closed {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsClosed (supportLatticeCell μ R hR k z) :=
  closedNetCell_isClosed _ _ _

theorem supportLatticeCell_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : supportLatticeCell μ R hR k z ⊆ μ.support :=
  closedNetCell_subset _ μ.isClosed_support _ _

theorem supportLatticeCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ supportLatticeCell μ R hR k z := by
  obtain ⟨z, hz, hcell⟩ := exists_closedNetCell_containing R hR (supportLatticeNets μ R hR) k ⟨x, hx⟩
  exact ⟨⟨z, hz⟩, hcell⟩

theorem supportLatticeCell_measure_bounds {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (supportLatticeCell μ R hR k z) ∧
      μ (supportLatticeCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  have hball : μ (μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8)) =
      μ (ball (z : Ambient d) (latticeRadius R k / 8)) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    change (x ∈ μ.support ∧ x ∈ ball (z : Ambient d) (latticeRadius R k / 8)) ↔
      x ∈ ball (z : Ambient d) (latticeRadius R k / 8)
    simp only [hx, true_and]
  constructor
  · calc
      _ ≤ μ (ball (z : Ambient d) (latticeRadius R k / 8)) :=
        hlower z ((supportLatticeNets μ R hR k).subset z.property) _ hcore
      _ = _ := hball.symm
      _ ≤ _ := measure_mono (supportLatticeCell_bounds μ R hR k z).1
  · have hsub : closedBall (z : Ambient d) (2 * latticeRadius R k) ⊆
        ball (z : Ambient d) (3 * latticeRadius R k) :=
      closedBall_subset_ball (by have hp := latticeRadius_pos R hR k; linarith)
    apply (measure_mono ((supportLatticeCell_bounds μ R hR k z).2.trans hsub)).trans
    exact hg.2 z _ (mul_pos (by norm_num) (latticeRadius_pos R hR k))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null overlaps of support lattice cells

The countable union of intersections of distinct closed cells is measurable and avoids
every deep core ball. Upper growth and lower AD bounds turn these holes into nullity;
when a core radius exceeds the support diameter, separation makes the overlap empty.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeOverlap_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : MeasurableSet (supportLatticeOverlap μ R hR k) := by
  classical
  let : Countable (supportLatticeNets μ R hR k).points :=
    (supportLatticeNets_countable μ R hR k).to_subtype
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro w
  split_ifs
  · exact MeasurableSet.empty
  · exact (supportLatticeCell_closed μ R hR k z).measurableSet.inter
      (supportLatticeCell_closed μ R hR k w).measurableSet

theorem supportLatticeOverlap_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : supportLatticeOverlap μ R hR k ⊆ μ.support := by
  intro x hx
  obtain ⟨z, _, _, hz, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
  exact supportLatticeCell_subset_support μ R hR k z hz

theorem supportLatticeOverlap_null_of_admissible_core {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 4)) :
    μ (supportLatticeOverlap μ R hR k) = 0 := by
  apply measurable_set_null_of_uniform_ball_holes μ C G hC hG hg hlower
    (supportLatticeOverlap μ R hR k) (supportLatticeOverlap_measurable μ R hR k)
    (fun q => latticeRadius R (k + q)) (fun q => latticeRadius_pos R hR (k + q))
  · simpa only [latticeRadius_add, mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)
  · intro q
    refine ⟨div_pos (latticeRadius_pos R hR (k + q)) (by norm_num), ?_⟩
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (latticeRadius_antitone R hR.le (Nat.le_add_right k q)) (by norm_num))).trans hcore.2
  · intro x hx q
    have hxE := supportLatticeOverlap_subset_support μ R hR k hx
    obtain ⟨z, hz, hnear⟩ := (supportLatticeNets μ R hR (k + q)).covers x hxE
    exact ⟨z, (supportLatticeNets μ R hR (k + q)).subset hz, hnear.le,
      supportLatticeOverlap_disjoint_deep_core μ R hR k q ⟨z, hz⟩⟩

theorem supportLatticeOverlap_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) : μ (supportLatticeOverlap μ R hR k) = 0 := by
  by_cases hcore : ENNReal.ofReal (latticeRadius R k / 4) ≤ ediam μ.support
  · exact supportLatticeOverlap_null_of_admissible_core μ C G hC hG hg hlower R hR k
      ⟨div_pos (latticeRadius_pos R hR k) (by norm_num), hcore⟩
  · have hempty : supportLatticeOverlap μ R hR k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨z, w, hne, _, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
      have hsep := (supportLatticeNets μ R hR k).separated z.property w.property
        (fun h => hne (Subtype.ext h))
      have hdiam := edist_le_ediam_of_mem
        ((supportLatticeNets μ R hR k).subset z.property)
        ((supportLatticeNets μ R hR k).subset w.property)
      apply hcore
      have hp := latticeRadius_pos R hR k
      have hd : latticeRadius R k / 4 ≤ dist (z : Ambient d) (w : Ambient d) := by linarith
      exact (ENNReal.ofReal_le_ofReal hd).trans (by simpa only [edist_dist] using! hdiam)
    rw [hempty, measure_empty]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanSupportPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_cover {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (x : Ambient d) (hx : x ∈ μ.support) (hgood : x ∉ supportLatticeExceptional μ R hR) :
    ∃ z : (supportLatticeNets μ R hR k).points, x ∈ cleanSupportCell μ R hR k z := by
  obtain ⟨z, hz⟩ := supportLatticeCell_cover μ R hR k x hx
  exact ⟨z, hz, hgood⟩

theorem cleanSupportCell_measure_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = μ (supportLatticeCell μ R hR k z) :=
  measure_sdiff_null (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteSupportRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem cleanSupportCell_eq_iUnion_descendants {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z =
      ⋃ w ∈ supportDescendantsAt μ R hR k t z, cleanSupportCell μ R hR (k + t) w := by
  ext x
  constructor
  · intro hx
    have hxE := supportLatticeCell_subset_support μ R hR k z hx.1
    obtain ⟨w, hw⟩ := cleanSupportCell_cover μ R hR (k + t) x hxE hx.2
    have hp := cleanSupportCell_nested μ R hR k t w hw
    have hanc : supportLatticeAncestor μ R hR k t w = z := by
      by_contra hne
      exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) hp hx
    exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hanc, hw⟩⟩
  · intro hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
    have hp := cleanSupportCell_nested μ R hR k t w hxw
    change supportLatticeAncestor μ R hR k t w = z at hanc
    simpa only [hanc] using! hp

theorem cleanSupportCell_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (cleanSupportCell μ R hR k z) ∧
      μ (cleanSupportCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  rw [cleanSupportCell_measure_eq μ C G hC hG hg hlower R hR k z]
  exact supportLatticeCell_measure_bounds μ C G hg hlower R hR k hcore z

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.exists_ancestor_at_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (h : ℕ) (hh : h ≤ i.depth) :
    ∃ j : SupportCellDescendant μ R hR k z,
      j.depth = h ∧ i.cell ⊆ j.cell ∧ i.center ∈ j.cell := by
  have hlevel : k + h + (i.depth - h) = k + i.depth := by omega
  let v : (supportLatticeNets μ R hR (k + h + (i.depth - h))).points :=
    ⟨i.center, by rw [hlevel]; exact i.mem_net⟩
  let w := supportLatticeAncestor μ R hR (k + h) (i.depth - h) v
  have hsub : i.cell ⊆ cleanSupportCell μ R hR (k + h) w := by
    have ht := cleanSupportCell_nested μ R hR (k + h) (i.depth - h) v
    have heq : cleanSupportCell μ R hR (k + h + (i.depth - h)) v = i.cell := by
      simp only [SupportCellDescendant.cell, cleanSupportCell, supportLatticeCell,
        supportLatticeCenter, v, hlevel]
    rw [← heq]
    exact ht
  have hc := hsub i.center_mem_cell
  have hanc : supportLatticeAncestor μ R hR k h w = z := by
    have ht := cleanSupportCell_nested μ R hR k h w hc
    have hz := i.cell_subset_top i.center_mem_cell
    by_contra hne
    exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) ht hz
  let j : SupportCellDescendant μ R hR k z :=
    { depth := h, center := w, mem_net := w.property, ancestor := hanc }
  exact ⟨j, rfl, hsub, hc⟩

theorem SupportCellDescendant.dist_center_of_mem {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (a : Ambient d) (ha : a ∈ i.cell) :
    dist a i.center ≤ 2 * i.radius :=
  (supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2 ha.1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellChainComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.cell_nested_of_common_point {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hq : q.depth ≤ i.depth)
    (x : Ambient d) (hi : x ∈ i.cell) (hqx : x ∈ q.cell) : i.cell ⊆ q.cell := by
  obtain ⟨j, hj, hsub, _⟩ := i.exists_ancestor_at_depth q.depth hq
  have heq := j.eq_of_common_point_same_depth q hj x (hsub hi) hqx
  simpa only [heq] using! hsub

theorem SupportCellDescendant.compose_radius {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).radius = j.radius := by
  simp only [SupportCellDescendant.radius, SupportCellDescendant.compose, Nat.add_assoc]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SupportDescendantCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Countability of support-cell descendants

Every descendant is determined by its depth and its center in the corresponding
support lattice net. Encoding these data in a countable dependent sum proves
countability of the full descendant family, not only of each generation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem supportCellDescendant_countable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Countable (SupportCellDescendant μ R hR k z) := by
  let (t : ℕ) : Countable (supportLatticeNets μ R hR (k + t)).points :=
    (supportLatticeNets_countable μ R hR (k + t)).to_subtype
  let f (i : SupportCellDescendant μ R hR k z) :
      Σ t : ℕ, (supportLatticeNets μ R hR (k + t)).points :=
    ⟨i.depth, ⟨i.center, i.mem_net⟩⟩
  apply Function.Injective.countable (f := f)
  intro i j hij
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  have ht : ti = tj := congrArg Sigma.fst hij
  subst tj
  have hc : (⟨xi, hxi⟩ : (supportLatticeNets μ R hR (k + ti)).points) = ⟨xj, hxj⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  have hx : xi = xj := congrArg Subtype.val hc
  subst xj
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_PointCellChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_unique_support_descendant_at_point {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z) (t : ℕ) :
    ∃! i : SupportCellDescendant μ R hR k z, i.depth = t ∧ x ∈ i.cell := by
  rw [cleanSupportCell_eq_iUnion_descendants μ R hR k t z] at hx
  obtain ⟨w, hw⟩ := mem_iUnion.mp hx
  obtain ⟨hanc, hxw⟩ := mem_iUnion.mp hw
  let i : SupportCellDescendant μ R hR k z :=
    { depth := t, center := w, mem_net := w.property, ancestor := hanc }
  refine ⟨i, ⟨rfl, hxw⟩, ?_⟩
  intro j hj
  exact j.eq_of_common_point_same_depth i hj.1 x hj.2 hxw

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CellRegionStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Limits and stops of good cell regions

The limit region consists of points whose containing descendants all satisfy a
chosen good-cell predicate. Stops are the first failures along containment chains.
Countability of descendants makes the limit region measurable by removing the
union of bad cells from the starting cell.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_first_failing_cell {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hnot : x ∉ cellRegionLimit μ R hR k z Good) :
    ∃ i ∈ cellRegionStops μ R hR k z Good, x ∈ i.cell := by
  classical
  have hb : ∃ t : ℕ, ∃ i : SupportCellDescendant μ R hR k z,
      i.depth = t ∧ x ∈ i.cell ∧ ¬Good i := by
    by_contra hnone
    apply hnot
    refine ⟨hx, ?_⟩
    intro i hi
    by_contra hbad
    exact hnone ⟨i.depth, i, rfl, hi, hbad⟩
  obtain ⟨i, hi, hxi, hbad⟩ := Nat.find_spec hb
  refine ⟨i, ⟨hbad, ?_⟩, hxi⟩
  intro j hj hsub
  by_contra hjbad
  have hmin := Nat.find_min' hb ⟨j, rfl, hsub hxi, hjbad⟩
  omega

theorem cellRegionStops_pairwise_disjoint {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (cellRegionStops μ R hR k z Good).Pairwise (fun i j => Disjoint i.cell j.cell) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_trichotomy i.depth j.depth with hlt | heq | hgt
  · exact hi.1 (hj.2 i hlt (j.cell_nested_of_common_point i hlt.le x hxj hxi))
  · exact hne (i.eq_of_common_point_same_depth j heq x hxi hxj)
  · exact hj.1 (hi.2 j hgt (i.cell_nested_of_common_point j hgt.le x hxi hxj))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_StoppingCoreSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.mem_cell_of_mem_support_near_center {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (x : Ambient d)
    (hx : x ∈ μ.support) (hclean : x ∉ supportLatticeExceptional μ R hR)
    (hnear : dist x i.center < i.radius / 8) : x ∈ i.cell := by
  exact ⟨(supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).1
    ⟨hx, hnear⟩, hclean⟩

theorem SupportCellDescendant.distance_lower_of_clean_outside {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (x : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z) (hout : x ∉ i.cell) :
    i.radius / 8 ≤ dist x i.center := by
  by_contra hbad
  exact hout (i.mem_cell_of_mem_support_near_center x
    (supportLatticeCell_subset_support μ R hR k z hx.1) hx.2 (lt_of_not_ge hbad))

theorem cellRegionStops_centers_separated {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i j : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hj : j ∈ cellRegionStops μ R hR k z Good) (hne : i ≠ j) :
    max i.radius j.radius ≤ 8 * dist i.center j.center := by
  have hd := cellRegionStops_pairwise_disjoint μ R hR k z Good hi hj hne
  have hji : j.center ∉ i.cell := fun h => Set.disjoint_left.mp hd h j.center_mem_cell
  have hij : i.center ∉ j.cell := fun h => Set.disjoint_left.mp hd i.center_mem_cell h
  have hiD := i.distance_lower_of_clean_outside j.center (j.cell_subset_top j.center_mem_cell) hji
  have hjD := j.distance_lower_of_clean_outside i.center (i.cell_subset_top i.center_mem_cell) hij
  rw [dist_comm j.center i.center] at hiD
  exact max_le (by linarith) (by linarith)

theorem cellRegionLimit_stop_center_separated {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (x : Ambient d) (hx : x ∈ cellRegionLimit μ R hR k z Good) :
    i.radius ≤ 8 * dist x i.center := by
  have hout : x ∉ i.cell := fun h => hi.1 (hx.2 i h)
  have h := i.distance_lower_of_clean_outside x hx.1 hout
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FineCoherentRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem SupportCellDescendant.zero_depth_geometry {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    i.center = (z : Ambient d) ∧ i.radius = latticeRadius R k := by
  have hc := congrArg Subtype.val i.ancestor
  constructor
  · simpa only [supportLatticeAncestor, supportLatticeCenter, hi, netAncestor_zero] using! hc
  · simp only [SupportCellDescendant.radius, hi, Nat.add_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteNormalizedWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*}

theorem finiteWeightDenominator_ge_one (F : Finset ι) (w : ι → ℝ) :
    1 ≤ finiteWeightDenominator F w := le_max_left _ _

theorem finiteNormalizedWeight_eq_zero_iff (F : Finset ι) (w : ι → ℝ) (i : ι) :
    finiteNormalizedWeight F w i = 0 ↔ w i = 0 := by
  have hp : 0 < finiteWeightDenominator F w :=
    lt_of_lt_of_le zero_lt_one (finiteWeightDenominator_ge_one F w)
  simp only [finiteNormalizedWeight, div_eq_zero_iff, ne_of_gt hp, or_false]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_RescaledBallCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A Lipschitz chart on a centered ball can be translated and rescaled without changing its image.
Rescaling the parameter ball by the inverse factor multiplies the Lipschitz bound by that factor.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_rescaled_ball_chart {n d : ℕ}
    (r : ℝ) (a : Ambient n) (s : ℝ≥0) (hs : 0 < s)
    (f : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : Ambient n → Ambient d,
      LipschitzOnWith (M * s) g (ball a (r / (s : ℝ))) ∧
      g '' ball a (r / (s : ℝ)) = Set.range f := by
  classical
  have hsr : 0 < (s : ℝ) := hs
  have hnorm (u : Ambient n) : ‖(s : ℝ) • (u - a)‖ = (s : ℝ) * dist u a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg, dist_eq_norm]
  have hmem (u : Ambient n) (hu : u ∈ ball a (r / (s : ℝ))) :
      (s : ℝ) • (u - a) ∈ ball (0 : Ambient n) r := by
    rw [mem_ball_zero_iff]
    rw [hnorm]
    have h := (lt_div_iff₀ hsr).mp hu
    simpa only [mul_comm] using! h
  let T : ball a (r / (s : ℝ)) → ball (0 : Ambient n) r :=
    fun u => ⟨(s : ℝ) • (u.val - a), hmem u.val u.property⟩
  have hTdist (u v : ball a (r / (s : ℝ))) :
      dist (T u) (T v) = (s : ℝ) * dist u v := by
    change dist ((s : ℝ) • (u.val - a)) ((s : ℝ) • (v.val - a)) =
      (s : ℝ) * dist u.val v.val
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    congr 1
    simp only [dist_eq_norm]
    congr 1
    abel
  have hsurj : Function.Surjective T := by
    intro v
    let u : Ambient n := a + (s : ℝ)⁻¹ • v.val
    have hu : u ∈ ball a (r / (s : ℝ)) := by
      change dist (a + (s : ℝ)⁻¹ • v.val) a < r / (s : ℝ)
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsr)]
      have hv : ‖v.val‖ < r := mem_ball_zero_iff.mp v.property
      have h := mul_lt_mul_of_pos_left hv (inv_pos.mpr hsr)
      simpa only [div_eq_mul_inv, mul_comm] using! h
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    change (s : ℝ) • ((a + (s : ℝ)⁻¹ • v.val) - a) = v.val
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsr.ne', one_smul]
  let g : Ambient n → Ambient d := fun u =>
    if hu : u ∈ ball a (r / (s : ℝ)) then f (T ⟨u, hu⟩) else 0
  have hg (u : Ambient n) (hu : u ∈ ball a (r / (s : ℝ))) : g u = f (T ⟨u, hu⟩) := by
    simp only [g, dite_eq_left hu]
  refine ⟨g, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [hg u hu, hg v hv]
    have h := hf.dist_le_mul (T ⟨u, hu⟩) (T ⟨v, hv⟩)
    rw [hTdist] at h
    simpa only [NNReal.coe_mul, Subtype.dist_eq, mul_assoc] using! h
  · apply Set.Subset.antisymm
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨T ⟨u, hu⟩, (hg u hu).symm⟩
    · rintro y ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hsurj v
      exact ⟨u.val, u.property, (hg u.val u.property).trans (congrArg f hu)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_BoundedNormalizedBallCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded normalized ball charts

Metric projection onto a nonempty complete convex set gives a nonexpansive retraction.
Composing this retraction with a rescaled ball chart bounds its range by a closed ball
while preserving every point of the original image in that ball. The normalization
halves the domain radius and multiplies the Lipschitz bound by two.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_nonexpansive_retraction_of_complete_convex {d : ℕ}
    (K : Set (Ambient d)) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    ∃ p : Ambient d → Ambient d, LipschitzWith 1 p ∧
      (∀ x, p x ∈ K) ∧ ∀ x ∈ K, p x = x := by
  classical
  choose p hp hmin using exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex
  have hv (x : Ambient d) : ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconvex (hp x)).mp (hmin x)
  refine ⟨p, ?_, hp, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hx := hv x (p y) (hp y)
    have hy := hv y (p x) (hp x)
    have hid : inner ℝ (x - y) (p x - p y) = ‖p x - p y‖ ^ 2 -
        inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    have hc := real_inner_le_norm (x - y) (p x - p y)
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    nlinarith [norm_nonneg (x - y), norm_nonneg (p x - p y)]
  · intro x hx
    have h := hv x x hx
    rw [real_inner_self_eq_norm_sq] at h
    have hz : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exists_bounded_normalized_ball_chart {n d : ℕ}
    (r : ℝ) (c : Ambient d) (b : ℝ) (hb : 0 ≤ b)
    (f : ball (0 : Ambient n) (2 * r) → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (M * 2) g ∧ Set.range g ⊆ closedBall c b ∧
      (closedBall c b ∩ Set.range f) ⊆ Set.range g := by
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall c b) ⟨c, mem_closedBall_self hb⟩ isClosed_closedBall.isComplete (convex_closedBall c b)
  obtain ⟨h, hhLip, hhRange⟩ := exists_rescaled_ball_chart (2 * r) (0 : Ambient n)
    2 (by norm_num) f M hf
  have heq : (2 * r) / ((2 : ℝ≥0) : ℝ) = r := by change (2 * r) / 2 = r; ring
  rw [heq] at hhLip hhRange
  let h' : ball (0 : Ambient n) r → Ambient d := (ball (0 : Ambient n) r).domRestrict h
  have hh'Lip : LipschitzWith (M * 2) h' := hhLip.to_restrict
  have hh'Range : Set.range h' = Set.range f := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      exact hhRange ▸ mem_image_of_mem h u.property
    · intro y hy
      obtain ⟨u, hu, he⟩ := hhRange ▸ hy
      exact ⟨⟨u, hu⟩, he⟩
  refine ⟨p ∘ h', ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hp.comp hh'Lip
  · rintro y ⟨u, rfl⟩
    exact hpRange (h' u)
  · intro y hy
    obtain ⟨u, hu⟩ := hh'Range ▸ hy.2
    exact ⟨u, by change p (h' u) = y; rw [hu, hpFix y hy.1]⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FiniteChartParameterPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem finite_chart_parameter_center_mem {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    finiteChartParameterCenter e r N i ∈ closedBall (0 : Ambient n) (r / 2) := by
  have hi : (i.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [mem_closedBall_zero_iff, finiteChartParameterCenter, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), he, mul_one]
  have hden : 0 < 2 * ((N : ℝ) + 1) := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

theorem finite_chart_parameter_centers_separated {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ)
    (i j : Fin N) (hij : i ≠ j) :
    r + r ≤ (finiteChartPackingFactor N : ℝ) *
      dist (finiteChartParameterCenter e r N i) (finiteChartParameterCenter e r N j) := by
  let δ := r / (2 * ((N : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  have hneq : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have habs : 1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · have h : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hdist : δ ≤ dist (finiteChartParameterCenter e r N i) (finiteChartParameterCenter e r N j) := by
    rw [dist_eq_norm, finiteChartParameterCenter, finiteChartParameterCenter,
      ← sub_smul, norm_smul, Real.norm_eq_abs, he, mul_one]
    change δ ≤ |((i.val : ℝ) + 1) * δ - ((j.val : ℝ) + 1) * δ|
    rw [show ((i.val : ℝ) + 1) * δ - ((j.val : ℝ) + 1) * δ =
      ((i.val : ℝ) - (j.val : ℝ)) * δ by ring, abs_mul, abs_of_pos hδ]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right habs hδ.le
  have hid : (finiteChartPackingFactor N : ℝ) * δ = r + r := by
    change (4 * ((N : ℝ) + 1)) * (r / (2 * ((N : ℝ) + 1))) = r + r
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [← hid]
  exact mul_le_mul_of_nonneg_left hdist (finiteChartPackingFactor N).coe_nonneg

theorem finite_chart_parameter_island_subset {n : ℕ}
    (e : Ambient n) (he : ‖e‖ = 1) (r : ℝ) (hr : 0 < r) (N : ℕ) (i : Fin N) :
    ball (finiteChartParameterCenter e r N i) (r / (4 * (finiteChartPackingFactor N : ℝ))) ⊆
      ball (0 : Ambient n) r := by
  intro u hu
  have hc : dist (finiteChartParameterCenter e r N i) (0 : Ambient n) ≤ r / 2 :=
    finite_chart_parameter_center_mem e he r hr N i
  have hA : 4 ≤ (finiteChartPackingFactor N : ℝ) := by
    change 4 ≤ 4 * ((N : ℝ) + 1)
    have hN := Nat.cast_nonneg (α := ℝ) N
    linarith
  have hden : 0 < 4 * (finiteChartPackingFactor N : ℝ) := by linarith
  have hrad : r / (4 * (finiteChartPackingFactor N : ℝ)) ≤ r / 4 :=
    (div_le_iff₀ hden).mpr (by nlinarith)
  have ht := dist_triangle u (finiteChartParameterCenter e r N i) (0 : Ambient n)
  have hu' : dist u (finiteChartParameterCenter e r N i) <
      r / (4 * (finiteChartPackingFactor N : ℝ)) := hu
  change dist u (0 : Ambient n) < r
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SeparatedParameterPatchGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gluing separated parameter patches

Separation of the parameter centers and control of the image centers give a uniform
cross-patch Lipschitz estimate. The glued map extends to a parameter ball, whose
image covers all patches with an explicit Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem separated_parameter_patch_cross_dist_le {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (D : ι → Set (Ambient n)) (g : ι → Ambient n → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hparam : ∀ i : ι, ∀ u ∈ D i, dist u (a i) ≤ r i / (4 * (A : ℝ)))
    (himage : ∀ i : ι, ∀ u ∈ D i, dist (g i u) (c i) ≤ 3 * r i)
    (hLip : ∀ i : ι, LipschitzOnWith M (g i) (D i))
    (i j : ι) (u v : Ambient n) (hu : u ∈ D i) (hv : v ∈ D j) :
    dist (g i u) (g j v) ≤ (separatedPatchGluingConstant M A L : ℝ) * dist u v := by
  have hM : (M : ℝ) ≤ (separatedPatchGluingConstant M A L : ℝ) := by
    exact_mod_cast (le_max_left M (2 * (3 * A + L)))
  have hcross : 2 * (3 * (A : ℝ) + (L : ℝ)) ≤
      (separatedPatchGluingConstant M A L : ℝ) := by
    exact_mod_cast (le_max_right M (2 * (3 * A + L)))
  by_cases hij : i = j
  · subst j
    exact (hLip i |>.dist_le_mul u hu v hv).trans
      (mul_le_mul_of_nonneg_right hM dist_nonneg)
  have hAr : 0 < (A : ℝ) := hA
  have hden : 0 < 4 * (A : ℝ) := by positivity
  have hsmall : r i / (4 * (A : ℝ)) + r j / (4 * (A : ℝ)) ≤ dist (a i) (a j) / 4 := by
    calc
      _ = (r i + r j) / (4 * (A : ℝ)) := (add_div _ _ _).symm
      _ ≤ ((A : ℝ) * dist (a i) (a j)) / (4 * (A : ℝ)) :=
        div_le_div_of_nonneg_right (hsep i j hij) hden.le
      _ = _ := by field_simp
  have hcenterdist : dist (a i) (a j) ≤ 2 * dist u v := by
    have h1 := dist_triangle (a i) u (a j)
    have h2 := dist_triangle u v (a j)
    rw [dist_comm (a i) u] at h1
    have hpu := hparam i u hu
    have hpv := hparam j v hv
    have hd : 0 ≤ dist u v := dist_nonneg
    linarith
  have h1 := dist_triangle (g i u) (c i) (g j v)
  have h2 := dist_triangle (c i) (c j) (g j v)
  rw [dist_comm (c j) (g j v)] at h2
  calc
    _ ≤ 3 * (r i + r j) + (L : ℝ) * dist (a i) (a j) := by
      linarith [himage i u hu, himage j v hv, hcenters i j]
    _ ≤ (3 * (A : ℝ) + (L : ℝ)) * dist (a i) (a j) := by
      nlinarith [hsep i j hij]
    _ ≤ (3 * (A : ℝ) + (L : ℝ)) * (2 * dist u v) :=
      mul_le_mul_of_nonneg_left hcenterdist (by positivity)
    _ = (2 * (3 * (A : ℝ) + (L : ℝ))) * dist u v := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcross dist_nonneg

theorem exists_ball_lipschitz_cover_of_separated_parameter_patches {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (D : ι → Set (Ambient n)) (g : ι → Ambient n → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hparam : ∀ i : ι, ∀ u ∈ D i, dist u (a i) ≤ r i / (4 * (A : ℝ)))
    (himage : ∀ i : ι, ∀ u ∈ D i, dist (g i u) (c i) ≤ 3 * r i)
    (hLip : ∀ i : ι, LipschitzOnWith M (g i) (D i))
    (ρ : ℝ) (hball : (⋃ i : ι, D i) ⊆ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * separatedPatchGluingConstant M A L) F ∧
      (⋃ i : ι, g i '' D i) ⊆ Set.range F := by
  classical
  let U := ⋃ i : ι, D i
  let j : ∀ u : Ambient n, u ∈ U → ι := fun u hu => (mem_iUnion.mp hu).choose
  have hj (u : Ambient n) (hu : u ∈ U) : u ∈ D (j u hu) := (mem_iUnion.mp hu).choose_spec
  let G : Ambient n → Ambient d := fun u => if hu : u ∈ U then g (j u hu) u else 0
  have hG (u : Ambient n) (hu : u ∈ U) : G u = g (j u hu) u := by simp only [G, dite_eq_left hu]
  have hcross := separated_parameter_patch_cross_dist_le a c r D g M A L hA
    hsep hcenters hparam himage hLip
  have hGLip : LipschitzOnWith (separatedPatchGluingConstant M A L) G U := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [hG u hu, hG v hv]
    exact hcross (j u hu) (j v hv) u v (hj u hu) (hj v hv)
  have heq (i : ι) (u : Ambient n) (hu : u ∈ D i) : G u = g i u := by
    have huU : u ∈ U := mem_iUnion.mpr ⟨i, hu⟩
    rw [hG u huU]
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [dist_self, mul_zero] using! hcross (j u huU) i u u (hj u huU) hu
  obtain ⟨F, hFLip, hcover⟩ := exists_ball_lipschitz_extension ρ U hball G
    (separatedPatchGluingConstant M A L) hGLip
  refine ⟨F, hFLip, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  obtain ⟨u, hu, rfl⟩ := hi
  exact hcover ⟨u, mem_iUnion.mpr ⟨i, hu⟩, heq i u hu⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_RescaledChildChartGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_rescaled_children {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (f : ∀ i : ι, ball (0 : Ambient n) (r i) → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (himage : ∀ i : ι, Set.range (f i) ⊆ closedBall (c i) (3 * r i))
    (hLip : ∀ i : ι, LipschitzWith M (f i))
    (ρ : ℝ) (hball : ∀ i : ι, ball (a i) (r i / (4 * (A : ℝ))) ⊆ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * A)) A L) F ∧
      (⋃ i : ι, Set.range (f i)) ⊆ Set.range F := by
  classical
  have hs : 0 < 4 * A := by positivity
  have hc (i : ι) := exists_rescaled_ball_chart (r i) (a i) (4 * A) hs (f i) M (hLip i)
  choose g hg hrange using hc
  have hrange' (i : ι) : g i '' ball (a i) (r i / (4 * (A : ℝ))) = Set.range (f i) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hrange i
  have hg' (i : ι) : LipschitzOnWith (M * (4 * A)) (g i)
      (ball (a i) (r i / (4 * (A : ℝ)))) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hg i
  obtain ⟨F, hF, hcover⟩ := exists_ball_lipschitz_cover_of_separated_parameter_patches
    a c r (fun i => ball (a i) (r i / (4 * (A : ℝ)))) g (M * (4 * A)) A L hA hsep hcenters
    (fun _ _ hu => le_of_lt hu)
    (fun i u hu => himage i (hrange' i ▸ mem_image_of_mem (g i) hu)) hg'
    ρ (iUnion_subset hball)
  refine ⟨F, hF, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  exact hcover (mem_iUnion.mpr ⟨i, hrange' i ▸ hi⟩)

theorem small_parameter_ball_subset_double_ball {n : ℕ}
    (a : Ambient n) (ρ r : ℝ) (hρ : 0 < ρ) (ha : a ∈ closedBall (0 : Ambient n) ρ)
    (s : ℝ≥0) (hs : 1 ≤ s) (hr : r ≤ ρ) :
    ball a (r / (s : ℝ)) ⊆ ball (0 : Ambient n) (2 * ρ) := by
  intro u hu
  have hs' : 1 ≤ (s : ℝ) := hs
  have hsp : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs'
  have hrad : r / (s : ℝ) ≤ ρ := (div_le_iff₀ hsp).mpr (by nlinarith)
  have hnear : dist u a < r / (s : ℝ) := hu
  have hac : dist a (0 : Ambient n) ≤ ρ := ha
  have ht := dist_triangle u a (0 : Ambient n)
  change dist u (0 : Ambient n) < 2 * ρ
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FiniteBallChartUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite unions of ball charts

Separated parameter islands encode finitely many bounded Lipschitz charts in a single
ball chart. The union constant combines the packing factor, the gluing estimate, and
the ambient Lipschitz extension constant. Extension followed by a nonexpansive
retraction also handles charts initially defined on subsets of the parameter ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_finite_ball_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (f : Fin N → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      (⋃ i : Fin N, Set.range (f i)) ⊆ Set.range g := by
  have hdim : 0 < Module.finrank ℝ (Ambient n) := by simpa [Ambient] using! hn
  let : Nontrivial (Ambient n) := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨e, he⟩ := exists_norm_eq (Ambient n) (show 0 ≤ (1 : ℝ) by norm_num)
  have hA : 0 < finiteChartPackingFactor N := by unfold finiteChartPackingFactor; positivity
  exact exists_ball_lipschitz_cover_of_rescaled_children (finiteChartParameterCenter e r N)
    (fun _ => z) (fun _ => r) f M (finiteChartPackingFactor N) 0 hA
    (finite_chart_parameter_centers_separated e he r hr N)
    (fun _ _ => by simp only [dist_self, NNReal.coe_zero, zero_mul, le_refl])
    himage hLip r (finite_chart_parameter_island_subset e he r hr N)

theorem exists_ball_lipschitz_cover_of_finite_partial_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (D : Fin N → Set (Ambient n)) (hD : ∀ i, D i ⊆ ball (0 : Ambient n) r)
    (f : Fin N → Ambient n → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i, LipschitzOnWith M (f i) (D i))
    (himage : ∀ i, f i '' D i ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N (lipschitzExtensionConstant (Ambient d) * M)) g ∧
      (⋃ i : Fin N, f i '' D i) ⊆ Set.range g := by
  classical
  have hext (i : Fin N) := (hLip i).extend_finite_dimension
  choose F hF hEq using hext
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall z (3 * r)) ⟨z, mem_closedBall_self (by positivity)⟩
    isClosed_closedBall.isComplete (convex_closedBall z (3 * r))
  let g : Fin N → ball (0 : Ambient n) r → Ambient d :=
    fun i => p ∘ (ball (0 : Ambient n) r).domRestrict (F i)
  have hgLip (i : Fin N) : LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) (g i) := by
    simpa only [one_mul] using! hp.comp ((hF i).restrict (ball (0 : Ambient n) r))
  have hgRange (i : Fin N) : Set.range (g i) ⊆ closedBall z (3 * r) := by
    rintro y ⟨u, rfl⟩
    exact hpRange (F i u.val)
  obtain ⟨h, hhLip, hhCover⟩ := exists_ball_lipschitz_cover_of_finite_ball_charts hn N r hr z g
    (lipschitzExtensionConstant (Ambient d) * M) hgLip hgRange
  refine ⟨h, hhLip, ?_⟩
  intro y hy
  obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp hy
  apply hhCover
  apply mem_iUnion.mpr
  refine ⟨i, ⟨u, hD i hu⟩, ?_⟩
  change p (F i u) = f i u
  rw [← hEq i hu, hpFix (f i u) (himage i (mem_image_of_mem (f i) hu))]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FinitePieceCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coordinates selected from a Lipschitz ball cover

Choosing a preimage for each covered point produces coordinates in the parameter
ball. The Lipschitz bound on the covering map controls ambient distances by the
distances between these selected coordinates, without requiring continuity of
the selection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_coordinates_of_lipschitz_ball_cover {n d : ℕ}
    (E : Set (Ambient d)) (r : ℝ) (f : ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hf : LipschitzWith M f) (hcover : E ⊆ Set.range f) :
    ∃ coord : Ambient d → Ambient n,
      (∀ x ∈ E, coord x ∈ ball (0 : Ambient n) r) ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (M : ℝ) * dist (coord x) (coord y) := by
  classical
  let pre : ∀ x : Ambient d, x ∈ E → ball (0 : Ambient n) r :=
    fun x hx => (hcover hx).choose
  have hpre (x : Ambient d) (hx : x ∈ E) : f (pre x hx) = x := (hcover hx).choose_spec
  let coord : Ambient d → Ambient n := fun x => if hx : x ∈ E then (pre x hx).val else 0
  have hcoord (x : Ambient d) (hx : x ∈ E) : coord x = (pre x hx).val := by
    simp only [coord, dite_eq_left hx]
  refine ⟨coord, ?_, ?_⟩
  · intro x hx
    rw [hcoord x hx]
    exact (pre x hx).property
  · intro x hx y hy
    have h := hf.dist_le_mul (pre x hx) (pre y hy)
    rw [hpre x hx, hpre y hy] at h
    simpa only [hcoord x hx, hcoord y hy, Subtype.dist_eq] using! h

theorem finitePartialCoordinateConstant_ge_one (d N : ℕ) (M : ℝ≥0) :
    1 ≤ finitePartialCoordinateConstant d N M := le_max_left _ _

theorem exists_coordinates_of_finite_partial_charts {n d : ℕ} (hn : 0 < n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (D : Fin N → Set (Ambient n)) (hD : ∀ i, D i ⊆ ball (0 : Ambient n) r)
    (f : Fin N → Ambient n → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i, LipschitzOnWith M (f i) (D i))
    (himage : ∀ i, f i '' D i ⊆ closedBall z (3 * r)) :
    ∃ coord : Ambient d → Ambient n,
      (∀ x ∈ ⋃ i : Fin N, f i '' D i, coord x ∈ closedBall (0 : Ambient n) r) ∧
      ∀ x ∈ ⋃ i : Fin N, f i '' D i, ∀ y ∈ ⋃ i : Fin N, f i '' D i,
        dist x y ≤ (finitePartialCoordinateConstant d N M : ℝ) * dist (coord x) (coord y) := by
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_finite_partial_charts hn N r hr z
    D hD f M hLip himage
  have hg' : LipschitzWith (finitePartialCoordinateConstant d N M) g := hg.weaken (le_max_right _ _)
  obtain ⟨coord, hball, hsep⟩ := exists_coordinates_of_lipschitz_ball_cover
    (⋃ i : Fin N, f i '' D i) r g (finitePartialCoordinateConstant d N M) hg' hcover
  exact ⟨coord, fun x hx => ball_subset_closedBall (hball x hx), hsep⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GrowthHausdorffDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem global_growth_mass_le_ediam_power {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
    (A : Set (Ambient d)) (hfinite : ediam A ≠ ⊤) :
    μ A ≤ ENNReal.ofReal G * ediam A ^ n := by
  rcases eq_empty_or_nonempty A with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  let δ := diam A
  have hδ : 0 ≤ δ := diam_nonneg
  have hc : Continuous (fun r : ℝ => ENNReal.ofReal (G * r ^ n)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow n))
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (G * r ^ n))
      (𝓝[>] δ) (𝓝 (ENNReal.ofReal (G * δ ^ n))) := hc.continuousWithinAt.tendsto
  have hb : ∀ᶠ r in 𝓝[>] δ, μ A ≤ ENNReal.ofReal (G * r ^ n) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hδr : δ < r := hr
    have hsub : A ⊆ ball x r := by
      intro y hy
      exact (dist_le_diam_of_mem' hfinite hy hx).trans_lt hδr
    exact (measure_mono hsub).trans (hg.2 x r (hδ.trans_lt hδr))
  have h := ge_of_tendsto hlim hb
  have heq : ENNReal.ofReal (G * δ ^ n) = ENNReal.ofReal G * ediam A ^ n := by
    rw [ENNReal.ofReal_mul hg.1, ENNReal.ofReal_pow hδ]
    change ENNReal.ofReal G * (ENNReal.ofReal (ediam A).toReal) ^ n = _
    rw [ENNReal.ofReal_toReal hfinite]
  exact h.trans_eq heq

theorem global_growth_le_hausdorffMeasure {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ) :
    μ ≤ ENNReal.ofReal G • (μH[(n : ℝ)] : Measure (Ambient d)) := by
  have hμ : μ ≤ Measure.mkMetric (fun r : ℝ≥0∞ => ENNReal.ofReal G * r ^ n) := by
    apply Measure.le_mkMetric _ μ 1 (by norm_num)
    intro A hA
    exact global_growth_mass_le_ediam_power μ G hg A (ne_top_of_le_ne_top (by norm_num) hA)
  apply hμ.trans
  change (Measure.mkMetric (fun r : ℝ≥0∞ => ENNReal.ofReal G * r ^ n) : Measure (Ambient d)) ≤
    ENNReal.ofReal G • Measure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ))
  apply Measure.mkMetric_mono_smul ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.mpr hG).ne'
  exact Filter.Eventually.of_forall (fun r => by
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast, le_refl])

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FiniteCoverCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

theorem finiteCoverCutoff_eq_zero (c : X) (r : ℝ) (hr : 0 < r) (x : X)
    (hx : 4 * r ≤ dist x c) : finiteCoverCutoff c r x = 0 := by
  have hd : (4 : ℝ) ≤ dist x c / r := (le_div_iff₀ hr).mpr hx
  have h : min 1 (4 - dist x c / r) ≤ 0 :=
    (min_le_right _ _).trans (by linarith)
  exact max_eq_left h

theorem finiteCoverCutoff_ne_zero_iff (c : X) (r : ℝ) (hr : 0 < r) (x : X) :
    finiteCoverCutoff c r x ≠ 0 ↔ dist x c < 4 * r := by
  constructor
  · intro h
    by_contra hn
    exact h (finiteCoverCutoff_eq_zero c r hr x (le_of_not_gt hn))
  · intro hx
    have hd : dist x c / r < 4 := (div_lt_iff₀ hr).mpr hx
    have hm : 0 < min 1 (4 - dist x c / r) := lt_min (by norm_num) (by linarith)
    exact ne_of_gt (lt_of_lt_of_le hm (le_max_right _ _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

theorem activeRegionCell_good (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i) : Good i :=
  hi i le_rfl Subset.rfl

theorem activeRegionCell_of_strict_stop_ancestor (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : q.depth < i.depth) (hsub : i.cell ⊆ q.cell) : activeRegionCell Good q := by
  intro j hj hqj
  exact hi.2 j (hj.trans_lt hdepth) (hsub.trans hqj)

theorem activeRegionCell_stop_scale_separation (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (hq : activeRegionCell Good q) :
    i.radius / 8 ≤ dist i.center q.center + q.radius := by
  by_cases hdepth : q.depth ≤ i.depth
  · have hrad : i.radius ≤ q.radius :=
      latticeRadius_antitone R hR.le (Nat.add_le_add_left hdepth k)
    have hpos := i.radius_pos
    have hd : 0 ≤ dist i.center q.center := dist_nonneg
    linarith
  · have hdepth' : i.depth ≤ q.depth := (Nat.le_of_lt (Nat.lt_of_not_ge hdepth))
    have hout : q.center ∉ i.cell := by
      intro hmem
      have hsub := q.cell_nested_of_common_point i hdepth' q.center q.center_mem_cell hmem
      exact hi.1 (hq i hdepth' hsub)
    have hdist := i.distance_lower_of_clean_outside q.center
      (q.cell_subset_top q.center_mem_cell) hout
    rw [dist_comm q.center i.center] at hdist
    have hpos := q.radius_pos
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CappedStoppingDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Set Metric

theorem cappedStoppingDistance_bddBelow {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    BddBelow (range (fun i : Option ι => match i with
      | none => R
      | some i => dist x (c i) + r i)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  cases i with
  | none => exact hR
  | some i => exact add_nonneg dist_nonneg (hr i)

theorem cappedStoppingDistance_le_cap {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    cappedStoppingDistance R c r x ≤ R := by
  exact ciInf_le (cappedStoppingDistance_bddBelow R c r hR hr x) none

theorem cappedStoppingDistance_le_center_radius {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) (i : ι) :
    cappedStoppingDistance R c r x ≤ dist x (c i) + r i := by
  exact ciInf_le (cappedStoppingDistance_bddBelow R c r hR hr x) (some i)

theorem cappedStoppingDistance_le_add_dist {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x y : X) :
    cappedStoppingDistance R c r x ≤ cappedStoppingDistance R c r y + dist x y := by
  have hbound : cappedStoppingDistance R c r x - dist x y ≤
      cappedStoppingDistance R c r y := by
    apply le_ciInf
    intro i
    cases i with
    | none =>
      have hcap := cappedStoppingDistance_le_cap R c r hR hr x
      have hdist : 0 ≤ dist x y := dist_nonneg
      change cappedStoppingDistance R c r x - dist x y ≤ R
      linarith
    | some i =>
      have hcenter := cappedStoppingDistance_le_center_radius R c r hR hr x i
      have htriangle := dist_triangle x y (c i)
      change cappedStoppingDistance R c r x - dist x y ≤ dist y (c i) + r i
      linarith
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStoppingScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

theorem cellRegionStoppingScale_le_top (x : Ambient d) :
    cellRegionStoppingScale μ R hR k z Good x ≤ latticeRadius R k :=
  cappedStoppingDistance_le_cap _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x

theorem cellRegionStoppingScale_le_center_radius (x : Ambient d)
    (i : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i) :
    cellRegionStoppingScale μ R hR k z Good x ≤ dist x i.center + i.radius :=
  cappedStoppingDistance_le_center_radius (latticeRadius R k)
    (fun j : {j : SupportCellDescendant μ R hR k z // activeRegionCell Good j} => j.val.center)
    (fun j => j.val.radius) (latticeRadius_pos R hR k).le
    (fun j => j.val.radius_pos.le) x ⟨i, hi⟩

theorem cellRegionStoppingScale_le_add_dist (x y : Ambient d) :
    cellRegionStoppingScale μ R hR k z Good x ≤
      cellRegionStoppingScale μ R hR k z Good y + dist x y :=
  cappedStoppingDistance_le_add_dist _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x y

theorem cellRegionStoppingScale_lower_at_stop
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) :
    i.radius / 8 ≤ cellRegionStoppingScale μ R hR k z Good i.center := by
  unfold cellRegionStoppingScale cappedStoppingDistance
  apply le_ciInf
  intro q
  cases q with
  | none =>
    change i.radius / 8 ≤ latticeRadius R k
    have hr : i.radius ≤ latticeRadius R k :=
      latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
    have hp := i.radius_pos
    linarith
  | some q => exact activeRegionCell_stop_scale_separation Good i q.val hi q.property

theorem cellRegionStoppingScale_upper_at_stop
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) :
    cellRegionStoppingScale μ R hR k z Good i.center ≤ 192 * i.radius := by
  by_cases hzero : i.depth = 0
  · have hr : i.radius = latticeRadius R k := by simp only [SupportCellDescendant.radius, hzero, Nat.add_zero]
    have hcap := cellRegionStoppingScale_le_top μ R hR k z Good i.center
    rw [← hr] at hcap
    have hp := i.radius_pos
    linarith
  · obtain ⟨q, hq, hsub, hcenter⟩ := i.exists_ancestor_at_depth (i.depth - 1) (Nat.sub_le _ _)
    have hdepth : i.depth = q.depth + 1 := by omega
    have hactive := activeRegionCell_of_strict_stop_ancestor Good i q hi (by omega) hsub
    have hbound := cellRegionStoppingScale_le_center_radius μ R hR k z Good i.center q hactive
    have hdist := q.dist_center_of_mem i.center hcenter
    have hr : q.radius = 64 * i.radius := by
      change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
      rw [hdepth, ← Nat.add_assoc, latticeRadius_succ]
      ring
    linarith

theorem cellRegionStoppingScale_stop_core_bounds
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (x : Ambient d)
    (hx : dist x i.center ≤ i.radius / 16) :
    i.radius / 16 ≤ cellRegionStoppingScale μ R hR k z Good x ∧
      cellRegionStoppingScale μ R hR k z Good x ≤ 193 * i.radius := by
  have hl := cellRegionStoppingScale_lower_at_stop μ R hR k z Good i hi
  have hu := cellRegionStoppingScale_upper_at_stop μ R hR k z Good i hi
  have hxy := cellRegionStoppingScale_le_add_dist μ R hR k z Good x i.center
  have hyx := cellRegionStoppingScale_le_add_dist μ R hR k z Good i.center x
  rw [dist_comm i.center x] at hyx
  have hp := i.radius_pos
  constructor <;> linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem active_level_local_card_bound {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (F : Finset (SupportCellDescendant μ R hR k z))
    (hF : ∀ i ∈ F, i ∈ activeRegionLevel μ R hR k z Good t)
    (x : Ambient d) (A : ℝ) (hA : 0 ≤ A)
    (hnear : ∀ i ∈ F, dist i.center x ≤ A * latticeRadius R (k + t)) :
    (F.card : ℝ) ≤ (2 * A + 1) ^ d := by
  classical
  let r := latticeRadius R (k + t)
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  let f : SupportCellDescendant μ R hR k z → Ambient d := fun i => i.center - x
  have hinj : Set.InjOn f F := by
    intro i hi j hj hij
    have hc : i.center = j.center := by
      have h := congrArg (fun y : Ambient d => y + x) hij
      simpa only [f, sub_add_cancel] using! h
    apply i.eq_of_common_point_same_depth j ((hF i hi).1.trans (hF j hj).1.symm)
      i.center i.center_mem_cell
    rw [hc]
    exact j.center_mem_cell
  have hb : ∀ y ∈ F.image f, ‖y‖ ≤ A * r := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa only [f, ← dist_eq_norm] using! hnear i hi
  have hs : ∀ u ∈ F.image f, ∀ v ∈ F.image f, u ≠ v → 2 * (r / 2) ≤ dist u v := by
    intro u hu v hv huv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    have hci : i.center ∈ (supportLatticeNets μ R hR (k + t)).points := by
      have hd : i.depth = t := (hF i hi).1
      rw [← hd]
      exact i.mem_net
    have hcj : j.center ∈ (supportLatticeNets μ R hR (k + t)).points := by
      have hd : j.depth = t := (hF j hj).1
      rw [← hd]
      exact j.mem_net
    have hcne : i.center ≠ j.center := fun h => huv (congrArg (fun y => y - x) h)
    have hsep := (supportLatticeNets μ R hR (k + t)).separated hci hcj hcne
    simpa only [f, dist_sub_right, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! hsep
  have hcard := euclidean_separated_card_le (F.image f) (A * r) (r / 2)
    (mul_nonneg hA hr.le) (by positivity) hb hs
  have heq : (A * r + r / 2) / (r / 2) = 2 * A + 1 := by
    apply (div_eq_iff (show r / 2 ≠ 0 by positivity)).mpr
    ring
  rw [Finset.card_image_iff.mpr hinj, heq] at hcard
  exact hcard

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)

theorem activeLevelWeight_ne_zero_iff (i : SupportCellDescendant μ R hR k z)
    (x : Ambient d) :
    activeLevelWeight μ R hR k z Good t i x ≠ 0 ↔
      dist x i.center < 4 * latticeRadius R (k + t) := by
  rw [activeLevelWeight, ne_eq, finiteNormalizedWeight_eq_zero_iff]
  exact finiteCoverCutoff_ne_zero_iff _ _ (latticeRadius_pos R hR (k + t)) _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ImmediateChildPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem supportImmediateChild_radius {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (i : supportImmediateChildren μ R hR k z) :
    i.val.radius = latticeRadius R k / 64 := by
  have hi := (mem_supportImmediateChildren μ R hR k z i.val).mp i.property
  simp only [SupportCellDescendant.radius, hi, latticeRadius_succ]

theorem cleanSupportCell_eq_immediate_children {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    cleanSupportCell μ R hR k z = ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx 1
    exact mem_iUnion.mpr ⟨⟨i, (mem_supportImmediateChildren μ R hR k z i).mpr hi.1⟩, hi.2⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact i.val.cell_subset_top hi

theorem supportImmediateChildren_card_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    (supportImmediateChildren μ R hR k z).card ≤ 257 ^ d := by
  have hnear : ∀ i ∈ supportImmediateChildren μ R hR k z,
      dist i.center (z : Ambient d) ≤ 128 * latticeRadius R (k + 1) := by
    intro i _
    rw [latticeRadius_succ]
    linarith [i.center_dist_top]
  have h := active_level_local_card_bound μ R hR k z (fun _ => True) 1
    (supportImmediateChildren μ R hR k z)
    (fun i hi => (mem_activeLevelIndex μ R hR k z (fun _ => True) 1 i).mp hi)
    (z : Ambient d) 128 (by norm_num) hnear
  norm_num at h
  exact_mod_cast h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.eq_root_of_zero_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    i = supportCellRoot μ R hR k z := by
  have hc := (i.zero_depth_geometry hi).1
  rcases i with ⟨t, x, hx, ha⟩
  change t = 0 at hi
  subst t
  change x = (z : Ambient d) at hc
  subst x
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_FiniteProjectionAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite projection averages

Weighted displacement averages interpolate between the identity and local
projections. Nonnegative weights control displacement from the original point
or a common reference point, and continuous data give a continuous average.
-/

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*} {d : ℕ}

theorem finiteProjectionAverage_eq_self (F : Finset ι) (θ : ι → Ambient d → ℝ)
    (π : ι → Ambient d → Ambient d) (x : Ambient d)
    (hθ : ∀ i ∈ F, θ i x = 0) : finiteProjectionAverage F θ π x = x := by
  unfold finiteProjectionAverage
  have hsum : (∑ i ∈ F, θ i x • (π i x - x)) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hθ i hi, zero_smul])
  rw [hsum, add_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionTubeLocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Orthogonal projection and distances to an affine plane control ambient distances.
The same estimate locates a chart from its planar coordinates and height bound.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem dist_le_projection_add_plane_distances {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x c : Ambient d) :
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
      infDist x (S : Set (Ambient d)) + infDist c (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  have hn := normal_projection_bound_by_plane_distances S x c
  have ht := norm_add_le (S.direction.starProjection (x - c))
    ((S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c))
  rw [S.direction.starProjection_add_starProjection_orthogonal] at ht
  rw [map_sub, ← dist_eq_norm x c,
    ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection c)] at ht
  calc
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
        ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c)‖ := ht
    _ ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
        (infDist x (S : Set (Ambient d)) + infDist c (S : Set (Ambient d))) :=
      add_le_add le_rfl hn
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelProjectionMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

theorem activeLevelProjectionMap_eq_self_of_large_scale (x : Ambient d)
    (hx : 5 * latticeRadius R (k + t) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    activeLevelProjectionMap μ R hR k z Good t S hS x = x := by
  apply finiteProjectionAverage_eq_self
  intro i hi
  by_contra hn
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  have hscale := cellRegionStoppingScale_le_center_radius μ R hR k z Good x i hiA.2
  have hrad : i.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  rw [hrad] at hscale
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

theorem activeRegionSurface_eq_image (t : ℕ) :
    activeRegionSurface μ R hR k z Good S hS t =
      (activeRegionParameterMap μ R hR k z Good S hS t) ''
        (S (supportCellRoot μ R hR k z) : Set (Ambient d)) := by
  induction t with
  | zero => simp only [activeRegionSurface, activeRegionParameterMap, Set.image_id]
  | succ t ih =>
    simp only [activeRegionSurface, activeRegionParameterMap, ih, Set.image_image, Function.comp_def]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

theorem activeRegionParameterMap_stabilizes_of_large_scale
    (u : Ambient d) (t : ℕ)
    (hlarge : 5 * latticeRadius R (k + (t + 1)) ≤
      cellRegionStoppingScale μ R hR k z Good
        (activeRegionParameterMap μ R hR k z Good S hS t u)) :
    ∀ s, t ≤ s → activeRegionParameterMap μ R hR k z Good S hS s u =
      activeRegionParameterMap μ R hR k z Good S hS t u := by
  have hfixed : ∀ j, activeRegionParameterMap μ R hR k z Good S hS (t + j) u =
      activeRegionParameterMap μ R hR k z Good S hS t u := by
    intro j
    induction j with
    | zero => simp only [Nat.add_zero]
    | succ j ih =>
      rw [← Nat.add_assoc, activeRegionParameterMap, Function.comp_apply, ih]
      apply activeLevelProjectionMap_eq_self_of_large_scale
      have hr := latticeRadius_antitone R hR.le
        (show k + (t + 1) ≤ k + (t + j + 1) by omega)
      exact (mul_le_mul_of_nonneg_left hr (by norm_num)).trans hlarge
  intro s hs
  simpa only [Nat.add_sub_of_le hs] using! hfixed (s - t)

theorem active_region_limit_eq_parameter_of_large_scale
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hpoint : ∀ u : S (supportCellRoot μ R hR k z),
      Tendsto (fun t => activeRegionParameterMap μ R hR k z Good S hS t u) atTop (𝓝 (f u)))
    (u : S (supportCellRoot μ R hR k z)) (t : ℕ)
    (hlarge : 5 * latticeRadius R (k + (t + 1)) ≤
      cellRegionStoppingScale μ R hR k z Good
        (activeRegionParameterMap μ R hR k z Good S hS t u)) :
    f u = activeRegionParameterMap μ R hR k z Good S hS t u := by
  have hfixed := activeRegionParameterMap_stabilizes_of_large_scale μ R hR k z Good S hS u t hlarge
  have hevent : ∀ᶠ s in atTop, activeRegionParameterMap μ R hR k z Good S hS s u =
      activeRegionParameterMap μ R hR k z Good S hS t u :=
    Filter.eventually_atTop.mpr ⟨t, hfixed⟩
  have hconst : Tendsto (fun s => activeRegionParameterMap μ R hR k z Good S hS s u) atTop
      (𝓝 (activeRegionParameterMap μ R hR k z Good S hS t u)) :=
    tendsto_const_nhds.congr' (hevent.mono (fun _ hs => hs.symm))
  exact tendsto_nhds_unique (hpoint u) hconst

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLocalStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem active_region_limit_eq_finite_of_tail_small {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i))
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hpoint : ∀ u : S (supportCellRoot μ R hR k z),
      Tendsto (fun t => activeRegionParameterMap μ R hR k z Good S hS t u) atTop (𝓝 (f u)))
    (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ t (u : S (supportCellRoot μ R hR k z)),
      dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤ B * latticeRadius R (k + t))
    (K : Set (Ambient d)) (δ : ℝ)
    (hK : ∀ x ∈ K, δ ≤ cellRegionStoppingScale μ R hR k z Good x)
    (t : ℕ) (hsmall : (B + 5) * latticeRadius R (k + t) < δ) :
    Set.range f ∩ K = activeRegionSurface μ R hR k z Good S hS t ∩ K := by
  let D := cellRegionStoppingScale μ R hR k z Good
  have hr := latticeRadius_pos R hR (k + t)
  have hrad := latticeRadius_antitone R hR.le (show k + t ≤ k + (t + 1) by omega)
  have hnext : 5 * latticeRadius R (k + (t + 1)) ≤ δ := by nlinarith
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, hxK⟩
    have hD := cellRegionStoppingScale_le_add_dist μ R hR k z Good (f u)
      (activeRegionParameterMap μ R hR k z Good S hS t u)
    rw [dist_comm (f u)] at hD
    have hbound := htail t u
    have hx := hK (f u) hxK
    have hlarge : 5 * latticeRadius R (k + (t + 1)) ≤
        D (activeRegionParameterMap μ R hR k z Good S hS t u) := by
      change δ ≤ D (f u) at hx
      change D (f u) ≤ D (activeRegionParameterMap μ R hR k z Good S hS t u) +
        dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) at hD
      nlinarith
    have heq := active_region_limit_eq_parameter_of_large_scale μ R hR k z Good S hS f hpoint u t hlarge
    refine ⟨?_, hxK⟩
    rw [heq, activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  · rintro ⟨hx, hxK⟩
    rw [activeRegionSurface_eq_image] at hx
    obtain ⟨a, ha, hax⟩ := hx
    let u : S (supportCellRoot μ R hR k z) := ⟨a, ha⟩
    have hlarge : 5 * latticeRadius R (k + (t + 1)) ≤
        D (activeRegionParameterMap μ R hR k z Good S hS t u) := by
      change 5 * latticeRadius R (k + (t + 1)) ≤ D (activeRegionParameterMap μ R hR k z Good S hS t a)
      rw [hax]
      exact hnext.trans (hK x hxK)
    have heq := active_region_limit_eq_parameter_of_large_scale μ R hR k z Good S hS f hpoint u t hlarge
    exact ⟨⟨u, heq.trans hax⟩, hxK⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellSurfaceApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bilateral approximation by active-cell surfaces

Exact tangential chart coordinates and the reference-plane height bound locate surface points
near support points. Conversely, surface points in the inner ball remain close to the support
by projecting onto the bilaterally approximating plane. Both estimates retain the explicit
error constant at the cell radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (q : SupportCellDescendant μ R hR k z)
  (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
  (ε : ℝ)
  (hfit : bilateralPlaneError μ q.center (1024 * q.radius) S < ε)
  (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)

include hS hfit hchart

theorem active_cell_support_point_near_surface (x : Ambient d) (hx : x ∈ μ.support)
    (hnear : dist x q.center ≤ 2 * q.radius) :
    ∃ y ∈ A, dist x y ≤ (263168 * ε) * q.radius := by
  obtain ⟨g, _, _, hgCoords, _⟩ := hchart
  let P := S.direction
  have hr := q.radius_pos
  have hu : P.orthogonalProjectionOnto x ∈ closedBall (P.orthogonalProjectionOnto q.center)
      ((5 / 2 : ℝ) * q.radius) := by
    have hp := P.norm_starProjection_apply_le (x - q.center)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    change dist (P.starProjection x) (P.starProjection q.center) ≤ (5 / 2 : ℝ) * q.radius
    linarith
  let u : closedBall (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) :=
    ⟨P.orthogonalProjectionOnto x, hu⟩
  refine ⟨g u, (hgCoords u).1, ?_⟩
  have hc : P.starProjection (g u) = P.starProjection x :=
    congrArg (fun v : P => (v : Ambient d)) (hgCoords u).2.1
  have ht := dist_le_projection_add_plane_distances S hS.1 x (g u)
  change dist x (g u) ≤ dist (P.starProjection x) (P.starProjection (g u)) +
    infDist x (S : Set (Ambient d)) + infDist (g u) (S : Set (Ambient d)) at ht
  rw [hc, dist_self, zero_add] at ht
  have hxheight := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) S hS hfit).1 x
      (by change dist x q.center < 1024 * q.radius; linarith) hx
  have hyheight := (hgCoords u).2.2.1
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionTransitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (s : ℕ)

theorem activeRegionParameterMap_add (j : ℕ) (u : Ambient d) :
    activeRegionParameterMap μ R hR k z Good S hS (s + j) u =
      activeRegionTransitionMap μ R hR k z Good S hS s j
        (activeRegionParameterMap μ R hR k z Good S hS s u) := by
  induction j with
  | zero => simp only [Nat.add_zero, activeRegionTransitionMap, id_eq]
  | succ j ih =>
    rw [← Nat.add_assoc, activeRegionParameterMap, activeRegionTransitionMap, Function.comp_apply,
      Function.comp_apply, ih]

theorem activeRegionSurface_add (j : ℕ) :
    activeRegionSurface μ R hR k z Good S hS (s + j) =
      (activeRegionTransitionMap μ R hR k z Good S hS s j) ''
        activeRegionSurface μ R hR k z Good S hS s := by
  induction j with
  | zero => simp only [Nat.add_zero, activeRegionTransitionMap, Set.image_id]
  | succ j ih =>
    rw [← Nat.add_assoc, activeRegionSurface, ih, Set.image_image]
    rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionTransitionMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem active_region_transition_surface_movement {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (s j : ℕ) (y : Ambient d) (hy : y ∈ activeRegionSurface μ R hR k z Good S hS s) :
    dist (activeRegionTransitionMap μ R hR k z Good S hS s j y) y ≤
      (2 * ((17039360 * ε) / 63)) * latticeRadius R (k + s) := by
  obtain ⟨_, _, _, htail, _, _, _⟩ := hmodel
  rw [activeRegionSurface_eq_image] at hy
  obtain ⟨a, ha, hay⟩ := hy
  let u : S (supportCellRoot μ R hR k z) := ⟨a, ha⟩
  have hs := htail s u
  have hsj := htail (s + j) u
  have ht := dist_triangle
    (activeRegionParameterMap μ R hR k z Good S hS (s + j) u) (f u)
    (activeRegionParameterMap μ R hR k z Good S hS s u)
  rw [dist_comm (f u)] at ht
  have hrad := latticeRadius_antitone R hR.le (show k + s ≤ k + (s + j) by omega)
  have hm := mul_le_mul_of_nonneg_left hrad
    (show 0 ≤ (17039360 * ε) / 63 by positivity)
  have hdist : dist (activeRegionParameterMap μ R hR k z Good S hS (s + j) u)
      (activeRegionParameterMap μ R hR k z Good S hS s u) ≤
        (2 * ((17039360 * ε) / 63)) * latticeRadius R (k + s) := by nlinarith
  rw [activeRegionParameterMap_add] at hdist
  change dist (activeRegionTransitionMap μ R hR k z Good S hS s j
    (activeRegionParameterMap μ R hR k z Good S hS s a))
    (activeRegionParameterMap μ R hR k z Good S hS s a) ≤ _ at hdist
  rwa [hay] at hdist

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PlaneDiskLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem planeUnitHausdorffMeasure_pos (n : ℕ) :
    0 < planeUnitHausdorffMeasure n := by
  have h := measure_closedBall_pos
    (μH[(Module.finrank ℝ (Ambient n) : ℝ)] : Measure (Ambient n))
    (0 : Ambient n) (by norm_num : (0 : ℝ) < 1)
  simpa only [finrank_euclideanSpace_fin, planeUnitHausdorffMeasure] using! h

theorem planeDiskLowerAreaConstant_pos (n : ℕ) (L : ℝ≥0) :
    0 < planeDiskLowerAreaConstant n L := by
  exact ENNReal.div_pos (planeUnitHausdorffMeasure_pos n).ne' (by finiteness)

theorem planeDiskLowerAreaConstant_lt_top (n : ℕ) (L : ℝ≥0) (hL : 0 < L) :
    planeDiskLowerAreaConstant n L < ⊤ := by
  have hL0 : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL.ne'
  exact ENNReal.div_lt_top (planeUnitHausdorffMeasure_lt_top n).ne
    (pow_ne_zero n hL0)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveLocalLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionPositiveLocalLowerAreaConstant_pos (n : ℕ) :
    0 < activeRegionPositiveLocalLowerAreaConstant n := by
  exact ENNReal.mul_pos (planeDiskLowerAreaConstant_pos n 64).ne' (by positivity)

theorem activeRegionPositiveLocalLowerAreaConstant_lt_top (n : ℕ) :
    activeRegionPositiveLocalLowerAreaConstant n < ⊤ := by
  exact ENNReal.mul_lt_top (planeDiskLowerAreaConstant_lt_top n 64 (by norm_num))
    (by finiteness)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStopCoreStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem active_region_stop_core_stabilizes_after_two_levels {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε) (hεtiny : ε ≤ 1 / 268435456)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (t : ℕ) (ht : i.depth + 2 ≤ t) :
    Set.range f ∩ closedBall i.center (i.radius / 16) =
      activeRegionSurface μ R hR k z Good S hS t ∩ closedBall i.center (i.radius / 16) := by
  obtain ⟨_, _, hUnif, htail, _, _, _⟩ := hmodel
  let B := (17039360 * ε) / 63
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hBsmall : B ≤ 1 := by dsimp [B] <;> linarith
  have hr := latticeRadius_pos R hR (k + t)
  have hri := i.radius_pos
  have hrad := latticeRadius_antitone R hR.le (Nat.add_le_add_left ht k)
  have hbase : latticeRadius R (k + (i.depth + 2)) = i.radius / 4096 := by
    change latticeRadius R (k + (i.depth + 2)) = latticeRadius R (k + i.depth) / 4096
    rw [show k + (i.depth + 2) = (k + i.depth) + 2 by omega, latticeRadius_add]
    norm_num
    ring
  rw [hbase] at hrad
  have hmul := mul_le_mul_of_nonneg_right hBsmall hr.le
  have hsmall : (B + 5) * latticeRadius R (k + t) < i.radius / 16 := by nlinarith
  apply active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hUnif.tendsto_at u) B hB htail (closedBall i.center (i.radius / 16))
    (i.radius / 16) ?_ t hsmall
  intro x hx
  exact (cellRegionStoppingScale_stop_core_bounds μ R hR k z Good i hi x hx).1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStopCoreLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεfine hsmall hfit hmodel

theorem exists_active_region_limit_point_near_stop_center
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    ∃ x ∈ Set.range f, dist x i.center ≤ i.radius / 1024 := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth (i.depth - 1) (Nat.sub_le _ _)
  have hid : i.depth = q.depth + 1 := by omega
  have hqA := activeRegionCell_of_strict_stop_ancestor Good i q hi (by omega) hsub
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hqA⟩
  have hscale : q.radius = 64 * i.radius := by
    change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
    rw [hid, ← Nat.add_assoc, latticeRadius_succ]
    ring
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨y, hy, hnear⟩ := active_cell_support_point_near_surface μ R hR k z q (S q) (hS q)
    ε (hfit q hqA) (activeRegionSurface μ R hR k z Good S hS q.depth) (hcharts q hqF)
    i.center i.center_mem_support (q.dist_center_of_mem i.center hc)
  let x := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3 y
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS
    ε hε.le f hmodel q.depth 3 y hy
  change dist x y ≤ (2 * ((17039360 * ε) / 63)) * q.radius at hmove
  have hclose : dist x i.center ≤ i.radius / 1024 := by
    have ht := dist_triangle x y i.center
    rw [dist_comm y i.center] at ht
    have hcoeff : (263168 * ε + 2 * ((17039360 * ε) / 63)) * 64 ≤ 1 / 1024 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff i.radius_pos.le
    rw [hscale] at hnear hmove
    nlinarith
  have hcore : x ∈ closedBall i.center (i.radius / 16) := by
    change dist x i.center ≤ i.radius / 16
    have hri := i.radius_pos
    linarith
  have hfinite : x ∈ activeRegionSurface μ R hR k z Good S hS (i.depth + 2) := by
    rw [show i.depth + 2 = q.depth + 3 by omega, activeRegionSurface_add]
    exact ⟨y, hy, rfl⟩
  have hstable := active_region_stop_core_stabilizes_after_two_levels μ R hR k z Good S hS
    ε hε.le hεtiny f hmodel i hi (i.depth + 2) le_rfl
  exact ⟨x, (hstable.symm ▸ (show x ∈ activeRegionSurface μ R hR k z Good S hS
    (i.depth + 2) ∩ closedBall i.center (i.radius / 16) from ⟨hfinite, hcore⟩)).1, hclose⟩

theorem active_region_stop_core_area_ge
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (i.radius / 128)) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d))
        (Set.range f ∩ closedBall i.center (i.radius / 32)) := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨x, hx, hclose⟩ := exists_active_region_limit_point_near_stop_center μ R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel i hi hdepth
  have hri := i.radius_pos
  have hcore : x ∈ closedBall i.center (i.radius / 16) := by
    change dist x i.center ≤ i.radius / 16
    linarith
  have hD := (cellRegionStoppingScale_stop_core_bounds μ R hR k z Good i hi x hcore).1
  have hri0 : i.radius ≤ latticeRadius R k := by
    exact latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
  have harea := active_region_positive_stopping_scale_local_ball_area_ge μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel x hx (by linarith) (i.radius / 128) (by positivity)
    (by linarith) (by linarith)
  refine harea.trans (measure_mono ?_)
  intro y hy
  refine ⟨hy.1, ?_⟩
  have hyb : dist y x ≤ i.radius / 128 := hy.2
  have ht := dist_triangle y x i.center
  change dist y i.center ≤ i.radius / 32
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStopMassArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Stopping-cell mass controlled by model area

Global growth bounds and the lower area of stopping cores control the mass of
stopping cells by Hausdorff measure on the limit model. Disjoint cores allow these
estimates to be summed over countable families inside a prescribed region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem cellRegionStops_small_cores_pairwise_disjoint {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (cellRegionStops μ R hR k z Good).Pairwise
      (fun i j => Disjoint (closedBall i.center (i.radius / 32))
        (closedBall j.center (j.radius / 32))) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hs := cellRegionStops_centers_separated μ R hR k z Good i j hi hj hne
  have hi' := (le_max_left i.radius j.radius).trans hs
  have hj' := (le_max_right i.radius j.radius).trans hs
  have ht := dist_triangle i.center x j.center
  rw [dist_comm i.center x] at ht
  have hxi' : dist x i.center ≤ i.radius / 32 := hxi
  have hxj' : dist x j.center ≤ j.radius / 32 := hxj
  have hr := i.radius_pos
  linarith

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
  (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hg hε hεfine hsmall hfit hmodel

theorem active_region_stop_cell_mass_le_core_area
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hdepth : 0 < i.depth) :
    μ i.cell ≤ activeRegionStopMassAreaConstant n G *
      (μH[(n : ℝ)] : Measure (Ambient d))
        (Set.range f ∩ closedBall i.center (i.radius / 32)) := by
  have hri := i.radius_pos
  have hGnonneg : 0 ≤ G := hg.1
  have hupper : μ i.cell ≤ ENNReal.ofReal (G * 384 ^ n) *
      (ENNReal.ofReal (i.radius / 128)) ^ n := by
    calc
      _ ≤ μ (ball i.center (3 * i.radius)) := measure_mono (fun x hx => by
        have h := i.dist_center_of_mem x hx
        change dist x i.center < 3 * i.radius
        linarith)
      _ ≤ ENNReal.ofReal (G * (3 * i.radius) ^ n) := hg.2 i.center _ (by positivity)
      _ = _ := by
        rw [show 3 * i.radius = 384 * (i.radius / 128) by ring, mul_pow, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity : 0 ≤ G * 384 ^ n),
          ENNReal.ofReal_pow (by positivity : 0 ≤ i.radius / 128)]
  have harea := active_region_stop_core_area_ge μ R hR k z Good S hS ε hε hεfine
    hsmall hfit f hmodel i hi hdepth
  calc
    _ ≤ ENNReal.ofReal (G * 384 ^ n) * (ENNReal.ofReal (i.radius / 128)) ^ n := hupper
    _ = activeRegionStopMassAreaConstant n G *
        (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (i.radius / 128)) ^ n) := by
      unfold activeRegionStopMassAreaConstant
      rw [← mul_assoc, ENNReal.div_mul_cancel
        (activeRegionPositiveLocalLowerAreaConstant_pos n).ne'
        (activeRegionPositiveLocalLowerAreaConstant_lt_top n).ne]
    _ ≤ _ := mul_le_mul_right harea _

theorem active_region_stop_subfamily_mass_le_area
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω : Set (Ambient d))
    (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    (∑' i : F, μ i.val.cell) ≤ activeRegionStopMassAreaConstant n G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := by
  let := supportCellDescendant_countable μ R hR k z
  let A := fun i : F => Set.range f ∩ closedBall i.val.center (i.val.radius / 32)
  have hclosed : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using! hmodel.2.1.isClosedMap Set.univ isClosed_univ
  have hm : ∀ i : F, MeasurableSet (A i) :=
    fun _ => hclosed.measurableSet.inter isClosed_closedBall.measurableSet
  have hd : Pairwise (fun i j : F => Disjoint (A i) (A j)) := by
    intro i j hij
    have h := cellRegionStops_small_cores_pairwise_disjoint μ R hR k z Good
      (hF i.property) (hF j.property) (fun heq => hij (Subtype.ext heq))
    exact h.mono inter_subset_right inter_subset_right
  have hs : (⋃ i : F, A i) ⊆ Set.range f ∩ Ω := by
    apply iUnion_subset
    intro i x hx
    exact ⟨hx.1, hΩ i.val i.property hx.2⟩
  calc
    _ ≤ ∑' i : F, activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) (A i) :=
      ENNReal.tsum_le_tsum (fun i => active_region_stop_cell_mass_le_core_area
        μ G hg R hR k z Good S hS ε hε hεfine hsmall hfit f hmodel i.val
          (hF i.property) (hdepth i.val i.property))
    _ = activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) (⋃ i : F, A i) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion hd hm]
    _ ≤ _ := mul_le_mul_right (measure_mono hs) _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPieceLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass lost outside an active-region piece

Stopping cells whose inner balls miss a chosen piece are charged to discarded
surface area. Combining this estimate with Hausdorff domination bounds the mass
of both the uncovered limit set and the unrepresented stopping cells.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
  (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hg hε hεfine hsmall hfit hmodel

theorem active_region_missed_stop_mass_le_discarded_area
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω E : Set (Ambient d)) (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    (∑' i : {i : SupportCellDescendant μ R hR k z //
      i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, μ i.val.cell) ≤
      activeRegionStopMassAreaConstant n G *
        (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
  let B : Set (SupportCellDescendant μ R hR k z) :=
    {i | i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}
  have hB : B ⊆ cellRegionStops μ R hR k z Good := fun _ hi => hF hi.1
  have hloc : ∀ i ∈ B, closedBall i.center (i.radius / 32) ⊆ Ω \ E := by
    intro i hi x hx
    exact ⟨hΩ i hi.1 hx, fun hE => Set.disjoint_left.mp hi.2 hx hE⟩
  have h := active_region_stop_subfamily_mass_le_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel B hB (fun i hi => hdepth i hi.1) (Ω \ E) hloc
  have heq : Set.range f ∩ (Ω \ E) = (Set.range f ∩ Ω) \ E := by ext x; simp only [mem_inter_iff, mem_sdiff]; tauto
  rwa [heq] at h

theorem active_region_unrepresented_mass_le_discarded_area
    (hG : 0 < G)
    (F : Set (SupportCellDescendant μ R hR k z))
    (hF : F ⊆ cellRegionStops μ R hR k z Good) (hdepth : ∀ i ∈ F, 0 < i.depth)
    (Ω E : Set (Ambient d)) (hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω) :
    μ (((cellRegionLimit μ R hR k z Good ∩ Ω) \ E) ∪
      ⋃ i : {i : SupportCellDescendant μ R hR k z //
        i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
  let := supportCellDescendant_countable μ R hR k z
  let A := (cellRegionLimit μ R hR k z Good ∩ Ω) \ E
  let B := {i : SupportCellDescendant μ R hR k z |
    i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}
  have hsub : A ⊆ (Set.range f ∩ Ω) \ E := by
    intro x hx
    exact ⟨⟨hmodel.2.2.2.2.2.1 hx.1.1, hx.1.2⟩, hx.2⟩
  have hsurv : μ A ≤ ENNReal.ofReal G *
      (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := by
    have h := global_growth_le_hausdorffMeasure μ G hG hg A
    simp only [Measure.smul_apply, smul_eq_mul] at h
    exact h.trans (mul_le_mul_right (measure_mono hsub) _)
  have hstops := active_region_missed_stop_mass_le_discarded_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel F hF hdepth Ω E hΩ
  calc
    _ ≤ μ A + μ (⋃ i : B, i.val.cell) := measure_union_le _ _
    _ ≤ μ A + ∑' i : B, μ i.val.cell := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal G * (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) +
        activeRegionStopMassAreaConstant n G *
          (μH[(n : ℝ)] : Measure (Ambient d)) ((Set.range f ∩ Ω) \ E) := add_le_add hsurv hstops
    _ = _ := (add_mul _ _ _).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellPieceSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem active_cell_covered_by_survivors_and_deeper_stops {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    q.cell ⊆ (cellRegionLimit μ R hR k z Good ∩ q.cell) ∪
      ⋃ i : activeCellStopDescendants μ R hR k z Good q, i.val.cell := by
  intro x hx
  by_cases hs : x ∈ cellRegionLimit μ R hR k z Good
  · exact Or.inl ⟨hs, hx⟩
  obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell μ R hR k z Good x (q.cell_subset_top hx) hs
  have hdepth : q.depth < i.depth := by
    by_contra hn
    have hid : i.depth ≤ q.depth := le_of_not_gt hn
    exact hi.1 (hq i hid (q.cell_nested_of_common_point i hid x hx hxi))
  have hisub := i.cell_nested_of_common_point q hdepth.le x hxi hx
  exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi, hdepth, hisub⟩, hxi⟩)

theorem descendant_small_core_subset_cell_enlargement {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (q i : SupportCellDescendant μ R hR k z)
    (hdepth : q.depth ≤ i.depth) (hsub : i.cell ⊆ q.cell) :
    closedBall i.center (i.radius / 32) ⊆ closedBall q.center (3 * q.radius) := by
  intro x hx
  have hnear := q.dist_center_of_mem i.center (hsub i.center_mem_cell)
  have hrad : i.radius ≤ q.radius :=
    latticeRadius_antitone R hR.le (Nat.add_le_add_left hdepth k)
  have hb : dist x i.center ≤ i.radius / 32 := hx
  have ht := dist_triangle x i.center q.center
  have hrq := q.radius_pos
  change dist x q.center ≤ 3 * q.radius
  linarith

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G)
  (hg : GlobalUpperGrowth n G μ) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hG hg hε hεfine hsmall hfit hmodel

theorem active_cell_remainder_mass_le_discarded_area
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) :
    μ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) := by
  classical
  let F := activeCellStopDescendants μ R hR k z Good q
  let Ω := closedBall q.center (3 * q.radius)
  have hloc : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω := by
    intro i hi
    exact descendant_small_core_subset_cell_enlargement μ R hR k z q i hi.2.1.le hi.2.2
  have hcover : q.cell \ activeCellRepresentedSet μ R hR k z Good q E ⊆
      ((cellRegionLimit μ R hR k z Good ∩ Ω) \ E) ∪
      ⋃ i : {i : SupportCellDescendant μ R hR k z //
        i ∈ F ∧ Disjoint (closedBall i.center (i.radius / 32)) E}, i.val.cell := by
    intro x hx
    have hxnot := hx.2
    change x ∉ (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E) ∪ _ at hxnot
    rcases active_cell_covered_by_survivors_and_deeper_stops μ R hR k z Good q hq hx.1 with hs | ht
    · refine Or.inl ⟨⟨hs.1, ?_⟩, ?_⟩
      · have hd := q.dist_center_of_mem x hx.1
        have hr := q.radius_pos
        change dist x q.center ≤ 3 * q.radius
        linarith
      · exact fun hE => hxnot (Or.inl ⟨hs, hE⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp ht
      have hd : Disjoint (closedBall i.val.center (i.val.radius / 32)) E := by
        by_contra hn
        exact hxnot (Or.inr (mem_iUnion.mpr ⟨⟨i.val, i.property, hn⟩, hi⟩))
      exact Or.inr (mem_iUnion.mpr ⟨⟨i.val, i.property, hd⟩, hi⟩)
  exact (measure_mono hcover).trans
    (active_region_unrepresented_mass_le_discarded_area μ G hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel hG F (fun _ hi => hi.1)
      (fun _ hi => lt_of_le_of_lt (Nat.zero_le q.depth) hi.2.1) Ω E hloc)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedStopCoreGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem stop_core_points_radius_separation {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i j : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good)
    (hj : j ∈ cellRegionStops μ R hR k z Good) (hne : i ≠ j)
    (x y : Ambient d) (hx : x ∈ closedBall i.center (i.radius / 32))
    (hy : y ∈ closedBall j.center (j.radius / 32)) :
    max i.radius j.radius ≤ 16 * dist x y := by
  have hs := cellRegionStops_centers_separated μ R hR k z Good i j hi hj hne
  have hx' : dist x i.center ≤ i.radius / 32 := hx
  have hy' : dist y j.center ≤ j.radius / 32 := hy
  have h1 := dist_triangle i.center x j.center
  have h2 := dist_triangle x y j.center
  rw [dist_comm i.center x] at h1
  have hiM := le_max_left i.radius j.radius
  have hjM := le_max_right i.radius j.radius
  linarith

theorem survivor_stop_core_point_radius_separation {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (x y : Ambient d) (hx : x ∈ closedBall i.center (i.radius / 32))
    (hy : y ∈ cellRegionLimit μ R hR k z Good) :
    i.radius ≤ 16 * dist x y := by
  have hs := cellRegionLimit_stop_center_separated μ R hR k z Good i hi y hy
  have hx' : dist x i.center ≤ i.radius / 32 := hx
  have ht := dist_triangle y x i.center
  rw [dist_comm y x] at ht
  have hd : 0 ≤ dist x y := dist_nonneg
  linarith

theorem stop_core_parameter_radii_separated {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (F : Set (SupportCellDescendant μ R hR k z)) (hF : F ⊆ cellRegionStops μ R hR k z Good)
    (x : F → Ambient d) (a : F → Ambient n) (M : ℝ≥0)
    (hx : ∀ i : F, x i ∈ closedBall i.val.center (i.val.radius / 32))
    (hcoord : ∀ i j : F, dist (x i) (x j) ≤ (M : ℝ) * dist (a i) (a j)) :
    ∀ i j : F, i ≠ j → i.val.radius + j.val.radius ≤ 32 * (M : ℝ) * dist (a i) (a j) := by
  intro i j hij
  have hs := stop_core_points_radius_separation μ R hR k z Good i.val j.val
    (hF i.property) (hF j.property) (fun heq => hij (Subtype.ext heq))
    (x i) (x j) (hx i) (hx j)
  have hc := hcoord i j
  have hiM := le_max_left i.val.radius j.val.radius
  have hjM := le_max_right i.val.radius j.val.radius
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ChildAndPointChartGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_children_and_points {n d : ℕ} {ι κ : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (b : κ → Ambient n) (y : κ → Ambient d)
    (f : ∀ i : ι, ball (0 : Ambient n) (r i) → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (hsepPoint : ∀ i : ι, ∀ j : κ, r i ≤ (A : ℝ) * dist (a i) (b j))
    (hcenterPoint : ∀ i : ι, ∀ j : κ, dist (c i) (y j) ≤ (L : ℝ) * dist (a i) (b j))
    (hpointLip : ∀ i j : κ, dist (y i) (y j) ≤ (L : ℝ) * dist (b i) (b j))
    (himage : ∀ i : ι, Set.range (f i) ⊆ closedBall (c i) (3 * r i))
    (hLip : ∀ i : ι, LipschitzWith M (f i))
    (ρ : ℝ) (hball : ∀ i : ι, ball (a i) (r i / (4 * (A : ℝ))) ⊆ ball (0 : Ambient n) ρ)
    (hpointBall : ∀ j : κ, b j ∈ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * A)) A L) F ∧
      ((⋃ i : ι, Set.range (f i)) ∪ Set.range y) ⊆ Set.range F := by
  classical
  have hs : 0 < 4 * A := by positivity
  have hc (i : ι) := exists_rescaled_ball_chart (r i) (a i) (4 * A) hs (f i) M (hLip i)
  choose g hg hrange using hc
  have hrange' (i : ι) : g i '' ball (a i) (r i / (4 * (A : ℝ))) = Set.range (f i) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hrange i
  have hg' (i : ι) : LipschitzOnWith (M * (4 * A)) (g i)
      (ball (a i) (r i / (4 * (A : ℝ)))) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hg i
  let a' : Sum ι κ → Ambient n := Sum.elim a b
  let c' : Sum ι κ → Ambient d := Sum.elim c y
  let r' : Sum ι κ → ℝ := Sum.elim r (fun _ => 0)
  let D' : Sum ι κ → Set (Ambient n) :=
    Sum.elim (fun i => ball (a i) (r i / (4 * (A : ℝ)))) (fun j => {b j})
  let g' : Sum ι κ → Ambient n → Ambient d := Sum.elim g (fun j _ => y j)
  have hsep' (i j : Sum ι κ) (hij : i ≠ j) :
      r' i + r' j ≤ (A : ℝ) * dist (a' i) (a' j) := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hsep i j (fun heq => hij (congrArg Sum.inl heq))
      | inr j => simpa only [r', a', Sum.elim_inl, Sum.elim_inr, add_zero] using! hsepPoint i j
    | inr i =>
      cases j with
      | inl j => simpa only [r', a', Sum.elim_inl, Sum.elim_inr, zero_add, dist_comm] using! hsepPoint j i
      | inr j =>
        change 0 + 0 ≤ _
        rw [zero_add]
        exact mul_nonneg A.coe_nonneg dist_nonneg
  have hcenters' (i j : Sum ι κ) : dist (c' i) (c' j) ≤ (L : ℝ) * dist (a' i) (a' j) := by
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hcenters i j
      | inr j => exact hcenterPoint i j
    | inr i =>
      cases j with
      | inl j => simpa only [c', a', Sum.elim_inl, Sum.elim_inr, dist_comm] using! hcenterPoint j i
      | inr j => exact hpointLip i j
  have hparam' (i : Sum ι κ) (u : Ambient n) (hu : u ∈ D' i) :
      dist u (a' i) ≤ r' i / (4 * (A : ℝ)) := by
    cases i with
    | inl i => exact le_of_lt hu
    | inr j =>
      have heq : u = b j := hu
      simp only [a', r', Sum.elim_inr, heq, dist_self, zero_div, le_refl]
  have himage' (i : Sum ι κ) (u : Ambient n) (hu : u ∈ D' i) :
      dist (g' i u) (c' i) ≤ 3 * r' i := by
    cases i with
    | inl i => exact himage i (hrange' i ▸ mem_image_of_mem (g i) hu)
    | inr j => simp only [g', c', r', Sum.elim_inr, dist_self, mul_zero, le_refl]
  have hLip' (i : Sum ι κ) : LipschitzOnWith (M * (4 * A)) (g' i) (D' i) := by
    cases i with
    | inl i => exact hg' i
    | inr j =>
      apply LipschitzOnWith.of_dist_le_mul
      intro u hu v hv
      change dist (y j) (y j) ≤ _
      rw [dist_self]
      positivity
  have hball' : (⋃ i : Sum ι κ, D' i) ⊆ ball (0 : Ambient n) ρ := by
    apply iUnion_subset
    intro i
    cases i with
    | inl i => exact hball i
    | inr j => exact singleton_subset_iff.mpr (hpointBall j)
  obtain ⟨F, hF, hcover⟩ := exists_ball_lipschitz_cover_of_separated_parameter_patches
    a' c' r' D' g' (M * (4 * A)) A L hA hsep' hcenters' hparam' himage' hLip' ρ hball'
  refine ⟨F, hF, ?_⟩
  intro v hv
  rcases hv with hchild | hpoint
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hchild
    have hi' : v ∈ g i '' ball (a i) (r i / (4 * (A : ℝ))) := hrange' i ▸ hi
    exact hcover (mem_iUnion.mpr ⟨Sum.inl i, hi'⟩)
  · obtain ⟨j, rfl⟩ := hpoint
    exact hcover (mem_iUnion.mpr ⟨Sum.inr j, b j, mem_singleton (b j), rfl⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedStopChildGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_stop_children_and_survivors {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (ρ : ℝ) (hρ : 0 < ρ) (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) ρ)
    (F : Set (SupportCellDescendant μ R hR k z)) (hF : F ⊆ cellRegionStops μ R hR k z Good)
    (x : F → Ambient d)
    (hx : ∀ i : F, x i ∈ closedBall i.val.center (i.val.radius / 32))
    (hxE : ∀ i : F, x i ∈ E) (hradius : ∀ i : F, i.val.radius ≤ ρ)
    (f : ∀ i : F, ball (0 : Ambient n) i.val.radius → Ambient d) (M : ℝ≥0)
    (hLip : ∀ i : F, LipschitzWith M (f i))
    (himage : ∀ i : F, Set.range (f i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (2 * ρ) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) g ∧
      ((cellRegionLimit μ R hR k z Good ∩ E) ∪ ⋃ i : F, Set.range (f i)) ⊆ Set.range g := by
  let P := cellRegionLimit μ R hR k z Good ∩ E
  let a : F → Ambient n := fun i => coord (x i)
  let b : P → Ambient n := fun y => coord y.val
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hA : 0 < 32 * L := by positivity
  have hsep (i j : F) (hij : i ≠ j) :
      i.val.radius + j.val.radius ≤ ((32 * L : ℝ≥0) : ℝ) * dist (a i) (a j) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using!
      stop_core_parameter_radii_separated μ R hR k z Good F hF x a L hx
        (fun i j => hcoord (x i) (hxE i) (x j) (hxE j)) i j hij
  have hcenter (i j : F) : dist (x i) (x j) ≤ (L : ℝ) * dist (a i) (a j) :=
    hcoord (x i) (hxE i) (x j) (hxE j)
  have hsepPoint (i : F) (y : P) :
      i.val.radius ≤ ((32 * L : ℝ≥0) : ℝ) * dist (a i) (b y) := by
    have hs := survivor_stop_core_point_radius_separation μ R hR k z Good
      i.val (hF i.property) (x i) y.val (hx i) y.property.1
    have hc := hcoord (x i) (hxE i) y.val y.property.2
    change i.val.radius ≤ (32 * (L : ℝ)) * dist (coord (x i)) (coord y.val)
    nlinarith [show 0 ≤ dist (x i) y.val from dist_nonneg]
  have hcenterPoint (i : F) (y : P) :
      dist (x i) y.val ≤ (L : ℝ) * dist (a i) (b y) :=
    hcoord (x i) (hxE i) y.val y.property.2
  have hpointLip (y w : P) : dist y.val w.val ≤ (L : ℝ) * dist (b y) (b w) :=
    hcoord y.val y.property.2 w.val w.property.2
  have himage' (i : F) : Set.range (f i) ⊆ closedBall (x i) (3 * i.val.radius) := by
    intro y hy
    have hc : dist y i.val.center ≤ 2 * i.val.radius := himage i hy
    have hx' : dist (x i) i.val.center ≤ i.val.radius / 32 := hx i
    have ht := dist_triangle y i.val.center (x i)
    rw [dist_comm i.val.center (x i)] at ht
    have hr := i.val.radius_pos
    change dist y (x i) ≤ 3 * i.val.radius
    linarith
  have hs : 1 ≤ 4 * (32 * L) := by nlinarith
  have hball (i : F) :
      ball (a i) (i.val.radius / (4 * (32 * (L : ℝ)))) ⊆ ball (0 : Ambient n) (2 * ρ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using!
      small_parameter_ball_subset_double_ball (a i) ρ i.val.radius hρ
        (hcoordBall (x i) (hxE i)) (4 * (32 * L)) hs (hradius i)
  have hpointBall (y : P) : b y ∈ ball (0 : Ambient n) (2 * ρ) := by
    have h := hcoordBall y.val y.property.2
    change dist (coord y.val) (0 : Ambient n) ≤ ρ at h
    change dist (coord y.val) (0 : Ambient n) < 2 * ρ
    linarith
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_children_and_points
    a x (fun i => i.val.radius) b (fun y : P => y.val) f M (32 * L) L hA
    hsep hcenter hsepPoint hcenterPoint hpointLip himage' hLip (2 * ρ) hball hpointBall
  refine ⟨g, hg, ?_⟩
  intro y hy
  rcases hy with hp | hc
  · exact hcover (Or.inr ⟨⟨y, hp⟩, rfl⟩)
  · exact hcover (Or.inl hc)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellDeficitAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Deficit bounds for active-cell chart assembly

The uncovered mass of an active cell splits into discarded parent surface area
and deficits of the selected stopping children. Gluing the parent pieces and
child charts preserves their covered sets and transfers this estimate to a
bounded ball chart, with the stated finite-piece Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G)
  (hg : GlobalUpperGrowth n G μ) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hG hg hε hεfine hsmall hfit hmodel

theorem active_cell_deficit_le_selected_losses
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d))
    (B : activeCellSelectedStopSet μ R hR k z Good q E → Set (Ambient d))
    (T : Set (Ambient d))
    (hparent : cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ T)
    (hchild : ∀ i, i.val.cell ∩ B i ⊆ T) :
    μ (q.cell \ T) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
      ∑' i : activeCellSelectedStopSet μ R hR k z Good q E, μ (i.val.cell \ B i) := by
  classical
  let := supportCellDescendant_countable μ R hR k z
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hsub : q.cell \ T ⊆ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) ∪
      ⋃ i : F, i.val.cell \ B i := by
    intro x hx
    by_cases hrep : x ∈ activeCellRepresentedSet μ R hR k z Good q E
    · rcases hrep with hp | hc
      · exact (hx.2 (hparent hp)).elim
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
        exact Or.inr (mem_iUnion.mpr ⟨i, hi, fun hb => hx.2 (hchild i ⟨hi, hb⟩)⟩)
    · exact Or.inl ⟨hx.1, hrep⟩
  have hmass : μ (q.cell \ T) ≤ μ (q.cell \ activeCellRepresentedSet μ R hR k z Good q E) +
      ∑' i : F, μ (i.val.cell \ B i) :=
    ((measure_mono hsub).trans (measure_union_le _ _)).trans
    (add_le_add le_rfl (measure_iUnion_le _))
  exact hmass.trans (add_le_add
    (active_cell_remainder_mass_le_discarded_area μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel q hq E) le_rfl)

theorem exists_active_cell_chart_with_deficit_bound
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (E : Set (Ambient d)) (coord : Ambient d → Ambient n) (L : ℝ≥0) (hL : 1 ≤ L)
    (hcoord : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (L : ℝ) * dist (coord x) (coord y))
    (hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) q.radius)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith ((lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * (32 * L))) (32 * L) L) * 2) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  classical
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hx (i : F) : ∃ x : Ambient d, x ∈ closedBall i.val.center (i.val.radius / 32) ∧ x ∈ E :=
    Set.not_disjoint_iff.mp i.property.2
  choose x hxcore hxE using hx
  have hradius (i : F) : i.val.radius ≤ q.radius :=
    latticeRadius_antitone R hR.le (Nat.add_le_add_left i.property.1.2.1.le k)
  obtain ⟨g, hgLip, hcover⟩ := exists_ball_lipschitz_cover_of_stop_children_and_survivors
    μ R hR k z Good E coord L hL hcoord q.radius q.radius_pos hcoordBall F
    (fun _ hi => hi.1.1) x hxcore hxE hradius child M hLip himage
  obtain ⟨g', hg'Lip, hg'Range, hpreserve⟩ := exists_bounded_normalized_ball_chart q.radius
    q.center (2 * q.radius) (by linarith [q.radius_pos]) g _ hgLip
  have hparent : cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g' := by
    intro y hy
    apply hpreserve
    exact ⟨q.dist_center_of_mem y hy.1.2, hcover (Or.inl ⟨hy.1.1, hy.2⟩)⟩
  have hchild : ∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g' := by
    intro i y hy
    apply hpreserve
    exact ⟨q.dist_center_of_mem y (i.property.1.2.2 hy.1),
      hcover (Or.inr (mem_iUnion.mpr ⟨i, hy.2⟩))⟩
  exact ⟨g', hg'Lip, hg'Range, hparent, hchild,
    active_cell_deficit_le_selected_losses μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel q hq E (fun i => Set.range (child i))
      (Set.range g') hparent hchild⟩

theorem exists_active_cell_finite_piece_deficit_assembly (hn : 0 < n)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (N : ℕ) (D : Fin N → Set (Ambient n))
    (hD : ∀ j, D j ⊆ ball (0 : Ambient n) q.radius)
    (piece : Fin N → Ambient n → Ambient d) (P : ℝ≥0)
    (hpieceLip : ∀ j, LipschitzOnWith P (piece j) (D j))
    (hpieceImage : ∀ j, piece j '' D j ⊆ closedBall q.center (3 * q.radius))
    (E : Set (Ambient d)) (hE : E = ⋃ j : Fin N, piece j '' D j)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (activeCellFinitePieceAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          μ (i.val.cell \ Set.range (child i)) := by
  obtain ⟨coord, hcoordBall, hcoord⟩ := exists_coordinates_of_finite_partial_charts hn N
    q.radius q.radius_pos q.center D hD piece P hpieceLip hpieceImage
  rw [← hE] at hcoordBall hcoord
  exact exists_active_cell_chart_with_deficit_bound μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq E coord (finitePartialCoordinateConstant d N P)
    (finitePartialCoordinateConstant_ge_one d N P) hcoord hcoordBall child M hLip himage

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellFinitePieceMassFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Retained mass from finite-piece assembly

For finite mass, two relative deficit bounds leave at least the fraction `1 - δ - η` in the
retained set. Applying this estimate to parent surface loss and uncovered child mass upgrades
finite-piece assembly to a chart with an explicit retained cell-mass fraction, while preserving
its Lipschitz bound and image containment.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem mass_fraction_of_two_deficits (m a b c : ℝ≥0∞) (hm : m ≠ ⊤)
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmass : m ≤ a + b + c)
    (hb : b ≤ ENNReal.ofReal δ * m) (hc : c ≤ ENNReal.ofReal η * m) :
    ENNReal.ofReal (1 - δ - η) * m ≤ a := by
  have htotal : m ≤ a + ENNReal.ofReal (δ + η) * m := by
    have h := hmass.trans (add_le_add (add_le_add le_rfl hb) hc)
    simpa only [ENNReal.ofReal_add hδ hη, add_mul, add_assoc] using! h
  rw [sub_sub, ENNReal.ofReal_sub 1 (add_nonneg hδ hη), ENNReal.ofReal_one,
    ENNReal.sub_mul (fun _ _ => hm), one_mul]
  exact tsub_le_iff_right.mpr htotal

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FiniteChartUnionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem finiteBallChartUnionConstant_mono (d : ℕ) {N K : ℕ} (hNK : N ≤ K)
    {M L : ℝ≥0} (hML : M ≤ L) :
    finiteBallChartUnionConstant d N M ≤ finiteBallChartUnionConstant d K L := by
  have hNK' : (N : ℝ≥0) ≤ (K : ℝ≥0) := by exact_mod_cast hNK
  unfold finiteBallChartUnionConstant separatedPatchGluingConstant finiteChartPackingFactor
  gcongr

theorem exists_ball_lipschitz_cover_of_bounded_finite_family {n d : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (N : ℕ) (hN : Fintype.card ι ≤ N)
    (r : ℝ) (hr : 0 < r) (z : Ambient d)
    (f : ι → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall z (3 * r)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      (⋃ i : ι, Set.range (f i)) ⊆ Set.range g := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_finite_ball_charts hn
    (Fintype.card ι) r hr z (fun j => f (e j)) M (fun j => hLip (e j)) (fun j => himage (e j))
  refine ⟨g, hg.weaken (finiteBallChartUnionConstant_mono d hN le_rfl), ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  apply hcover
  apply mem_iUnion.mpr
  exact ⟨e.symm i, by simpa only [e.apply_symm_apply] using! hi⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ImmediateChildChartRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Immediate-child charts on a parent ball

Rescaling immediate-child charts to the parent lattice ball preserves their images and divides
their Lipschitz bounds by the fixed radius ratio of 64. Restricting the rescaled maps to the open
parent ball gives a common parameter domain for all children.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_immediate_child_charts_on_parent_ball {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (f : ∀ i : supportImmediateChildren μ R hR k z, ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i)) :
    ∃ F : supportImmediateChildren μ R hR k z → ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      (∀ i, LipschitzWith (M / 64) (F i)) ∧ ∀ i, Set.range (F i) = Set.range (f i) := by
  classical
  have hcharts (i : supportImmediateChildren μ R hR k z) :
      ∃ g : Ambient n → Ambient d,
        LipschitzOnWith (M / 64) g (ball (0 : Ambient n) (latticeRadius R k)) ∧
        g '' ball (0 : Ambient n) (latticeRadius R k) = Set.range (f i) := by
    have h := exists_rescaled_ball_chart i.val.radius (0 : Ambient n) (1 / 64)
      (by norm_num) (f i) M (hLip i)
    have hdom : i.val.radius / ((1 / 64 : ℝ≥0) : ℝ) = latticeRadius R k := by
      change i.val.radius / (1 / 64 : ℝ) = latticeRadius R k
      rw [supportImmediateChild_radius μ R hR k z i]
      ring
    rw [hdom] at h
    simpa only [one_div, div_eq_mul_inv, one_mul] using! h
  choose g hg hRange using hcharts
  refine ⟨fun i => (ball (0 : Ambient n) (latticeRadius R k)).domRestrict (g i),
    fun i => (hg i).to_restrict, ?_⟩
  intro i
  apply Set.Subset.antisymm
  · rintro y ⟨u, rfl⟩
    exact hRange i ▸ mem_image_of_mem (g i) u.property
  · intro y hy
    obtain ⟨u, hu, he⟩ := hRange i ▸ hy
    exact ⟨⟨u, hu⟩, he⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ImmediateChildChartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_immediate_child_chart_assembly {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (f : ∀ i : supportImmediateChildren μ R hR k z, ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i))
    (himage : ∀ i, Set.range (f i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      LipschitzWith (immediateChildAssemblyConstant d M) g ∧
      Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
      (∀ i, i.val.cell ∩ Set.range (f i) ⊆ Set.range g) ∧
      μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
        ∑ i : supportImmediateChildren μ R hR k z, μ (i.val.cell \ Set.range (f i)) := by
  classical
  have hr : 0 < latticeRadius R k := latticeRadius_pos R hR k
  obtain ⟨F, hF, hFRange⟩ := exists_immediate_child_charts_on_parent_ball μ R hR k z f M hLip
  have hcount : Fintype.card (supportImmediateChildren μ R hR k z) ≤ 257 ^ d := by
    simpa using! supportImmediateChildren_card_le μ R hR k z
  have hFImage (i : supportImmediateChildren μ R hR k z) :
      Set.range (F i) ⊆ closedBall (z : Ambient d) (3 * latticeRadius R k) := by
    intro y hy
    have hnear : dist y i.val.center ≤ 2 * i.val.radius := himage i (hFRange i ▸ hy)
    have hc := i.val.center_dist_top
    have ht := dist_triangle y i.val.center (z : Ambient d)
    rw [supportImmediateChild_radius μ R hR k z i] at hnear
    change dist y (z : Ambient d) ≤ 3 * latticeRadius R k
    linarith
  obtain ⟨g, hgLip, hgCover⟩ := exists_ball_lipschitz_cover_of_bounded_finite_family hn
    (257 ^ d) hcount (latticeRadius R k) hr (z : Ambient d) F (M / 64) hF hFImage
  obtain ⟨p, hpLip, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall (z : Ambient d) (2 * latticeRadius R k))
    ⟨(z : Ambient d), mem_closedBall_self (by positivity)⟩ isClosed_closedBall.isComplete
    (convex_closedBall (z : Ambient d) (2 * latticeRadius R k))
  have hcover (i : supportImmediateChildren μ R hR k z) (y : Ambient d)
      (hy : y ∈ i.val.cell) (hyRange : y ∈ Set.range (f i)) : y ∈ Set.range (p ∘ g) := by
    have htop := i.val.cell_subset_top hy
    have hball : y ∈ closedBall (z : Ambient d) (2 * latticeRadius R k) :=
      (supportLatticeCell_bounds μ R hR k z).2 htop.1
    have hyF : y ∈ Set.range (F i) := hFRange i ▸ hyRange
    obtain ⟨u, hu⟩ := hgCover (mem_iUnion.mpr ⟨i, hyF⟩)
    exact ⟨u, by change p (g u) = y; rw [hu, hpFix y hball]⟩
  have hsub : cleanSupportCell μ R hR k z \ Set.range (p ∘ g) ⊆
      ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell \ Set.range (f i) := by
    intro y hy
    have hpart : y ∈ ⋃ i : supportImmediateChildren μ R hR k z, i.val.cell :=
      cleanSupportCell_eq_immediate_children μ R hR k z ▸ hy.1
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpart
    exact mem_iUnion.mpr ⟨i, hi, fun h => hy.2 (hcover i y hi h)⟩
  refine ⟨p ∘ g, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hpLip.comp hgLip
  · rintro y ⟨u, rfl⟩
    exact hpRange (g u)
  · intro i y hy
    exact hcover i y hy.1 hy.2
  · have h : μ (cleanSupportCell μ R hR k z \ Set.range (p ∘ g)) ≤
        ∑' i : supportImmediateChildren μ R hR k z, μ (i.val.cell \ Set.range (f i)) :=
      (measure_mono hsub).trans (measure_iUnion_le _)
    simpa only [tsum_fintype] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_RestartChartStepBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lipschitz constants for restart-chart iteration

The step constant simultaneously bounds the inherited chart constant, one, and
the two constants needed for immediate-child and active-cell assembly. Iterating
this monotone envelope gives nondecreasing bounds for every finite restart depth.
-/

namespace RieszRectifiability

noncomputable section

open scoped NNReal

theorem restartChartStepConstant_bounds (d N : ℕ) (P M : ℝ≥0) :
    M ≤ restartChartStepConstant d N P M ∧
    1 ≤ restartChartStepConstant d N P M ∧
    immediateChildAssemblyConstant d M ≤ restartChartStepConstant d N P M ∧
    activeCellFinitePieceAssemblyConstant d N P M ≤ restartChartStepConstant d N P M := by
  unfold restartChartStepConstant
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_, ?_⟩
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem restartChartStepConstant_mono (d N : ℕ) (P : ℝ≥0) :
    Monotone (restartChartStepConstant d N P) := by
  intro M L hML
  unfold restartChartStepConstant immediateChildAssemblyConstant finiteBallChartUnionConstant
    activeCellFinitePieceAssemblyConstant separatedPatchGluingConstant
  gcongr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_GoodRegionRestartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Restart chart assembly in a good region

Immediate-child charts first assemble at selected stopping cells, then join the
finite pieces of the active region. The resulting ball chart covers both families;
its uncovered mass is bounded by the omitted surface area and child deficits.
The Lipschitz constant is controlled by two restart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem goodRegionRestartAssemblyConstant_le_two_steps (d N : ℕ) (P M : ℝ≥0) :
    goodRegionRestartAssemblyConstant d N P M ≤
      restartChartStepConstant d N P (restartChartStepConstant d N P M) := by
  have hgood := (restartChartStepConstant_bounds d N P (immediateChildAssemblyConstant d M)).2.2.2
  have hbad := (restartChartStepConstant_bounds d N P M).2.2.1
  exact hgood.trans (restartChartStepConstant_mono d N P hbad)

theorem exists_good_region_restart_chart {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (N : ℕ) (D : Fin N → Set (Ambient n))
    (hD : ∀ j, D j ⊆ ball (0 : Ambient n) q.radius)
    (piece : Fin N → Ambient n → Ambient d) (P : ℝ≥0)
    (hpieceLip : ∀ j, LipschitzOnWith P (piece j) (D j))
    (hpieceImage : ∀ j, piece j '' D j ⊆ closedBall q.center (3 * q.radius))
    (E : Set (Ambient d)) (hE : E = ⋃ j : Fin N, piece j '' D j)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ∀ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
        ball (0 : Ambient n) j.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i j, LipschitzWith M (child i j))
    (himage : ∀ i j, Set.range (child i j) ⊆ closedBall j.val.center (2 * j.val.radius)) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (goodRegionRestartAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      (cellRegionLimit μ R hR k z Good ∩ q.cell ∩ E ⊆ Set.range g) ∧
      (∀ i j, j.val.cell ∩ Set.range (child i j) ⊆ Set.range g) ∧
      μ (q.cell \ Set.range g) ≤
        (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
          (μH[(n : ℝ)] : Measure (Ambient d))
            ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) +
        ∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
          ∑ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
            μ (j.val.cell \ Set.range (child i j)) := by
  classical
  let F := activeCellSelectedStopSet μ R hR k z Good q E
  have hcharts (i : F) : ∃ h : ball (0 : Ambient n) i.val.radius → Ambient d,
      LipschitzWith (immediateChildAssemblyConstant d M) h ∧
      Set.range h ⊆ closedBall i.val.center (2 * i.val.radius) ∧
      (∀ j, j.val.cell ∩ Set.range (child i j) ⊆ Set.range h) ∧
      μ (i.val.cell \ Set.range h) ≤
        ∑ j : supportImmediateChildren μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩,
          μ (j.val.cell \ Set.range (child i j)) :=
    exists_immediate_child_chart_assembly hn μ R hR (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ (child i) M (hLip i) (himage i)
  choose stopped hstoppedLip hstoppedRange hstoppedCover hstoppedDeficit using hcharts
  obtain ⟨g, hgLip, hgRange, hparent, hstopCover, hdeficit⟩ :=
    exists_active_cell_finite_piece_deficit_assembly μ G hG hg R hR k z Good S hS
      ε hε hεfine hsmall hfit f hmodel hn q hq N D hD piece P hpieceLip hpieceImage E hE
      stopped (immediateChildAssemblyConstant d M) hstoppedLip hstoppedRange
  refine ⟨g, hgLip, hgRange, hparent, ?_, ?_⟩
  · intro i j y hy
    exact hstopCover i ⟨j.val.cell_subset_top hy.1, hstoppedCover i j hy⟩
  · exact hdeficit.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum hstoppedDeficit))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

theorem SupportCellDescendant.compose_root (q : SupportCellDescendant μ R hR k z) :
    q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) = q := by
  refine (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)).eq_of_common_point_same_depth
    q rfl q.center ?_ q.center_mem_cell
  rw [SupportCellDescendant.compose_cell]
  exact q.center_mem_cell

theorem relative_restart_root_active
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) :
    activeRegionCell (relativeRestartGood Bad q)
      (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) := by
  intro i hi _
  have hi0 : i.depth = 0 := Nat.eq_zero_of_le_zero hi
  rw [i.eq_root_of_zero_depth hi0]
  change ¬ Bad (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩))
  rwa [SupportCellDescendant.compose_root]

theorem selected_restart_remainder_of_bad_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : Bad q) (E : Set (Ambient d)) :
    selectedRestartRemainder Bad q E = ∅ := by
  let root := supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
  have hroot : root ∈ relativeSelectedRestartStops Bad q E := by
    refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
    · change ¬ ¬ Bad (q.compose root)
      rw [SupportCellDescendant.compose_root]
      exact not_not.mpr hq
    · intro j hj _
      exact False.elim (Nat.not_lt_zero j.depth hj)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨root, hroot⟩, hx.1⟩))

theorem selected_restart_stops_of_good_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d)) :
    relativeSelectedRestartStops Bad q E =
      activeCellSelectedStopSet μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
        (relativeRestartGood Bad q)
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) E := by
  ext i
  constructor
  · intro hi
    have hi0 : i.depth ≠ 0 := by
      intro hh
      have hgood := activeRegionCell_good (relativeRestartGood Bad q) _
        (relative_restart_root_active Bad q hq)
      exact hi.1.1 (i.eq_root_of_zero_depth hh ▸ hgood)
    exact ⟨⟨hi.1, Nat.pos_of_ne_zero hi0, i.cell_subset_top⟩,
      hi.2.resolve_left hi0⟩
  · intro hi
    exact ⟨hi.1.1, Or.inr hi.2⟩

theorem selected_restart_parent_eq
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    selectedRestartParent Bad q E =
      cellRegionLimit μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) ∩
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩).cell ∩ E := by
  ext x
  exact ⟨fun hx => ⟨⟨hx.1, hx.1.1⟩, hx.2⟩, fun hx => ⟨hx.1.1, hx.2⟩⟩

theorem selected_restart_remainder_of_good_root
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d)) :
    selectedRestartRemainder Bad q E = q.cell \
      activeCellRepresentedSet μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
        (relativeRestartGood Bad q)
        (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) E := by
  unfold selectedRestartRemainder
  rw [selected_restart_parent_eq, selected_restart_stops_of_good_root Bad q hq E]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Surface data for selected restart assembly

Finite Lipschitz surface pieces and an active-region limit model supply the parent chart
at a good restart. At a bad restart the selected stop is the root, so immediate-child
assembly suffices. Both cases share a bound given by two restart-chart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

theorem exists_chart_at_equal_radius (r s : ℝ) (hrs : r = s)
    (f : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : ball (0 : Ambient n) s → Ambient d,
      LipschitzWith M g ∧ Set.range g = Set.range f := by
  subst s
  exact ⟨f, hf, rfl⟩

theorem relative_selected_stop_eq_root_of_bad
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : Bad q) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E) :
    i.val = supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ := by
  apply i.val.eq_root_of_zero_depth
  by_contra hi
  have hgood := i.property.1.2
    (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)
    (Nat.pos_of_ne_zero hi) i.val.cell_subset_top
  change ¬ Bad (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)) at hgood
  exact hgood (q.compose_root ▸ hq)

/-- Assemble child charts and the parent surface with a uniform two-step Lipschitz bound. -/
theorem has_selected_restart_assembly_of_surface_data (hn : 0 < n)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
    (ε : ℝ) (hε : 0 < ε) (hεfine : ε ≤ 1 / 281474976710656)
    (hsmall : activeProjectionError d ε ≤ 1 / 128) (N : ℕ) (P : ℝ≥0)
    (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
      ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P) :
    HasSelectedRestartAssembly n Bad E
      (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) := by
  classical
  intro q M child hchildLip hchildImage
  have hlocal (i : relativeSelectedRestartStops Bad q.val (E q))
      (j : supportImmediateChildren μ R hR (k + q.val.depth + i.val.depth)
        ⟨i.val.center, i.val.mem_net⟩) :
      ∃ f : ball (0 : Ambient n) j.val.radius → Ambient d,
        LipschitzWith M f ∧ Set.range f = Set.range (child (selectedRestartChildNode Bad q.val (E q) i j)) := by
    apply exists_chart_at_equal_radius _ _ _ _ M
      (hchildLip (selectedRestartChildNode Bad q.val (E q) i j))
    change (q.val.compose (i.val.compose j.val)).radius = j.val.radius
    simp only [SupportCellDescendant.compose_radius]
  choose localChart hlocalLip hlocalRange using hlocal
  have hlocalImage (i : relativeSelectedRestartStops Bad q.val (E q))
      (j : supportImmediateChildren μ R hR (k + q.val.depth + i.val.depth)
        ⟨i.val.center, i.val.mem_net⟩) :
      Set.range (localChart i j) ⊆ closedBall j.val.center (2 * j.val.radius) := by
    rw [hlocalRange i j]
    have h := hchildImage (selectedRestartChildNode Bad q.val (E q) i j)
    change Set.range _ ⊆ closedBall j.val.center (2 * (q.val.compose (i.val.compose j.val)).radius) at h
    simpa only [SupportCellDescendant.compose_radius] using! h
  have hassembled : ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (restartChartStepConstant d N P (restartChartStepConstant d N P M)) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      selectedRestartParent Bad q.val (E q) ⊆ Set.range g ∧
      ∀ i j, j.val.cell ∩ Set.range (localChart i j) ⊆ Set.range g := by
    by_cases hbad : Bad q.val
    · let root := supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
      have hroot : root ∈ relativeSelectedRestartStops Bad q.val (E q) := by
        refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
        · change ¬ ¬ Bad (q.val.compose root)
          rw [SupportCellDescendant.compose_root]
          exact not_not.mpr hbad
        · intro i hi _
          exact False.elim (Nat.not_lt_zero i.depth hi)
      let i0 : relativeSelectedRestartStops Bad q.val (E q) := ⟨root, hroot⟩
      obtain ⟨g, hgLip, hgRange, hgCover, _⟩ := exists_immediate_child_chart_assembly hn
        μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
        (localChart i0) M (hlocalLip i0) (hlocalImage i0)
      have hconstant := (restartChartStepConstant_bounds d N P M).2.2.1.trans
        (restartChartStepConstant_bounds d N P (restartChartStepConstant d N P M)).1
      refine ⟨g, hgLip.weaken hconstant, hgRange, ?_, ?_⟩
      · intro x hx
        have hr := hx.1.2 root hx.1.1
        change ¬ Bad (q.val.compose root) at hr
        rw [SupportCellDescendant.compose_root] at hr
        exact False.elim (hr hbad)
      · intro i
        have hi : i = i0 := Subtype.ext (relative_selected_stop_eq_root_of_bad Bad q.val hbad (E q) i)
        subst i
        exact hgCover
    · let a := data q hbad
      let root := supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
      have heq := selected_restart_stops_of_good_root Bad q.val hbad (E q)
      let lift := fun i : activeCellSelectedStopSet μ R hR (k + q.val.depth)
        ⟨q.val.center, q.val.mem_net⟩ (relativeRestartGood Bad q.val) root (E q) =>
          (⟨i.val, heq.symm ▸ i.property⟩ : relativeSelectedRestartStops Bad q.val (E q))
      obtain ⟨g, hgLip, hgRange, hgParent, hgCover, _⟩ := exists_good_region_restart_chart hn
        μ G hG hg R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
        (relativeRestartGood Bad q.val) a.planes a.isPlane ε hε hεfine hsmall a.fits
        a.model a.isModel root (relative_restart_root_active Bad q.val hbad)
        N a.domains a.domains_bounded a.pieces P a.pieces_lipschitz a.pieces_bounded (E q) a.pieces_cover
        (fun i => localChart (lift i)) M (fun i => hlocalLip (lift i)) (fun i => hlocalImage (lift i))
      refine ⟨g, hgLip.weaken (goodRegionRestartAssemblyConstant_le_two_steps d N P M), hgRange, ?_, ?_⟩
      · rw [selected_restart_parent_eq]
        exact hgParent
      · intro i j
        exact hgCover ⟨i.val, heq ▸ i.property⟩ j
  obtain ⟨g, hgLip, hgRange, hgParent, hgCover⟩ := hassembled
  refine ⟨g, hgLip, hgRange, hgParent, ?_⟩
  intro w x hx
  obtain ⟨i, j, hw⟩ := w.property
  have heq : selectedRestartChildNode Bad q.val (E q) i j = w :=
    Subtype.ext (Subtype.ext hw.symm)
  have hxcell : x ∈ j.val.cell := by
    have h := hx.1
    rw [hw, SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell] at h
    exact h
  have hxrange : x ∈ Set.range (localChart i j) := by
    rw [hlocalRange i j, heq]
    exact hx.2
  exact hgCover i j ⟨hxcell, hxrange⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_SelectedRestartAreaLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Surface-area loss in selected restart charts

At a good restart root, the mass left outside a selected surface piece is bounded
by its discarded Hausdorff area. Applying this estimate at each selected root
turns an area-loss hypothesis into the uniform deficit required by the recursive
chart assembly; bad roots contribute an empty remainder.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- A good restart root converts discarded model area into a bound for the remaining mass. -/
theorem selected_restart_remainder_mass_le_surface_loss {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : ¬ Bad q) (E : Set (Ambient d))
    (ε : ℝ) (hε : 0 < ε) (hεfine : ε ≤ 1 / 281474976710656)
    (hsmall : activeProjectionError d ε ≤ 1 / 128) (N : ℕ) (P : ℝ≥0)
    (a : SelectedRestartSurfaceData n Bad q E ε N P) :
    μ (selectedRestartRemainder Bad q E) ≤
      (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
        (μH[(n : ℝ)] : Measure (Ambient d))
          ((Set.range a.model ∩ closedBall q.center (3 * q.radius)) \ E) := by
  rw [selected_restart_remainder_of_good_root Bad q hq E]
  exact active_cell_remainder_mass_le_discarded_area μ G hG hg R hR (k + q.depth)
    ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) a.planes a.isPlane
    ε hε hεfine hsmall a.fits a.model a.isModel
    (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)
    (relative_restart_root_active Bad q hq) E

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanCellChartTargetBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From clean-cell deficits to ball charts

A relative chart deficit `ζ` leaves at least the fraction `1 - ζ` of a finite
cell's mass in the chart image. For a support ball of radius `r`, a clean cell at
scale `r / 4` lies inside that ball and contains a core of radius `r / 32`.
The lower AD bound supplies the retained mass fraction `(1 - ζ) / (C * 32 ^ n)`;
rescaling the chart domain to radius `r` multiplies its Lipschitz bound by `1 / 4`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem retained_mass_of_chart_deficit {d : ℕ} (μ : Measure (Ambient d))
    (Q T : Set (Ambient d)) (hfinite : μ Q ≠ ⊤) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (hdeficit : μ (Q \ T) ≤ ENNReal.ofReal ζ * μ Q) :
    ENNReal.ofReal (1 - ζ) * μ Q ≤ μ (Q ∩ T) := by
  have hsub : Q ⊆ (Q ∩ T) ∪ (Q \ T) := by
    intro x hx
    by_cases ht : x ∈ T
    · exact Or.inl ⟨hx, ht⟩
    · exact Or.inr ⟨hx, ht⟩
  have hmass : μ Q ≤ μ (Q ∩ T) + μ (Q \ T) + 0 := by
    simpa only [add_zero] using! (measure_mono (μ := μ) hsub).trans (measure_union_le _ _)
  have h := mass_fraction_of_two_deficits _ _ _ 0 hfinite ζ 0 hζ le_rfl hmass hdeficit (by simp)
  simpa only [sub_zero] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Uniformity_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_total_mass_of_bounded_support {d n : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (hpos : μ.support.Nontrivial) (hfin : ediam μ.support ≠ ⊤) :
    μ Set.univ ≤ ENNReal.ofReal ((9 : ℝ) ^ d * C * (diam μ.support / 2) ^ n) := by
  classical
  let D := diam μ.support
  have hb : Bornology.IsBounded μ.support := isBounded_iff_ediam_ne_top.mpr hfin
  have hD : 0 < D := diam_pos hpos hb
  have hc : IsCompact μ.support := isCompact_iff_isClosed_bounded.mpr ⟨μ.isClosed_support, hb⟩
  obtain ⟨N, _, hNE, hsep, hcover⟩ := exists_separated_cover_extension μ.support ∅
    (D / 4) (by positivity) (empty_subset _) (by simp)
  have hNfin : N.Finite := by
    have h := separated_set_finite_inter_compact N μ.support (D / 4)
      (by positivity) hsep hc
    simpa only [inter_eq_left.mpr hNE] using! h
  let s := hNfin.toFinset
  obtain ⟨a, ha⟩ := hpos.nonempty
  let t := s.image (fun x => x - a)
  have hcard : t.card = s.card := Finset.card_image_of_injective _ (fun x y h => sub_left_inj.mp h)
  have hball : ∀ x ∈ t, ‖x‖ ≤ D := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hb (hNE (hNfin.mem_toFinset.mp hy)) ha
  have hsep' : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 2 * (D / 8) ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    rw [dist_sub_right]
    have hn : z ≠ w := by rintro rfl; exact hxy rfl
    have hh := hsep (hNfin.mem_toFinset.mp hz) (hNfin.mem_toFinset.mp hw) hn
    linarith
  have hs : (s.card : ℝ) ≤ (9 : ℝ) ^ d := by
    have hp := euclidean_separated_card_le t D (D / 8) hD.le (by positivity) hball hsep'
    have heq : (D + D / 8) / (D / 8) = 9 := by field_simp <;> ring
    simpa only [hcard, heq] using! hp
  have hadmiss : AdmissibleRadius μ (D / 2) := by
    refine ⟨by positivity, ?_⟩
    calc
      ENNReal.ofReal (D / 2) ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ediam μ.support := ENNReal.ofReal_toReal hfin
  have hcov : μ.support ⊆ ⋃ x ∈ s, ball x (D / 2) := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := hcover y hy
    exact mem_iUnion₂.mpr ⟨x, hNfin.mem_toFinset.mpr hx, lt_trans hyx (by linarith)⟩
  have heq : μ μ.support = μ Set.univ := by
    simpa only [univ_inter] using! (measure_inter_conull (μ := μ) (s := Set.univ) μ.measure_compl_support)
  calc
    μ Set.univ = μ μ.support := heq.symm
    _ ≤ μ (⋃ x ∈ s, ball x (D / 2)) := measure_mono hcov
    _ ≤ ∑ x ∈ s, μ (ball x (D / 2)) := measure_biUnion_finset_le s _
    _ ≤ ∑ _x ∈ s, ENNReal.ofReal (C * (D / 2) ^ n) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (hAD.2 x (hNE (hNfin.mem_toFinset.mp hx)) _ hadmiss).2
    _ = ENNReal.ofReal ((s.card : ℝ) * (C * (D / 2) ^ n)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity : 0 ≤ (s.card : ℝ)), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (9 ^ d * C * (D / 2) ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      have hC : 0 ≤ C := zero_le_one.trans hAD.1
      nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg hC (pow_nonneg (by positivity : 0 ≤ D / 2) n))]

theorem quantitative_global_growth {d n : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (hpos : μ.support.Nontrivial) :
    GlobalUpperGrowth n ((9 : ℝ) ^ d * C) μ := by
  have hC : 0 ≤ C := zero_le_one.trans hAD.1
  have hG : 0 ≤ (9 : ℝ) ^ d * C := mul_nonneg (by positivity) hC
  refine ⟨hG, ?_⟩
  intro a r hr
  by_cases hz : μ (ball a r) = 0
  · rw [hz]
    exact zero_le
  obtain ⟨x, hxa, hx⟩ := μ.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hz)
  by_cases hsmall : ENNReal.ofReal (2 * r) ≤ ediam μ.support
  · have hsub : ball a r ⊆ ball x (2 * r) := by
      intro y hy
      change dist y x < 2 * r
      calc
        dist y x ≤ dist y a + dist a x := dist_triangle _ _ _
        _ < r + r := add_lt_add hy (by simpa only [mem_ball, dist_comm] using! hxa)
        _ = 2 * r := by ring
    have hpow : (2 : ℝ) ^ n ≤ 9 ^ d :=
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ 9) n).trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 9) hnd)
    calc
      μ (ball a r) ≤ μ (ball x (2 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := (hAD.2 x hx _ ⟨by positivity, hsmall⟩).2
      _ ≤ ENNReal.ofReal (9 ^ d * C * r ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_pow]
        nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hC (pow_nonneg hr.le n))]
  · have hdiam : ediam μ.support < ENNReal.ofReal (2 * r) := lt_of_not_ge hsmall
    have hfin : ediam μ.support ≠ ⊤ := ne_top_of_lt hdiam
    have hdr : diam μ.support < 2 * r := by
      have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hdiam
      simpa only [diam, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)] using! h
    calc
      μ (ball a r) ≤ μ Set.univ := measure_mono (subset_univ _)
      _ ≤ ENNReal.ofReal (9 ^ d * C * (diam μ.support / 2) ^ n) :=
        quantitative_total_mass_of_bounded_support μ C hAD hpos hfin
      _ ≤ ENNReal.ofReal (9 ^ d * C * r ^ n) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg diam_nonneg (by norm_num)) (by linarith) n) hG

end
end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Uniformity_RestartBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform budgets for bad cells and restarts

The class-uniform bad-beta packing constant controls multiplicity tails and the
total mass of restart roots. A relative loss tolerance and a finite bad-depth
budget are chosen before the measure, using only the fixed geometric and Riesz
bounds. Splitting the desired deficit into two halves pays separately for the
discarded high-multiplicity set and the remainders of selected restart regions.
These budgets feed the recursive chart assembly without changing its image or
Lipschitz conclusions.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_recursive_chart_from_surface_pieces {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (D : ℝ≥0) (hC : 1 ≤ C) (hG : 0 < G) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧ ∀ (N : ℕ) (P : ℝ≥0), ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant (p + 1) C μ →
      GlobalUpperGrowth (p + 1) G μ → RieszL2BoundedWithConstant (p + 1) D μ →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      let Bad := fun i : SupportCellDescendant μ R hR k z =>
        ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
      ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
        (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
          ¬ Bad q.val → SelectedRestartSurfaceData (p + 1) Bad q.val (E q) ε N P),
        (∀ q hq, (ENNReal.ofReal G + activeRegionStopMassAreaConstant (p + 1) G) *
          (μH[((p + 1 : ℕ) : ℝ)] : Measure (Ambient d))
            ((Set.range (data q hq).model ∩ closedBall q.val.center (3 * q.val.radius)) \ E q) ≤
              ENNReal.ofReal δ * μ q.val.cell) →
        ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
          LipschitzWith (badBudgetChartConstant
            (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b) g ∧
          Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
          μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
            ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, b, hb, hcharts⟩ := quantitative_selected_restart_uniform_deficit
    hnd C G D hC hG H ε hH hε ζ hζ
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro N P μ _hreg hAD hg hRiesz R hR k z hcore
  have hcharts := hcharts μ hAD hg hRiesz
  dsimp only
  intro E data hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  have hassemble := has_selected_restart_assembly_of_surface_data (Nat.succ_pos p)
    G hG hg Bad E ε hε hεfine hsmall N P data
  apply hcharts R hR k z hcore E _ hassemble
  intro q
  by_cases hq : Bad q.val
  · rw [selected_restart_remainder_of_bad_root Bad q.val hq (E q), measure_empty]
    exact zero_le
  · exact (selected_restart_remainder_mass_le_surface_loss μ G hG hg R hR k z
      Bad q.val hq (E q) ε hε hεfine hsmall N P (data q hq)).trans (hloss q hq)

end
end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Uniformity_Rectifiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative ball images with constants chosen before the measure

Clean-cell charts with relative deficit `ζ` yield genuine ball images with mass
fraction `(1 - ζ) / (C * 32 ^ n)` and the rescaled Lipschitz bound. The final
assembly chooses the surface-piece and restart budgets from the fixed dimension,
AD constant, and common Riesz bound before introducing the measure. Degenerate
supports are handled directly through the admissible-radius condition.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

theorem quantitative_ball_images_of_clean_cell_deficits {n d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hAD : ADRegularWithConstant n C μ)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (ζ : ℝ) (hζ : 0 ≤ ζ) (hζone : ζ < 1) (M : ℝ≥0)
    (hcharts : ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∃ f : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith M f ∧ μ (cleanSupportCell μ R hR k z \ Set.range f) ≤
          ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z)) : BallImageConclusion n μ ((1 - ζ) / (C * 32 ^ n)) (M * (1 / 4)) := by
  obtain ⟨hC, hballs⟩ := hAD
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hkeep : 0 < 1 - ζ := sub_pos.mpr hζone
  let θ := (1 - ζ) / (C * 32 ^ n)
  have hθ : 0 < θ := div_pos hkeep (mul_pos hCpos (by positivity))
  change BallImageConclusion n μ θ (M * (1 / 4))
  intro x hx r hr
  have hR : 0 < r / 4 := div_pos hr.1 (by norm_num)
  obtain ⟨zc, hzc, hnear⟩ := (supportLatticeNets μ (r / 4) hR 0).covers x hx
  let z : (supportLatticeNets μ (r / 4) hR 0).points := ⟨zc, hzc⟩
  have hrad : latticeRadius (r / 4) 0 = r / 4 := by simp only [latticeRadius, pow_zero, mul_one]
  have hcore : AdmissibleRadius μ (latticeRadius (r / 4) 0 / 8) := by
    refine ⟨div_pos (latticeRadius_pos _ hR 0) (by norm_num), ?_⟩
    apply (ENNReal.ofReal_le_ofReal ?_).trans hr.2
    rw [hrad]
    linarith [hr.1]
  obtain ⟨f, hf, hdeficit⟩ := hcharts (r / 4) hR 0 z hcore
  have hmass := cleanSupportCell_measure_bounds μ C G hCpos hG hg
    (fun y hy s hs => (hballs y hy s hs).1) (r / 4) hR 0 hcore z
  have hfinite : μ (cleanSupportCell μ (r / 4) hR 0 z) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass.2
  have hret := retained_mass_of_chart_deficit μ _ (Set.range f) hfinite ζ hζ hdeficit
  have hcoef : θ * r ^ n = (1 - ζ) * ((latticeRadius (r / 4) 0 / 8) ^ n / C) := by
    rw [hrad]
    change (1 - ζ) / (C * 32 ^ n) * r ^ n = (1 - ζ) * ((r / 4 / 8) ^ n / C)
    rw [div_div, show (4 : ℝ) * 8 = 32 by norm_num, div_pow]
    ring
  have hretained : ENNReal.ofReal (θ * r ^ n) ≤
      μ (cleanSupportCell μ (r / 4) hR 0 z ∩ Set.range f) := by
    rw [hcoef, ENNReal.ofReal_mul hkeep.le]
    exact (mul_le_mul_right hmass.1 (ENNReal.ofReal (1 - ζ))).trans hret
  have hcell : cleanSupportCell μ (r / 4) hR 0 z ⊆ ball x r := by
    intro y hy
    have hdist := (supportLatticeCell_bounds μ (r / 4) hR 0 z).2 hy.1
    change dist y zc ≤ 2 * latticeRadius (r / 4) 0 at hdist
    rw [hrad] at hdist hnear
    have htri := dist_triangle y zc x
    rw [dist_comm zc x] at htri
    change dist y x < r
    linarith [hr.1]
  obtain ⟨F, hF, hFRange⟩ := exists_rescaled_ball_chart (latticeRadius (r / 4) 0)
    (0 : Ambient n) (1 / 4) (by norm_num) f M hf
  have hdomain : latticeRadius (r / 4) 0 / ((1 / 4 : ℝ≥0) : ℝ) = r := by
    rw [hrad]
    norm_num
    ring
  rw [hdomain] at hF hFRange
  let g := (ball (0 : Ambient n) r).domRestrict F
  have hcover : Set.range f ⊆ Set.range g := by
    intro y hy
    obtain ⟨u, hu, hFu⟩ := hFRange.symm ▸ hy
    exact ⟨⟨u, hu⟩, hFu⟩
  refine ⟨g, hF.to_restrict, hretained.trans (measure_mono ?_)⟩
  exact fun y hy => ⟨hcell hy.1, hcover hy.2⟩

theorem quantitative_higher_codimension_riesz_rectifiability_oai : QuantitativeFullStatement := by
  intro d n _hd hn hnd C hC D
  cases n with
  | zero => omega
  | succ p =>
    have hnd' : p + 1 ≤ d := by omega
    let G : ℝ := 9 ^ d * C
    have hG : 0 < G := mul_pos (by positivity) (zero_lt_one.trans_le hC)
    obtain ⟨ε, hε, hεfine, hsmall, hpieces⟩ :=
      quantitative_uniform_restart_surface_pieces (Nat.succ_pos p) hnd' C G hC hG
    obtain ⟨δ, hδ, b, _hb, hcharts⟩ := quantitative_recursive_chart_from_surface_pieces
      hnd' C G D hC hG 1024 ε (by norm_num) hε hεfine hsmall (1 / 2) (by norm_num)
    obtain ⟨N, P, hdata⟩ := hpieces δ hδ
    let M := badBudgetChartConstant
      (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) b
    refine ⟨(1 - (1 / 2 : ℝ)) / (C * 32 ^ (p + 1)),
      div_pos (by norm_num) (mul_pos (zero_lt_one.trans_le hC) (by positivity)),
      M * (1 / 4), ?_⟩
    intro μ hreg hAD hRiesz
    let : μ.Regular := hreg
    by_cases hsupport : μ.support.Nontrivial
    · have hg : GlobalUpperGrowth (p + 1) G μ := quantitative_global_growth hnd' μ C hAD hsupport
      apply quantitative_ball_images_of_clean_cell_deficits μ C hAD G hG hg
        (1 / 2) (by norm_num) (by norm_num) M
      intro R hR k z hcore
      obtain ⟨E, data, hloss⟩ := hdata μ hAD hg R hR k z hcore
      obtain ⟨g, hglip, _, hdeficit⟩ := hcharts N P μ hAD hg hRiesz R hR k z hcore E data hloss
      exact ⟨g, hglip, hdeficit⟩
    · intro x _hx r hr
      have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr (Set.not_nontrivial_iff.mp hsupport)
      have hz : ENNReal.ofReal r = 0 := le_antisymm (hdiam ▸ hr.2) zero_le
      exact ((ENNReal.ofReal_pos.mpr hr.1).ne' hz).elim

end
end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability_oai := @OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability_oai
