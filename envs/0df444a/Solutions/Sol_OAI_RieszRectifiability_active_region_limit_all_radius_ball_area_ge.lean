-- Prove2me | solution 1 for OAI.RieszRectifiability.active_region_limit_all_radius_ball_area_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:36.813807+00:00
-- url     : https://prove2.me/submissions/e2e45a34-a59a-4cbf-a716-9bd6b9a97db3

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_activeRegionSurface_charts
import Theorems.Thm_OAI_RieszRectifiability_active_region_positive_stopping_scale_local_ball_area_ge

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionConeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal graphs from projection cones

A cone estimate makes tangential projection injective on a set. Its inverse supplies
the normal component of a Lipschitz graph over the projected set.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem projection_cone_injOn {d : ℕ} (P : Submodule ℝ (Ambient d))
    (A : Set (Ambient d)) (L : ℝ)
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        L * dist (P.starProjection x) (P.starProjection y)) :
    Set.InjOn P.starProjection A := by
  intro x hx y hy hxy
  have hp : P.starProjection (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have h := hcone x hx y hy
  rw [hxy, dist_self, mul_zero] at h
  have hq : (Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y) = 0 :=
    norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hd := P.starProjection_add_starProjection_orthogonal (x - y)
  rw [hp, hq, zero_add] at hd
  exact sub_eq_zero.mp hd.symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_CoveredProjectionCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Charts over covered projections

A cone bound makes orthogonal projection injective on the given set. Over any
covered projection domain, its inverse is a Lipschitz chart whose normal component
has the prescribed Lipschitz bound and whose range is exactly the corresponding slice.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_chart_on_covered_projection {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (A : Set (Ambient d)) (L : ℝ≥0)
    (D : Set P) (hcover : D ⊆ P.orthogonalProjectionOnto '' A)
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y)) :
    ∃ h : D → Ambient d,
      LipschitzWith (1 + L) h ∧
      LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ A ∧ P.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = A ∩ P.orthogonalProjectionOnto ⁻¹' D := by
  classical
  have hex (u : D) : ∃ x ∈ A, P.orthogonalProjectionOnto x = u.val := hcover u.property
  choose h hm hc using hex
  have hstar (u : D) : P.starProjection (h u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hc u)
  have hnormal (u v : D) :
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u - h v)‖ ≤ (L : ℝ) * dist u v := by
    have hn := hcone (h u) (hm u) (h v) (hm v)
    rw [hstar u, hstar v] at hn
    exact hn
  have hLip : LipschitzWith (1 + L) h := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hp : ‖P.starProjection (h u - h v)‖ = dist u v := by
      rw [map_sub, hstar u, hstar v]
      rfl
    have htri := norm_add_le (P.starProjection (h u - h v))
      ((Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u - h v))
    rw [P.starProjection_add_starProjection_orthogonal, hp] at htri
    rw [NNReal.coe_add, NNReal.coe_one, dist_eq_norm]
    have hn := hnormal u v
    nlinarith
  have hnormalLip : LipschitzWith L
      (fun u : D => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, ← map_sub]
    exact hnormal u v
  refine ⟨h, hLip, hnormalLip, fun u => ⟨hm u, hc u⟩, ?_⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨hm u, ?_⟩
    change P.orthogonalProjectionOnto (h u) ∈ D
    rw [hc u]
    exact u.property
  · rintro ⟨hx, hD⟩
    let u : D := ⟨P.orthogonalProjectionOnto x, hD⟩
    refine ⟨u, ?_⟩
    apply projection_cone_injOn P A (L : ℝ) hcone (hm u) hx
    exact congrArg (fun v : P => (v : Ambient d)) (hc u)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_AnnularLatticeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem annularLatticeDepth_radius_upper (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r) :
    latticeRadius R (k + annularLatticeDepth R k r hr) ≤ r / 8 := by
  classical
  exact Nat.find_spec (exists_annular_lattice_depth R k r hr)

theorem annularLatticeDepth_minimal (R : ℝ) (k : ℕ) (r : ℝ) (hr : 0 < r)
    (t : ℕ) (ht : latticeRadius R (k + t) ≤ r / 8) :
    annularLatticeDepth R k r hr ≤ t := by
  classical
  exact Nat.find_min' (exists_annular_lattice_depth R k r hr) ht

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

theorem activeRegionCell_ancestor (Good : SupportCellDescendant μ R hR k z → Prop)
    (i q : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i)
    (hdepth : q.depth ≤ i.depth) (hsub : i.cell ⊆ q.cell) : activeRegionCell Good q := by
  intro j hj hqj
  exact hi j (hj.trans hdepth) (hsub.trans hqj)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelCover
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

theorem exists_active_level_center_of_small_stopping_scale (t : ℕ) (x : Ambient d)
    (hx : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t)) :
    ∃ i ∈ activeRegionLevel μ R hR k z Good t,
      dist x i.center < 3 * latticeRadius R (k + t) := by
  classical
  unfold cellRegionStoppingScale cappedStoppingDistance at hx
  obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt hx
  cases j with
  | none =>
    have hle := latticeRadius_antitone R hR.le (Nat.le_add_right k t)
    exact (not_lt_of_ge hle hj).elim
  | some j =>
    change dist x j.val.center + j.val.radius < latticeRadius R (k + t) at hj
    have hdepth : t ≤ j.val.depth := by
      by_contra h
      have hle := latticeRadius_antitone R hR.le (Nat.add_le_add_left (Nat.le_of_lt (Nat.lt_of_not_ge h)) k)
      change latticeRadius R (k + t) ≤ j.val.radius at hle
      have hd : 0 ≤ dist x j.val.center := dist_nonneg
      linarith
    obtain ⟨i, hi, hsub, hc⟩ := j.val.exists_ancestor_at_depth t hdepth
    have hactive := activeRegionCell_ancestor Good j.val i j.property (by omega) hsub
    have hrad : i.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hi]
    have hcenter := i.dist_center_of_mem j.val.center hc
    have htri := dist_triangle x j.val.center i.center
    have hr := j.val.radius_pos
    refine ⟨i, ⟨hi, hactive⟩, ?_⟩
    rw [hrad] at hcenter
    linarith

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionDiskCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disk coverage by active projections

Affine projection preserves tangential coordinates in the reference plane. The tangential part
of the active projection is therefore a small Lipschitz perturbation of the identity on a disk.
Its displacement bound gives coverage of a shrunken disk, and the quantitative smallness
condition yields coverage of the concentric half disk at the lattice scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped NNReal

theorem nonemptyAffineProjection_tangential {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x : Ambient d) :
    S.direction.orthogonalProjectionOnto (nonemptyAffineProjection S hS x) =
      S.direction.orthogonalProjectionOnto x := by
  let : Nonempty S := hS.to_subtype
  have h := orthogonalProjection_vsub_orthogonalProjection S x
  change S.direction.orthogonalProjectionOnto (x - (orthogonalProjection S x : Ambient d)) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_InitialAffineCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Initial affine-plane charts

Orthogonal coordinates parametrize each affine-plane disk by a 1-Lipschitz chart with
constant normal component and exact range. A distance estimate locates the chart near
an ambient center, with error given by that center's distance to the plane.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry
open scoped NNReal

theorem exists_affine_plane_disk_chart {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : S.direction) (ρ : ℝ) :
    ∃ g : closedBall a ρ → Ambient d,
      LipschitzWith 1 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹' closedBall a ρ := by
  let : Nonempty S := hS.to_subtype
  have hcover : closedBall a ρ ⊆ S.direction.orthogonalProjectionOnto '' (S : Set (Ambient d)) := by
    intro v _
    refine ⟨nonemptyAffineProjection S hS (v : Ambient d), ?_, ?_⟩
    · exact orthogonalProjection_mem (v : Ambient d)
    · rw [nonemptyAffineProjection_tangential]
      exact S.direction.orthogonalProjectionOnto_mem_subspace_eq_self v
  have hcone : ∀ x ∈ (S : Set (Ambient d)), ∀ y ∈ (S : Set (Ambient d)),
      ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        ((0 : ℝ≥0) : ℝ) * dist (S.direction.starProjection x) (S.direction.starProjection y) := by
    intro x hx y hy
    have hv : x - y ∈ S.direction := AffineSubspace.vsub_mem_direction hx hy
    rw [S.direction.starProjection_orthogonal_val,
      S.direction.starProjection_eq_self_iff.mpr hv, sub_self, norm_zero, NNReal.coe_zero, zero_mul]
  simpa only [add_zero] using!
    exists_chart_on_covered_projection S.direction (S : Set (Ambient d)) 0 (closedBall a ρ) hcover hcone

theorem affine_plane_dist_le_projection_add_offset {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x c : Ambient d) (hx : x ∈ S) :
    dist x c ≤ dist (S.direction.starProjection x) (S.direction.starProjection c) +
      infDist c (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  have hn := normal_projection_bound_by_plane_distances S x c
  rw [infDist_zero_of_mem hx, zero_add] at hn
  have ht := norm_add_le (S.direction.starProjection (x - c))
    ((S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - c))
  rw [S.direction.starProjection_add_starProjection_orthogonal] at ht
  rw [map_sub, ← dist_eq_norm x c,
    ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection c)] at ht
  exact ht.trans (add_le_add le_rfl hn)

theorem exists_located_affine_plane_disk_chart {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : Ambient d) (ρ : ℝ) :
    ∃ g : closedBall (S.direction.orthogonalProjectionOnto c) ρ → Ambient d,
      LipschitzWith 1 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val ∧
        dist (g u) c ≤ ρ + infDist c (S : Set (Ambient d))) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto c) ρ := by
  obtain ⟨g, hLip, hnLip, hcoords, hrange⟩ :=
    exists_affine_plane_disk_chart S hS (S.direction.orthogonalProjectionOnto c) ρ
  refine ⟨g, hLip, hnLip, ?_, hrange⟩
  intro u
  refine ⟨(hcoords u).1, (hcoords u).2, ?_⟩
  have hstar : S.direction.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : S.direction => (v : Ambient d)) (hcoords u).2
  have h := affine_plane_dist_le_projection_add_offset S hS (g u) c (hcoords u).1
  rw [hstar] at h
  have hu : dist (u.val : Ambient d) (S.direction.starProjection c) ≤ ρ := u.property
  exact h.trans (add_le_add hu le_rfl)

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

theorem plane_closedBall_hausdorffMeasure {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure P) (closedBall a r) =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  let b : OrthonormalBasis (Fin n) ℝ P :=
    (stdOrthonormalBasis ℝ P).reindex (finCongr hdim)
  let E : Ambient n ≃ₗᵢ[ℝ] P := b.repr.symm
  have hd : 0 ≤ (n : ℝ) := by positivity
  have hE : (μH[(n : ℝ)] : Measure P) (closedBall 0 r) =
      (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall 0 r) := by
    have h := E.isometry.hausdorffMeasure_image (Or.inl hd) (closedBall 0 r)
    have himage : E '' closedBall 0 r = closedBall 0 r := by
      have h' := E.toIsometryEquiv.image_closedBall 0 r
      change E '' closedBall 0 r = closedBall (E 0) r at h'
      simpa only [map_zero] using! h'
    rw [himage] at h
    exact h
  have htranslate : (μH[(n : ℝ)] : Measure P) (closedBall a r) =
      (μH[(n : ℝ)] : Measure P) (closedBall 0 r) := by
    have h := (IsometryEquiv.addRight a).isometry.hausdorffMeasure_image
      (Or.inl hd) (closedBall 0 r)
    rw [(IsometryEquiv.addRight a).image_closedBall] at h
    change (μH[(n : ℝ)] : Measure P) (closedBall (0 + a) r) = _ at h
    simpa only [zero_add] using! h
  have hscale := Measure.hausdorffMeasure_smul₀ (𝕜 := ℝ) hd hr.ne'
    (closedBall (0 : Ambient n) 1)
  have hnorm : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← Real.toNNReal_eq_nnnorm_of_nonneg hr.le]
    rfl
  rw [htranslate, hE]
  simpa only [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le,
    mul_one, NNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_pow, hnorm, planeUnitHausdorffMeasure] using! hscale

theorem plane_closedBall_subtype_hausdorffMeasure {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (closedBall a r)) Set.univ =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  have h := (isometry_subtype_coe (s := closedBall a r)).hausdorffMeasure_image
    (Or.inl (show 0 ≤ (n : ℝ) by positivity)) Set.univ
  have heq : (μH[(n : ℝ)] : Measure (closedBall a r)) Set.univ =
      (μH[(n : ℝ)] : Measure P) (closedBall a r) := by
    simpa only [Set.image_univ, Subtype.range_coe] using! h.symm
  rw [heq, plane_closedBall_hausdorffMeasure P hdim a r hr]

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

theorem plane_disk_antilipschitz_range_hausdorffMeasure_ge {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) (L : ℝ≥0) (hL : 0 < L)
    (g : closedBall a r → Ambient e) (hg : AntilipschitzWith L g) :
    planeDiskLowerAreaConstant n L * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g) := by
  have h := hg.le_hausdorffMeasure_image (show 0 ≤ (n : ℝ) by positivity) Set.univ
  simp only [Set.image_univ, ENNReal.rpow_natCast,
    plane_closedBall_subtype_hausdorffMeasure P hdim a r hr] at h
  have hL0 : (L : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast hL.ne')
  have hLt : (L : ℝ≥0∞) ^ n ≠ ⊤ := by finiteness
  have hdiv := (ENNReal.div_le_iff' hL0 hLt).mpr h
  convert! hdiv using 1
  all_goals try with_reducible_and_instances rfl
  unfold planeDiskLowerAreaConstant
  simp only [div_eq_mul_inv]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineExteriorDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive-dimensional affine planes contain prescribed-distance points away from a chosen center.
Affine disk coordinates convert this separation into exterior disk patches.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_affine_point_away_from_center {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hdim : 0 < Module.finrank ℝ S.direction)
    (y z : Ambient d) (hy : y ∈ S) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ q ∈ S, dist q y = ρ ∧ ρ ≤ dist q z := by
  let : Nontrivial S.direction := Module.nontrivial_of_finrank_pos hdim
  obtain ⟨v, hv⟩ := exists_norm_eq S.direction hρ
  have hv' : ‖(v : Ambient d)‖ = ρ := hv
  have hp : (v : Ambient d) + y ∈ S :=
    AffineSubspace.vadd_mem_of_mem_direction v.property hy
  have hm : -(v : Ambient d) + y ∈ S :=
    AffineSubspace.vadd_mem_of_mem_direction (S.direction.neg_mem v.property) hy
  have hpd : dist ((v : Ambient d) + y) y = ρ := by
    simpa only [dist_eq_norm, add_sub_cancel_right] using! hv'
  have hmd : dist (-(v : Ambient d) + y) y = ρ := by
    simpa only [dist_eq_norm, add_sub_cancel_right, norm_neg] using! hv'
  have hdiam : dist ((v : Ambient d) + y) (-(v : Ambient d) + y) = 2 * ρ := by
    rw [dist_eq_norm, show (v : Ambient d) + y - (-(v : Ambient d) + y) =
      (2 : ℝ) • (v : Ambient d) by module, norm_smul, hv']
    norm_num
  by_cases hfar : ρ ≤ dist ((v : Ambient d) + y) z
  · exact ⟨(v : Ambient d) + y, hp, hpd, hfar⟩
  · refine ⟨-(v : Ambient d) + y, hm, hmd, ?_⟩
    have ht := dist_triangle_right ((v : Ambient d) + y) (-(v : Ambient d) + y) z
    rw [hdiam] at ht
    linarith [lt_of_not_ge hfar]

theorem exists_affine_exterior_disk {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hdim : 0 < Module.finrank ℝ S.direction)
    (p y z : Ambient d) (hy : y ∈ S) (r : ℝ) (hr : 0 < r)
    (hnear : dist y p ≤ r / 8) :
    ∃ a : S.direction, ∃ g : closedBall a (r / 8) → Ambient d,
      LipschitzWith 1 g ∧ AntilipschitzWith 1 g ∧
      Set.range g ⊆ (S : Set (Ambient d)) ∩ closedBall p r ∧
      ∀ x ∈ Set.range g, 3 * r / 8 ≤ dist x z := by
  obtain ⟨q, hq, hqy, hqz⟩ := exists_affine_point_away_from_center S hdim y z hy
    (r / 2) (by positivity)
  obtain ⟨g, hLip, _, hcoords, _⟩ := exists_located_affine_plane_disk_chart S ⟨y, hy⟩ q (r / 8)
  have hloc (u) : dist (g u) q ≤ r / 8 := by
    simpa only [infDist_zero_of_mem hq, add_zero] using! (hcoords u).2.2
  have hsep : AntilipschitzWith 1 g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    simp only [NNReal.coe_one, one_mul]
    change dist u.val v.val ≤ dist (g u) (g v)
    rw [← (hcoords u).2.1, ← (hcoords v).2.1]
    have h := S.direction.norm_starProjection_apply_le (g u - g v)
    rw [map_sub] at h
    exact h
  refine ⟨S.direction.orthogonalProjectionOnto q, g, hLip, hsep, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨(hcoords u).1, ?_⟩
    have h1 := dist_triangle (g u) q y
    have h2 := dist_triangle (g u) y p
    change dist (g u) p ≤ r
    linarith [hloc u]
  · rintro _ ⟨u, rfl⟩
    have ht := dist_triangle q (g u) z
    rw [dist_comm q (g u)] at ht
    linarith [hloc u]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_LatticeRadiusAbove
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem exists_lattice_radius_above (R : ℝ) (k : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (htop : δ ≤ latticeRadius R k) :
    ∃ t : ℕ, δ ≤ latticeRadius R (k + t) ∧ latticeRadius R (k + t) ≤ 64 * δ := by
  let N := annularLatticeDepth R k (8 * δ) (by positivity)
  have hN : latticeRadius R (k + N) ≤ δ := by
    have hu := annularLatticeDepth_radius_upper R k (8 * δ) (by positivity)
    change latticeRadius R (k + N) ≤ (8 * δ) / 8 at hu
    linarith
  by_cases hz : N = 0
  · refine ⟨0, by simpa only [Nat.add_zero] using! htop, ?_⟩
    rw [hz, Nat.add_zero] at hN
    simp only [Nat.add_zero]
    linarith
  · have hlow : δ < latticeRadius R (k + (N - 1)) := by
      by_contra hbad
      have hm := annularLatticeDepth_minimal R k (8 * δ) (by positivity) (N - 1)
        (by linarith [le_of_not_gt hbad])
      change N ≤ N - 1 at hm
      omega
    have hscale : latticeRadius R (k + (N - 1)) = 64 * latticeRadius R (k + N) := by
      rw [show k + N = (k + (N - 1)) + 1 by omega, latticeRadius_succ]
      ring
    refine ⟨N - 1, hlow.le, ?_⟩
    rw [hscale]
    exact mul_le_mul_of_nonneg_left hN (by norm_num)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelOriginalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem SupportCellDescendant.radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) (i : SupportCellDescendant μ R hR k z) :
    (ENNReal.ofReal i.radius) ^ n ≤ ENNReal.ofReal (C * 8 ^ n) * μ i.cell := by
  have hci : AdmissibleRadius μ (i.radius / 8) := by
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using! i.core_admissible hcore
  have hl := (cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR
    (k + i.depth) hci ⟨i.center, i.mem_net⟩).1
  change ENNReal.ofReal ((i.radius / 8) ^ n / C) ≤ μ i.cell at hl
  have heq : (ENNReal.ofReal i.radius) ^ n =
      ENNReal.ofReal (C * 8 ^ n) * ENNReal.ofReal ((i.radius / 8) ^ n / C) := by
    rw [← ENNReal.ofReal_pow i.radius_pos.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * 8 ^ n)]
    congr 1
    rw [div_pow]
    field_simp
  rw [heq]
  exact mul_le_mul_right hl _

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

theorem activeRegionStopMassAreaConstant_lt_top (n : ℕ) (G : ℝ) :
    activeRegionStopMassAreaConstant n G < ⊤ := by
  exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
    (activeRegionPositiveLocalLowerAreaConstant_pos n).ne'

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveCellMassArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Active-cell mass controlled by limit-model area

An active cell splits into its limiting region and a countable family of stopping
descendants. Hausdorff domination on the limiting region and the stopping-core
mass estimate bound its original measure by nearby area of the limit model.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

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

theorem active_cell_original_mass_le_limit_area
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    μ q.cell ≤ (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall q.center (3 * q.radius)) := by
  let := supportCellDescendant_countable μ R hR k z
  let F : Set (SupportCellDescendant μ R hR k z) :=
    {i | i ∈ cellRegionStops μ R hR k z Good ∧ q.depth < i.depth ∧ i.cell ⊆ q.cell}
  let A := cellRegionLimit μ R hR k z Good ∩ q.cell
  let Ω := closedBall q.center (3 * q.radius)
  have hcover : q.cell ⊆ A ∪ ⋃ i : F, i.val.cell := by
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
  have hsub : A ⊆ Set.range f ∩ Ω := by
    intro x hx
    refine ⟨hmodel.2.2.2.2.2.1 hx.1, ?_⟩
    have h := q.dist_center_of_mem x hx.2
    change dist x q.center ≤ 3 * q.radius
    have hrq := q.radius_pos
    linarith
  have hsurv : μ A ≤ ENNReal.ofReal G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := by
    have h := global_growth_le_hausdorffMeasure μ G hG hg A
    simp only [Measure.smul_apply, smul_eq_mul] at h
    exact h.trans (mul_le_mul_right (measure_mono hsub) _)
  have hΩ : ∀ i ∈ F, closedBall i.center (i.radius / 32) ⊆ Ω := by
    intro i hi x hx
    have hnear := q.dist_center_of_mem i.center (hi.2.2 i.center_mem_cell)
    have hrad : i.radius ≤ q.radius :=
      latticeRadius_antitone R hR.le (Nat.add_le_add_left hi.2.1.le k)
    have hb : dist x i.center ≤ i.radius / 32 := hx
    have ht := dist_triangle x i.center q.center
    have hrq := q.radius_pos
    change dist x q.center ≤ 3 * q.radius
    linarith
  have hstops := active_region_stop_subfamily_mass_le_area μ G hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel F (fun _ hi => hi.1)
    (fun _ hi => lt_of_le_of_lt (Nat.zero_le q.depth) hi.2.1) Ω hΩ
  calc
    _ ≤ μ (A ∪ ⋃ i : F, i.val.cell) := measure_mono hcover
    _ ≤ μ A + μ (⋃ i : F, i.val.cell) := measure_union_le _ _
    _ ≤ μ A + ∑' i : F, μ i.val.cell := add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ ENNReal.ofReal G * (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) +
        activeRegionStopMassAreaConstant n G *
          (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ Ω) := add_le_add hsurv hstops
    _ = _ := (add_mul _ _ _).symm

theorem active_cell_radius_power_le_limit_area
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    (ENNReal.ofReal q.radius) ^ n ≤
      (ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall q.center (3 * q.radius)) := by
  have hmass := SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z q
  have harea := active_cell_original_mass_le_limit_area μ G hG hg R hR k z Good S hS
    ε hε hεfine hsmall hfit f hmodel q hq
  exact (hmass.trans (mul_le_mul_right harea _)).trans_eq (mul_assoc _ _ _).symm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionExteriorPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cellRegionStoppingScale_eq_top_of_far {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (x : Ambient d) (hfar : 3 * latticeRadius R k ≤ dist x (z : Ambient d)) :
    cellRegionStoppingScale μ R hR k z Good x = latticeRadius R k := by
  apply le_antisymm (cellRegionStoppingScale_le_top μ R hR k z Good x)
  unfold cellRegionStoppingScale cappedStoppingDistance
  apply le_ciInf
  intro i
  cases i with
  | none => exact le_rfl
  | some i =>
    have hc := (supportCellRoot μ R hR k z).dist_center_of_mem i.val.center
      (i.val.cell_subset_top i.val.center_mem_cell)
    have hc' : dist i.val.center (z : Ambient d) ≤ 2 * latticeRadius R k := by
      simpa only [supportCellRoot, SupportCellDescendant.radius, Nat.add_zero] using! hc
    have ht := dist_triangle x i.val.center (z : Ambient d)
    have hr := i.val.radius_pos
    change latticeRadius R k ≤ dist x i.val.center + i.val.radius
    linarith

theorem active_region_limit_fixes_exterior_plane {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (u : S (supportCellRoot μ R hR k z))
    (hfar : 3 * latticeRadius R k ≤ dist (u : Ambient d) (z : Ambient d)) :
    f u = u := by
  have hD := cellRegionStoppingScale_eq_top_of_far μ R hR k z Good u hfar
  have hr0 := latticeRadius_pos R hR k
  have h := active_region_limit_eq_parameter_of_large_scale μ R hR k z Good S hS f
    (fun v => hmodel.2.2.1.tendsto_at v) u 0 (by
      simp only [activeRegionParameterMap, id_eq, zero_add]
      rw [hD, latticeRadius_succ]
      linarith)
  simpa only [activeRegionParameterMap, id_eq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLargeRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem active_region_limit_large_radius_ball_area_ge {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεtiny : ε ≤ 1 / 268435456)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f)
    (r : ℝ) (hr : 0 < r) (hrlarge : 8 * latticeRadius R k ≤ r) :
    activeRegionLargeRadiusLowerAreaConstant n * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨u, hu⟩ := hp
  have hr0 := latticeRadius_pos R hR k
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hnear : dist (u : Ambient d) p ≤ r / 8 := by
    have ht : dist (u : Ambient d) p ≤ ((17039360 * ε) / 63) * latticeRadius R k := by
      simpa only [activeRegionParameterMap, id_eq, Nat.add_zero, hu] using! hmodel.2.2.2.1 0 u
    linarith
  have hdim : 0 < Module.finrank ℝ (S (supportCellRoot μ R hR k z)).direction := by
    rw [(hS _).2]
    exact hn
  obtain ⟨a, g, _, hsep, hinto, hfar⟩ := exists_affine_exterior_disk
    (S (supportCellRoot μ R hR k z)) hdim p u (z : Ambient d) u.property r hr hnear
  have hsub : Set.range g ⊆ Set.range f ∩ closedBall p r := by
    intro x hx
    have hxS := (hinto hx).1
    have hfix := active_region_limit_fixes_exterior_plane μ R hR k z Good S hS ε f hmodel
      ⟨x, hxS⟩ (by change 3 * latticeRadius R k ≤ dist x (z : Ambient d); linarith [hfar x hx])
    exact ⟨⟨⟨x, hxS⟩, hfix⟩, (hinto hx).2⟩
  have harea := (plane_disk_antilipschitz_range_hausdorffMeasure_ge
    (S (supportCellRoot μ R hR k z)).direction (hS _).2 a (r / 8) (by positivity)
    1 (by norm_num) g hsep).trans (measure_mono hsub)
  have heq : planeDiskLowerAreaConstant n 1 * (ENNReal.ofReal (r / 8)) ^ n =
      activeRegionLargeRadiusLowerAreaConstant n * (ENNReal.ofReal r) ^ n := by
    rw [show r / 8 = (1 / 8) * r by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8), mul_pow]
    exact (mul_assoc _ _ _).symm
  rwa [heq] at harea

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSmallRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem activeRegionLowScaleAreaFactor_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < activeRegionLowScaleAreaFactor n C G := by
  have hfirst : 0 < (384 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) := by
    exact ENNReal.mul_pos (by positivity) (by positivity)
  exact ENNReal.mul_pos hfirst.ne' (ne_of_gt (lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr hG) (le_add_right le_rfl)))

theorem activeRegionLowScaleAreaFactor_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionLowScaleAreaFactor n C G < ⊤ := by
  have hs := activeRegionStopMassAreaConstant_lt_top n G
  unfold activeRegionLowScaleAreaFactor
  finiteness

variable {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
  (hg : GlobalUpperGrowth n G μ)
  (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
  (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hC hG hg hlower hcore hε hεfine hsmall hfit hmodel

theorem active_region_low_stopping_scale_ball_area_ge
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (hrtop : r ≤ 384 * latticeRadius R k)
    (hD : cellRegionStoppingScale μ R hR k z Good p < r / 384) :
    (activeRegionLowScaleAreaFactor n C G)⁻¹ * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  obtain ⟨t, htlo, hthi⟩ := exists_lattice_radius_above R k (r / 384) (by positivity) (by linarith)
  obtain ⟨q, hq, hpq⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t p
    (hD.trans_le htlo)
  have hqr : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hq.1]
  rw [← hqr] at htlo hthi hpq
  have hsub : Set.range f ∩ closedBall q.center (3 * q.radius) ⊆
      Set.range f ∩ closedBall p r := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hxq : dist x q.center ≤ 3 * q.radius := hx.2
    have ht := dist_triangle x q.center p
    rw [dist_comm q.center p] at ht
    change dist x p ≤ r
    linarith
  have harea := active_cell_radius_power_le_limit_area μ G hG hg R hR k z Good S hS ε
    hε hεfine hsmall hfit f hmodel C hC hlower hcore q hq.2
  have hrq : (ENNReal.ofReal r) ^ n ≤ (384 : ℝ≥0∞) ^ n * (ENNReal.ofReal q.radius) ^ n := by
    have h : r ≤ 384 * q.radius := by linarith
    have he := pow_le_pow_left' (ENNReal.ofReal_le_ofReal h) n
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 384),
      ENNReal.ofReal_ofNat, mul_pow] using! he
  have hbound : (ENNReal.ofReal r) ^ n ≤ activeRegionLowScaleAreaFactor n C G *
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
    calc
      _ ≤ (384 : ℝ≥0∞) ^ n * (ENNReal.ofReal q.radius) ^ n := hrq
      _ ≤ (384 : ℝ≥0∞) ^ n *
          ((ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall q.center (3 * q.radius))) := mul_le_mul_right harea _
      _ ≤ (384 : ℝ≥0∞) ^ n *
          ((ENNReal.ofReal (C * 8 ^ n) * (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G)) *
            (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r)) := by
        gcongr
      _ = _ := by unfold activeRegionLowScaleAreaFactor; ring
  exact (ENNReal.inv_mul_le_iff (activeRegionLowScaleAreaFactor_pos n C G hC hG).ne'
    (activeRegionLowScaleAreaFactor_lt_top n C G).ne).mpr hbound

theorem active_region_limit_small_radius_ball_area_ge
    (p : Ambient d) (hp : p ∈ Set.range f)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k) :
    activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  by_cases hD : cellRegionStoppingScale μ R hR k z Good p < r / 384
  · have h := active_region_low_stopping_scale_ball_area_ge μ C G hC hG hg hlower R hR k hcore
      z Good S hS ε hε hεfine hsmall hfit f hmodel p r hr (by linarith) hD
    exact (mul_le_mul_left (min_le_left _ _) _).trans h
  · have hDlarge : r / 384 ≤ cellRegionStoppingScale μ R hR k z Good p := le_of_not_gt hD
    have harea := active_region_positive_stopping_scale_local_ball_area_ge μ R hR k z Good S hS
      ε hε (by linarith) hsmall hfit f hmodel p hp (by linarith) (r / 1024) (by positivity)
      (by linarith) (by linarith)
    have hsub : Set.range f ∩ closedBall p (r / 1024) ⊆ Set.range f ∩ closedBall p r := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hxp : dist x p ≤ r / 1024 := hx.2
      change dist x p ≤ r
      linarith
    have heq : activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (r / 1024)) ^ n =
        (activeRegionPositiveLocalLowerAreaConstant n * (ENNReal.ofReal (1 / 1024 : ℝ)) ^ n) *
          (ENNReal.ofReal r) ^ n := by
      rw [show r / 1024 = (1 / 1024) * r by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 1024), mul_pow]
      exact (mul_assoc _ _ _).symm
    rw [heq] at harea
    exact ((mul_le_mul_left (min_le_right _ _) _).trans harea).trans (measure_mono hsub)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionAllRadiusLowerArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem active_region_limit_all_radius_ball_area_ge_oai {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r) :
    activeRegionAllRadiusLowerAreaConstant n C G * (ENNReal.ofReal r) ^ n ≤
      (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  by_cases hlarge : 8 * latticeRadius R k ≤ r
  · have harea := active_region_limit_large_radius_ball_area_ge hn μ R hR k z Good S hS ε
      (by linarith) f hmodel p hp r hr hlarge
    exact (mul_le_mul_left (min_le_right _ _) _).trans harea
  · have harea := active_region_limit_small_radius_ball_area_ge μ C G hC hG hg hlower R hR k hcore
      z Good S hS ε hε hεfine hsmall hfit f hmodel p hp (r / 8) (by positivity) (by linarith)
    have hsub : Set.range f ∩ closedBall p (r / 8) ⊆ Set.range f ∩ closedBall p r := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hx' : dist x p ≤ r / 8 := hx.2
      change dist x p ≤ r
      linarith
    have heq : activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (r / 8)) ^ n =
        (activeRegionSmallRadiusLowerAreaConstant n C G * (ENNReal.ofReal (1 / 8 : ℝ)) ^ n) *
          (ENNReal.ofReal r) ^ n := by
      rw [show r / 8 = (1 / 8) * r by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8), mul_pow]
      exact (mul_assoc _ _ _).symm
    rw [heq] at harea
    exact ((mul_le_mul_left (min_le_left _ _) _).trans harea).trans (measure_mono hsub)

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.active_region_limit_all_radius_ball_area_ge_oai := @OAI.RieszRectifiability.active_region_limit_all_radius_ball_area_ge_oai
