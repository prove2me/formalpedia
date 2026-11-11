-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_active_region_low_matched_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:17.951216+00:00
-- url     : https://prove2.me/submissions/99d3bfcf-5b9c-4f33-92d2-f51de02a25fb

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
import Definitions.Def_OAIQ231Rr001
import Theorems.Thm_OAI_RieszRectifiability_activeRegionSurface_charts

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

theorem direction_normal_bound_of_local_plane_tube {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty W]
    (a : Ambient d) (ha : a ∈ S) (r η : ℝ) (hr : 0 < r)
    (htube : ∀ x ∈ S, x ∈ closedBall a r → infDist x (W : Set (Ambient d)) ≤ η * r) :
    ∀ v ∈ S.direction,
      ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (2 * η) * ‖v‖ := by
  intro v hv
  by_cases hv0 : v = 0
  · simp only [hv0, map_zero, norm_zero, mul_zero, le_refl]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hc : 0 < r / ‖v‖ := div_pos hr hvp
  let x := (r / ‖v‖) • v + a
  have hxs : x ∈ S := S.vadd_mem_of_mem_direction (S.direction.smul_mem (r / ‖v‖) hv) ha
  have hxa : dist x a = r := by
    change ‖(r / ‖v‖) • v + a - a‖ = r
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc, div_mul_cancel₀ _ hvp.ne']
  have hnear := htube x hxs (by rw [mem_closedBall, hxa])
  have hbase := htube a ha (mem_closedBall_self hr.le)
  have hn := normal_projection_bound_by_plane_distances W x a
  have hscaled : (r / ‖v‖) * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
      2 * η * r := by
    have hxsub : x - a = (r / ‖v‖) • v := by dsimp [x]; abel
    rw [hxsub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hn
    linarith
  apply le_of_mul_le_mul_left (a := r) _ hr
  calc
    r * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ =
        ((r / ‖v‖) * ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖) * ‖v‖ := by
      field_simp [hvp.ne']
    _ ≤ (2 * η * r) * ‖v‖ := mul_le_mul_of_nonneg_right hscaled hvp.le
    _ = r * ((2 * η) * ‖v‖) := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_CommonBallPlaneDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem direction_bound_of_common_support_tubes {d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (a : Ambient d)
    (r η : ℝ) (hr : 0 < r) (hη : η ≤ 1 / 8)
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S] [Nonempty W]
    (hcenter : infDist a (S : Set (Ambient d)) ≤ η * r)
    (hreverse : ∀ x ∈ ball a r, x ∈ S → infDist x μ.support < η * r)
    (hforward : ∀ x ∈ ball a r, x ∈ μ.support →
      infDist x (W : Set (Ambient d)) < η * r) :
    ∀ v ∈ S.direction,
      ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (8 * η) * ‖v‖ := by
  let b : Ambient d := orthogonalProjection S a
  have hbS : b ∈ S := orthogonalProjection_mem a
  have hba : dist b a ≤ η * r := by
    have heq : dist b a = infDist a (S : Set (Ambient d)) := by
      rw [dist_comm]
      exact dist_orthogonalProjection_eq_infDist S a
    rwa [heq]
  have htube : ∀ x ∈ S, x ∈ closedBall b (r / 2) →
      infDist x (W : Set (Ambient d)) ≤ (4 * η) * (r / 2) := by
    intro x hxS hxb
    have hxb' : dist x b ≤ r / 2 := hxb
    have hxa : x ∈ ball a r := by
      have ht := dist_triangle x b a
      rw [mem_ball]
      nlinarith
    obtain ⟨y, hyμ, hxy⟩ := (infDist_lt_iff hμ).mp (hreverse x hxa hxS)
    have hya : y ∈ ball a r := by
      have ht := dist_triangle y x a
      have ht' := dist_triangle x b a
      rw [dist_comm y x] at ht
      rw [mem_ball]
      nlinarith
    have hyW := hforward y hya hyμ
    have hdist := infDist_le_infDist_add_dist (x := x) (y := y) (s := (W : Set (Ambient d)))
    nlinarith
  have h := direction_normal_bound_of_local_plane_tube S W b hbS (r / 2) (4 * η)
    (by positivity) htube
  intro v hv
  convert! h v hv using 1
  all_goals try with_reducible_and_instances rfl
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SpanCoefficientControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficient bounds from separation from a span

Distance to a subspace is the norm of the orthogonal component. A positive
lower bound for that distance controls the coefficient of an added vector,
and extends an existing coordinate bound to the enlarged family.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem submodule_infDist_eq_normal_projection {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (x : Ambient d) :
    infDist x (S : Set (Ambient d)) = ‖Sᗮ.starProjection x‖ := by
  let : Nonempty S.toAffineSubspace := ⟨0, S.zero_mem⟩
  have hp : (orthogonalProjection S.toAffineSubspace x : Ambient d) = S.starProjection x := by
    simpa only [Submodule.toAffineSubspace_direction, vsub_eq_sub, sub_zero,
      vadd_eq_add, add_zero, Submodule.coe_orthogonalProjectionOnto_apply] using!
      orthogonalProjection_apply_mem S.toAffineSubspace S.zero_mem (p := x)
  change infDist x (S.toAffineSubspace : Set (Ambient d)) = _
  rw [← dist_orthogonalProjection_eq_infDist S.toAffineSubspace x, hp, dist_eq_norm]
  have h := S.starProjection_add_starProjection_orthogonal x
  have hx : x - S.starProjection x = Sᗮ.starProjection x := by
    exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
  rw [hx]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_GreedyAffineAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped BigOperators

theorem infDist_affine_translate {d : ℕ} (p x : Ambient d)
    (U : Submodule ℝ (Ambient d)) :
    infDist x (AffineSubspace.mk' p U : Set (Ambient d)) =
      infDist (x - p) (U : Set (Ambient d)) := by
  have hi : Isometry (fun v : Ambient d => v + p) := (IsometryEquiv.vaddConst p).isometry
  have hset : (AffineSubspace.mk' p U : Set (Ambient d)) =
      (fun v : Ambient d => v + p) '' (U : Set (Ambient d)) := by
    ext y
    constructor
    · intro hy
      refine ⟨y - p, ?_, sub_add_cancel y p⟩
      exact AffineSubspace.mem_mk'.mp hy
    · rintro ⟨v, hv, rfl⟩
      apply AffineSubspace.mem_mk'.mpr
      simpa only [vsub_eq_sub, add_sub_cancel_right] using! hv
  rw [hset]
  simpa only [sub_add_cancel] using! (infDist_image hi (x := x - p) (t := (U : Set (Ambient d))))

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NeighborCellPlaneDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Direction comparison for neighboring cell planes

Bilateral plane estimates on nearby cells of comparable radii yield common support tubes.
These tubes bound the normal projections between the two plane directions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem neighbor_cell_plane_common_tubes {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hsmall : i.radius ≤ q.radius) (hlarge : q.radius ≤ 64 * i.radius)
    (hnear : dist i.center q.center ≤ 128 * q.radius)
    (ε : ℝ) (hε : 0 < ε)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε) :
    ((∀ x ∈ ball i.center (768 * i.radius), x ∈ μ.support →
        infDist x (S : Set (Ambient d)) < (128 * ε) * (768 * i.radius)) ∧
      (∀ x ∈ ball i.center (768 * i.radius), x ∈ S →
        infDist x μ.support < (128 * ε) * (768 * i.radius))) ∧
    ((∀ x ∈ ball i.center (768 * i.radius), x ∈ μ.support →
        infDist x (W : Set (Ambient d)) < (128 * ε) * (768 * i.radius)) ∧
      (∀ x ∈ ball i.center (768 * i.radius), x ∈ W →
        infDist x μ.support < (128 * ε) * (768 * i.radius))) := by
  have hμ : μ.support.Nonempty := ⟨i.center, i.center_mem_support⟩
  obtain ⟨hSf, hSr⟩ := bilateralPlaneError_lt_pointwise μ hμ i.center (1024 * i.radius) ε
    (mul_pos (by norm_num) i.radius_pos) S hS hSi
  obtain ⟨hWf, hWr⟩ := bilateralPlaneError_lt_pointwise μ hμ q.center (1024 * q.radius) ε
    (mul_pos (by norm_num) q.radius_pos) W hW hWq
  have hiBall (x : Ambient d) (hx : x ∈ ball i.center (768 * i.radius)) :
      x ∈ ball i.center (1024 * i.radius) := by
    have hx' : dist x i.center < 768 * i.radius := hx
    have hr := i.radius_pos
    rw [mem_ball]
    linarith
  have hqBall (x : Ambient d) (hx : x ∈ ball i.center (768 * i.radius)) :
      x ∈ ball q.center (1024 * q.radius) := by
    have hx' : dist x i.center < 768 * i.radius := hx
    have ht := dist_triangle x i.center q.center
    have hr := i.radius_pos
    rw [mem_ball]
    linarith
  have heSi : ε * (1024 * i.radius) ≤ (128 * ε) * (768 * i.radius) := by
    nlinarith [mul_pos hε i.radius_pos]
  have heWq : ε * (1024 * q.radius) ≤ (128 * ε) * (768 * i.radius) := by
    have hmul := mul_le_mul_of_nonneg_left hlarge hε.le
    nlinarith [mul_pos hε i.radius_pos]
  exact ⟨⟨fun x hx hxs => (hSf x (hiBall x hx) hxs).trans_le heSi,
    fun x hx hxs => (hSr x (hiBall x hx) hxs).trans_le heSi⟩,
    ⟨fun x hx hxw => (hWf x (hqBall x hx) hxw).trans_le heWq,
    fun x hx hxw => (hWr x (hqBall x hx) hxw).trans_le heWq⟩⟩

theorem neighbor_cell_plane_directions_close {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hsmall : i.radius ≤ q.radius) (hlarge : q.radius ≤ 64 * i.radius)
    (hnear : dist i.center q.center ≤ 128 * q.radius)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε) :
    (∀ v ∈ S.direction,
      ‖(W.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1024 * ε) * ‖v‖) ∧
    (∀ v ∈ W.direction,
      ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (1024 * ε) * ‖v‖) := by
  let : Nonempty S := hS.1.to_subtype
  let : Nonempty W := hW.1.to_subtype
  obtain ⟨⟨hSf, hSr⟩, ⟨hWf, hWr⟩⟩ := neighbor_cell_plane_common_tubes μ R hR k z i q
    hsmall hlarge hnear ε hε S W hS hW hSi hWq
  have hr : 0 < 768 * i.radius := mul_pos (by norm_num) i.radius_pos
  have hη : 128 * ε ≤ 1 / 8 := by linarith
  have hSf0 := (hSf i.center (mem_ball_self hr) i.center_mem_support).le
  have hWf0 := (hWf i.center (mem_ball_self hr) i.center_mem_support).le
  have hSW := direction_bound_of_common_support_tubes μ ⟨i.center, i.center_mem_support⟩
    i.center (768 * i.radius) (128 * ε) hr hη S W hSf0 hSr hWf
  have hWS := direction_bound_of_common_support_tubes μ ⟨i.center, i.center_mem_support⟩
    i.center (768 * i.radius) (128 * ε) hr hη W S hWf0 hWr hSf
  constructor
  · intro v hv
    convert! hSW v hv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro v hv
    convert! hWS v hv using 1
    all_goals try with_reducible_and_instances rfl
    ring

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

theorem finiteNormalizedWeight_nonneg (F : Finset ι) (w : ι → ℝ)
    (i : ι) (hi : 0 ≤ w i) : 0 ≤ finiteNormalizedWeight F w i :=
  div_nonneg hi (le_trans (by norm_num) (finiteWeightDenominator_ge_one F w))

theorem finiteNormalizedWeight_eq_zero_iff (F : Finset ι) (w : ι → ℝ) (i : ι) :
    finiteNormalizedWeight F w i = 0 ↔ w i = 0 := by
  have hp : 0 < finiteWeightDenominator F w :=
    lt_of_lt_of_le zero_lt_one (finiteWeightDenominator_ge_one F w)
  simp only [finiteNormalizedWeight, div_eq_zero_iff, ne_of_gt hp, or_false]

theorem finiteNormalizedWeight_sum_le_one (F : Finset ι) (w : ι → ℝ) :
    (∑ i ∈ F, finiteNormalizedWeight F w i) ≤ 1 := by
  have hp : 0 < finiteWeightDenominator F w :=
    lt_of_lt_of_le zero_lt_one (finiteWeightDenominator_ge_one F w)
  simp only [finiteNormalizedWeight, ← Finset.sum_div]
  exact (div_le_one hp).mpr (le_max_right _ _)

theorem finiteWeightDenominator_abs_sub_le (F : Finset ι) (w v : ι → ℝ) :
    |finiteWeightDenominator F w - finiteWeightDenominator F v| ≤
      ∑ i ∈ F, |w i - v i| := by
  have h := abs_max_sub_max_le_max (1 : ℝ) (∑ i ∈ F, w i) 1 (∑ i ∈ F, v i)
  simp only [sub_self, abs_zero] at h
  rw [max_eq_right (abs_nonneg ((∑ i ∈ F, w i) - ∑ i ∈ F, v i))] at h
  apply h.trans
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem finiteNormalizedWeight_sum_abs_sub_le (F : Finset ι) (w v : ι → ℝ)
    (hv : ∀ i ∈ F, 0 ≤ v i) :
    (∑ i ∈ F, |finiteNormalizedWeight F w i - finiteNormalizedWeight F v i|) ≤
      2 * ∑ i ∈ F, |w i - v i| := by
  let A := finiteWeightDenominator F w
  let B := finiteWeightDenominator F v
  let D := ∑ i ∈ F, |w i - v i|
  have hA : 1 ≤ A := finiteWeightDenominator_ge_one F w
  have hB : 1 ≤ B := finiteWeightDenominator_ge_one F v
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hAB : |B - A| ≤ D := by
    rw [abs_sub_comm]
    exact finiteWeightDenominator_abs_sub_le F w v
  have hpoint (i : ι) (hi : i ∈ F) :
      |finiteNormalizedWeight F w i - finiteNormalizedWeight F v i| ≤
        |w i - v i| + finiteNormalizedWeight F v i * D := by
    change |w i / A - v i / B| ≤ |w i - v i| + (v i / B) * D
    have heq : w i / A - v i / B =
        (w i - v i) / A + (v i / B) * ((B - A) / A) := by
      field_simp
      ring
    have hvB : 0 ≤ v i / B := div_nonneg (hv i hi) hBp.le
    rw [heq]
    calc
      _ ≤ |(w i - v i) / A| + |(v i / B) * ((B - A) / A)| := abs_add_le _ _
      _ = |w i - v i| / A + (v i / B) * (|B - A| / A) := by
        rw [abs_div, abs_of_pos hAp, abs_mul, abs_of_nonneg hvB,
          abs_div, abs_of_pos hAp]
      _ ≤ |w i - v i| + (v i / B) * |B - A| :=
        add_le_add (div_le_self (abs_nonneg _) hA)
          (mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hA) hvB)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hAB hvB)
  calc
    _ ≤ ∑ i ∈ F, (|w i - v i| + finiteNormalizedWeight F v i * D) :=
      Finset.sum_le_sum hpoint
    _ = D + (∑ i ∈ F, finiteNormalizedWeight F v i) * D := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ D + 1 * D :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (finiteNormalizedWeight_sum_le_one F v) hD)
    _ = 2 * D := by ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FiniteCoverCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

theorem finiteCoverCutoff_nonneg (c : X) (r : ℝ) (x : X) :
    0 ≤ finiteCoverCutoff c r x := le_max_left _ _

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

theorem finiteCoverCutoff_lipschitz (c : X) (r : ℝ) (hr : 0 < r) :
    LipschitzWith (Real.toNNReal (1 / r)) (finiteCoverCutoff c r) := by
  have h : LipschitzWith (Real.toNNReal (1 / r))
      (fun x : X => 4 - dist x c / r) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have hd : |dist x c - dist y c| ≤ dist x y := by
      simpa only [Real.dist_eq] using! dist_dist_dist_le_left x y c
    rw [Real.dist_eq]
    have heq : (4 - dist x c / r) - (4 - dist y c / r) =
        -(dist x c - dist y c) / r := by ring
    rw [heq, abs_div, abs_neg, abs_of_pos hr]
    calc
      _ ≤ dist x y / r := div_le_div_of_nonneg_right hd hr.le
      _ = (1 / r) * dist x y := by ring
  exact (h.const_min 1).const_max 0

theorem finiteCoverCutoff_abs_sub_le (c : X) (r : ℝ) (hr : 0 < r) (x y : X) :
    |finiteCoverCutoff c r x - finiteCoverCutoff c r y| ≤ dist x y / r := by
  have h := (finiteCoverCutoff_lipschitz c r hr).dist_le_mul x y
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity : 0 ≤ 1 / r)] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using! h

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionOperatorCloseness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounds on the perpendicular components of vectors in two subspaces control cross-projection norms
and hence the operator-norm difference of their orthogonal projections.
-/

namespace RieszRectifiability

noncomputable section

theorem projection_cross_norm_le {d : ℕ} (S W : Submodule ℝ (Ambient d))
    (α : ℝ) (hα : 0 ≤ α)
    (hSW : ∀ v ∈ S,
      ‖(Wᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ α * ‖v‖) :
    ‖((Wᗮ : Submodule ℝ (Ambient d)).starProjection).comp S.starProjection‖ ≤ α := by
  apply ContinuousLinearMap.opNorm_le_bound _ hα
  intro x
  have hmem : S.starProjection x ∈ S := (S.orthogonalProjectionOnto x).property
  exact (hSW _ hmem).trans (mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le x) hα)

theorem projection_difference_norm_le {d : ℕ} (S W : Submodule ℝ (Ambient d))
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hSW : ∀ v ∈ S,
      ‖(Wᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ α * ‖v‖)
    (hWS : ∀ v ∈ W,
      ‖(Sᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ β * ‖v‖) :
    ‖S.starProjection - W.starProjection‖ ≤ α + β := by
  have hA := projection_cross_norm_le S W α hα hSW
  have hC := projection_cross_norm_le W S β hβ hWS
  have hAdj : ContinuousLinearMap.adjoint
      (((Sᗮ : Submodule ℝ (Ambient d)).starProjection).comp W.starProjection) =
      W.starProjection.comp (Sᗮ : Submodule ℝ (Ambient d)).starProjection := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection W).adjoint_eq,
      (isSelfAdjoint_starProjection (Sᗮ : Submodule ℝ (Ambient d))).adjoint_eq]
  have hB : ‖W.starProjection.comp (Sᗮ : Submodule ℝ (Ambient d)).starProjection‖ ≤ β := by
    rw [← hAdj, ContinuousLinearMap.adjoint.norm_map]
    exact hC
  have hid : S.starProjection - W.starProjection =
      ((Wᗮ : Submodule ℝ (Ambient d)).starProjection).comp S.starProjection -
        W.starProjection.comp (Sᗮ : Submodule ℝ (Ambient d)).starProjection := by
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      W.starProjection_orthogonal_val, S.starProjection_orthogonal_val, map_sub]
    abel_nf
  rw [hid]
  exact (norm_sub_le _ _).trans (add_le_add hA hB)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_AffineProjectionCloseness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Affine orthogonal projections are compared using their separation at a base point and the
operator-norm difference of the projections onto their direction subspaces.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem affine_projection_pair_base_bound {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S] [Nonempty W]
    (a : Ambient d) :
    dist (orthogonalProjection S a : Ambient d) (orthogonalProjection W a : Ambient d) ≤
      infDist a (S : Set (Ambient d)) + infDist a (W : Set (Ambient d)) := by
  have ht := dist_triangle (orthogonalProjection S a : Ambient d) a
    (orthogonalProjection W a : Ambient d)
  rw [dist_comm (orthogonalProjection S a : Ambient d) a,
    dist_orthogonalProjection_eq_infDist S a, dist_orthogonalProjection_eq_infDist W a] at ht
  exact ht

theorem affine_projection_pair_dist_bound {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S] [Nonempty W]
    (a x : Ambient d) (K : ℝ)
    (hK : ‖S.direction.starProjection - W.direction.starProjection‖ ≤ K) :
    dist (orthogonalProjection S x : Ambient d) (orthogonalProjection W x : Ambient d) ≤
      K * dist x a + infDist a (S : Set (Ambient d)) + infDist a (W : Set (Ambient d)) := by
  have hS := affine_projection_difference S x a
  have hW := affine_projection_difference W x a
  have hid : (orthogonalProjection S x : Ambient d) - (orthogonalProjection W x : Ambient d) =
      (S.direction.starProjection - W.direction.starProjection) (x - a) +
        ((orthogonalProjection S a : Ambient d) - (orthogonalProjection W a : Ambient d)) := by
    rw [sub_apply, ← hS, ← hW]
    abel
  have hop := (S.direction.starProjection - W.direction.starProjection).le_opNorm (x - a)
  have hbase := affine_projection_pair_base_bound S W a
  calc
    _ = ‖(S.direction.starProjection - W.direction.starProjection) (x - a) +
        ((orthogonalProjection S a : Ambient d) - (orthogonalProjection W a : Ambient d))‖ := by
      rw [dist_eq_norm, hid]
    _ ≤ ‖(S.direction.starProjection - W.direction.starProjection) (x - a)‖ +
        ‖(orthogonalProjection S a : Ambient d) - (orthogonalProjection W a : Ambient d)‖ :=
      norm_add_le _ _
    _ ≤ K * ‖x - a‖ +
        (infDist a (S : Set (Ambient d)) + infDist a (W : Set (Ambient d))) := by
      exact add_le_add (hop.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))) hbase
    _ = _ := by rw [dist_eq_norm]; ring

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

theorem finiteProjectionAverage_dist_self_le (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x : Ambient d) (L : ℝ) (hL : 0 ≤ L)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x) (hsum : (∑ i ∈ F, θ i x) ≤ 1)
    (hπ : ∀ i ∈ F, θ i x ≠ 0 → dist (π i x) x ≤ L) :
    dist (finiteProjectionAverage F θ π x) x ≤ L := by
  have hterm (i : ι) (hi : i ∈ F) : ‖θ i x • (π i x - x)‖ ≤ θ i x * L := by
    by_cases hz : θ i x = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i hi)]
      exact mul_le_mul_of_nonneg_left (hπ i hi hz) (hθ i hi)
  calc
    _ = ‖∑ i ∈ F, θ i x • (π i x - x)‖ := by
      rw [dist_eq_norm, finiteProjectionAverage, add_sub_cancel_left]
    _ ≤ ∑ i ∈ F, ‖θ i x • (π i x - x)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, θ i x * L := Finset.sum_le_sum hterm
    _ = (∑ i ∈ F, θ i x) * L := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * L := mul_le_mul_of_nonneg_right hsum hL
    _ = L := one_mul _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_NonemptyAffineProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine projection with an explicit nonemptiness witness

This projection takes the plane's nonemptiness as an argument rather than a typeclass
assumption. Its displacement is the distance to the plane, and the map is 1-Lipschitz.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem nonemptyAffineProjection_dist_self {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x : Ambient d) :
    dist (nonemptyAffineProjection S hS x) x = infDist x (S : Set (Ambient d)) := by
  let : Nonempty S := hS.to_subtype
  change dist (orthogonalProjection S x : Ambient d) x = _
  rw [dist_comm, dist_orthogonalProjection_eq_infDist]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_NonemptyAffineProjectionIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Increments of affine projections

Affine projection increments are projections onto the direction subspace. Consequently,
operator-norm bounds for two direction projections control the difference of increments.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem nonemptyAffineProjection_sub {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x y : Ambient d) :
    nonemptyAffineProjection S hS x - nonemptyAffineProjection S hS y =
      S.direction.starProjection (x - y) := by
  let : Nonempty S := hS.to_subtype
  exact affine_projection_difference S x y

theorem nonemptyAffineProjection_increment_difference_le {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (x y : Ambient d) (K : ℝ)
    (hK : ‖S.direction.starProjection - W.direction.starProjection‖ ≤ K) :
    ‖(nonemptyAffineProjection S hS x - nonemptyAffineProjection S hS y) -
      (nonemptyAffineProjection W hW x - nonemptyAffineProjection W hW y)‖ ≤ K * dist x y := by
  rw [nonemptyAffineProjection_sub, nonemptyAffineProjection_sub]
  have h := (S.direction.starProjection - W.direction.starProjection).le_opNorm (x - y)
  change ‖S.direction.starProjection (x - y) - W.direction.starProjection (x - y)‖ ≤
    ‖S.direction.starProjection - W.direction.starProjection‖ * ‖x - y‖ at h
  exact h.trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_NeighborProjectionEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection estimates for neighboring cell planes

Direction comparisons control the difference of the linear projections. Combining them with
the common support tubes gives quantitative affine projection bounds near the smaller cell.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (i q : SupportCellDescendant μ R hR k z)
  (hsmall : i.radius ≤ q.radius) (hlarge : q.radius ≤ 64 * i.radius)
  (hnear : dist i.center q.center ≤ 128 * q.radius)
  (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
  (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
  (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
  (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε)

include hsmall hlarge hnear hε hεsmall hS hW hSi hWq

theorem neighbor_cell_projection_operator_norm_le :
    ‖S.direction.starProjection - W.direction.starProjection‖ ≤ 2048 * ε := by
  obtain ⟨hSW, hWS⟩ := neighbor_cell_plane_directions_close μ R hR k z i q
    hsmall hlarge hnear ε hε hεsmall S W hS hW hSi hWq
  have h := projection_difference_norm_le S.direction W.direction (1024 * ε) (1024 * ε)
    (by positivity) (by positivity) hSW hWS
  linarith

theorem neighbor_cell_affine_projections_close_on_32ball
    (x : Ambient d) (hx : x ∈ closedBall i.center (32 * i.radius)) :
    dist (nonemptyAffineProjection S hS.1 x) (nonemptyAffineProjection W hW.1 x) ≤
      (262144 * ε) * i.radius := by
  let : Nonempty S := hS.1.to_subtype
  let : Nonempty W := hW.1.to_subtype
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    hsmall hlarge hnear ε hε hεsmall S W hS hW hSi hWq
  obtain ⟨⟨hSf, _⟩, ⟨hWf, _⟩⟩ := neighbor_cell_plane_common_tubes μ R hR k z i q
    hsmall hlarge hnear ε hε S W hS hW hSi hWq
  have hr : 0 < 768 * i.radius := mul_pos (by norm_num) i.radius_pos
  have hS0 := hSf i.center (mem_ball_self hr) i.center_mem_support
  have hW0 := hWf i.center (mem_ball_self hr) i.center_mem_support
  have h := affine_projection_pair_dist_bound S W i.center x (2048 * ε) hop
  have hx' : dist x i.center ≤ 32 * i.radius := hx
  have hm := mul_le_mul_of_nonneg_left hx' (show 0 ≤ 2048 * ε by positivity)
  change dist (orthogonalProjection S x : Ambient d) (orthogonalProjection W x : Ambient d) ≤ _
  nlinarith [mul_pos hε i.radius_pos]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionAverageGlobalIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

theorem finiteProjectionAverage_residual_increment {ι : Type*} {d : ℕ}
    (F : Finset ι) (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x y : Ambient d) :
    (finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (x - y) =
      (∑ i ∈ F, θ i x • ((π i x - x) - (π i y - y))) +
        ∑ i ∈ F, (θ i x - θ i y) • (π i y - y) := by
  unfold finiteProjectionAverage
  simp only [smul_sub, sub_smul, Finset.sum_sub_distrib]
  abel

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionAverageResidualBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

theorem finiteProjectionAverage_residual_norm_le {ι : Type*} {d : ℕ}
    (F : Finset ι) (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x y : Ambient d) (K B : ℝ) (hK : 0 ≤ K)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x) (hsum : (∑ i ∈ F, θ i x) ≤ 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - x) - (π i y - y)‖ ≤ K * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ B) :
    ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (x - y)‖ ≤
      K * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := by
  have hfirst : ‖∑ i ∈ F, θ i x • ((π i x - x) - (π i y - y))‖ ≤ K * dist x y := by
    calc
      _ ≤ ∑ i ∈ F, ‖θ i x • ((π i x - x) - (π i y - y))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, θ i x * (K * dist x y) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = 0
        · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i hi)]
          exact mul_le_mul_of_nonneg_left (hlinear i hi hz) (hθ i hi)
      _ = (∑ i ∈ F, θ i x) * (K * dist x y) := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (K * dist x y) := mul_le_mul_of_nonneg_right hsum (mul_nonneg hK dist_nonneg)
      _ = K * dist x y := one_mul _
  have hsecond : ‖∑ i ∈ F, (θ i x - θ i y) • (π i y - y)‖ ≤
      B * (∑ i ∈ F, |θ i x - θ i y|) := by
    calc
      _ ≤ ∑ i ∈ F, ‖(θ i x - θ i y) • (π i y - y)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, |θ i x - θ i y| * B := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = θ i y
        · simp only [hz, sub_self, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hoffset i hi hz) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  rw [finiteProjectionAverage_residual_increment]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

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

theorem activeLevelWeight_nonneg (i : SupportCellDescendant μ R hR k z) (x : Ambient d) :
    0 ≤ activeLevelWeight μ R hR k z Good t i x :=
  finiteNormalizedWeight_nonneg _ _ i (finiteCoverCutoff_nonneg _ _ _)

theorem activeLevelWeight_sum_le_one (x : Ambient d) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      activeLevelWeight μ R hR k z Good t i x) ≤ 1 :=
  finiteNormalizedWeight_sum_le_one _ _

theorem activeLevelWeight_ne_zero_iff (i : SupportCellDescendant μ R hR k z)
    (x : Ambient d) :
    activeLevelWeight μ R hR k z Good t i x ≠ 0 ↔
      dist x i.center < 4 * latticeRadius R (k + t) := by
  rw [activeLevelWeight, ne_eq, finiteNormalizedWeight_eq_zero_iff]
  exact finiteCoverCutoff_ne_zero_iff _ _ (latticeRadius_pos R hR (k + t)) _

theorem active_level_cutoff_support_card_bound (x : Ambient d) :
    ((activeLevelIndex μ R hR k z Good t).filter
      (fun i => activeLevelCutoff μ R hR k z t i x ≠ 0)).card ≤ (9 : ℝ) ^ d := by
  classical
  have h := active_level_local_card_bound μ R hR k z Good t
    ((activeLevelIndex μ R hR k z Good t).filter
      (fun i => activeLevelCutoff μ R hR k z t i x ≠ 0))
    (fun i hi => (mem_activeLevelIndex μ R hR k z Good t i).mp (Finset.mem_filter.mp hi).1)
    x 4 (by norm_num) (by
      intro i hi
      have hnear := (finiteCoverCutoff_ne_zero_iff i.center _
        (latticeRadius_pos R hR (k + t)) x).mp (Finset.mem_filter.mp hi).2
      simpa only [dist_comm] using! hnear.le)
  norm_num at h ⊢
  exact h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelWeightStability
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

theorem activeLevelCutoff_sum_abs_sub_le (x y : Ambient d) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      |activeLevelCutoff μ R hR k z t i x - activeLevelCutoff μ R hR k z t i y|) ≤
      (2 * (9 : ℝ) ^ d) * (dist x y / latticeRadius R (k + t)) := by
  classical
  let F := activeLevelIndex μ R hR k z Good t
  let χ := activeLevelCutoff μ R hR k z t
  let Fx := F.filter (fun i => χ i x ≠ 0)
  let Fy := F.filter (fun i => χ i y ≠ 0)
  let U := Fx ∪ Fy
  have hFx : (Fx.card : ℝ) ≤ (9 : ℝ) ^ d :=
    active_level_cutoff_support_card_bound μ R hR k z Good t x
  have hFy : (Fy.card : ℝ) ≤ (9 : ℝ) ^ d :=
    active_level_cutoff_support_card_bound μ R hR k z Good t y
  have hcard : (U.card : ℝ) ≤ 2 * (9 : ℝ) ^ d := by
    have h : (U.card : ℝ) ≤ (Fx.card : ℝ) + (Fy.card : ℝ) := by
      exact_mod_cast Finset.card_union_le Fx Fy
    linarith
  have hsub : U ⊆ F := by
    intro i hi
    rcases Finset.mem_union.mp hi with hix | hiy
    · exact (Finset.mem_filter.mp hix).1
    · exact (Finset.mem_filter.mp hiy).1
  have hsum : (∑ i ∈ F, |χ i x - χ i y|) = ∑ i ∈ U, |χ i x - χ i y| := by
    symm
    apply Finset.sum_subset hsub
    intro i hi hnot
    have hx0 : χ i x = 0 := by
      by_contra h
      exact hnot (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hi, h⟩)))
    have hy0 : χ i y = 0 := by
      by_contra h
      exact hnot (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, h⟩)))
    simp only [hx0, hy0, sub_self, abs_zero]
  change (∑ i ∈ F, |χ i x - χ i y|) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _i ∈ U, dist x y / latticeRadius R (k + t) := by
      apply Finset.sum_le_sum
      intro i _
      exact finiteCoverCutoff_abs_sub_le i.center _ (latticeRadius_pos R hR (k + t)) x y
    _ = (U.card : ℝ) * (dist x y / latticeRadius R (k + t)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (div_nonneg dist_nonneg (latticeRadius_pos R hR (k + t)).le)

theorem activeLevelWeight_sum_abs_sub_le (x y : Ambient d) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      |activeLevelWeight μ R hR k z Good t i x -
        activeLevelWeight μ R hR k z Good t i y|) ≤
      (4 * (9 : ℝ) ^ d) * (dist x y / latticeRadius R (k + t)) := by
  have h := finiteNormalizedWeight_sum_abs_sub_le
    (activeLevelIndex μ R hR k z Good t)
    (fun i => activeLevelCutoff μ R hR k z t i x)
    (fun i => activeLevelCutoff μ R hR k z t i y)
    (fun i _ => finiteCoverCutoff_nonneg i.center _ y)
  apply h.trans
  calc
    _ ≤ 2 * ((2 * (9 : ℝ) ^ d) * (dist x y / latticeRadius R (k + t))) :=
      mul_le_mul_of_nonneg_left
        (activeLevelCutoff_sum_abs_sub_le μ R hR k z Good t x y) (by norm_num)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionSurfaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Surface bounds for active-level projections

Height bounds control the displacement of the active-level projection map on a
surface. Local comparison with a reference affine plane also bounds the distance
of the projected image from that plane at the current lattice scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

theorem activeLevelProjectionMap_surface_displacement
    (A : Set (Ambient d)) (B : ℝ) (hB : 0 ≤ B)
    (hheight : ∀ i ∈ activeLevelIndex μ R hR k z Good t, ∀ x ∈ A,
      dist x i.center < 4 * latticeRadius R (k + t) →
        infDist x (S i : Set (Ambient d)) ≤ B) :
    ∀ x ∈ A, dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤ B := by
  intro x hx
  apply finiteProjectionAverage_dist_self_le _ _ _ x B hB
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  rw [nonemptyAffineProjection_dist_self]
  exact hheight i hi x hx ((activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Active-cell chart predicates

Input charts parametrize a larger tangential disk and capture the surface near an active cell.
Surface charts retain exact tangential coordinates on a smaller disk together with quantitative
normal slope, height, and local image bounds. These predicates package the geometric data used
to propagate charts through the active projection construction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

theorem HasActiveCellSurfaceChart.height_on_inner_ball
    (q : SupportCellDescendant μ R hR k z) (S : AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)
    (x : Ambient d) (hx : x ∈ A) (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    infDist x (S : Set (Ambient d)) ≤ (262144 * ε) * q.radius := by
  obtain ⟨h, _, _, hcoords, hcapture⟩ := hchart
  have hin : x ∈ Set.range h := (hcapture ▸ (show x ∈ A ∩ closedBall q.center
    ((9 / 4 : ℝ) * q.radius) from ⟨hx, hnear⟩)).1
  obtain ⟨u, rfl⟩ := hin
  exact (hcoords u).2.2.1

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceSuccessorMovement
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
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d))
  (hprevious : ∀ q ∈ activeLevelIndex μ R hR k z Good t, ∀ x ∈ A,
    x ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) →
      infDist x (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t))

include hS hε hεsmall hfit hprevious

theorem active_successor_cell_plane_height
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1))
    (x : Ambient d) (hx : x ∈ A)
    (hnear : dist x i.center < 4 * latticeRadius R (k + (t + 1))) :
    infDist x (S i : Set (Ambient d)) ≤ (17039360 * ε) * latticeRadius R (k + (t + 1)) := by
  let r := latticeRadius R (k + (t + 1))
  let rp := latticeRadius R (k + t)
  have hr : 0 < r := latticeRadius_pos R hR (k + (t + 1))
  have hrp : rp = 64 * r := by
    dsimp [rp, r]
    rw [← Nat.add_assoc, latticeRadius_succ]
    ring
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth t (by rw [hiA.1]; omega)
  have hqA : activeRegionCell Good q :=
    activeRegionCell_ancestor Good i q hiA.2 (by rw [hqdepth, hiA.1]; omega) hsub
  have hq : q ∈ activeLevelIndex μ R hR k z Good t :=
    (mem_activeLevelIndex μ R hR k z Good t q).mpr ⟨hqdepth, hqA⟩
  have hri : i.radius = r := by simp only [SupportCellDescendant.radius, hiA.1, r]
  have hrq : q.radius = rp := by simp only [SupportCellDescendant.radius, hqdepth, rp]
  have hcenters := q.dist_center_of_mem i.center hc
  have hxq : x ∈ closedBall q.center ((9 / 4 : ℝ) * rp) := by
    have ht := dist_triangle x i.center q.center
    rw [hrq] at hcenters
    change dist x q.center ≤ (9 / 4 : ℝ) * rp
    change dist x i.center < 4 * r at hnear
    nlinarith
  have hp := hprevious q hq x hx hxq
  have hπ := neighbor_cell_affine_projections_close_on_32ball μ R hR k z i q
    (by rw [hri, hrq, hrp]; linarith)
    (by rw [hri, hrq, hrp])
    (by have hpos := q.radius_pos; linarith)
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA) x
    (by change dist x i.center ≤ 32 * i.radius; rw [hri]; change dist x i.center < 4 * r at hnear; linarith)
  have ht := dist_triangle (nonemptyAffineProjection (S i) (hS i).1 x)
    (nonemptyAffineProjection (S q) (hS q).1 x) x
  rw [nonemptyAffineProjection_dist_self, nonemptyAffineProjection_dist_self] at ht
  rw [hri] at hπ
  change infDist x (S q : Set (Ambient d)) ≤ (262144 * ε) * rp at hp
  rw [hrp] at hp
  change infDist x (S i : Set (Ambient d)) ≤ (17039360 * ε) * r
  nlinarith

theorem activeLevelProjectionMap_successor_surface_displacement :
    ∀ x ∈ A, dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x) x ≤
      (17039360 * ε) * latticeRadius R (k + (t + 1)) := by
  have hr := latticeRadius_pos R hR (k + (t + 1))
  apply activeLevelProjectionMap_surface_displacement μ R hR k z Good (t + 1) S hS A
    ((17039360 * ε) * latticeRadius R (k + (t + 1))) (by positivity)
  exact active_successor_cell_plane_height μ R hR k z Good t S hS ε hε hεsmall hfit A hprevious

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceInnerCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inner-ball cone bounds for active surfaces

The capture property places surface points in the inner ball inside an active chart.
Its normal-component Lipschitz bound and the contraction of orthogonal coordinates
control normal increments by ambient distances.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem HasActiveCellSurfaceChart.normal_increment_on_inner_ball {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (q : SupportCellDescendant μ R hR k z) (S : AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (hε : 0 ≤ ε) (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A)
    (hxnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius))
    (hynear : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      (4 * activeProjectionError d ε) * dist x y := by
  obtain ⟨g, _, hnormal, hcoords, hcapture⟩ := hchart
  have hxg : x ∈ Set.range g := (hcapture ▸ (show x ∈ A ∩
    closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hx, hxnear⟩)).1
  have hyg : y ∈ Set.range g := (hcapture ▸ (show y ∈ A ∩
    closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hynear⟩)).1
  obtain ⟨u, hu⟩ := hxg
  obtain ⟨v, hv⟩ := hyg
  have hnonneg : 0 ≤ 4 * activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hn := hnormal.dist_le_mul u v
  rw [Real.coe_toNNReal _ hnonneg, hu, hv] at hn
  have hux : S.direction.orthogonalProjectionOnto x = u.val := by rw [← hu]; exact (hcoords u).2.1
  have hvy : S.direction.orthogonalProjectionOnto y = v.val := by rw [← hv]; exact (hcoords v).2.1
  have huv : dist u v ≤ dist x y := by
    change dist u.val v.val ≤ dist x y
    rw [← hux, ← hvy]
    have hp := S.direction.norm_starProjection_apply_le (x - y)
    rw [map_sub, ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection y),
      ← dist_eq_norm x y] at hp
    exact hp
  rw [map_sub, ← dist_eq_norm]
  exact hn.trans (mul_le_mul_of_nonneg_left huv hnonneg)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSuccessorFiveBall
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
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)

theorem active_successor_parent_captures_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
    ∃ q ∈ activeLevelIndex μ R hR k z Good t,
      q.radius = 64 * i.radius ∧ dist i.center q.center ≤ 2 * q.radius ∧
      closedBall i.center (5 * i.radius) ⊆
        closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth t (by rw [hiA.1]; omega)
  have hqA : activeRegionCell Good q :=
    activeRegionCell_ancestor Good i q hiA.2 (by rw [hqdepth, hiA.1]; omega) hsub
  have hq : q ∈ activeLevelIndex μ R hR k z Good t :=
    (mem_activeLevelIndex μ R hR k z Good t q).mpr ⟨hqdepth, hqA⟩
  have hscale : q.radius = 64 * i.radius := by
    simp only [SupportCellDescendant.radius, hqdepth, hiA.1]
    rw [← Nat.add_assoc, latticeRadius_succ]
    ring
  have hcenters := q.dist_center_of_mem i.center hc
  refine ⟨q, hq, hscale, hcenters, ?_⟩
  intro x hx
  change dist x i.center ≤ 5 * i.radius at hx
  change dist x q.center ≤ (9 / 4 : ℝ) * q.radius
  have ht := dist_triangle x i.center q.center
  have hr := i.radius_pos
  nlinarith

variable (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεsmall hfit hcharts

theorem active_successor_plane_height_on_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1))
    (x : Ambient d) (hx : x ∈ A) (hnear : x ∈ closedBall i.center (5 * i.radius)) :
    infDist x (S i : Set (Ambient d)) ≤ (17039360 * ε) * i.radius := by
  obtain ⟨q, hq, hscale, hcenters, hballs⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hp := (hcharts q hq).height_on_inner_ball q (S q) ε A x hx (hballs hnear)
  have hπ := neighbor_cell_affine_projections_close_on_32ball μ R hR k z i q
    (by rw [hscale]; have hr := i.radius_pos; linarith) (by rw [hscale])
    (by have hr := q.radius_pos; linarith)
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA.2) x
    (by change dist x i.center ≤ 32 * i.radius; have hr := i.radius_pos; exact le_trans hnear (by linarith))
  have ht := dist_triangle (nonemptyAffineProjection (S i) (hS i).1 x)
    (nonemptyAffineProjection (S q) (hS q).1 x) x
  rw [nonemptyAffineProjection_dist_self, nonemptyAffineProjection_dist_self] at ht
  rw [hscale] at hp
  nlinarith

theorem active_successor_projection_residual_on_five_ball
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1))
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A)
    (hxnear : x ∈ closedBall i.center (5 * i.radius))
    (hynear : y ∈ closedBall i.center (5 * i.radius)) :
    ‖(nonemptyAffineProjection (S i) (hS i).1 x - x) -
      (nonemptyAffineProjection (S i) (hS i).1 y - y)‖ ≤
        (4 * activeProjectionError d ε + 2048 * ε) * dist x y := by
  obtain ⟨q, hq, hscale, hcenters, hballs⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hn := (hcharts q hq).normal_increment_on_inner_ball q (S q) ε hε.le A
    x y hx hy (hballs hxnear) (hballs hynear)
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    (by rw [hscale]; have hr := i.radius_pos; linarith) (by rw [hscale])
    (by have hr := q.radius_pos; linarith)
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA.2)
  have hd := nonemptyAffineProjection_increment_difference_le (S i) (S q)
    (hS i).1 (hS q).1 x y (2048 * ε) hop
  have hparent : ‖(nonemptyAffineProjection (S q) (hS q).1 x -
      nonemptyAffineProjection (S q) (hS q).1 y) - (x - y)‖ ≤
      (4 * activeProjectionError d ε) * dist x y := by
    rw [nonemptyAffineProjection_sub]
    rw [(S q).direction.starProjection_orthogonal_val, norm_sub_rev] at hn
    exact hn
  have hid : (nonemptyAffineProjection (S i) (hS i).1 x - x) -
      (nonemptyAffineProjection (S i) (hS i).1 y - y) =
      ((nonemptyAffineProjection (S i) (hS i).1 x -
        nonemptyAffineProjection (S i) (hS i).1 y) -
       (nonemptyAffineProjection (S q) (hS q).1 x -
        nonemptyAffineProjection (S q) (hS q).1 y)) +
      ((nonemptyAffineProjection (S q) (hS q).1 x -
        nonemptyAffineProjection (S q) (hS q).1 y) - (x - y)) := by abel
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hd hparent).trans_eq (by ring))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceNonCollapse
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
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεsmall hfit hcharts

theorem activeLevelProjectionMap_surface_residual_le
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A) :
    ‖(activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x -
      activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) - (x - y)‖ ≤
        (72 * activeProjectionError d ε) * dist x y := by
  let r := latticeRadius R (k + (t + 1))
  let F := activeLevelIndex μ R hR k z Good (t + 1)
  let θ := activeLevelWeight μ R hR k z Good (t + 1)
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  let σ := activeLevelProjectionMap μ R hR k z Good (t + 1) S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + (t + 1))
  have hri : ∀ i ∈ F, i.radius = r := by
    intro i hi
    have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
    simp only [SupportCellDescendant.radius, hiA.1, r]
  have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hpowε := mul_le_mul_of_nonneg_right hpow hε.le
  by_cases hnear : dist x y ≤ r
  · have hlinear : ∀ i ∈ F, θ i x ≠ 0 →
        ‖(π i x - x) - (π i y - y)‖ ≤
          (4 * activeProjectionError d ε + 2048 * ε) * dist x y := by
      intro i hi hn
      have hxi := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i x).mp hn
      change dist x i.center < 4 * r at hxi
      have ht := dist_triangle y x i.center
      rw [dist_comm y x] at ht
      apply active_successor_projection_residual_on_five_ball μ R hR k z Good t
        S hS ε hε hεsmall hfit A hcharts i hi x y hx hy
      · change dist x i.center ≤ 5 * i.radius
        rw [hri i hi]
        linarith
      · change dist y i.center ≤ 5 * i.radius
        rw [hri i hi]
        linarith
    have hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ (17039360 * ε) * r := by
      intro i hi hchange
      have hyi : dist y i.center ≤ 5 * r := by
        by_cases hny : θ i y = 0
        · have hnx : θ i x ≠ 0 := fun hx0 => hchange (hx0.trans hny.symm)
          have hxi := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i x).mp hnx
          have ht := dist_triangle y x i.center
          rw [dist_comm y x] at ht
          change dist x i.center < 4 * r at hxi
          linarith
        · have hyj := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i y).mp hny
          change dist y i.center < 4 * r at hyj
          linarith
      have h := active_successor_plane_height_on_five_ball μ R hR k z Good t
        S hS ε hε hεsmall hfit A hcharts i hi y hy
        (by change dist y i.center ≤ 5 * i.radius; rwa [hri i hi])
      change dist (nonemptyAffineProjection (S i) (hS i).1 y) y ≤ _
      rw [nonemptyAffineProjection_dist_self]
      rwa [hri i hi] at h
    have hK : 0 ≤ 4 * activeProjectionError d ε + 2048 * ε := by
      unfold activeProjectionError
      positivity
    have h := finiteProjectionAverage_residual_norm_le F θ π x y
      (4 * activeProjectionError d ε + 2048 * ε) ((17039360 * ε) * r) hK
      (fun i _ => activeLevelWeight_nonneg μ R hR k z Good (t + 1) i x)
      (activeLevelWeight_sum_le_one μ R hR k z Good (t + 1) x) hlinear hoffset
    have hvar : (∑ i ∈ F, |θ i x - θ i y|) ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
      activeLevelWeight_sum_abs_sub_le μ R hR k z Good (t + 1) x y
    calc
      ‖(σ x - σ y) - (x - y)‖ ≤
          (4 * activeProjectionError d ε + 2048 * ε) * dist x y +
          ((17039360 * ε) * r) * (∑ i ∈ F, |θ i x - θ i y|) := h
      _ ≤ (4 * activeProjectionError d ε + 2048 * ε) * dist x y +
          ((17039360 * ε) * r) * ((4 * (9 : ℝ) ^ d) * (dist x y / r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar (by positivity))
      _ = (4 * activeProjectionError d ε + 2048 * ε +
            68157440 * (9 : ℝ) ^ d * ε) * dist x y := by
        field_simp [ne_of_gt hr]
        ring
      _ ≤ (72 * activeProjectionError d ε) * dist x y := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        unfold activeProjectionError
        nlinarith
  · have hprevious : ∀ q ∈ activeLevelIndex μ R hR k z Good t, ∀ w ∈ A,
        w ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) →
        infDist w (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
      intro q hq w hw hball
      have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
      have hrad : q.radius = latticeRadius R (k + t) := by
        simp only [SupportCellDescendant.radius, hqA.1]
      have hp := (hcharts q hq).height_on_inner_ball q (S q) ε A w hw (by rwa [hrad])
      rwa [hrad] at hp
    have hmove := activeLevelProjectionMap_successor_surface_displacement μ R hR k z Good t
      S hS ε hε hεsmall hfit A hprevious
    have hdx : dist (σ x) x ≤ (17039360 * ε) * r := hmove x hx
    have hdy : dist (σ y) y ≤ (17039360 * ε) * r := hmove y hy
    have hid : (σ x - σ y) - (x - y) = (σ x - x) - (σ y - y) := by abel
    have hconst : 34078720 * ε ≤ 72 * activeProjectionError d ε := by
      unfold activeProjectionError
      nlinarith
    calc
      ‖(σ x - σ y) - (x - y)‖ = ‖(σ x - x) - (σ y - y)‖ := congrArg norm hid
      _ ≤ ‖σ x - x‖ + ‖σ y - y‖ := norm_sub_le _ _
      _ ≤ (17039360 * ε) * r + (17039360 * ε) * r := add_le_add hdx hdy
      _ = (34078720 * ε) * r := by ring
      _ ≤ (34078720 * ε) * dist x y := mul_le_mul_of_nonneg_left (le_of_not_ge hnear) (by positivity)
      _ ≤ (72 * activeProjectionError d ε) * dist x y :=
        mul_le_mul_of_nonneg_right hconst dist_nonneg

theorem activeLevelProjectionMap_surface_dist_bounds
    (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A) :
    (1 / 4 : ℝ) * dist x y ≤
        dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x)
          (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) ∧
      dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x)
        (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) ≤ 2 * dist x y := by
  let σ := activeLevelProjectionMap μ R hR k z Good (t + 1) S hS
  have h := activeLevelProjectionMap_surface_residual_le μ R hR k z Good t
    S hS ε hε hεsmall hfit A hcharts x y hx hy
  have hu := norm_sub_le (σ x - σ y) (x - y)
  have hl := norm_sub_norm_le (x - y) (σ x - σ y)
  have ht := norm_sub_norm_le (σ x - σ y) (x - y)
  rw [norm_sub_rev (x - y) (σ x - σ y)] at hl
  change ‖(σ x - σ y) - (x - y)‖ ≤ (72 * activeProjectionError d ε) * dist x y at h
  have hc := mul_le_mul_of_nonneg_right hsmall (dist_nonneg : 0 ≤ dist x y)
  change (1 / 4 : ℝ) * ‖x - y‖ ≤ ‖σ x - σ y‖ ∧ ‖σ x - σ y‖ ≤ 2 * ‖x - y‖
  rw [dist_eq_norm] at h hc
  constructor <;> nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionFiniteDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionParameterMap_dist_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (t : ℕ) (u v : (S (supportCellRoot μ R hR k z) : Set (Ambient d))) :
    (1 / 4 : ℝ) ^ t * dist u v ≤
        dist (activeRegionParameterMap μ R hR k z Good S hS t u)
          (activeRegionParameterMap μ R hR k z Good S hS t v) ∧
      dist (activeRegionParameterMap μ R hR k z Good S hS t u)
        (activeRegionParameterMap μ R hR k z Good S hS t v) ≤ 2 ^ t * dist u v := by
  induction t with
  | zero =>
    simp only [pow_zero, one_mul, activeRegionParameterMap, id_eq, Subtype.dist_eq]
    exact ⟨le_rfl, le_rfl⟩
  | succ t ih =>
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
    have hu : activeRegionParameterMap μ R hR k z Good S hS t u ∈
        activeRegionSurface μ R hR k z Good S hS t := by
      rw [activeRegionSurface_eq_image]
      exact ⟨u.val, u.property, rfl⟩
    have hv : activeRegionParameterMap μ R hR k z Good S hS t v ∈
        activeRegionSurface μ R hR k z Good S hS t := by
      rw [activeRegionSurface_eq_image]
      exact ⟨v.val, v.property, rfl⟩
    have hstep := activeLevelProjectionMap_surface_dist_bounds μ R hR k z Good t
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS t)
      hcharts hsmall (activeRegionParameterMap μ R hR k z Good S hS t u)
      (activeRegionParameterMap μ R hR k z Good S hS t v) hu hv
    constructor
    · calc
        (1 / 4 : ℝ) ^ (t + 1) * dist u v = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ t * dist u v) := by
          rw [pow_succ]
          ring
        _ ≤ (1 / 4 : ℝ) * dist (activeRegionParameterMap μ R hR k z Good S hS t u)
            (activeRegionParameterMap μ R hR k z Good S hS t v) :=
          mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _ ≤ _ := hstep.1
    · calc
        _ ≤ 2 * dist (activeRegionParameterMap μ R hR k z Good S hS t u)
            (activeRegionParameterMap μ R hR k z Good S hS t v) := hstep.2
        _ ≤ 2 * (2 ^ t * dist u v) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = 2 ^ (t + 1) * dist u v := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_LipschitzChartLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Set
open scoped NNReal

theorem exists_lipschitz_lift_of_antilipschitz {X U V : Type*}
    [MetricSpace X] [MetricSpace U] [MetricSpace V]
    (F : U → V) (K : ℝ≥0) (hF : AntilipschitzWith K F)
    (g : X → V) (L : ℝ≥0) (hg : LipschitzWith L g)
    (hinto : Set.range g ⊆ Set.range F) :
    ∃ h : X → U, LipschitzWith (K * L) h ∧ ∀ x, F (h x) = g x := by
  classical
  have hpre : ∀ x : X, ∃ u : U, F u = g x := fun x => hinto ⟨x, rfl⟩
  choose h hh using hpre
  refine ⟨h, ?_, hh⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := hF.le_mul_dist (h x) (h y)
  rw [hh x, hh y] at hb
  calc
    dist (h x) (h y) ≤ (K : ℝ) * dist (g x) (g y) := hb
    _ ≤ (K : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) K.coe_nonneg
    _ = ((K * L : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_mul]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionChartLift
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
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hS hε hεtiny hsmall hfit

theorem activeRegionParameterMap_antilipschitz (t : ℕ) :
    AntilipschitzWith ((4 : ℝ≥0) ^ t)
      (fun u : S (supportCellRoot μ R hR k z) =>
        activeRegionParameterMap μ R hR k z Good S hS t u) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro u v
  have h := (activeRegionParameterMap_dist_bounds μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit t u v).1
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) t)
  have hid : (4 : ℝ) ^ t * ((1 / 4 : ℝ) ^ t * dist u v) = dist u v := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [hid] at hm
  simpa only [NNReal.coe_pow, NNReal.coe_ofNat] using! hm

theorem exists_active_region_finite_chart_lift {X : Type*} [MetricSpace X]
    (t : ℕ) (g : X → Ambient d) (L : ℝ≥0) (hg : LipschitzWith L g)
    (hinto : Set.range g ⊆ activeRegionSurface μ R hR k z Good S hS t) :
    ∃ h : X → S (supportCellRoot μ R hR k z),
      LipschitzWith ((4 : ℝ≥0) ^ t * L) h ∧
      ∀ x, activeRegionParameterMap μ R hR k z Good S hS t (h x) = g x := by
  apply exists_lipschitz_lift_of_antilipschitz
    (fun u : S (supportCellRoot μ R hR k z) =>
      activeRegionParameterMap μ R hR k z Good S hS t u) ((4 : ℝ≥0) ^ t)
    (activeRegionParameterMap_antilipschitz μ R hR k z Good S hS ε hε hεtiny hsmall hfit t)
    g L hg
  rintro _ ⟨x, rfl⟩
  have hx := hinto ⟨x, rfl⟩
  rw [activeRegionSurface_eq_image] at hx
  obtain ⟨u, hu, heq⟩ := hx
  exact ⟨⟨u, hu⟩, heq⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.cubical_sperner_prep
set_option backward.isDefEq.respectTransparency false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Classical


/-
The Cubical Sperner's Lemma.
We mostly follow Kuhn 1960 "Some Combinatorial Lemmas in Topology"
-/

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}


lemma one_of_ABCD (I : Fin (n1 +1) → SC.G) :
    case_A SC I ∨ case_B SC I ∨ case_C SC I ∨ case_D SC I := by {
  by_cases h1 : case_D SC I
  exact Or.inr (Or.inr (Or.inr h1))
  unfold case_D at h1
  push Not at h1
  obtain ⟨j , ⟨ q, h2 ⟩⟩ := h1
  by_cases q0 : q = 0
  {
    apply Or.inl
    use j
    rwa [← q0]
  }
  by_cases qp : q = Fin.last SC.p
  {
    apply Or.inr (Or.inl _)
    use j
    intro k
    rwa [h2 k]
  }
  suffices h3 : case_C SC I by {
    simp only [h3, true_or, or_true]
  }
  use j, q
}


section simplex_properties


lemma monotone_1_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1))
    (h1 : i1 ≤ i2) : ∀ j, I i1 j ≤ I i2 j := by {
  intro j
  let f := fun i ↦ I i j
  have h2 := @Fin.monotone_iff_le_succ m _ _ f
  suffices h3 : Monotone f by exact (h3 h1)
  rw [h2]
  clear i1 i2 h1
  intro i1
  have h3 := (hs.2 i1.1 i1.2 j).1
  simp only [Fin.val_fin_le] at h3
  convert h3 <;> ext <;> simp [Fin.ofNat_eq_cast, Nat.mod_eq_of_lt]
}

lemma monotone_2_of_simplex {m:ℕ } (I : Fin (m+1)→ SC.G) (hs : simplex SC m I) (i1 i2 : Fin (m+1)) :
    i1 ≤ i2 ↔ ∀ j, I i1 j ≤ I i2 j := by {
  apply Iff.intro
  {
    intro h1 j
    apply monotone_1_of_simplex _ I hs i1 i2 h1
  }
  {
    intro h1
    by_contra h2
    have h3 : i1 ≠ i2 := ne_of_not_le h2
    apply h3
    apply hs.1
    apply funext
    intro j
    apply le_antisymm (h1 j)
    apply monotone_1_of_simplex _ _ hs i2 i1 (le_of_not_ge h2)
  }
}

lemma last_of_simplex {m: ℕ} I (hs : simplex SC m I) j :
    (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1 := by {
  cases m
  simp only [Fin.last_zero, Fin.isValue, le_add_iff_nonneg_right, zero_le]
  rename_i m
  have h3 : 0 < m + 1 := by omega
  exact (hs.2 0 h3 j).2
}

lemma le_add_one_of_simplex {m: ℕ} I (hs : simplex SC m I) (i1 i2 : Fin (m+1)) j :
    (I i1 j).1 ≤ (I i2 j).1 + 1 := by {
  have h1 := last_of_simplex SC I hs j
  apply le_trans _ (le_trans h1 _)
  apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  apply Nat.add_le_add_right
  apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2)
}

end simplex_properties


lemma p_ne_zero_of_cube {hn1 : n1 + 1 = SC.n}: Fin.last SC.p ≠ 0 := by {
  simp only [ne_eq, Fin.last_eq_zero_iff]
  intro h1
  let v : Fin SC.n → Fin (SC.p + 1) := fun _ ↦ 0
  have h3 : NeZero SC.n := by {
    rw [←hn1]
    exact instNeZeroNatHAdd_1
  }
  have h4 : v 0 = 0 := by {rfl}
  have h2 := (SC.rl_proper v).2 0
  simp only [Fin.val_zero, ne_eq, h1, Fin.val_eq_zero_iff, nonpos_iff_eq_zero] at h2
  exact h2.1 h4 (h2.2 h4)
}


section simplex_child


lemma insert_index_ne j a : @insert_index SC n1 hn1 j a ≠ j := by {
  apply Fin.ne_of_val_ne
  unfold insert_index
  by_cases hlt : a.val < j.val
  {
    simp only [hlt, ↓reduceIte]
    omega
  }
  {
    simp only [hlt, ↓reduceIte, ne_eq]
    omega
  }
}

lemma almost_surjective_of_insert_index (j : Fin (SC.n+1)) (a : Fin (SC.n+1)) (h : a ≠ j)
    : ∃ k : Fin (n1 + 1) , a = @insert_index SC n1 hn1 j k := by {
  unfold insert_index
  by_cases hlt : a.1 < j.1
  {
    use (Fin.ofNat _ a.1)
    have h2 : a.1 = (Fin.ofNat (n1 + 1) a.1) := by {
      rw [Fin.ofNat_eq_cast, Fin.val_cast_of_lt]
      rw [hn1]
      apply lt_of_lt_of_le hlt
      exact Fin.is_le j
    }
    simp only [← h2, hlt]
    rfl
  }
  {
    have h2 : j.1 < a.1 := by {
      have := Fin.val_ne_of_ne (id (Ne.symm h))
      omega
    }
    let a1 := a.1 - 1
    have h3 : a1 + 1 = a.1 := by {
      show a.1 - 1 + 1 = a.1
      omega
    }
    let a1f := Fin.ofNat (n1 + 1) a1
    use a1f
    ext
    have h4 : a1 < n1 +1 := by {
      have h5 := a.2
      show a.1 - 1 < n1 + 1
      omega
    }
    have h6 : a1f.1 = a1 := by {
      unfold a1f
      simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact h4
    }
    have h5 : ¬ (a1f < j.1) := by {
      simp only [not_lt, h6]
      show j.1 ≤ a.1 - 1
      omega
    }
    simp only [h5, ↓reduceIte]
    rw [← h3, h6]
  }
}

lemma insert_index_strict_mono j : StrictMono (@insert_index SC n1 hn1 j) := by {
  intro a b h1
  have h2 : a.1 < b.1 := by {exact h1}
  have h21 : a.1 < b.1 + 1 := by omega
  unfold insert_index
  by_cases h3 : a.1 < j.1
  {
    by_cases h4 : b.1 < j.1
    repeat {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, Fin.val_fin_lt, gt_iff_lt]
      assumption
    }
  }
  {
    by_cases h4 : b.1 < j.1
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
    {
      simp only [h3, ↓reduceIte, h4, Fin.mk_lt_mk, gt_iff_lt]
      omega
    }
  }
}

lemma insert_index_inj j : Function.Injective (@insert_index SC n1 hn1 j) := by {
  apply StrictMono.injective
  apply insert_index_strict_mono
}


lemma delete_vertex_inj J {hs : simplex SC SC.n J} i1 i2
    (h1 : @delete_vertex SC n1 hn1 i1 J = @delete_vertex SC n1 hn1 i2 J ) : i1 = i2 := by {
  by_contra h2
  obtain ⟨k, h3 ⟩ := @almost_surjective_of_insert_index SC n1 hn1 i2 i1 h2
  apply @insert_index_ne SC n1 hn1 i1 k
  apply hs.1
  nth_rewrite 2 [h3]
  exact (congrFun h1) k
}

lemma delete_vertex_simplex J {hs : simplex SC SC.n J} i :
    simplex SC n1 (@delete_vertex SC n1 hn1 i J) := by {
  apply And.intro
  {
    intro k1 k2 h2
    apply insert_index_inj SC i
    apply hs.1 h2
  }
  {
    intro i2 hi2 j
    unfold delete_vertex
    apply And.intro
    {
      apply monotone_1_of_simplex SC J hs
      rw [StrictMono.le_iff_le]
      {
        simp only [Fin.ofNat_eq_cast]
        apply Fin.natCast_mono hi2
        exact Nat.le_add_right i2 1
      }
      apply insert_index_strict_mono
    }
    apply le_add_one_of_simplex SC J hs
  }
}

lemma delete_vertex_is_face J {hs : simplex SC SC.n J} i :
    is_face SC (@delete_vertex SC n1 hn1 i J) J := by {
  apply And.intro
  {
    apply delete_vertex_simplex
    exact hs
  }
  {
    apply And.intro hs
    intro c hc
    obtain ⟨ i2, hi2 ⟩ := hc
    use @insert_index SC n1 hn1 i i2
    exact hi2
  }
}

lemma is_id_of_strict_mono (m: ℕ ) (f : Fin m → Fin m) (hsm : StrictMono f)
    : ∀ k, f k = k := by {
  suffices h1 : ∀ (a : ℕ), ∀ k, k.1 < a → f k = k by {
    intro k
    exact h1 m k k.2
  }
  intro a
  induction' a with a ha
  {
    intro k h1
    omega
  }
  {
    have h1 : Function.Injective f := by {exact StrictMono.injective hsm}
    have h2 : Function.Surjective f := Finite.surjective_of_injective h1
    intro k hk
    have h3 j : j < k → f j = j := by {
      intro hj
      apply ha
      omega
    }
    by_cases h4 : f k < k
    apply h1 (h3 (f k) h4)
    simp only [not_lt] at h4
    apply le_antisymm _ h4
    obtain ⟨l, h9⟩ := h2 k
    suffices h8 : k ≤ l by {rwa [← hsm.le_iff_le, h9] at h8}
    by_contra! h6
    have h7 := h3 l h6
    rw [h9] at h7
    rw [h7] at h6
    exact (lt_self_iff_false l).mp h6
  }
}

lemma is_insert_index_of_strict_mono f (hsm : StrictMono f)
    : ∃ j, f = @insert_index SC n1 hn1 j := by {
  have h31 : Function.Injective f := by {exact hsm.injective}
  have hns : ∃ j, ∀ i, f i ≠ j := by {
    by_contra! h1
    have h2 : Function.Surjective f := by {exact h1 }
    have h5 : Function.Bijective f :=  And.intro h31 h2
    have h4 := Nat.card_eq_of_bijective f h5
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.add_right_cancel_iff] at h4
    rw [h4] at hn1
    simp only [Nat.add_eq_left, one_ne_zero] at hn1
  }
  obtain ⟨ j, hj⟩ := hns
  use j
  have h1 : ∀ k1, ∃ k2, f k1 = @insert_index SC n1 hn1 j k2 := by {
    intro k1
    apply almost_surjective_of_insert_index
    exact hj k1
  }
  obtain ⟨g, hg⟩ := axiomOfChoice h1
  have h2 : StrictMono g := by {
    intro k1 k2
    contrapose!
    intro h4
    rw [←hsm.le_iff_le, hg k1, hg k2]
    have h5 := @insert_index_strict_mono SC n1 hn1 j
    rw [h5.le_iff_le]
    exact h4
  }
  have h3 := is_id_of_strict_mono _ g h2
  ext1 k
  rw [hg k, h3 k]
}

lemma child_simplex_char (I : Fin (n1 +1) → SC.G) J {hs : simplex SC SC.n J}
    : is_face SC I J ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J := by {
  apply Iff.intro
  {
    intro h1
    have h2 : ∃ (f : Fin (n1+1) → Fin (SC.n+1)), ∀ k, I k = J (f k) := by {
      have h2 := h1.2.2
      have h3 : ∀ k, ∃ j, I k = J j := by {
        intro k
        have h4 : I k ∈ Set.range I := by {
          exact Set.mem_range_self k
        }
        have h3 := h2 h4
        obtain ⟨j, hj⟩ := h2 h4
        use j
        exact hj.symm
      }
      apply axiom_of_choice h3
    }
    obtain ⟨f, hf ⟩ := h2
    have h31 : Function.Injective f := by {
      intro k1 k2 h2
      apply h1.1.1
      rw [hf k1, hf k2, h2]
    }
    have h3 : StrictMono f := by {
      apply Monotone.strictMono_of_injective _ h31
      intro k1 k2 h2
      rw [monotone_2_of_simplex SC J hs]
      rw [← hf k1, ← hf k2]
      rwa [←monotone_2_of_simplex SC I h1.1]
    }
    obtain ⟨j, hj⟩ := is_insert_index_of_strict_mono SC f h3
    use j
    ext k
    unfold delete_vertex
    rw [hf k, hj]
  }
  {
    intro h1
    obtain ⟨ i, hi⟩ := h1
    rw [hi]
    apply @delete_vertex_is_face SC _ _ J hs
  }
}

end simplex_child


section cases_ABCD

lemma insert_vertex I (v : SC.G) j :
    ∃ J, I = @delete_vertex SC n1 hn1 j J ∧ J j = v := by {
  have h1 : ∀ j2, ∃ w, (j2 = j → w = v)
      ∧ ∀ i, @insert_index SC n1 hn1 j i = j2 → I i = w := by {
    intro j2
    by_cases h1 : j2 = j
    {
      use v
      simp only [implies_true, true_and]
      intro i
      have h3 : @insert_index SC n1 hn1 j i ≠ j := by {apply insert_index_ne}
      simp only [h1, h3, IsEmpty.forall_iff]
    }
    {
      have h3 : ∃ i, j2 = @insert_index SC n1 hn1 j i := by {
        apply almost_surjective_of_insert_index
        exact h1
      }
      obtain ⟨ i, hi⟩ := h3
      use (I i)
      simp only [h1, IsEmpty.forall_iff, true_and]
      intro i2 h2
      congr!
      apply insert_index_inj SC j
      rw [h2, hi]
    }
  }
  obtain ⟨J, h2⟩ := axiomOfChoice h1
  use J
  apply And.intro
  {
    ext i
    exact (h2 (@insert_index SC n1 hn1 j i)).2 i rfl
  }
  exact (h2 j).1 rfl
}

lemma surround_index (j : Fin (SC.n + 1)) (i : Fin (n1 + 1)) (hij : i.1 + 1 = j.1 )
    (hj1 : j ≠ Fin.last SC.n): ((@insert_index SC n1 hn1 j i).1 + 1 = j.1
    ∧ j.1 + 1 = @insert_index SC n1 hn1 j (i+1)) := by {
  unfold insert_index
  have h2 : i.1 < j.1 := by omega
  have h3 : (i+1).1 = i.1 + 1 := by {
    refine Fin.val_add_one_of_lt ?_
    simp only [Nat.succ_eq_add_one]
    show i.1 < n1
    have h6 := Fin.val_lt_last hj1
    omega
  }
  apply And.intro
  {
    simp only [h2, ↓reduceIte]
    exact hij
  }
  simp only [h3, hij, lt_self_iff_false, ↓reduceIte]
}

lemma parent_injective I (hs : simplex SC n1 I) J j
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    : Function.Injective J := by {
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3
    := by {apply almost_surjective_of_insert_index}
  intro j1 j2 h4
  have h7 j3 : J j3 = J j → j3 = j := by {
      intro h7
      by_contra h51
      apply h2
      obtain ⟨i3, hi3⟩ := h5 j3 h51
      use i3
      rw [←h7,h1,hi3]
      rfl
  }
  by_cases h8 : j1 = j
  {
    rw [h8, h7 j2]
    rw [←h8,h4]
  }
  by_cases h9 : j2 = j
  {
    rw [h9, h7 j1]
    rw [←h9,h4]
  }
  obtain ⟨i1, hi1⟩ := h5 j1 h8
  obtain ⟨i2, hi2⟩ := h5 j2 h9
  suffices h11 : i1 = i2 by {rw [hi1,hi2,h11] }
  apply hs.1
  rw [h1]
  unfold delete_vertex
  rw [← hi1,← hi2, h4]
}

lemma parent_simplex_case_BC I (hs : simplex SC n1 I) J
    (h1 : I = @delete_vertex SC n1 hn1 0 J) (h2 : J 0 ≠ I 0)
    (h3 : ∀ k, J 0 k ≤ I 0 k ∧ (I (Fin.last n1) k).1 ≤ (J 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use 0
    exact h4
  }
  have h4 : J 0 ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i1)
  }
  apply And.intro ( parent_injective SC I hs J 0 h1 h4)
  have h5 j2 : j2 < n1 + 1 →  J (Fin.ofNat _ (j2+1)) = I (Fin.ofNat _ j2) := by {
    rw [h1]
    unfold delete_vertex insert_index
    congr! with h7
    simp only [Fin.ofNat_eq_cast, Fin.val_zero, not_lt_zero, ↓reduceIte]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt h7]
    omega
  }
  intro j1 hj1 k1
  apply And.intro
  {
    rw [←hn1] at hj1
    rw [h5 j1 hj1]
    cases j1
    {
      simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
      exact (h3 k1).1
    }
    rename_i j2
    rw [h5 j2]
    apply monotone_1_of_simplex SC I hs
    simp only [Fin.ofNat_eq_cast]
    apply Fin.natCast_mono
    exact Nat.le_of_lt_succ hj1
    exact Nat.le_add_right j2 1
    exact Nat.lt_of_succ_lt hj1
  }
  {
    have h6 := h5 n1 (lt_add_one n1)
    have e1 : (Fin.ofNat (SC.n + 1) (n1 + 1) : Fin (SC.n + 1)) = Fin.last SC.n := by
      rw [← hn1]; simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    have e2 : (Fin.ofNat (n1 + 1) n1 : Fin (n1 + 1)) = Fin.last n1 := by
      simp [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rw [e1, e2] at h6
    rw [congrFun h6 k1]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_AC I (hs : simplex SC n1 I) J j (hj : j = Fin.last SC.n)
    (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ≠ I (Fin.last n1))
    (h3 : ∀ k, I (Fin.last n1) k ≤ J j k ∧ (J j k).1 ≤ (I 0 k).1 + 1) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h4 : J j ∉ Set.range I := by {
    intro h5
    obtain ⟨i1, hi1⟩ := h5
    apply h2
    apply funext
    intro k
    apply le_antisymm _ (h3 k).1
    rw [←hi1]
    apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i1)
  }
  have h5 j2 : j2 < SC.n → J (Fin.ofNat _ j2) = I (Fin.ofNat _ j2) := by {
    intro h6
    rw [h1,hj]
    unfold delete_vertex insert_index
    congr!
    have h7 : (Fin.ofNat (n1+1) j2).1 < (Fin.last SC.n).1 := by {
      simp only [Fin.ofNat_eq_cast, Fin.val_last]
      rw [Fin.val_cast_of_lt]
      exact h6
      rwa [←hn1] at h6
    }
    simp only [h7,↓reduceIte]
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt, Fin.val_cast_of_lt]
    rwa [←hn1] at h6
    exact Nat.lt_add_right 1 h6
  }
  apply And.intro ( parent_injective SC I hs J j h1 h4)
  intro j1 hj1 k1
  apply And.intro
  {
    rw [h5 _ hj1]
    by_cases h12 : j1 + 1 < SC.n
    {
      rw [h5 _ h12]
      apply monotone_1_of_simplex SC I hs
      simp only [Fin.ofNat_eq_cast]
      apply Fin.natCast_mono
      apply Nat.le_of_lt_add_one
      rwa [hn1]
      exact Nat.le_add_right j1 1
    }
    have h16 : j1+1 = SC.n := by omega
    have h13 : Fin.ofNat _ j1 = Fin.last n1 := by {
      suffices h15 : j1 = n1 by {
        simp only [h15, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
      }
      omega
    }
    have h14 : Fin.ofNat _ (j1+1) = j := by {
      rw [hj]
      simp only [h16, Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    }
    rw [h13,h14]
    exact (h3 k1).1
  }
  {
    have h7 : J 0 = I 0 := by {
      have h6 := h5 0 (Nat.zero_lt_of_lt hj1)
      simp only [Fin.ofNat_eq_cast] at h6
      exact h6
    }
    rw [h7,←hj]
    exact (h3 k1).2
  }
}

lemma parent_simplex_case_D I (hs : simplex SC n1 I) J j i
    (hij : i.1 + 1 = j.1 ) (h1 : I = @delete_vertex SC n1 hn1 j J) (h2 : J j ∉ Set.range I)
    (h3 : ∀ k, I i k ≤ J j k ∧ J j k ≤ I (i+1) k) : is_face SC I J := by {
  suffices h4 : simplex SC SC.n J by {
    rw [child_simplex_char]
    use j
    exact h4
  }
  have h5 j3 : j3 ≠ j → ∃ i3, j3 = @insert_index SC n1 hn1 j i3 := by {
    apply almost_surjective_of_insert_index
  }
  have h6 j3 : j3 ≠ j → ∃ i3, I i3 = J j3 := by {
    intro h7
    obtain ⟨i3, hi3⟩ := h5 j3 h7
    use i3
    rw [h1, hi3]
    rfl
  }
  apply And.intro (parent_injective SC I hs J j h1 h2)
  intro i2 h4 k2
  have h5 := h3 k2
  apply And.intro
  {
    simp only [Fin.ofNat_eq_cast, Fin.val_fin_le]
    rw [h1] at h5
    unfold delete_vertex at h5
    have h6 : (@insert_index SC n1 hn1 j i).1 + 1 = j := by {
      unfold insert_index
      have h7 : i.1 < j.1 := by omega
      simp only [h7, ↓reduceIte]
      exact hij
    }
    by_cases h8 : i2 = j.1
    {
      convert h5.2
      simp only [h8, Fin.cast_val_eq_self]
      have h11 : j ≠ Fin.last SC.n := by {
        suffices h12 : j.1 ≠ SC.n by exact Ne.symm (Fin.ne_of_val_ne (Ne.symm h12))
        rw [←h8]
        exact Nat.ne_of_lt h4
      }
      have h9 := @surround_index SC n1 hn1 j i hij h11
      rw [h8, h9.2]
      exact Fin.cast_val_eq_self (insert_index SC j (i + 1))
    }
    by_cases h9 : i2 + 1 = j.1
    {
      rw [←h9] at h6
      simp only [Nat.add_right_cancel_iff] at h6
      convert h5.1
      rw [←h6]
      simp only [Fin.cast_val_eq_self]
      rw [h9]
      simp only [Fin.cast_val_eq_self]
    }
    have h11 : ∃ i3, (Fin.ofNat _ i2) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h8
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      apply lt_trans h4 (lt_add_one SC.n)
    }
    have h12 : ∃ i3, (Fin.ofNat _ (i2+1)) = @insert_index SC n1 hn1 j i3 := by {
      apply almost_surjective_of_insert_index
      intro h12
      apply h9
      rw [← h12]
      simp only [Fin.ofNat_eq_cast]
      rw [Fin.val_cast_of_lt]
      omega
    }
    simp only [Fin.ofNat_eq_cast] at h11 h12
    obtain ⟨i3, hi3⟩ := h11
    obtain ⟨i4, hi4⟩ := h12
    rw [hi3, hi4]
    suffices h21 : I i3 k2 ≤ I i4 k2 by {rwa [h1] at h21}
    apply monotone_1_of_simplex SC I hs
    have h21 : StrictMono (@insert_index SC n1 hn1 j) := by {
      apply insert_index_strict_mono
    }
    rw [←h21.le_iff_le]
    rw [←hi3, ← hi4]
    refine (Fin.natCast_le_natCast ?_ h4).mpr ?_
    exact Nat.le_of_succ_le h4
    exact Nat.le_succ i2
  }
  {
    have h11 : (J (Fin.last SC.n) k2).1 ≤ (I (Fin.last n1) k2).1 := by {
      simp only [Fin.val_fin_le]
      by_cases h12 : Fin.last SC.n = j
      {
        rw [h12]
        apply le_trans h5.2
        apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
      }
      obtain ⟨ i3, hi3⟩ := h6 _ h12
      rw [←hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last _)
    }
    have h13 := last_of_simplex SC I hs k2
    apply le_trans h11 (le_trans h13 _)
    simp only [add_le_add_iff_right, Fin.val_fin_le]
    by_cases h14 : 0 = j
    {
      rw [h14]
      apply le_trans _ h5.1
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
    {
      obtain ⟨i3, hi3⟩ := h6 _ h14
      rw [← hi3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.zero_le _)
    }
  }
}


lemma ccc_add {m} I (hs : simplex SC m I) (i1 i2 i3) (h1 : i1 ≤ i2 ∧ i2 ≤ i3) :
    coord_change_count SC (I i1) (I i3) =
    coord_change_count SC (I i1) (I i2) + coord_change_count SC (I i2) (I i3) := by {
  unfold coord_change_count
  rw [←Finset.card_union_of_disjoint]
  congr
  apply Finset.ext_iff.mpr
  intro k2
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [←Decidable.not_and_iff_not_or_not]
  apply Iff.intro
  {
    intro h3 h4
    apply h3
    rw [h4.1, h4.2]
  }
  {
    intro h2 h3
    apply h2
    have h4 := monotone_1_of_simplex SC I hs i1 i2 h1.1 k2
    have h5 := monotone_1_of_simplex SC I hs i2 i3 h1.2 k2
    rw [h3] at h4 ⊢
    suffices h1 : I i3 k2 = I i2 k2 by exact ⟨h1, Eq.symm h1⟩
    exact Fin.le_antisymm h4 h5
  }
  {
    apply Finset.disjoint_filter.mpr
    intro k1 hk1 h2 h3
    apply h3
    have h4 : ∀ k, I i1 k ≤ I i2 k :=  monotone_1_of_simplex SC I hs i1 i2 h1.1
    have h5 : I i1 k1 < I i2 k1 := lt_of_le_of_ne (h4 k1) h2
    have h6 : (I i3 k1).1 ≤ (I i1 k1).1 + 1 := by {
      apply le_add_one_of_simplex _ _ hs
    }
    apply le_antisymm ( monotone_1_of_simplex SC I hs i2 i3 h1.2 k1)
    apply le_trans h6 h5
  }
}

lemma ccc_pos {m} I (hs : simplex SC m I) i1 i2 (h1 : i1 ≠ i2)
    : 0 < coord_change_count SC (I i1) (I i2) := by {
  unfold coord_change_count
  by_contra! h2
  apply h1
  apply hs.1
  simp only [ne_eq, nonpos_iff_eq_zero, Finset.card_eq_zero] at h2
  apply funext
  intro k
  rw [Finset.filter_eq_empty_iff] at h2
  simp only [Finset.mem_univ, Decidable.not_not, forall_const] at h2
  apply h2
}

lemma ccc_fun_strict_mono {m} I (hs : simplex SC m I) :
    StrictMono (ccc_fun SC I) := by {
  intro i1 i2 h1
  unfold ccc_fun
  simp only [Fin.mk_lt_mk]
  have h3 : 0 ≤ i1 ∧ i1 ≤ i2 := ⟨ (Fin.zero_le i1), (Fin.le_of_lt h1) ⟩
  rw [ccc_add SC I hs 0 i1 i2 h3]
  simp only [lt_add_iff_pos_right, gt_iff_lt]
  apply ccc_pos SC I hs _ _ $ Fin.ne_of_lt h1
}

lemma ccc_fun_is_insert_index I (hs : simplex SC n1 I) :
    ∃ j, ccc_fun SC I = @insert_index SC n1 hn1 j := by {
  apply is_insert_index_of_strict_mono
  apply ccc_fun_strict_mono SC I hs
}



lemma ccc_fun_case_D_iff {m} I (hs : simplex SC m I) :
    case_D SC I ↔ ccc_fun SC I (Fin.last m) = Fin.last SC.n := by {
  have h1 : (ccc_fun SC I (Fin.last m) = Fin.last SC.n) ↔ ∀ k, I 0 k ≠ I (Fin.last m) k  := by {
    unfold ccc_fun coord_change_count
    rw [Fin.mk.inj_iff]
    have h3 : SC.n = Fintype.card (Fin SC.n) := by {exact Eq.symm (Fintype.card_fin SC.n)}
    simp only [ne_eq, Fin.val_last]
    nth_rewrite 7 [h3]
    rw [Finset.card_eq_iff_eq_univ, Finset.eq_univ_iff_forall]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  }
  apply Iff.trans _ h1.symm
  unfold case_D
  apply Iff.intro
  {
    intro h2 k1
    obtain ⟨i2, hi2⟩ := h2 k1 (I 0 k1)
    intro h3
    apply hi2
    apply le_antisymm
    {
      rw [h3]
      apply monotone_1_of_simplex SC I hs _ _ (Fin.le_last i2)
    }
    exact monotone_1_of_simplex SC I hs _ _ (Fin.zero_le i2) k1
  }
  {
    contrapose!
    intro h2
    obtain ⟨k2, ⟨q, hq⟩ ⟩ := h2
    use k2
    rw [hq, hq]
  }
}

lemma last_eq_first_add_one J (hs : simplex SC SC.n J)
    : ∀ k, (J (Fin.last SC.n) k).1 = (J 0 k).1 + 1 := by {
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  have h2 := (ccc_fun_case_D_iff SC J hs).mpr (h3 _)
  unfold case_D at h2
  intro k
  apply le_antisymm  (last_of_simplex SC J hs k)
  apply Nat.add_one_le_of_lt
  obtain ⟨j1, hj1⟩ := h2 k (J 0 k)
  have h4 := monotone_1_of_simplex SC J hs _ _ (Fin.le_last j1) k
  apply lt_of_lt_of_le _ h4
  apply lt_of_le_of_ne (monotone_1_of_simplex SC J hs _ _ (Fin.zero_le j1) k) hj1.symm
}

lemma delete_vertex_ccc_fun_match J (hs : simplex SC SC.n J) j1 j2
    ( h1 : ccc_fun SC (@delete_vertex SC n1 hn1 j1 J) = @insert_index SC n1 hn1 j2)
    : (j1 = 0 → j2 = Fin.last SC.n) ∧ (j1 ≠ 0 → j1 = j2) := by {
  let I := @delete_vertex SC n1 hn1 j1 J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by { exact h2.1}
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j1
  }
  have scnpos : 0 < SC.n := by omega
  by_cases h4 : j1 = 0
  {
    simp only [h4, forall_const, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
    have h5 : I 0 = J 1 := by {
      unfold I delete_vertex insert_index
      congr!
      rw [h4]
      simp only [Fin.val_zero, lt_self_iff_false, ↓reduceIte, zero_add]
      simp only [Fin.val_one']
      refine Eq.symm (Nat.mod_eq_of_lt ?_)
      exact Nat.lt_add_of_pos_left scnpos
    }
    symm
    by_contra h6
    obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h6
    have h8 : (ccc_fun SC I i1).1 = SC.n := by {
      unfold I
      rw [h1, ← hi1]
      simp only [Fin.val_last]
    }
    unfold ccc_fun at h8
    simp only [h5] at h8
    unfold I delete_vertex at h8
    let c2 := coord_change_count SC (J 0) (J 1)
    have c2pos : 0 < c2 := by {
      apply ccc_pos _ _ hs
      simp only [ne_eq, Fin.zero_eq_one_iff, Nat.add_eq_right]
      omega
    }
    let j3 := @insert_index SC n1 hn1 j1 i1
    have h9 : (ccc_fun SC J j3).1 = c2 + SC.n:= by {
      simp only [← h8]
      apply ccc_add SC J hs
      simp only [Fin.zero_le, true_and]
      suffices h9 : j3 ≠ j1 by {
        rw [h4] at h9
        exact Fin.one_le_of_ne_zero h9
      }
      apply insert_index_ne
    }
    have h10 : c2 + SC.n ≤ SC.n := by {
      rw [←h9]
      exact Fin.is_le (ccc_fun SC J j3)
    }
    simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h10
    omega
  }
  simp only [h4, IsEmpty.forall_iff, ne_eq, not_false_eq_true, forall_const, true_and]
  have h2 : I 0 = J 0 := by {
    unfold I delete_vertex
    congr!
    unfold insert_index
    simpa only [Fin.val_zero, Fin.val_pos_iff, zero_add, Fin.mk_eq_zero,
        ite_eq_left_iff, not_lt,Fin.le_zero_iff, one_ne_zero, imp_false]
  }
  have h3 : ∀ j3, ccc_fun SC J j3 = j3 := by {
    apply is_id_of_strict_mono
    apply ccc_fun_strict_mono SC J hs
  }
  symm
  by_contra h5
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 _ _ h5
  have h6 : ccc_fun SC I i1 = ccc_fun SC J j2 := by {
    unfold ccc_fun
    simp [h2]
    congr
    rw [hi1]
    rfl
  }
  rw [h1, h3 j2] at h6
  contrapose h6
  apply insert_index_ne
}

lemma case_D_iff_not_end_1 I (hs : simplex SC n1 I) j
    (h1 : ccc_fun SC I = @insert_index SC n1 hn1 j) :
    case_D SC I ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  rw [ccc_fun_case_D_iff SC I hs, h1]
  have h2 : j ≠ 0 := by {
    intro h3
    apply @insert_index_ne SC n1 hn1 j 0
    rw [←h1, h3]
    unfold ccc_fun coord_change_count
    simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty, Fin.zero_eta]
  }
  simp only [ne_eq, h2, not_false_eq_true, true_and]
  apply Iff.intro
  {
    intro h3 h4
    apply @insert_index_ne SC n1 hn1 j (Fin.last n1)
    rw [h3,h4]
  }
  {
    intro h3
    have h32 : Fin.last SC.n ≠ j := fun a ↦ h3 (Eq.symm a)
    obtain ⟨i2, hi2⟩  := @almost_surjective_of_insert_index SC n1 hn1 j (Fin.last SC.n) h32
    apply le_antisymm
    exact Fin.le_last (insert_index SC j (Fin.last n1))
    rw [hi2]
    have h4 := @insert_index_strict_mono SC n1 hn1 j
    rw [h4.le_iff_le]
    exact Fin.le_last i2
  }
}

lemma case_D_iff_not_end_2 J (hs : simplex SC SC.n J) j :
    case_D SC (@delete_vertex SC n1 hn1 j J) ↔ j ≠ 0 ∧ j ≠ Fin.last SC.n := by {
  let I := @delete_vertex SC n1 hn1 j J
  have hsI : simplex SC n1 I := by {
    suffices h2 : is_face SC I J by exact h2.1
    rw [@child_simplex_char SC n1 hn1 I J hs]
    use j
  }
  obtain ⟨j2, hj2⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hsI
  have h1 := @delete_vertex_ccc_fun_match SC n1 hn1 J hs j j2 hj2
  by_cases h2 : j = 0
  {
    rw [ccc_fun_case_D_iff SC I hsI]
    simp only [h2, ne_eq, not_true_eq_false, Fin.zero_eq_last_iff, false_and, iff_false]
    rw [←h1.1 h2, hj2]
    apply insert_index_ne
  }
  rw [@case_D_iff_not_end_1 SC n1 hn1 I hsI]
  rw [hj2, ← h1.2 h2]
}

lemma same_delete_index_eq_iff J1 J2 j
    (h1 : @delete_vertex SC n1 hn1 j J1 = @delete_vertex SC n1 hn1 j J2)
    : J1 = J2 ↔ J1 j = J2 j := by {
  apply Iff.intro (fun a ↦ congrFun a j)
  intro h2
  ext j2
  by_cases h3 : j2 = j
  rw [h3,h2]
  obtain ⟨i1, hi1⟩ := @almost_surjective_of_insert_index SC n1 hn1 j j2 h3
  rw [hi1]
  exact congrFun h1 i1
}


lemma case_D_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_D SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨ j1, hj1 ⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
  have h2 : j1 ≠ 0 ∧ j1 ≠ Fin.last SC.n := by {
    rw [←case_D_iff_not_end_1 SC I hs j1 hj1]
    exact h1
  }
  have h3 : ∃ (i1: Fin (n1 + 1)), i1.1 + 1 = j1.1 := by {
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq_of_ne_zero h2.1
    rw [← ha]
    simp only [Fin.val_succ, Nat.add_right_cancel_iff]
    use ⟨ a.1, by {rw [hn1]; exact a.2}⟩
  }
  obtain ⟨ i1, hi1⟩ := h3
  have h32 : i1 ≤ i1 + 1 := by {
    refine Fin.le_of_lt ?_
    refine Fin.lt_add_one_iff.mpr ?_
    show i1.1 < n1
    have h3 := Fin.val_lt_last h2.2
    omega
  }
  have h11 := @surround_index SC n1 hn1 j1 i1 hi1 h2.2
  have h12 : @insert_index SC n1 hn1 j1 i1 ≤ j1 ∧ j1 ≤ @insert_index SC n1 hn1 j1 (i1+1) := by {
    rw [Fin.le_def, Fin.le_def, ←h11.2]
    apply And.intro
    rw [←h11.1]
    apply Nat.le_add_right
    apply Nat.le_add_right
  }
  have h3 : coord_change_count SC (I i1) (I (i1+1)) = 2 := by {
    have h3 : (@insert_index SC n1 hn1 j1 i1).1 + 2
        = (@insert_index SC n1 hn1 j1 (i1 +1)).1 := by {
      rw [← h11.2, ←h11.1]
    }
    have h4 : (ccc_fun SC I (i1+1)).1 = (ccc_fun SC I i1).1
        + coord_change_count SC (I i1) (I (i1 + 1)) := by {
      apply ccc_add SC I hs
      simp only [Fin.zero_le, true_and, h32]
    }
    rw [← hj1, h4 ] at h3
    simp only [Nat.add_left_cancel_iff] at h3
    exact h3.symm
  }
  have h4 : ∃ k1, ∃ k2, k1 ≠ k2 ∧ {k | I i1 k ≠ I (i1 +1) k} = {k1, k2} := by {
    unfold coord_change_count at h3
    rw [Finset.card_eq_two] at h3
    convert h3
    simp only [ne_eq]
    rw [←Finset.coe_eq_pair]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  }
  obtain ⟨k1, ⟨k2, h4⟩ ⟩ := h4
  have hk1 : I i1 k1 ≠ I (i1+1) k1 := by {
    have h5 := Set.mem_insert k1 {k2}
    rwa [←h4.2] at h5
  }
  have hk2 : I i1 k2 ≠ I (i1+1) k2 := by {
    have h5 : k2 ∈ ({k1, k2} : Set _) := Set.mem_insert_of_mem k1 rfl
    rwa [←h4.2] at h5
  }
  have h5 k3 : I i1 k3 ≠ I (i1+1) k3 → ∃ J3,
      I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3 := by {
    intro h21
    let ins : SC.G := fun k ↦ if k = k3 then I (i1 + 1) k else I i1 k
    obtain ⟨J3, hJ3⟩ := @insert_vertex SC n1 hn1 I ins j1
    have h6 : ∀ k, I i1 k ≤ ins k ∧ ins k ≤ I (i1+1) k := by {
      intro k
      unfold ins
      have h13 : I i1 k3 ≤ I (i1+1) k3 := monotone_1_of_simplex SC I hs _ _ h32 k3
      by_cases h12 : k = k3
      simp only [h12, ↓reduceIte, le_refl, and_true, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k3
      simp only [h12, ↓reduceIte, le_refl, true_and, ge_iff_le]
      exact monotone_1_of_simplex SC I hs _ _ h32 k
    }
    have h22 : J3 j1 k3 ≠ I i1 k3 := by {
      rw [hJ3.2]
      unfold ins
      simp only [↓reduceIte, ne_eq]
      exact h21.symm
    }
    have h23 : ∃ k4, k3 ≠ k4 ∧ I i1 k4 ≠ I (i1+1) k4 := by {
      by_cases h24 : k3 = k1
      use k2
      rw [h24]
      apply And.intro h4.1 hk2
      use k1
    }
    have h7 : ins ∉ Set.range I := by {
      intro h9
      obtain ⟨i2,hi2⟩ := h9
      rw [forall_and, ← hi2] at h6
      rw [← monotone_2_of_simplex _ _ hs,← monotone_2_of_simplex _ _ hs] at h6
      have h13 : i2 = i1 ∨ i2 = i1 + 1 := by {
        refine (WCovBy.le_and_le_iff ?_).mp h6
        apply And.intro h32
        intro i3 h33
        simp only [not_lt]
        exact Fin.add_one_le_of_lt h33
      }
      cases' h13 with h13 h13
      apply h22
      rw [hJ3.2, ←hi2, h13]
      obtain ⟨k4, hk4⟩ := h23
      apply hk4.2
      rw [←h13, hi2]
      unfold ins
      simp only [right_eq_ite_iff]
      intro h33
      exact False.elim $ hk4.1 h33.symm
    }
    use J3
    apply And.intro hJ3.1 (And.intro _ h22)
    apply @parent_simplex_case_D SC n1 hn1 I hs J3 _ _ hi1 hJ3.1
    rwa [hJ3.2]
    rwa [hJ3.2]
  }
  obtain ⟨J1, hJ1⟩ := h5 k1 hk1
  obtain ⟨J2, hJ2⟩ := h5 k2 hk2
  have h6 J3 : I = @delete_vertex SC n1 hn1 j1 J3 → is_face SC I J3
    → ∀ k, I i1 k ≤ J3 j1 k ∧ J3 j1 k ≤ I (i1+1) k := by {
    intro h14 h13 k3
    rw [h14]
    apply And.intro
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.1
    apply monotone_1_of_simplex SC J3 h13.2.1 _ _ h12.2
  }
  have h7 J3 k3 : I = @delete_vertex SC n1 hn1 j1 J3 ∧ is_face SC I J3 ∧ J3 j1 k3 ≠ I i1 k3
      → J3 j1 k3 = I (i1+1) k3 ∧ ∀ k4, k3 ≠ k4 → J3 j1 k4 = I i1 k4 := by {
    intro h9
    have h6 := h6 J3 h9.1 h9.2.1
    have h31 := h3
    rw [h9.1] at h31
    have h21 := ccc_add SC J3 h9.2.1.2.1 _ _ _ h12
    unfold delete_vertex at h31
    rw [h31] at h21
    have h22 c1 c2 : 2 = c1 + c2 → 0 < c2 → c1 ≤ 1 := by omega
    have h23 : coord_change_count SC (I i1) (J3 j1) ≤ 1 := by {
      rw [h9.1]
      apply h22 _ _ h21
      apply ccc_pos SC
      exact h9.2.1.2.1
      symm
      apply insert_index_ne
    }
    apply And.intro
    {
      apply le_antisymm (h6 k3).2
      rw [Fin.le_def]
      have h24 := le_add_one_of_simplex SC I hs (i1+1) i1 k3
      apply le_trans h24
      apply Fin.val_add_one_le_of_lt (lt_of_le_of_ne (h6 k3).1 h9.2.2.symm)
    }
    intro k4 hk4
    contrapose! h23
    refine Finset.one_lt_card_iff.mpr ?_
    use k3, k4
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    exact And.intro h9.2.2.symm ( And.intro h23.symm hk4)
  }
  refine Finset.card_eq_two.mpr ?_
  use J1, J2
  apply And.intro
  {
    have h71 := (h7 J1 k1 hJ1).2 k2 h4.1
    intro h9
    apply hJ2.2.2
    rw [←h9, h71]
  }
  apply subset_antisymm
  {
    intro J3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    intro hJ3
    have h14 := (@child_simplex_char SC n1 hn1 I J3 hJ3.2.1).mp hJ3
    obtain ⟨j2, hj2⟩ := h14
    rw [hj2] at hj1
    have h13 := @delete_vertex_ccc_fun_match SC n1 hn1 J3 hJ3.2.1 j2 j1 hj1
    have h15 := @case_D_iff_not_end_2 SC n1 hn1 J3 hJ3.2.1 j2
    rw [←hj2] at h15
    have h16 : j2 = j1 := h13.2 (h15.mp h1).1
    rw [h16] at hj2
    rw [same_delete_index_eq_iff SC J3 J1 j1, same_delete_index_eq_iff SC J3 J2 j1]
    have h71 := h7 J1 k1 hJ1
    have h72 := h7 J2 k2 hJ2
    have h18 : ∃ k5, J3 j1 k5 ≠ I i1 k5 := by {
      suffices h19 : J3 j1 ≠ I i1 by exact Function.ne_iff.mp h19
      intro h19
      apply @insert_index_ne SC n1 hn1 j1 i1
      apply hJ3.2.1.1
      rw [h19, hj2]
      rfl
    }
    obtain ⟨k5, hk5⟩ := h18
    have h73 := h7 J3 k5 ⟨hj2, ⟨ hJ3, hk5⟩ ⟩
    clear h15 h13
    have h19 : k5 = k1 ∨ k5 = k2 := by {
      have h21 : I i1 k5 ≠ I (i1+1) k5 := by {
        rw [←h73.1]
        exact hk5.symm
      }
      exact h4.2.subset h21
    }
    have h20 (J4 : _ → SC.G) : (J4 j1 k5 = I (i1+1) k5 ∧ ∀ k4, k5 ≠ k4 → J4 j1 k4 = I i1 k4)
        → J3 j1 = J4 j1:= by {
      intro h21
      apply funext
      intro k6
      by_cases h22 : k5 = k6
      rw [←h22,h21.1,h73.1]
      rw [h21.2 k6 h22, h73.2 k6 h22]
    }
    cases h19
    left
    rename_i h21
    apply h20
    rwa [h21]
    right
    rename_i h21
    apply h20
    rwa [h21]
    rw [←hJ2.1, ←hj2]
    any_goals exact hn1
    rw [←hJ1.1, ←hj2]
  }
  {
    refine Finset.insert_subset ?_ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ1.2.1
    simp only [Finset.singleton_subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hJ2.2.1
  }
}


lemma unique_const_ABC {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) k1 q1
    (h1 : ∀ i, I i k1 = q1): ∀ k2, k1 ≠ k2 → I 0 k2 ≠ I (Fin.last n1) k2 := by {
  intro k2 h3 h2
  let s : Finset (Fin SC.n) := {i | I 0 i ≠ I (Fin.last n1) i}
  have h4 : n1 ≤ s.card := by {
    obtain ⟨j, hj⟩ := @ccc_fun_is_insert_index SC n1 hn1 I hs
    show n1 ≤ (ccc_fun SC I (Fin.last n1)).1
    rw [hj]
    unfold insert_index
    simp only [Fin.val_last]
    by_cases h11 : n1 < j.1
    simp only [h11, ↓reduceIte, le_refl]
    simp only [h11, ↓reduceIte, le_add_iff_nonneg_right, zero_le]
  }
  have h6 : 2 ≤ sᶜ.card := by {
    show 1 < sᶜ.card
    rw [Finset.one_lt_card]
    use k2
    unfold s
    simp only [ne_eq, Finset.compl_filter, Decidable.not_not, Finset.mem_filter,
        Finset.mem_univ,h2, and_self, true_and]
    use k1
    apply And.intro _ h3.symm
    rw [h1,h1]
  }
  have h7 := add_le_add h4 h6
  simp only [Finset.card_add_card_compl, Fintype.card_fin] at h7
  rw [←hn1,add_le_add_iff_left] at h7
  simp only [Nat.not_ofNat_le_one] at h7
}


lemma case_AC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hAC : q ≠ Fin.last SC.p)
    : ∃! J, I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J := by {
  have h1 k2 : I 0 k2 ≠ Fin.last SC.p := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hAC
      rw [←hABC 0,h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.le_last (I (Fin.last n1) k2)
  }
  let ins2 : SC.G := fun k ↦ (I 0 k) + 1
  have h2 k : (ins2 k).1 = (I 0 k).1 + 1 := by {
    apply Fin.val_add_one_of_lt
    rw [Fin.lt_last_iff_ne_last]
    exact h1 k
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 (Fin.last SC.n)
  have h3 : J1 (Fin.last SC.n) ≠ I (Fin.last n1) := by {
    intro h12
    have h11 : I 0 k1 = I 0 k1 + 1 := by {
      show I 0 k1 = ins2 k1
      rw [←hJ1.2, h12,hABC,hABC]
    }
    simp only [left_eq_add, Fin.one_eq_zero_iff, Nat.add_eq_right] at h11
    apply @p_ne_zero_of_cube SC n1 hn1
    simp only [Fin.last_eq_zero_iff, h11]
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_AC SC I hs J1 (Fin.last SC.n) rfl hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    {
      rw [Fin.le_def, h2 k2]
      apply le_add_one_of_simplex SC I hs
    }
    rw [h2 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1)]
  rw [hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  rw [h5, h2 k1]
  suffices h6 : I 0 = J2 0 by {rw [h6]}
  rw [hJ2.1]
  unfold delete_vertex insert_index
  congr!
  simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
    not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
  rw [←hn1]
  omega
}

lemma case_B_not_last I (h1 : case_B SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I 0 = J 0 := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    congr!
    simp only [Fin.val_zero, Fin.val_last, zero_add, ite_eq_left_iff,
        not_lt, nonpos_iff_eq_zero,one_ne_zero, imp_false]
    rw [←hn1]
    omega
  }
  have h5 := (J (Fin.last SC.n) k1).is_le
  rw [h3 k1,←h4,hk1 0] at h5
  contrapose! h5
  exact lt_add_one SC.p
}


lemma case_BC_ex_unique I (hs : simplex SC n1 I) k1 q
    (hABC : ∀ i, I i k1 = q) (hBC : q ≠ 0)
    : ∃! J, I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J := by {
  have h1 k2 : I (Fin.last n1) k2 ≠ 0 := by {
    intro h11
    have h12 : k1 ≠ k2 := by {
      intro h13
      apply hBC
      rw [←hABC (Fin.last n1),h13,h11]
    }
    apply @unique_const_ABC SC n1 hn1 I hs k1 q hABC k2 h12
    apply le_antisymm
    apply monotone_1_of_simplex SC I hs
    exact Fin.zero_le (Fin.last n1)
    rw [h11]
    exact Fin.zero_le (I 0 k2)
  }
  let ins2 : SC.G := fun k ↦ (I (Fin.last n1) k) - 1
  have h22 k := Fin.val_sub_one_of_ne_zero (h1 k)
  have h21 k : (ins2 k).1 + 1 = (I (Fin.last n1) k).1  := by {
    rw [h22]
    apply Nat.sub_one_add_one ( Fin.val_ne_zero_iff.mpr (h1 k))
  }
  obtain ⟨J1, hJ1⟩ := @insert_vertex SC n1 hn1 I ins2 0
  have h3 : J1 0 ≠ I 0 := by {
    intro h12
    have h11 : (ins2 k1).1 + 1 = ins2 k1 := by {
      rw [h21 k1, hABC, ←hJ1.2,h12,hABC]
    }
    simp only [Nat.add_eq_left, one_ne_zero] at h11
  }
  have h4 : is_face SC I J1 := by {
    apply parent_simplex_case_BC SC I hs J1 hJ1.1 h3
    intro k2
    rw [hJ1.2]
    apply And.intro
    rw [Fin.le_def, ←add_le_add_iff_right 1, h21 k2]
    exact le_add_one_of_simplex SC I hs (Fin.last n1) 0 k2
    rw [h21 k2]
  }
  use J1
  simp only
  apply And.intro (And.intro hJ1.1 h4)
  intro J2 hJ2
  rw [@same_delete_index_eq_iff SC n1 hn1 _ _ _ (hJ2.1.symm.trans hJ1.1), hJ1.2]
  apply funext
  intro k1
  ext
  have h5 := last_eq_first_add_one SC J2 hJ2.2.2.1 k1
  have h6 : I (Fin.last n1) = J2 (Fin.last SC.n) := by {
    rw [hJ2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  rw [←h6, ←h21 k1] at h5
  omega
}

lemma zero_ne_last {hn1 : n1 + 1 = SC.n} : 0 ≠ Fin.last SC.n := by {
  simp only [ne_eq, Fin.zero_eq_last_iff]
  rw [←hn1]
  omega
}

lemma case_A_not_zero I (h1 : case_A SC I) J
    (h2 : I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J) : False := by {
  have h3 := last_eq_first_add_one SC J h2.2.2.1
  obtain ⟨k1, hk1⟩ := h1
  have h4 : I (Fin.last n1) = J (Fin.last SC.n) := by {
    rw [h2.1]
    unfold delete_vertex insert_index
    simp only [Fin.val_last, Fin.val_zero, not_lt_zero, ↓reduceIte]
    congr!
  }
  apply Nat.zero_ne_add_one (J 0 k1).1
  rw [←h3 k1,← h4,hk1]
  rfl
}



lemma case_ABC_count_disj {hn1 : n1 + 1 = SC.n} I k1 q
    (hABC : ∀ i, I i k1 = q) : Finset.card { J | is_face SC I J}
    = Finset.card {J | I = @delete_vertex SC n1 hn1 0 J ∧ is_face SC I J}
    + Finset.card {J | I = @delete_vertex SC n1 hn1 (Fin.last SC.n) J ∧ is_face SC I J} := by {
  have hnd : ¬ case_D SC I := by {
    contrapose! hABC
    exact hABC k1 q
  }
  rw [←Finset.card_union_of_disjoint]
  congr
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  apply Iff.intro
  {
    intro h1
    simp only [h1, and_true]
    rw [child_simplex_char] at h1
    obtain ⟨j1, hj1⟩ := h1
    have h2 := @case_D_iff_not_end_2 SC n1 hn1 J h1.2.1 j1
    rw [hj1,h2] at hnd
    have h3 := Decidable.or_iff_not_not_and_not.mpr hnd
    cases' h3 with h3 h3
    rw [hj1,h3]
    exact Or.inl rfl
    rw [hj1,h3]
    exact Or.inr rfl
    · exact hn1
    · exact h1.2.1
  }
  {
    intro h1
    rw [←or_and_right] at h1
    exact h1.2
  }
  apply Finset.disjoint_filter.mpr
  intro J h1 h2 h3
  apply @zero_ne_last SC n1 hn1
  apply @delete_vertex_inj SC n1 hn1 J h2.2.2.1
  rw [←h2.1,←h3.1]
}


lemma case_C_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h1 : case_C SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 2 := by {
  obtain ⟨k1,q, h1⟩  := h1
  have h2 := @case_AC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.2
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 q h1.2 h1.1.1
  rw [Fintype.existsUnique_iff_card_one] at h2 h3
  rw [case_ABC_count_disj SC I k1 q h1.2,h2,h3]
  exact hn1
}

lemma case_B_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_B SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_BC_ex_unique SC n1 hn1 I hs k1 _ h1 h4
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 (Fin.last SC.p) h1, h3]
  simp only [Nat.add_eq_left]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_B_not_last SC I h2
  exact hn1
}

lemma case_A_parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) (h2 : case_A SC I )
    : Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} = 1 := by {
  obtain ⟨k1, h1⟩  := id h2
  have h4 : Fin.last SC.p ≠ 0 := @p_ne_zero_of_cube SC n1 hn1
  have h3 := @case_AC_ex_unique SC n1 hn1 I hs k1 _ h1 h4.symm
  rw [Fintype.existsUnique_iff_card_one] at h3
  rw [case_ABC_count_disj SC I k1 0 h1, h3]
  simp only [Nat.add_eq_right]
  apply Finset.card_filter_eq_zero_iff.mpr
  intro J h5
  apply case_A_not_zero SC I h2
  exact hn1
}

end cases_ABCD

-- used in other file
lemma boundary_is_A_or_B {hn1 : n1 + 1 = SC.n} I (hbf : @is_boundary_face SC n1 I)
    : case_A SC I ∨ case_B SC I := by {
  have hs : simplex SC n1 I := by {
    obtain ⟨J,hJ⟩ := hbf
    exact hJ.1.1
  }
  unfold is_boundary_face at hbf
  rw [Fintype.existsUnique_iff_card_one] at hbf
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  assumption
  cases' h1 with h1 h1
  rw [@case_C_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
  rw [@case_D_parent_count SC n1 hn1 I hs h1] at hbf
  simp only [OfNat.ofNat_ne_one] at hbf
}

-- used in other file
lemma case_B_boundary {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I)
    (h1 : case_B SC I) : is_boundary_face SC I :=
  (Fintype.existsUnique_iff_card_one _).mpr (@case_B_parent_count SC n1 hn1 I hs h1)


-- used in other file
lemma parent_count {hn1 : n1 + 1 = SC.n} I (hs : simplex SC n1 I) :
    Finset.card { J : Fin (SC.n + 1) → SC.G | is_face SC I J} ∈ {c | c = 1 ∨ c = 2} := by {
  simp only [Set.mem_setOf_eq]
  have h1 := one_of_ABCD SC I
  rw [←or_assoc] at h1
  cases' h1 with h1 h1
  left
  cases' h1 with h2 h2
  exact @case_A_parent_count SC n1 hn1 I hs h2
  exact @case_B_parent_count SC n1 hn1 I hs h2
  right
  cases' h1 with h2 h2
  exact @case_C_parent_count SC n1 hn1 I hs h2
  exact @case_D_parent_count SC n1 hn1 I hs h2
}
end

section
-- module Solutions.OAIQ231_RR.cubical_sperner
set_option backward.isDefEq.respectTransparency false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open Classical



section completeness

lemma complete_simplex_iff {SC} m I(hs : simplex SC m I) :
    complete_simplex SC m I ↔ ∀ c, c ≤ m → ∃ i, SC.RL (I i) = c := by {
  apply Iff.intro
  {
    intro h1 c hc
    rwa [← Set.mem_range, h1.2, Set.mem_setOf_eq]
  }
  {
    intro c1
    apply And.intro hs
    refine Set.toFinset_inj.mp ?_
    refine (Finset.eq_iff_card_ge_of_superset ?_).mp ?_
    {
      simp only [Set.toFinset_range, Set.toFinset_subset, Finset.coe_image, Finset.coe_univ,
        Set.image_univ]
      intro c hc
      simp only [Set.mem_range, c1 c hc]
    }
    let f1 := fun (j : ℕ ) ↦ SC.RL (I (Fin.ofNat _ j))
    apply Finset.card_le_card_of_surjOn f1
    intro j h1
    simp only [Set.toFinset_range, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_range] at h1
    obtain ⟨ i, hi⟩ := h1
    use i
    simp only [Set.coe_toFinset, Set.mem_setOf_eq]
    apply And.intro (Fin.is_le i)
    unfold f1
    rw [← hi]
    simp only [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]
  }
}


lemma rl_inj_of_complete {SC} m I (hcs : complete_simplex SC m I):
    ∀ i1 i2, SC.RL (I i1) = SC.RL (I i2) → i1 = i2 := by {
  let f1 : Fin (m+1) → Fin (m+1) := fun j ↦ Fin.ofNat _ (SC.RL (I j))
  suffices h1 : Function.Injective f1 by {
    intro i1 i2 h2
    apply h1
    unfold f1
    rw [h2]
  }
  have h2 := hcs.2
  apply Function.Surjective.injective_of_finite
  rfl
  rw [complete_simplex_iff _ _ hcs.1] at hcs
  intro c
  obtain ⟨a, ha⟩ := hcs c (Fin.is_le c)
  use a
  unfold f1
  rw [ha]
  exact Fin.cast_val_eq_self c
}


lemma char_complete_face {SC n1 hn1} I J (hs : simplex SC SC.n J) :
    complete_simplex SC n1 I ∧ is_face SC I J
    ↔ ∃ i, I = @delete_vertex SC n1 hn1 i J
    ∧ ∀ (c:ℕ ), c ≤ n1 → ∃ i2, i2 ≠ i ∧ SC.RL (J i2) = c := by {
  apply Iff.intro
  {
    rw [child_simplex_char]
    intro h1
    obtain ⟨i, hi1 ⟩ := h1.2
    use i
    apply And.intro hi1
    intro c hc
    have h2 := (complete_simplex_iff n1 I h1.1.1).mp h1.1 c hc
    obtain ⟨j, hj⟩ := h2
    rw [← hj, hi1]
    unfold delete_vertex
    use @insert_index SC n1 hn1 i j
    apply And.intro _ rfl
    apply insert_index_ne
    exact hn1
    exact hs
  }
  {
    intro h1
    obtain ⟨i, hi1 ⟩ := h1
    have hface : is_face SC I J := by {
      rw [child_simplex_char]
      use i
      exact hi1.1
      exact hs
    }
    apply And.intro _ hface
    rw [complete_simplex_iff n1 I hface.1]
    intro c hc
    obtain ⟨i2, hi2⟩ := hi1.2 c hc
    have h3 := @almost_surjective_of_insert_index SC n1 hn1 i i2 hi2.1
    obtain ⟨j, hj⟩ := h3
    use j
    rw [hi1.1, ← hi2.2, hj]
    rfl
  }
}


lemma complete_child_uniq {SC n1} {hn1 : n1 + 1 = SC.n} J (hcs : complete_simplex SC SC.n J) :
    ∃! (I : Fin (n1+1) → SC.G), complete_simplex SC n1 I ∧ is_face SC I J := by {
  have h4 : ∃ i, SC.RL (J i) = SC.n := by {
    rw [← Set.mem_range, hcs.2]
    simp only [Set.mem_setOf_eq, le_refl]
  }
  obtain ⟨ i, hi⟩ := h4
  let I := @delete_vertex SC n1 hn1 i J
  have hs2 : simplex SC n1 I := by {
    apply delete_vertex_simplex
    exact hcs.1
  }
  use I
  have h1 : complete_simplex SC n1 I ∧ is_face SC I J := by
  {
    rw [@char_complete_face SC n1 hn1 _ _ hcs.1]
    use i
    apply And.intro rfl
    rw [complete_simplex_iff] at hcs
    {
      intro c hc
      have h3 : c ≤ SC.n := by omega
      obtain ⟨i2, hi2 ⟩ := hcs c h3
      use i2
      apply And.intro _ hi2
      intro h4
      rw [h4, hi, ← hn1] at hi2
      rw [← hi2] at hc
      revert hc
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, imp_self]
    }
    {
      exact hcs.1
    }
  }
  simp only
  apply And.intro h1
  intro I2 h2
  rw [@char_complete_face SC n1 hn1 _ _ hcs.1] at h2
  obtain ⟨ i2, hi2 ⟩ := h2
  have h2 : SC.RL (J i2) = SC.n := by {
    let c2 := SC.RL (J i2)
    suffices h3 : ¬ (c2 ≤ n1) by {
      apply le_antisymm (SC.rl_proper (J i2)).1
      omega
    }
    intro h2
    obtain ⟨i3, hi3⟩ := hi2.2 c2 h2
    apply hi3.1
    apply rl_inj_of_complete SC.n J hcs
    exact hi3.2
  }
  suffices h3 : i2 = i by {
    rw [hi2.1, h3]
  }
  apply rl_inj_of_complete SC.n J hcs
  rw [h2]
  exact (Eq.symm hi)
}


lemma incomplete_childs {SC n1} {hn1 : n1 + 1 = SC.n} J (hs : simplex SC SC.n J)
    (hnc : ¬ complete_simplex SC SC.n J):
    Even (Finset.card { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}) := by {
  let S : Finset _:= { I : Fin (n1 + 1) → SC.G | complete_simplex SC n1 I ∧ is_face SC I J}
  let c := S.card
  suffices h1 : c > 0 → c = 2 by {
    suffices h2 : Even c by {exact h2}
    by_cases h3 : c > 0
    rw [h1 h3]
    exact even_two
    use 0
    omega
  }
  intro cpos
  have h1 : Finset.Nonempty S := by {
    apply Finset.card_ne_zero.mp
    omega
  }
  obtain ⟨I1, h1 ⟩ := h1
  have hI1S := h1
  unfold S at h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1
  obtain ⟨i1, hi1 ⟩ := (@char_complete_face SC n1 hn1 I1 J hs).mp h1
  apply Finset.card_eq_two.mpr
  have h2 : SC.RL (J i1) ≤ n1 := by {
    by_contra h3
    apply hnc
    rw [complete_simplex_iff _ _ hs]
    intro c hc
    by_cases h4 : c ≤ n1
    {
      obtain ⟨i2, hi2 ⟩ := hi1.2 c h4
      use i2
      exact hi2.2
    }
    {
      use i1
      have h6 : c = SC.n := le_antisymm hc (le_of_eq_of_le hn1.symm (not_le.mp h4))
      rw [h6]
      apply le_antisymm (SC.rl_proper (J i1)).1
      exact le_of_eq_of_le hn1.symm (not_le.mp h3)
    }
  }
  obtain ⟨i2, hi2⟩ := hi1.2 (SC.RL (J i1)) h2
  let I2 := @delete_vertex SC n1 hn1 i2 J
  have hI2S : I2 ∈ S := by {
    unfold S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [@char_complete_face SC n1 hn1 I2 J hs]
    use i2
    apply And.intro rfl
    intro c hc
    obtain ⟨i3, hi3⟩ := hi1.2 c hc
    by_cases h4 : i3 = i2
    {
      use i1
      rw [← hi3.2,h4, hi2.2]
      exact And.intro hi2.1.symm rfl
    }
    {
      use i3
      exact And.imp_left (fun a ↦ h4) hi3
    }
  }
  use I1, I2
  apply And.intro
  {
    intro h3
    apply hi2.1
    apply @delete_vertex_inj SC n1 hn1 J hs
    rw [← hi1.1, h3]
  }
  ext I3
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Iff.intro
  {
    intro h3
    unfold S at h3
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h3
    have h31 := h3
    rw [@char_complete_face SC n1 hn1 I3 J hs] at h3
    obtain ⟨ i3, hi3 ⟩ := h3
    by_contra h4
    simp only [not_or] at h4
    rw [hi1.1] at h4
    have h7 : ∀ i4, ¬ (I3 = @delete_vertex SC n1 hn1 i4 J) → i4 ≠ i3 := by {
      intro i4 h8 h9
      apply h8
      rw [hi3.1, h9]
    }
    have h5 := @almost_surjective_of_insert_index SC n1 hn1 i3
    obtain ⟨ k1, hk1 ⟩ := h5 i1 (h7 i1 h4.1)
    obtain ⟨ k2, hk2 ⟩ := h5 i2 (h7 i2 h4.2)
    apply hi2.1
    suffices h7 : k1 = k2 by {
      rw [hk1, hk2, h7]
    }
    apply rl_inj_of_complete n1 I3 h31.1
    rw [hi3.1]
    unfold delete_vertex
    rw [← hk1, ← hk2]
    exact hi2.2.symm
  }
  {
    intro h5
    cases h5
    rename_i h9
    rwa [h9]
    rename_i h9
    rwa [h9]
  }
}


lemma complete_boundary_face_last {SC n1} {hn1 : n1 + 1 = SC.n} (I : Fin (n1 + 1) → SC.G)
    (hcbf : complete_boundary_face SC I) :
    ∀ i, ∀ j, j.1 + 1 = SC.n →  (I i j).1 = SC.p := by {
  intro i j hj
  revert i
  have h3 := @boundary_is_A_or_B SC n1 hn1 I hcbf.1
  have h1 : j.1 = n1 := by omega
  have h4 : ∀ n2, n2 ≤ n1 → ∃ i, SC.RL (I i) = n2 := by {
    intro n2 hn2
    rw [← Set.mem_range, hcbf.2.2]
    simp only [Set.mem_setOf_eq, hn2]
  }
  have h6 (j2 : Fin SC.n) : j2.1 ≤ n1 := by omega
  cases h3
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    exfalso
    obtain ⟨i, hi⟩ := h4 j2.1 (h6 j2)
    have h5 := ((SC.rl_proper (I i)).2 j2).1 (hj2 i)
    exact h5 hi
  }
  {
    rename_i h1
    obtain ⟨ j2, hj2⟩ := h1
    have hj3 i : (I i j2).1 = SC.p := by {
      rw [hj2 i]
      exact Fin.val_last SC.p
    }
    suffices h3 : j = j2 by {
      intro i
      rw [h3, hj3 i]
    }
    have h3 := SC.rl_proper
    obtain ⟨i, hi⟩ := h4 n1 (Nat.le_refl n1)
    have h5 := ((SC.rl_proper (I i)).2 j2).2 (hj3 i)
    rw [hi] at h5
    ext
    rw [h1]
    exact Nat.le_antisymm h5 (h6 j2)
  }
}

end completeness



section handshake

variable {A B : Type*}
variable [Fintype A] [Fintype B]

lemma handshake_3 (r : A → B → Prop) (c : A → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    : Odd (Finset.card {a | c a}) ↔ Odd (∑ a, Finset.card {b | r a b}) := by {
  rw [Finset.odd_sum_iff_odd_card_odd]
  rw [iff_eq_eq]
  congr
  ext a
  exact h1 a
}

lemma handshake_2 (r : A → B → Prop)
    (c : A → Prop) (d : B → Prop)
    (h1 : ∀ a, c a ↔ Odd (Finset.card {b | r a b}))
    (h2 : ∀ b, d b ↔ Odd (Finset.card {a | r a b})) :
    Odd (Finset.card {a | c a}) → Odd (Finset.card {b | d b}) := by {
  intro h3
  have h5 : ∑ a, Finset.card {b | r a b} = ∑ b, Finset.card {a | r a b} := by {
    apply Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
  }
  let r2 b a := r a b
  rw [handshake_3 r2 d h2, ←h5]
  rwa [←handshake_3 r c h1]
}

lemma handshake_1 (r : A → B → Prop)
    (c1 c2 c3: A → Prop) (d1 d2: B → Prop)
    (h1 : ∀ b, d1 b → ∃! a, c2 a ∧ r a b)
    (h2 : ∀ b, d2 b → ¬ d1 b → Even (Finset.card { a | c2 a ∧ r a b}))
    (h3 : ∀ a, c3 a → Finset.card { b | r a b} ∈ {c | c = 1 ∨ c = 2})
    (h5 : ∀ a, c1 a ↔ (∃! b, r a b) ∧ c2 a)
    (h6 : ∀ a, c2 a → c3 a) (h7 : ∀ b, ∀ a, r a b → d2 b)
    : Odd (Finset.card {a : A | c1 a}) → Odd (Finset.card {b : B | d1 b}) := by {
  let r2 a b := c2 a ∧ r a b
  apply handshake_2 r2
  {
    intro a
    rw [h5]
    by_cases p1 : c2 a
    unfold r2
    simp only [p1, and_true, true_and]
    rw [Fintype.existsUnique_iff_card_one]
    apply Iff.intro
    {
      intro p2
      use 0
      rwa [mul_zero, zero_add]
    }
    {
      intro p2
      have p3 := h3 a (h6 a p1)
      simp only [Set.mem_setOf_eq] at p3
      cases p3
      rename_i p4
      exact p4
      rename_i p4
      rw [p4] at p2
      exfalso
      revert p2
      simp only [imp_false, Nat.not_odd_iff_even, even_two]
    }
    {
      unfold r2
      simp only [p1, and_false, false_and, Finset.filter_false, Finset.card_empty, Nat.not_odd_zero]
    }
  }
  {
    intro b
    by_cases p1 : d1 b
    {
      simp only [p1, true_iff]
      use 0
      rw [mul_zero, zero_add]
      rw [← Fintype.existsUnique_iff_card_one]
      exact h1 b p1
    }
    {
      simp only [p1, false_iff]
      intro p2
      have p5 : Finset.Nonempty {a | r2 a b} := by {
        have p3 : Odd (Finset.card { a | r2 a b}) := by {
          convert p2
        }
        apply Finset.card_ne_zero.mp
        intro p4
        revert p3
        rw [p4]
        simp only [Nat.not_odd_zero, imp_self]
      }
      have p3 : d2 b := by {
        obtain ⟨a, p6⟩ := p5
        apply h7 b a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at p6
        exact p6.2
      }
      revert p2
      have p4 := h2 b p3 p1
      simp only [imp_false, Nat.not_odd_iff_even]
      convert p4
    }
  }
}

end handshake



lemma odd_of_boundary_faces SC {n1} {hn1 : n1 + 1 = SC.n}:
    Odd (Finset.card { I : Fin (n1 + 1) → SC.G | complete_boundary_face SC I})
    → Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  apply handshake_1 (is_face SC)
  apply @complete_child_uniq SC n1 hn1
  apply @incomplete_childs SC n1 hn1
  apply @parent_count SC n1 hn1
  {
    intro I
    rfl
  }
  exact fun _ h1 ↦ h1.1
  exact fun _ _ h1 ↦ h1.2.1
}


section induction_step

variable (SC : SpernerCube)
variable {n1 : ℕ}


lemma child_map_inj {hn1 : n1 + 1 = SC.n }: Function.Injective (@child_map SC n1) := by {
  intro v1 v2 h1
  ext i
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  rw [← child_map_applied SC v1]
  rw [← child_map_applied SC v2]
  rwa [h1]
  exact hn1
}

lemma child_map_surj_on {hn1 : n1 + 1 = SC.n} w
    (h1 : ∀ j, j.1 + 1 = SC.n → w j = SC.p)
    : ∃ v, @child_map SC n1 v = w := by {
  have h0 : NeZero SC.n := by {
    rw [← hn1]
    exact instNeZeroNatHAdd_1
  }
  let v2 : Fin n1 → Fin (SC.p +1) := fun i ↦ w (Fin.ofNat _ i.1)
  use v2
  apply funext
  intro i
  unfold child_map
  cases n1
  {
    simp only
    have h2 := h1 0
    simp only [Fin.val_zero, zero_add] at h2 hn1
    have h3 : i = 0 := by {
      have h4 := i.2
      simp only [← hn1] at h4
      ext
      simp only [Fin.val_zero]
      exact Nat.lt_one_iff.mp h4
    }
    rw [h3]
    exact Fin.eq_of_val_eq (id (Eq.symm (h2 hn1)))
  }
  {
    rename_i n2
    have h2 := h1 i
    by_cases h3 : i.1 +1 = SC.n
    {
      simp only [h3, ↓reduceIte]
      exact Eq.symm (Fin.eq_of_val_eq (h1 i h3))
    }
    simp only [h3, ↓reduceIte, Nat.succ_eq_add_one]
    unfold v2
    congr
    simp only [Fin.ofNat_eq_cast]
    rw [Fin.val_cast_of_lt]
    exact Fin.cast_val_eq_self i
    have h4 := i.2
    simp only [← hn1] at h3 h4
    omega
  }
}


end induction_step


lemma induction_start (SC : SpernerCube) (h0 : 0 = SC.n)
    : Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  use 0
  simp only [mul_zero, zero_add]
  rw [←Fintype.existsUnique_iff_card_one]
  let b : SC.G := fun _ ↦ 0
  let a : Fin (SC.n + 1) → SC.G := fun _ ↦ b
  use a
  simp only
  have h1 (x : Fin (SC.n+1)) : x = 0 := by {
    ext
    simp only [Fin.val_zero]
    rw [← Nat.lt_one_iff]
    apply Fin.val_lt_of_le x
    rw [←h0]
  }
  have hf (j : Fin SC.n) : False := by {
    apply Fin.elim0
    rwa [h0]
  }
  apply And.intro
  apply And.intro
  apply And.intro
  {
    intro x1 x2 _
    rw [h1 x1, h1 x2]
  }
  {
    intro i hi j
    exact False.elim ( hf j )
  }
  {
    ext i
    simp only [← h0]
    simp only [Set.mem_range, nonpos_iff_eq_zero, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    have h3 : ∀ c, SC.RL (a c) = 0 := by {
      intro c
      have h2 := (SC.rl_proper (a c)).1
      simp only [← h0] at h2
      omega
    }
    apply Iff.intro
    {
      intro h2
      cases h2
      rename_i c hc
      rw [h3 c] at hc
      exact (Eq.symm hc)
    }
    {
      intro hi0
      use 0
      rw [hi0]
      exact h3 0
    }
  }
  {
    intro a2 h2
    ext i
    apply funext
    intro j
    exact False.elim ( hf j )
  }
}

theorem strong_cubical_sperner (k: ℕ ) : ∀ (SC : SpernerCube), k = SC.n →
    Odd (Finset.card { I | complete_simplex SC SC.n I}) := by {
  induction' k with k hind
  {
    intro SC hk
    exact induction_start SC hk
  }
  {
    intro SC1 hk1
    apply @odd_of_boundary_faces SC1 k hk1
    let SC2 := @child_cube SC1 k hk1
    have hnz : NeZero SC1.n := by {
      rw [← hk1]
      exact instNeZeroNatHAdd_1
    }
    have h2 := hind SC2 rfl
    apply Eq.mpr _ h2
    apply congrArg
    let f1 : SC2.G → SC1.G := child_map SC1
    let f2 : (Fin (k+1)→ SC2.G) → (Fin (k+1)→ SC1.G) := fun a ↦ fun b ↦ f1 (a b)
    have hf1inj : Function.Injective f1 := by {
      apply child_map_inj SC1
      rw [← hk1]
      rfl
    }
    symm
    have hcomp I : complete_boundary_face SC1 (f2 I) ↔ complete_simplex SC2 SC2.n I := by {
      unfold complete_boundary_face complete_simplex
      have h_last j k: j.1 + 1 = SC1.n → f2 I k j = SC1.p := by {
        apply child_map_last
      }
      have h_bf : simplex SC1 k (f2 I) ↔ is_boundary_face SC1 (f2 I) ∧ simplex SC1 k (f2 I):= by {
        simp only [iff_and_self]
        intro hs
        apply @case_B_boundary SC1 k hk1
        exact hs
        use (Fin.ofNat _ k)
        intro i
        ext
        apply h_last
        simp [← hk1]
      }
      rw [← and_assoc, ←h_bf]
      have h3 : SC2.n = k := rfl
      apply and_congr
      apply and_congr
      {
        apply Iff.intro
        {
          intro h4 i1 i2 h5
          exact h4 (congrArg f1 h5)
        }
        {
          intro h4 i1 i2 h5
          apply h4
          apply hf1inj h5
        }
      }
      {
        simp only [h3]
        apply forall₂_congr
        intro i hi1
        apply Iff.intro
        {
          intro h4 j
          have h6 k : (f2 I k (Fin.ofNat _ j.1)) = (I k j) := by {
            unfold f2
            apply child_map_applied
            rw [← hk1]
            rfl
          }
          rw [← h6, ← h6, ←h6, ← h6]
          exact h4 (Fin.ofNat _ j.1)
        }
        {
          intro h4 j
          by_cases h5 : j.1 + 1 = SC1.n
          {
            rw [h_last, h_last, h_last, h_last]
            simp only [le_refl, le_add_iff_nonneg_right, zero_le,
              and_self]
            repeat' exact h5
          }
          {
            have h7 : j.1 < SC2.n := by {
              rw [h3]
              have h6 := j.2
              simp only [← hk1] at h5 h6
              omega
            }
            have hn02 : NeZero SC2.n := by {
              exact NeZero.of_gt hi1
            }
            let j2 : Fin SC2.n := (Fin.ofNat _ j.1)
            have h8 : j = (Fin.ofNat _ j2.1) := by {
              unfold j2
              simp only [Fin.ofNat_eq_cast,]
              rw [Fin.val_cast_of_lt]
              exact Eq.symm (Fin.cast_val_eq_self j)
              exact h7
            }
            have h6 k : (f2 I k j) = (I k j2) := by {
              unfold f2
              rw [h8]
              apply child_map_applied
              exact hk1
            }
            rw [h6, h6, h6, h6]
            exact h4 j2
          }
        }
      }
      exact Eq.congr_right rfl
    }
    apply Finset.card_nbij f2
    {
      intro I hI
      have hI' : complete_simplex SC2 SC2.n I :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hI)).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp I).mpr hI'⟩)
    }
    {
      intro I1 h41 I2 h42 h5
      ext i
      apply hf1inj
      exact congrFun h5 i
    }
    {
      simp only [Finset.coe_filter, Finset.mem_univ, true_and]
      intro J
      simp only [Set.mem_setOf_eq, Set.mem_image]
      intro h3
      have h4 : ∃ I, f2 I = J := by {
        suffices h6 : ∀ i, ∃ ii, f1 ii = J i by {
          obtain ⟨I, h5⟩  := axiomOfChoice h6
          use I
          ext i
          exact h5 i
        }
        intro i
        have h5 := @child_map_surj_on SC1 k hk1
        apply h5
        exact @complete_boundary_face_last SC1 k hk1 J h3 i
      }
      obtain ⟨I, h4⟩ := h4
      use I
      simp only [h4, and_true]
      exact (hcomp I).mp (h4 ▸ h3)
    }
  }

}

theorem weaker_cubical_sperner SC : ∃ I, complete_simplex SC SC.n I := by {
  have h1 := strong_cubical_sperner SC.n SC rfl
  obtain ⟨k1, hk1⟩ := h1
  have h2 : 0 < 2 * k1 + 1 := by omega
  rw [←hk1, Finset.card_pos] at h2
  obtain ⟨I, hI1⟩ := h2
  use I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI1
  exact hI1
}
end

section
-- module Solutions.OAIQ231_RR.apply_cubical_sperner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Classical

/-
shows the fixed-point theorem for the unit cube
by applying the cubical sperner's lemma
-/


variable {n : ℕ}

lemma reduced_label_props_3 (f : @unit_cube n → @unit_cube n) (x : @unit_cube n) (k : Fin n)
    : (@rl_point n f x = k → (f x).1 k ≤ x.1 k) ∧ (@rl_point n f x > k → (f x).1 k ≥ x.1 k) := by {
  have h1 := (reduced_label_props_1 f x).2 k
  apply And.intro
  {
    intro h2
    cases h1.1 h2
    (expose_names; exact le_of_lt h)
    rename_i h3
    rw [h3]
    exact (f x).2.2 k
  }
  {
    contrapose!
    intro h2
    apply h1.2
    exact Or.inl h2
  }
}

lemma dist_discrete_map p (ppos: 0 < p) (v1 v2 : Fin n → Fin (p+1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discrete_map p v1) (discrete_map p v2) ≤ 1 / p := by {
  let x1 := (discrete_map p v1).1
  let x2 := (discrete_map p v2).1
  show dist x1 x2 ≤ 1 / p
  refine (dist_pi_le_iff ?_).mpr ?_
  simp only [one_div, inv_nonneg, Nat.cast_nonneg]
  intro k
  have hx1 : x1 k = (v1 k).1 / p := by {rfl}
  have hx2 : x2 k = (v2 k).1 / p := by {rfl}
  rw [hx1, hx2]
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1k := (h1 k).1
  have h2k := (h1 k).2
  apply And.intro
  repeat {
    rw [sub_le_iff_le_add', ← add_div]
    have ppos2 : 0 < (p : ℝ) := Nat.cast_pos'.mpr ppos
    rwa [div_le_div_iff_of_pos_right ppos2, ←Nat.cast_add_one, Nat.cast_le]
  }
}

lemma nearby_points (f : @unit_cube n → @unit_cube n) (p0:ℕ):
    ∃ x0 : @unit_cube n, ∀ k, (f x0).1 k ≥ x0.1 k ∧
    ∃ xk : @unit_cube n, dist x0 xk ≤ 1 / ↑(p0 +1) ∧ (f xk).1 k ≤ xk.1 k := by {
  let p := p0 + 1
  have ppos : 0 < p := by omega
  let SC := @sperner_cube_of_function n f p ppos
  obtain ⟨I, h3⟩ := weaker_cubical_sperner SC
  have h4 j : j ≤ n → ∃ i, SC.RL (I i) = j := by {
    intro h4
    exact h3.2.symm.subset h4
  }
  obtain ⟨i0, hi0⟩ := h4 n (Nat.le_refl n)
  let x0 := discrete_map SC.p (I i0)
  use x0
  intro k
  apply And.intro
  {
    apply (reduced_label_props_3 f x0 k).2
    have h6 : @rl_point _ f x0 = n := by exact hi0
    rw [h6]
    simp only [gt_iff_lt, Fin.is_lt]
  }
  obtain ⟨ik, hik⟩ := h4 k.1 k.is_le'
  let xk := discrete_map SC.p (I ik)
  use xk
  apply And.intro _ $ (reduced_label_props_3 f xk k).1 hik
  unfold x0 xk
  apply dist_discrete_map p ppos
  have h5 := le_add_one_of_simplex SC I h3.1
  intro k
  exact ⟨h5 i0 ik k, h5 ik i0 k⟩
}


theorem fixed_point_unit_cube (f : C(@unit_cube n, @unit_cube n)) : ∃ x, f x = x := by {
  obtain ⟨x0s, hx0⟩ := axiomOfChoice (nearby_points f)
  have hc1 : ∃ xx : @unit_cube n, ∃ (φ:ℕ → ℕ ), StrictMono φ ∧
      Filter.Tendsto (x0s ∘ φ ) Filter.atTop (nhds xx) := by {
    have hc1 : IsCompact (@unit_cube n) := isCompact_Icc
    let x0 : ℕ → Fin n → ℝ := fun i ↦ (x0s i).1
    have h2 : ∀ i, x0 i ∈ unit_cube := fun i ↦ (x0s i).2
    obtain ⟨a, ⟨ha, ⟨φ,h3⟩ ⟩ ⟩ := hc1.isSeqCompact h2
    use ⟨a, ha⟩
    use φ
    exact And.intro h3.1 $ tendsto_subtype_rng.mpr h3.2
  }
  obtain ⟨xxx, ⟨φ, h2⟩ ⟩ := hc1
  let y0 := x0s ∘ φ
  let g : Fin n → @unit_cube n → ℝ := fun k x ↦ x.1 k
  have hc2 k : Continuous (g k) := by {
    exact (continuous_apply k).comp continuous_subtype_val
  }
  have h3 k : xxx.1 k ≤ (f xxx).1 k := by {
    show g k xxx ≤ g k (f xxx)
    have h6 :=  (hc2 k).seqContinuous h2.2
    have h7 := (hc2 k).seqContinuous $ f.2.seqContinuous h2.2
    apply le_of_tendsto_of_tendsto' h6 h7
    exact fun i ↦ (hx0 (φ i) k).1
  }
  have h4 k : (f xxx).1 k ≤ xxx.1 k := by {
    show g k (f xxx) ≤ g k xxx
    have h5 n:= (hx0 (φ n) k).2
    obtain ⟨yk, h6⟩ := axiomOfChoice h5
    have h4 : Filter.Tendsto yk Filter.atTop (nhds xxx) := by {
      apply tendsto_of_tendsto_of_dist h2.2
      have h7 := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h7 _
      {
        intro i
        apply le_trans (h6 i).1
        simp only [Nat.cast_add, Nat.cast_one, one_div]
        apply inv_anti₀ (Nat.cast_add_one_pos i)
        simp only [add_le_add_iff_right, Nat.cast_le, h2.1.le_apply]
      }
      exact fun _ ↦ dist_nonneg
    }
    have h7 := (hc2 k).seqContinuous h4
    have h8 := (hc2 k).seqContinuous $ f.2.seqContinuous h4
    apply le_of_tendsto_of_tendsto' h8 h7
    exact fun i ↦ (h6 i).2
  }
  use xxx
  ext k
  apply le_antisymm (h4 k) (h3 k)
}
end

section
-- module Solutions.OAIQ231_RR.convex_homeos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


/-
some helper lemmas involving homeomorphisms.
-/


lemma homeo_unit_ball {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s)
    (hni : (interior s).Nonempty):
    Nonempty (s ≃ₜ Metric.closedBall (0: V) 1) := by {
  have h1 := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hcvx hni
  have h2 : Bornology.IsBounded s := IsCompact.isBounded hcmpct
  cases (h1 h2)
  rename_i e he
  have h4 := closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcmpct)
  have e2 := Homeomorph.image e s
  rw [h4] at he
  rw [he.2.1] at e2
  exact Nonempty.intro e2
}


theorem homeo_of_finrank_eq {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (hreq : Module.finrank ℝ V = Module.finrank ℝ W) :
    Nonempty (Metric.closedBall (0: V) 1 ≃ₜ Metric.closedBall (0: W) 1) := by {
  have L := ContinuousLinearEquiv.ofFinrankEq hreq
  let pL := L ⁻¹' (Metric.closedBall (0:W) 1)
  have hpL : pL = L.toHomeomorph ⁻¹' (Metric.closedBall (0:W) 1) := rfl
  have h4 : Convex ℝ pL := Convex.linear_preimage (convex_closedBall 0 1) L.toLinearMap
  have h5 : IsCompact pL := by {
    rw [hpL,Homeomorph.isCompact_preimage]
    exact isCompact_closedBall 0 1
  }
  have h6 : (interior pL).Nonempty := by {
    rw [hpL, ← Homeomorph.preimage_interior]
    refine (Function.Surjective.nonempty_preimage ?_).mpr ?_
    exact Homeomorph.surjective L.toHomeomorph
    use 0
    rw [interior_closedBall]
    {simp only [Metric.mem_ball, dist_self, zero_lt_one]}
    {exact Ne.symm (zero_ne_one' ℝ)}
  }
  have e1 : pL ≃ₜ Metric.closedBall (0:W) 1 := by {
    rw [hpL]
    exact L.toHomeomorph.sets hpL
  }
  have h7 := homeo_unit_ball _ h4 h5 h6
  cases h7
  rename_i e2
  apply Nonempty.intro
  exact e2.symm.trans e1
}


lemma unit_cube_homeo_unit_ball {n}
    : Nonempty (Set.Icc (0 : Fin n → ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin n → ℝ) 1 ) := by
  apply homeo_unit_ball _ (convex_Icc 0 1) isCompact_Icc
  have h1 : Set.Icc (0 : Fin n → ℝ) 1 = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x; simp [Set.mem_Icc, Pi.le_def]
  rw [h1, interior_pi_set Set.finite_univ]
  exact Set.univ_pi_nonempty_iff.mpr fun _ => by
    rw [interior_Icc]; exact ⟨1/2, by norm_num, by norm_num⟩

lemma homeo_unit_cube_of_convex_compact {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s: Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : s.Nonempty)
    : ∃ k, Nonempty (s ≃ₜ Set.Icc (0 : Fin k → ℝ) 1) := by {
  haveI := hne.coe_sort
  let W := affineSpan ℝ s
  obtain ⟨ps, hps⟩ := hne
  let pss : W := ⟨ps, mem_affineSpan ℝ hps⟩
  let g2 := AffineIsometryEquiv.constVSub ℝ pss
  let g1 : W → V := fun x ↦ x.1
  let s2 := g1 ⁻¹' s
  let s3 := g2.symm ⁻¹' s2
  have h32 : Convex ℝ s3 := by {
    exact hcvx.affine_preimage
      ((affineSpan ℝ s).subtype.comp
      (AffineIsometryEquiv.constVSub ℝ pss).symm.toAffineMap)
  }
  have h34 : (interior s3).Nonempty := by {
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top h32).mpr ?_
    unfold s3
    rw [←AffineIsometryEquiv.coe_toAffineEquiv]
    rw [← AffineSubspace.comap_span]
    rw [affineSpan_coe_preimage_eq_top]
    rfl
  }
  let g3 := g1.comp g2.symm
  have h4 : Topology.IsEmbedding g3 := by {
    apply Topology.IsEmbedding.subtypeVal.comp g2.symm.toHomeomorph.isEmbedding
  }
  have h5 : Set.MapsTo g3 s3 s := by {
    intro w h1
    unfold s3 s2 at h1
    rwa [Set.mem_preimage, Set.mem_preimage] at h1
  }
  have h6 : Function.Surjective (Set.MapsTo.restrict g3 s3 s h5) := by {
    refine (Set.MapsTo.restrict_surjective_iff h5).mpr ?_
    refine Set.SurjOn.comp_right ?_ ?_
    exact AffineIsometryEquiv.surjective g2.symm
    intro v h1
    refine (Set.mem_image g1 (g1 ⁻¹' s) v).mpr ?_
    have h11 : v ∈ affineSpan ℝ s := mem_affineSpan ℝ h1
    use ⟨v, h11⟩
    simp only [Set.mem_preimage]
    apply And.intro h1 rfl
  }
  let e1 := (h4.restrict h5).toHomeomorphOfSurjective h6
  have h31 : IsCompact s3 := by {
    have h51 : _ → IsCompact Set.univ := (Homeomorph.isCompact_image e1).mp
    simp only [Set.image_univ, EquivLike.range_eq_univ] at h51
    apply isCompact_iff_isCompact_univ.mpr
    apply h51 $ isCompact_iff_isCompact_univ.mp hcmpct
  }
  obtain ⟨e2⟩ := homeo_unit_ball s3 h32 h31 h34
  let k := Module.finrank ℝ W.direction
  obtain ⟨e3⟩ := @unit_cube_homeo_unit_ball k
  have h2 : k = Module.finrank ℝ (Fin k → ℝ) := (Module.finrank_fin_fun ℝ).symm
  obtain ⟨e4⟩ := homeo_of_finrank_eq h2
  let e5 := (e1.symm.trans e2).trans (e4.trans e3.symm)
  use k
  exact Nonempty.intro e5
}
end

section
-- module Solutions.OAIQ231_RR.brouwer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false



/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ContinuousPerturbedBallCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem closedBall_covered_by_continuous_perturbation {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (a : X) (r δ : ℝ) (hr : 0 ≤ r)
    (f : closedBall a r → X) (hf : Continuous f)
    (hdisp : ∀ x, dist (f x) x.val ≤ δ) :
    closedBall a (r - δ) ⊆ Set.range f := by
  intro z hz
  have hz' : ‖z - a‖ ≤ r - δ := by
    simpa only [mem_closedBall, dist_eq_norm] using! hz
  have hmaps (x : closedBall a r) : z - (f x - x.val) ∈ closedBall a r := by
    change dist (z - (f x - x.val)) a ≤ r
    calc
      _ = ‖(z - a) - (f x - x.val)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ ‖z - a‖ + ‖f x - x.val‖ := norm_sub_le _ _
      _ ≤ (r - δ) + δ := add_le_add hz'
        (by simpa only [dist_eq_norm] using! hdisp x)
      _ = r := by ring
  let T : C(closedBall a r, closedBall a r) :=
    ⟨fun x => ⟨z - (f x - x.val), hmaps x⟩,
      (continuous_const.sub (hf.sub continuous_subtype_val)).subtype_mk _⟩
  obtain ⟨u, hu⟩ := _root_.brouwer_fixed_point (closedBall a r)
    (convex_closedBall a r) (isCompact_closedBall a r)
    ⟨a, mem_closedBall_self hr⟩ T
  have heq := congrArg (fun x : closedBall a r => x.val) hu
  change z - (f u - u.val) = u.val at heq
  refine ⟨u, ?_⟩
  calc
    f u = (f u - u.val) + u.val := (sub_add_cancel _ _).symm
    _ = (f u - u.val) + (z - (f u - u.val)) :=
      congrArg (fun w => (f u - u.val) + w) heq.symm
    _ = z := by abel

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLimitFlatness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local flatness of active-region limits

Finite-stage charts lift into the limiting parameterization with controlled
tangential displacement and normal error. These estimates bound the height of the
limit over each active fitting plane and, conversely, approximate nearby points
of that plane by points of the limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology EuclideanGeometry

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem exists_active_region_limit_chart_with_normal_error
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q) :
    ∃ H : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      Continuous H ∧ Set.range H ⊆ Set.range f ∧
      (∀ u, dist ((S q).direction.orthogonalProjectionOnto (H u)) u.val ≤
        ((17039360 * ε) / 63) * q.radius) ∧
      (∀ u, infDist (H u) (S q : Set (Ambient d)) ≤ (534000 * ε) * q.radius) ∧
      (∀ u, H u ∈ closedBall q.center (4 * q.radius)) := by
  have hqi : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  obtain ⟨g, hg, _, hcoords, _⟩ :=
    activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth q hqi
  obtain ⟨j, hj, hjF⟩ := exists_active_region_finite_chart_lift μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit q.depth g 2 hg
    (by rintro _ ⟨a, rfl⟩; exact (hcoords a).1)
  let H := fun a => f (j a)
  have hdisp (a) : dist (H a) (g a) ≤ ((17039360 * ε) / 63) * q.radius := by
    have ht := hmodel.2.2.2.1 q.depth (j a)
    rw [hjF a, dist_comm] at ht
    exact ht
  refine ⟨H, hmodel.1.comp hj.continuous, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨j a, rfl⟩
  · intro a
    rw [← (hcoords a).2.1]
    have hp := (S q).direction.norm_starProjection_apply_le (H a - g a)
    rw [map_sub] at hp
    exact hp.trans (hdisp a)
  · intro a
    have hi : infDist (H a) (S q : Set (Ambient d)) ≤
        infDist (g a) (S q : Set (Ambient d)) + dist (H a) (g a) :=
      infDist_le_infDist_add_dist
    have hgplane := (hcoords a).2.2.1
    nlinarith [hdisp a, q.radius_pos]
  · intro a
    have ht := dist_triangle (H a) (g a) q.center
    have hgball : dist (g a) q.center ≤ 3 * q.radius := (hcoords a).2.2.2
    have hB : (17039360 * ε) / 63 ≤ 1 / 2 := by nlinarith
    have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
    change dist (H a) q.center ≤ 4 * q.radius
    nlinarith [hdisp a, q.radius_pos]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRequestedScaleSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_cell_at_requested_radius {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k / 16)
    (hD : cellRegionStoppingScale μ R hR k z Good p < r / 4) :
    ∃ t : ℕ, ∃ q ∈ activeLevelIndex μ R hR k z Good t,
      16 * r ≤ q.radius ∧ q.radius ≤ 1024 * r ∧
      dist p q.center < (131 / 64 : ℝ) * q.radius := by
  obtain ⟨t, htlo, hthi⟩ := exists_lattice_radius_above R k (16 * r) (by positivity) (by linarith)
  have hDlevel : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + (t + 1)) := by
    rw [← Nat.add_assoc, latticeRadius_succ]
    linarith
  obtain ⟨i, hi, hpi⟩ := exists_active_level_center_of_small_stopping_scale
    μ R hR k z Good (t + 1) p hDlevel
  have hiF : i ∈ activeLevelIndex μ R hR k z Good (t + 1) :=
    (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mpr hi
  obtain ⟨q, hq, hscale, hcenters, _⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hiF
  have hqdepth := ((mem_activeLevelIndex μ R hR k z Good t q).mp hq).1
  have hqr : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hqdepth]
  have hir : i.radius = latticeRadius R (k + (t + 1)) := by
    simp only [SupportCellDescendant.radius, hi.1]
  rw [← hir] at hpi
  refine ⟨t, q, hq, ?_, ?_, ?_⟩
  · rwa [hqr]
  · rw [hqr]
    linarith
  · have ht := dist_triangle p i.center q.center
    nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionAllScaleForwardFlatness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Forward flatness at arbitrary scales

Parallel translates of fitting planes pass through the requested center while
their height errors remain controlled by the original plane distances. Active-cell
selection handles small radii, and the root plane handles large radii, both with
the same quantitative forward-flatness bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem infDist_parallel_plane_through_point_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (p x : Ambient d) :
    infDist x (AffineSubspace.mk' p S.direction : Set (Ambient d)) ≤
      infDist x (S : Set (Ambient d)) + infDist p (S : Set (Ambient d)) := by
  rw [infDist_affine_translate, submodule_infDist_eq_normal_projection]
  exact normal_projection_bound_by_plane_distances S x p

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem active_region_limit_height_on_enlarged_active_ball
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (x : Ambient d) (hx : x ∈ Set.range f)
    (hlocal : x ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius)) :
    infDist x (S q : Set (Ambient d)) ≤ (534000 * ε) * q.radius := by
  obtain ⟨u, rfl⟩ := hx
  let y := activeRegionParameterMap μ R hR k z Good S hS q.depth u
  have hy : y ∈ activeRegionSurface μ R hR k z Good S hS q.depth := by
    rw [activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  have htail : dist y (f u) ≤ ((17039360 * ε) / 63) * q.radius := hmodel.2.2.2.1 q.depth u
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by nlinarith
  have hylocal : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have ht := dist_triangle y (f u) q.center
    have hxq : dist (f u) q.center ≤ (17 / 8 : ℝ) * q.radius := hlocal
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith [mul_le_mul_of_nonneg_right hB q.radius_pos.le]
  have hqi : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hc := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth q hqi
  have hyplane := hc.height_on_inner_ball q (S q) ε _ y hy hylocal
  have hdist : infDist (f u) (S q : Set (Ambient d)) ≤
      infDist y (S q : Set (Ambient d)) + dist (f u) y := infDist_le_infDist_add_dist
  rw [dist_comm (f u) y] at hdist
  nlinarith [q.radius_pos]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ContinuousChartInnerCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inner projection coverage of continuous charts

A chart whose projected displacement is small covers an inner ball in the plane direction.
Bounds on the chart height and the base point's distance to the plane keep the covering
points inside the required ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem continuous_chart_inner_projection_coverage {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : S.direction) (R : ℝ) (H : closedBall c R → Ambient d)
    (hH : Continuous H) (surface : Set (Ambient d)) (hRange : Set.range H ⊆ surface)
    (p : Ambient d) (ρ e a b : ℝ) (hρ : 0 ≤ ρ)
    (hroom : dist (S.direction.orthogonalProjectionOnto p) c + 2 * ρ ≤ R)
    (hDisp : ∀ u, dist (S.direction.orthogonalProjectionOnto (H u)) u.val ≤ e)
    (hHeight : ∀ u, infDist (H u) (S : Set (Ambient d)) ≤ a)
    (hBase : infDist p (S : Set (Ambient d)) ≤ b)
    (he : e ≤ ρ) (hab : a + b ≤ ρ) :
    closedBall (S.direction.orthogonalProjectionOnto p) ρ ⊆
      S.direction.orthogonalProjectionOnto '' (surface ∩ closedBall p (2 * ρ)) := by
  let P := S.direction
  have hsub : closedBall (P.orthogonalProjectionOnto p) (2 * ρ) ⊆ closedBall c R := by
    intro u hu
    have ht := dist_triangle u (P.orthogonalProjectionOnto p) c
    have hud : dist u (P.orthogonalProjectionOnto p) ≤ 2 * ρ := hu
    change dist u c ≤ R
    linarith
  let j : closedBall (P.orthogonalProjectionOnto p) (2 * ρ) → closedBall c R :=
    fun u => ⟨u.val, hsub u.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hCont : Continuous (fun u => P.orthogonalProjectionOnto (H (j u))) :=
    P.orthogonalProjectionOnto.continuous.comp (hH.comp hj)
  intro z hz
  have hz' : z ∈ closedBall (P.orthogonalProjectionOnto p) (2 * ρ - e) := by
    have hzd : dist z (P.orthogonalProjectionOnto p) ≤ ρ := hz
    change dist z (P.orthogonalProjectionOnto p) ≤ _
    linarith
  obtain ⟨u, hu⟩ := closedBall_covered_by_continuous_perturbation
    (P.orthogonalProjectionOnto p) (2 * ρ) e (by positivity)
    (fun u => P.orthogonalProjectionOnto (H (j u))) hCont (fun u => hDisp (j u)) hz'
  change P.orthogonalProjectionOnto (H (j u)) = z at hu
  refine ⟨H (j u), ⟨hRange ⟨j u, rfl⟩, ?_⟩, hu⟩
  have hprojected : dist (P.starProjection (H (j u))) (P.starProjection p) ≤ ρ := by
    change dist (P.orthogonalProjectionOnto (H (j u))) (P.orthogonalProjectionOnto p) ≤ ρ
    rw [hu]
    exact hz
  have ht := dist_le_projection_add_plane_distances S hS (H (j u)) p
  change dist (H (j u)) p ≤ 2 * ρ
  linarith [hHeight (j u)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLowMatchedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched projections at low stopping scales

An active cell at the requested radius supplies a fitting direction with small
forward height error. Its limiting chart also covers a definite projected ball,
so both estimates hold for the same plane through the requested center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_region_low_matched_projection_oai {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 72057594037927936) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrtop : r ≤ latticeRadius R k / 2097152)
    (hD : cellRegionStoppingScale μ R hR k z Good p ≤ 16384 * r) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ (281474976710656 * ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨t, q, hqF, hqlo, hqhi, hnear⟩ := exists_active_cell_at_requested_radius
    μ R hR k z Good p (131072 * r) (by positivity) (by linarith) (by linarith)
  have hq := ((mem_activeLevelIndex μ R hR k z Good t q).mp hqF).2
  let P := (S q).direction
  let : Nonempty (S q) := (hS q).1.to_subtype
  have hpq : p ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    change dist p q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith [q.radius_pos]
  have hpheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq p hp hpq
  obtain ⟨H, hH, hRange, hDisp, hHeight, _⟩ :=
    exists_active_region_limit_chart_with_normal_error μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq
  have hroom : dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) +
      2 * (r / 32) ≤ (5 / 2 : ℝ) * q.radius := by
    have hpj := P.norm_starProjection_apply_le (p - q.center)
    rw [map_sub] at hpj
    change dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) ≤ dist p q.center at hpj
    nlinarith
  have hAreaBudget : (534000 * ε) * q.radius + (534000 * ε) * q.radius ≤ r / 32 := by
    have hcoeff : 1068000 * 134217728 * ε ≤ 1 / 32 := by nlinarith
    have hqr := mul_le_mul_of_nonneg_left hqhi hε.le
    have hrr := mul_le_mul_of_nonneg_right hcoeff hr.le
    nlinarith
  have hDispBudget : ((17039360 * ε) / 63) * q.radius ≤ r / 32 := by
    nlinarith [mul_pos hε q.radius_pos]
  have hProjected := continuous_chart_inner_projection_coverage (S q) (hS q).1
    (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) H hH
    (Set.range f) hRange p (r / 32) (((17039360 * ε) / 63) * q.radius)
    ((534000 * ε) * q.radius) ((534000 * ε) * q.radius) (by positivity)
    hroom hDisp hHeight hpheight hDispBudget hAreaBudget
  rw [show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS q).2, ?_, hProjected⟩
  intro x hx
  have hxq : x ∈ closedBall q.center ((17 / 8 : ℝ) * q.radius) := by
    have ht := dist_triangle x p q.center
    have hxp : dist x p ≤ 1024 * r := hx.2
    change dist x q.center ≤ (17 / 8 : ℝ) * q.radius
    nlinarith
  have hxheight := active_region_limit_height_on_enlarged_active_ball μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq x hx.1 hxq
  have hparallel := infDist_parallel_plane_through_point_le (S q) p x
  change infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ _ at hparallel
  nlinarith [mul_le_mul_of_nonneg_left hqhi hε.le, mul_pos hε hr]

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_active_region_low_matched_projection_oai := @OAI.RieszRectifiability.exists_active_region_low_matched_projection_oai
