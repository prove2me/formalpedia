-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_active_region_positive_matched_projection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:19.540479+00:00
-- url     : https://prove2.me/submissions/72a27c37-863b-4696-8395-30aeca6c4880

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
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

theorem finiteProjectionAverage_eq_self (F : Finset ι) (θ : ι → Ambient d → ℝ)
    (π : ι → Ambient d → Ambient d) (x : Ambient d)
    (hθ : ∀ i ∈ F, θ i x = 0) : finiteProjectionAverage F θ π x = x := by
  unfold finiteProjectionAverage
  have hsum : (∑ i ∈ F, θ i x • (π i x - x)) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hθ i hi, zero_smul])
  rw [hsum, add_zero]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PerturbedBallCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ball coverage by a Lipschitz perturbation

A map with bounded displacement whose error from the identity is a strict
contraction covers a smaller concentric closed ball. A fixed point of the
associated correction map provides the preimage of each target point.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem closedBall_covered_by_lipschitz_perturbation {X : Type*}
    [NormedAddCommGroup X] [CompleteSpace X]
    (a : X) (r δ : ℝ) (hr : 0 ≤ r) (K : ℝ≥0) (hK : K < 1)
    (f : closedBall a r → X)
    (hdisp : ∀ x, dist (f x) x.val ≤ δ)
    (herr : LipschitzWith K (fun x : closedBall a r => f x - x.val)) :
    closedBall a (r - δ) ⊆ Set.range f := by
  intro z hz
  have hz' : ‖z - a‖ ≤ r - δ := by simpa only [mem_closedBall, dist_eq_norm] using! hz
  have hmaps (x : closedBall a r) : z - (f x - x.val) ∈ closedBall a r := by
    change dist (z - (f x - x.val)) a ≤ r
    calc
      _ = ‖(z - a) - (f x - x.val)‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ ≤ ‖z - a‖ + ‖f x - x.val‖ := norm_sub_le _ _
      _ ≤ (r - δ) + δ := add_le_add hz' (by simpa only [dist_eq_norm] using! hdisp x)
      _ = r := by ring
  let T : closedBall a r → closedBall a r :=
    fun x => ⟨z - (f x - x.val), hmaps x⟩
  have hLip : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (z - (f x - x.val)) (z - (f y - y.val)) ≤ K * dist x y
    have heq : (z - (f x - x.val)) - (z - (f y - y.val)) =
        -((f x - x.val) - (f y - y.val)) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    simpa only [dist_eq_norm] using! herr.dist_le_mul x y
  let : CompleteSpace (closedBall a r) :=
    (show IsClosed (closedBall a r) from isClosed_closedBall).isComplete.completeSpace_coe
  have hT : ContractingWith K T := ⟨hK, hLip⟩
  obtain ⟨u, hu, _, _⟩ := hT.exists_fixedPoint ⟨a, mem_closedBall_self hr⟩ (edist_ne_top _ _)
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionTransitionDistortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionTransitionMap_surface_dist_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (s j : ℕ) (x y : Ambient d)
    (hx : x ∈ activeRegionSurface μ R hR k z Good S hS s)
    (hy : y ∈ activeRegionSurface μ R hR k z Good S hS s) :
    (1 / 4 : ℝ) ^ j * dist x y ≤
        dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
          (activeRegionTransitionMap μ R hR k z Good S hS s j y) ∧
      dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
        (activeRegionTransitionMap μ R hR k z Good S hS s j y) ≤ 2 ^ j * dist x y := by
  induction j with
  | zero =>
    simp only [pow_zero, one_mul, activeRegionTransitionMap, id_eq]
    exact ⟨le_rfl, le_rfl⟩
  | succ j ih =>
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit (s + j)
    have hTx : activeRegionTransitionMap μ R hR k z Good S hS s j x ∈
        activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨x, hx, rfl⟩
    have hTy : activeRegionTransitionMap μ R hR k z Good S hS s j y ∈
        activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨y, hy, rfl⟩
    have hstep := activeLevelProjectionMap_surface_dist_bounds μ R hR k z Good (s + j)
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS (s + j))
      hcharts hsmall (activeRegionTransitionMap μ R hR k z Good S hS s j x)
      (activeRegionTransitionMap μ R hR k z Good S hS s j y) hTx hTy
    constructor
    · calc
        (1 / 4 : ℝ) ^ (j + 1) * dist x y = (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ j * dist x y) := by
          rw [pow_succ]
          ring
        _ ≤ (1 / 4 : ℝ) * dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
            (activeRegionTransitionMap μ R hR k z Good S hS s j y) :=
          mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _ ≤ _ := hstep.1
    · calc
        _ ≤ 2 * dist (activeRegionTransitionMap μ R hR k z Good S hS s j x)
            (activeRegionTransitionMap μ R hR k z Good S hS s j y) := hstep.2
        _ ≤ 2 * (2 ^ j * dist x y) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = 2 ^ (j + 1) * dist x y := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionTransitionResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeRegionTransitionMap_surface_residual_le {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (s j : ℕ) (x y : Ambient d)
    (hx : x ∈ activeRegionSurface μ R hR k z Good S hS s)
    (hy : y ∈ activeRegionSurface μ R hR k z Good S hS s) :
    ‖(activeRegionTransitionMap μ R hR k z Good S hS s j x -
      activeRegionTransitionMap μ R hR k z Good S hS s j y) - (x - y)‖ ≤
        (72 * activeProjectionError d ε) * ((2 : ℝ) ^ j - 1) * dist x y := by
  let K := 72 * activeProjectionError d ε
  have hK : 0 ≤ K := by dsimp [K, activeProjectionError] <;> positivity
  change _ ≤ K * ((2 : ℝ) ^ j - 1) * dist x y
  induction j with
  | zero => simp only [activeRegionTransitionMap, id_eq, sub_self, norm_zero, pow_zero, mul_zero, zero_mul, le_refl]
  | succ j ih =>
    let T := activeRegionTransitionMap μ R hR k z Good S hS s j
    let σ := activeLevelProjectionMap μ R hR k z Good (s + j + 1) S hS
    have hTx : T x ∈ activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨x, hx, rfl⟩
    have hTy : T y ∈ activeRegionSurface μ R hR k z Good S hS (s + j) := by
      rw [activeRegionSurface_add]
      exact ⟨y, hy, rfl⟩
    have hcharts := activeRegionSurface_charts μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit (s + j)
    have hstep := activeLevelProjectionMap_surface_residual_le μ R hR k z Good (s + j)
      S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS (s + j))
      hcharts (T x) (T y) hTx hTy
    have hdist := (activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit s j x y hx hy).2
    change ‖(σ (T x) - σ (T y)) - (T x - T y)‖ ≤ K * dist (T x) (T y) at hstep
    change dist (T x) (T y) ≤ (2 : ℝ) ^ j * dist x y at hdist
    change ‖(T x - T y) - (x - y)‖ ≤ K * ((2 : ℝ) ^ j - 1) * dist x y at ih
    change ‖(σ (T x) - σ (T y)) - (x - y)‖ ≤ _
    have hid : (σ (T x) - σ (T y)) - (x - y) =
        ((σ (T x) - σ (T y)) - (T x - T y)) + ((T x - T y) - (x - y)) := by abel
    calc
      _ ≤ ‖(σ (T x) - σ (T y)) - (T x - T y)‖ + ‖(T x - T y) - (x - y)‖ := by
        rw [hid]
        exact norm_add_le _ _
      _ ≤ K * dist (T x) (T y) + K * ((2 : ℝ) ^ j - 1) * dist x y := add_le_add hstep ih
      _ ≤ K * ((2 : ℝ) ^ j * dist x y) + K * ((2 : ℝ) ^ j - 1) * dist x y :=
        add_le_add (mul_le_mul_of_nonneg_left hdist hK) le_rfl
      _ = K * ((2 : ℝ) ^ (j + 1) - 1) * dist x y := by rw [pow_succ]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveScaleProjectionCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection charts at positive stopping scales

Transporting a local surface chart through three active-region transitions gives
a bi-Lipschitz chart containing the limit surface where the stopping scale stays
positive. Its tangential displacement and normal component retain quantitative
Lipschitz bounds controlled by the active projection error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_scale_projection_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (A : Set (Ambient d))
    (hnear : A ⊆ closedBall q.center ((17 / 8 : ℝ) * q.radius))
    (hscale : ∀ x ∈ A, q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ H : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      LipschitzWith 16 H ∧ AntilipschitzWith 64 H ∧
      LipschitzWith (Real.toNNReal (1008 * activeProjectionError d ε))
        (fun u => (S q).direction.orthogonalProjectionOnto (H u) - u.val) ∧
      LipschitzWith (Real.toNNReal (1012 * activeProjectionError d ε))
        (fun u => ((S q).directionᗮ : Submodule ℝ (Ambient d)).starProjection (H u)) ∧
      (∀ u, dist ((S q).direction.orthogonalProjectionOnto (H u)) u.val ≤
        (2 * ((17039360 * ε) / 63)) * q.radius) ∧
      Set.range H ⊆ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∧
      Set.range f ∩ A ⊆ Set.range H := by
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨g, hgLip, hgNormal, hcoords, hgCapture⟩ := hcharts q hqF
  let T := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3
  let P := (S q).direction
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hres (u v) : ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤
      (1008 * activeProjectionError d ε) * dist u v := by
    have h := activeRegionTransitionMap_surface_residual_le μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit q.depth 3 (g u) (g v) (hcoords u).1 (hcoords v).1
    have hb := hgLip.dist_le_mul u v
    norm_num at h hb
    change ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤ _ at h
    nlinarith [mul_le_mul_of_nonneg_left hb
      (show 0 ≤ 504 * activeProjectionError d ε by positivity)]
  have hprojected : LipschitzWith (Real.toNNReal (1008 * activeProjectionError d ε))
      (fun u => P.orthogonalProjectionOnto (T (g u)) - u.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    change ‖(P.starProjection (T (g u)) - (u.val : Ambient d)) -
      (P.starProjection (T (g v)) - (v.val : Ambient d))‖ ≤ _
    have hpu : P.starProjection (g u) = (u.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoords u).2.1
    have hpv : P.starProjection (g v) = (v.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoords v).2.1
    have hid : (P.starProjection (T (g u)) - (u.val : Ambient d)) -
        (P.starProjection (T (g v)) - (v.val : Ambient d)) =
        P.starProjection ((T (g u) - T (g v)) - (g u - g v)) := by
      rw [map_sub, map_sub, map_sub, hpu, hpv]
      abel
    rw [hid]
    exact (P.norm_starProjection_apply_le _).trans (hres u v)
  have hnormal : LipschitzWith (Real.toNNReal (1012 * activeProjectionError d ε))
      (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (T (g u))) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← map_sub]
    have hb := hgNormal.dist_le_mul u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← map_sub] at hb
    let e := (T (g u) - T (g v)) - (g u - g v)
    have hid : T (g u) - T (g v) = e + (g u - g v) := by dsimp [e]; abel
    calc
      _ ≤ ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection e‖ +
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (g u - g v)‖ := by
        rw [hid, map_add]
        exact norm_add_le _ _
      _ ≤ ‖e‖ + (4 * activeProjectionError d ε) * dist u v :=
        add_le_add ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le e) hb
      _ ≤ (1012 * activeProjectionError d ε) * dist u v := by
        have h := hres u v
        change ‖e‖ ≤ _ at h
        linarith
  have hdist (u v) :
      (1 / 64 : ℝ) * dist (g u) (g v) ≤ dist (T (g u)) (T (g v)) ∧
      dist (T (g u)) (T (g v)) ≤ 8 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit q.depth 3 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 16 (T ∘ g) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hbase := hgLip.dist_le_mul u v
    norm_num at hbase ⊢
    have h := (hdist u v).2
    change dist (T (g u)) (T (g v)) ≤ 16 * dist u v
    linarith
  have hsep : AntilipschitzWith 64 (T ∘ g) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hproj : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2.1, ← (hcoords v).2.1]
      have h := (S q).direction.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    have h := (hdist u v).1
    norm_num
    change dist u v ≤ 64 * dist (T (g u)) (T (g v))
    linarith
  have hinto : Set.range (T ∘ g) ⊆ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) := by
    rintro _ ⟨u, rfl⟩
    rw [activeRegionSurface_add]
    exact ⟨g u, (hcoords u).1, rfl⟩
  have hdisplacement (u) : dist (P.orthogonalProjectionOnto (T (g u))) u.val ≤
      (2 * ((17039360 * ε) / 63)) * q.radius := by
    have h := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
      f hmodel q.depth 3 (g u) (hcoords u).1
    change dist (T (g u)) (g u) ≤ (2 * ((17039360 * ε) / 63)) * q.radius at h
    rw [← (hcoords u).2.1]
    have hp := P.norm_starProjection_apply_le (T (g u) - g u)
    rw [map_sub] at hp
    exact hp.trans h
  have hrq := q.radius_pos
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) ((17039360 * ε) / 63) (by positivity)
    hmodel.2.2.2.1 A (q.radius / 8192) hscale (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB hrq.le
      nlinarith)
  refine ⟨T ∘ g, hLip, hsep, hprojected, hnormal, hdisplacement, hinto, ?_⟩
  intro x hx
  have hxN : x ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) :=
    (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hxN
  obtain ⟨y, hy, hTy⟩ := hxN
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
    f hmodel q.depth 3 y hy
  change dist (T y) y ≤ (2 * ((17039360 * ε) / 63)) * q.radius at hmove
  rw [hTy] at hmove
  have hBm := mul_le_mul_of_nonneg_right hB hrq.le
  have hyq : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have hxy := dist_triangle y x q.center
    rw [dist_comm y x] at hxy
    have hxq : dist x q.center ≤ (17 / 8 : ℝ) * q.radius := hnear hx.2
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hyg : y ∈ Set.range g := (hgCapture ▸ (show y ∈
    activeRegionSurface μ R hR k z Good S hS q.depth ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hyq⟩)).1
  obtain ⟨u, hu⟩ := hyg
  refine ⟨u, ?_⟩
  change T (g u) = x
  rw [hu]
  exact hTy

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveScaleBallSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_parent_at_stopping_scale {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    ∃ q : SupportCellDescendant μ R hR k z, activeRegionCell Good q ∧
      q.radius ≤ 4096 * cellRegionStoppingScale μ R hR k z Good x ∧
      64 * cellRegionStoppingScale μ R hR k z Good x < q.radius ∧
      dist x q.center < (131 / 64 : ℝ) * q.radius := by
  let δ := cellRegionStoppingScale μ R hR k z Good x
  let t := annularLatticeDepth R k (8 * δ) (by positivity)
  have ht : latticeRadius R (k + t) ≤ δ := by
    have h := annularLatticeDepth_radius_upper R k (8 * δ) (by positivity)
    change latticeRadius R (k + t) ≤ (8 * δ) / 8 at h
    linarith
  have htpos : 2 ≤ t := by
    by_contra h
    have hle := latticeRadius_antitone R hR.le (show k + t ≤ k + 1 by omega)
    change δ < latticeRadius R (k + 1) at hsmall
    linarith
  have hδ : δ < latticeRadius R (k + (t - 1)) := by
    by_contra h
    have hm := annularLatticeDepth_minimal R k (8 * δ) (by positivity) (t - 1)
      (by linarith [le_of_not_gt h])
    change t ≤ t - 1 at hm
    omega
  obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good
    (t - 1) x hδ
  obtain ⟨q, hqd, hsub, hc⟩ := i.exists_ancestor_at_depth (t - 2) (by have := hi.1; omega)
  have hqA := activeRegionCell_ancestor Good i q hi.2 (by have := hi.1; omega) hsub
  have hid : i.depth = q.depth + 1 := by have := hi.1; omega
  have hri : i.radius = latticeRadius R (k + (t - 1)) := by
    simp only [SupportCellDescendant.radius, hi.1]
  have hrq : q.radius = 64 * i.radius := by
    change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
    rw [hid, ← Nat.add_assoc, latticeRadius_succ]
    ring
  have hrt : i.radius = 64 * latticeRadius R (k + t) := by
    rw [hri, show k + t = (k + (t - 1)) + 1 by omega, latticeRadius_succ]
    ring
  have hdist := q.dist_center_of_mem i.center hc
  have htri := dist_triangle x i.center q.center
  rw [← hri] at hxi hδ
  refine ⟨q, hqA, ?_, ?_, ?_⟩
  · change q.radius ≤ 4096 * δ
    nlinarith
  · change 64 * δ < q.radius
    nlinarith
  · nlinarith

theorem active_stopping_ball_chart_geometry {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (q : SupportCellDescendant μ R hR k z)
    (hrhi : q.radius ≤ 4096 * cellRegionStoppingScale μ R hR k z Good x)
    (hrlo : 64 * cellRegionStoppingScale μ R hR k z Good x < q.radius)
    (hnear : dist x q.center < (131 / 64 : ℝ) * q.radius) :
    closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16) ⊆
      closedBall q.center ((17 / 8 : ℝ) * q.radius) ∧
    ∀ y ∈ closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16),
      q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good y := by
  have hr := q.radius_pos
  constructor
  · intro y hy
    have hyx : dist y x ≤ cellRegionStoppingScale μ R hR k z Good x / 16 := hy
    have htri := dist_triangle y x q.center
    change dist y q.center ≤ (17 / 8 : ℝ) * q.radius
    linarith
  · intro y hy
    have hyx : dist y x ≤ cellRegionStoppingScale μ R hR k z Good x / 16 := hy
    have hD := cellRegionStoppingScale_le_add_dist μ R hR k z Good x y
    rw [dist_comm x y] at hD
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ChartNormalCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem normal_projection_bound_on_chart_range {X : Type*} [PseudoMetricSpace X] {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (H : X → Ambient d) (K L : ℝ≥0)
    (hNormal : LipschitzWith K (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u)))
    (hSep : AntilipschitzWith L H)
    (x : Ambient d) (hx : x ∈ Set.range H) (y : Ambient d) (hy : y ∈ Set.range H) :
    ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      ((K * L : ℝ≥0) : ℝ) * dist x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have h := hNormal.dist_le_mul u v
  rw [dist_eq_norm, ← map_sub] at h
  calc
    _ ≤ (K : ℝ) * dist u v := h
    _ ≤ (K : ℝ) * ((L : ℝ) * dist (H u) (H v)) :=
      mul_le_mul_of_nonneg_left (hSep.le_mul_dist u v) K.coe_nonneg
    _ = _ := by rw [NNReal.coe_mul]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_CenteredPerturbedBallCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centered coverage for perturbed charts

Lipschitz perturbations of the identity cover balls centered at any parameter
with sufficient room in the domain. Applied to tangential projection, this gives
a disk covered by the portion of the surface inside a controlled ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem centered_ball_covered_by_lipschitz_perturbation {X : Type*}
    [NormedAddCommGroup X] [CompleteSpace X]
    (c : X) (R : ℝ) (f : closedBall c R → X) (K : ℝ≥0) (hK : K < 1)
    (herr : LipschitzWith K (fun u => f u - u.val))
    (a : closedBall c R) (r : ℝ) (hr : 0 ≤ r) (hroom : dist a.val c + r ≤ R) :
    ∀ z ∈ closedBall (f a) ((1 - (K : ℝ)) * r),
      ∃ u : closedBall c R, dist u a ≤ r ∧ f u = z := by
  have hsub : closedBall a.val r ⊆ closedBall c R := by
    intro x hx
    have hx' : dist x a.val ≤ r := hx
    change dist x c ≤ R
    exact (dist_triangle x a.val c).trans (by linarith)
  let j : closedBall a.val r → closedBall c R := fun u => ⟨u.val, hsub u.property⟩
  let g : closedBall a.val r → X := fun u => f (j u) - f a + a.val
  have hdisp : ∀ u, dist (g u) u.val ≤ (K : ℝ) * r := by
    intro u
    have hid : g u - u.val = (f (j u) - (j u).val) - (f a - a.val) := by
      dsimp [g, j]
      abel
    rw [dist_eq_norm, hid]
    have h := (herr.dist_le_mul (j u) a).trans
      (mul_le_mul_of_nonneg_left (show dist (j u) a ≤ r from u.property) K.coe_nonneg)
    simpa only [dist_eq_norm] using! h
  have hLip : LipschitzWith K (fun u : closedBall a.val r => g u - u.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hid : (g u - u.val) - (g v - v.val) =
        (f (j u) - (j u).val) - (f (j v) - (j v).val) := by
      dsimp [g, j]
      abel
    rw [dist_eq_norm, hid]
    simpa only [dist_eq_norm] using! herr.dist_le_mul (j u) (j v)
  intro z hz
  have hz' : z - f a + a.val ∈ closedBall a.val (r - (K : ℝ) * r) := by
    have hd : dist (z - f a + a.val) a.val = dist z (f a) := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [mem_closedBall, hd]
    have hzr : dist z (f a) ≤ (1 - (K : ℝ)) * r := hz
    nlinarith
  obtain ⟨u, hu⟩ := closedBall_covered_by_lipschitz_perturbation a.val r ((K : ℝ) * r)
    hr K hK g hdisp hLip hz'
  refine ⟨j u, u.property, ?_⟩
  change f (j u) - f a + a.val = z - f a + a.val at hu
  exact sub_left_inj.mp (add_right_cancel hu)

theorem centered_projection_disk_in_surface_ball {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (c : P) (R : ℝ)
    (H : closedBall c R → Ambient d) (K L : ℝ≥0)
    (hK : (K : ℝ) ≤ 1 / 2) (hL : (L : ℝ) ≤ 1 / 2)
    (hError : LipschitzWith K (fun u => P.orthogonalProjectionOnto (H u) - u.val))
    (hNormal : LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u)))
    (a : closedBall c R) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hroom : dist a.val c + 2 * ρ ≤ R)
    (surface : Set (Ambient d)) (hSurface : ∀ u, dist u a ≤ 2 * ρ → H u ∈ surface) :
    closedBall (P.orthogonalProjectionOnto (H a)) ρ ⊆
      P.orthogonalProjectionOnto '' (surface ∩ closedBall (H a) (2 * ρ)) := by
  have hKone : K < 1 := by
    have hreal : (K : ℝ) < 1 := by linarith
    exact_mod_cast hreal
  intro z hz
  have hz' : z ∈ closedBall (P.orthogonalProjectionOnto (H a)) ((1 - (K : ℝ)) * (2 * ρ)) := by
    have hdist : dist z (P.orthogonalProjectionOnto (H a)) ≤ ρ := hz
    change dist z (P.orthogonalProjectionOnto (H a)) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hK hρ]
  obtain ⟨u, hua, hu⟩ := centered_ball_covered_by_lipschitz_perturbation c R
    (fun v => P.orthogonalProjectionOnto (H v)) K hKone hError a (2 * ρ)
    (by positivity) hroom z hz'
  change P.orthogonalProjectionOnto (H u) = z at hu
  refine ⟨H u, ⟨hSurface u hua, ?_⟩, hu⟩
  have hp : ‖P.starProjection (H u - H a)‖ ≤ ρ := by
    rw [map_sub]
    change dist (P.orthogonalProjectionOnto (H u)) (P.orthogonalProjectionOnto (H a)) ≤ ρ
    rw [hu]
    exact hz
  have hn := hNormal.dist_le_mul u a
  rw [dist_eq_norm, ← map_sub] at hn
  have ht := norm_add_le (P.starProjection (H u - H a))
    ((Pᗮ : Submodule ℝ (Ambient d)).starProjection (H u - H a))
  rw [P.starProjection_add_starProjection_orthogonal] at ht
  change dist (H u) (H a) ≤ 2 * ρ
  rw [dist_eq_norm]
  have hnr : (L : ℝ) * dist u a ≤ ρ := by
    have hb := mul_le_mul_of_nonneg_left hua L.coe_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hL hρ]
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveMatchedProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched projection at positive stopping scales

A local chart at a positive stopping scale supplies an approximating plane and
covers a disk in that plane by projecting the nearby limit surface. The same
plane controls the surface's normal deviation on the larger comparison ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_matched_projection_oai {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 4096)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r)
    (hrsmall : 1024 * r ≤ cellRegionStoppingScale μ R hR k z Good p / 16) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
          (67108864 * activeProjectionError d ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  let D := cellRegionStoppingScale μ R hR k z Good p
  let B := (17039360 * ε) / 63
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hweak : activeProjectionError d ε ≤ 1 / 128 := by linarith
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good p q hqhi hqlo hnear
  obtain ⟨H, hLip, hSep, hError, hNormal, hDisp, hFinite, hCover⟩ :=
    exists_active_region_positive_scale_projection_chart μ R hR k z Good S hS
      ε hε hεtiny hweak hfit f hmodel q hq (closedBall p (D / 16)) hball hscale
  let P := (S q).direction
  have hpA : p ∈ Set.range f ∩ closedBall p (D / 16) :=
    ⟨hp, mem_closedBall_self (by dsimp [D] <;> positivity)⟩
  obtain ⟨a, ha⟩ := hCover hpA
  have hB : B ≤ 1 / 16 := by dsimp [B] <;> nlinarith
  have hamargin : dist a.val (P.orthogonalProjectionOnto q.center) ≤ (9 / 4 : ℝ) * q.radius := by
    have hda := hDisp a
    rw [ha] at hda
    rw [dist_comm] at hda
    have hpq := P.norm_starProjection_apply_le (p - q.center)
    rw [map_sub] at hpq
    have ht := dist_triangle a.val (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center)
    have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
    change dist a.val (P.orthogonalProjectionOnto p) ≤ (2 * B) * q.radius at hda
    change dist (P.orthogonalProjectionOnto p) (P.orthogonalProjectionOnto q.center) ≤
      dist p q.center at hpq
    nlinarith
  have hroom : dist a.val (P.orthogonalProjectionOnto q.center) + 2 * (r / 32) ≤
      (5 / 2 : ℝ) * q.radius := by
    change 64 * D < q.radius at hqlo
    change 1024 * r ≤ D / 16 at hrsmall
    linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hK : ∀ x ∈ closedBall p (D / 2), D / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    have hxp : dist x p ≤ D / 2 := hx
    change D ≤ cellRegionStoppingScale μ R hR k z Good x + dist x p at h
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B] <;> positivity)
    hmodel.2.2.2.1 (closedBall p (D / 2)) (D / 2) hK (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
      change q.radius ≤ 4096 * D at hqhi
      change 0 < D at hDpos
      nlinarith)
  have hSurface : ∀ u, dist u a ≤ 2 * (r / 32) → H u ∈ Set.range f := by
    intro u hu
    have hd := hLip.dist_le_mul u a
    rw [ha] at hd
    norm_num at hd
    have hlocal : H u ∈ closedBall p (D / 2) := by
      change dist (H u) p ≤ D / 2
      change 1024 * r ≤ D / 16 at hrsmall
      linarith
    exact (hstable.symm ▸ (show H u ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∩
      closedBall p (D / 2) from ⟨hFinite ⟨u, rfl⟩, hlocal⟩)).1
  have hKhalf : (Real.toNNReal (1008 * activeProjectionError d ε) : ℝ) ≤ 1 / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  have hLhalf : (Real.toNNReal (1012 * activeProjectionError d ε) : ℝ) ≤ 1 / 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  have hProjected := centered_projection_disk_in_surface_ball P (P.orthogonalProjectionOnto q.center)
    ((5 / 2 : ℝ) * q.radius) H (Real.toNNReal (1008 * activeProjectionError d ε))
    (Real.toNNReal (1012 * activeProjectionError d ε)) hKhalf hLhalf hError hNormal
    a (r / 32) (by positivity) hroom (Set.range f) hSurface
  rw [ha, show 2 * (r / 32) = r / 16 by ring] at hProjected
  refine ⟨P, (hS q).2, ?_, hProjected⟩
  intro x hx
  have hxA : x ∈ Set.range f ∩ closedBall p (D / 16) :=
    ⟨hx.1, (closedBall_subset_closedBall hrsmall (x := p)) hx.2⟩
  have hcone := normal_projection_bound_on_chart_range P H
    (Real.toNNReal (1012 * activeProjectionError d ε)) 64 hNormal hSep
    x (hCover hxA) p ⟨a, ha⟩
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_ofNat] at hcone
  rw [infDist_affine_translate, submodule_infDist_eq_normal_projection]
  have hxp : dist x p ≤ 1024 * r := hx.2
  nlinarith [mul_le_mul_of_nonneg_left hxp hη, mul_nonneg hη hr.le]

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_active_region_positive_matched_projection_oai := @OAI.RieszRectifiability.exists_active_region_positive_matched_projection_oai
