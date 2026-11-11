-- Prove2me | solution 1 for OAI.RieszRectifiability.active_region_high_scale_local_ball_area_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:35.583636+00:00
-- url     : https://prove2.me/submissions/90e8af7f-5a82-4060-a93a-889db5f22f17

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PlaneChartBallArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem plane_chart_ball_hausdorffMeasure_le {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (C : Set P) (g : C → Ambient e) (K L : ℝ≥0) (hL : 0 < L)
    (hg : LipschitzWith K g) (hsep : AntilipschitzWith L g)
    (p : Ambient e) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g ∩ closedBall p r) ≤
      planeChartBallAreaConstant n K L * (ENNReal.ofReal r) ^ n := by
  classical
  by_cases hempty : Set.range g ∩ closedBall p r = ∅
  · rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨a, ha⟩ := hy.1
  let T := g ⁻¹' closedBall p r
  have hdomain : (Subtype.val : C → P) '' T ⊆ closedBall a.val (2 * (L : ℝ) * r) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxball : dist (g x) p ≤ r := hx
    have hyball : dist (g a) p ≤ r := by rw [ha]; exact hy.2
    have ht := dist_triangle_right (g x) (g a) p
    have hpair : dist (g x) (g a) ≤ 2 * r := by linarith
    have h := (hsep.le_mul_dist x a).trans (mul_le_mul_of_nonneg_left hpair L.coe_nonneg)
    change dist x.val a.val ≤ 2 * (L : ℝ) * r
    change dist x.val a.val ≤ (L : ℝ) * (2 * r) at h
    linarith
  have hrad : 0 < 2 * (L : ℝ) * r := by
    have hLreal : 0 < (L : ℝ) := hL
    positivity
  have hdom : (μH[(n : ℝ)] : Measure C) T ≤
      (ENNReal.ofReal (2 * (L : ℝ) * r)) ^ n * planeUnitHausdorffMeasure n := by
    have hiso := (isometry_subtype_coe (s := C)).hausdorffMeasure_image
      (Or.inl (show 0 ≤ (n : ℝ) by positivity)) T
    rw [← hiso]
    exact (measure_mono hdomain).trans_eq (plane_closedBall_hausdorffMeasure P hdim a.val _ hrad)
  have himage : g '' T = Set.range g ∩ closedBall p r := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, rfl⟩, hu⟩
    · rintro ⟨⟨u, rfl⟩, hu⟩
      exact ⟨u, hu, rfl⟩
  have harea := hg.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) T
  rw [himage, ENNReal.rpow_natCast] at harea
  calc
    _ ≤ (K : ℝ≥0∞) ^ n * (μH[(n : ℝ)] : Measure C) T := harea
    _ ≤ (K : ℝ≥0∞) ^ n *
        ((ENNReal.ofReal (2 * (L : ℝ) * r)) ^ n * planeUnitHausdorffMeasure n) :=
      mul_le_mul_right hdom _
    _ = planeChartBallAreaConstant n K L * (ENNReal.ofReal r) ^ n := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (L : ℝ)),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
      unfold planeChartBallAreaConstant
      simp only [mul_pow]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionHighScaleLocalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local charts at high stopping scales

Two active projection steps transport a root-plane disk to a bilipschitz chart
covering the high-stopping-scale part of the limit model in a given ball.
The distance bounds on this chart yield local Hausdorff measure estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

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

theorem exists_active_region_high_scale_local_bilipschitz_chart
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (A : Set (Ambient d)) (hA : A ⊆ closedBall p r)
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ H : closedBall
        ((S (supportCellRoot μ R hR k z)).direction.orthogonalProjectionOnto p) ρ → Ambient d,
      LipschitzWith 4 H ∧ AntilipschitzWith 16 H ∧ Set.range f ∩ A ⊆ Set.range H := by
  let P := (S (supportCellRoot μ R hR k z)).direction
  let B := (17039360 * ε) / 63
  let ρ := r + 2 * B * latticeRadius R k
  have hρ : 0 < ρ := by dsimp [ρ, B]; have hr0 := latticeRadius_pos R hR k; positivity
  obtain ⟨g, hgLip, _, hcoords, hgRange⟩ := exists_affine_plane_disk_chart
    (S (supportCellRoot μ R hR k z)) (hS _).1 (P.orthogonalProjectionOnto p) ρ
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  have hdist (u v) : (1 / 16 : ℝ) * dist (g u) (g v) ≤ dist (T (g u)) (T (g v)) ∧
      dist (T (g u)) (T (g v)) ≤ 4 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit 0 2 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 4 (T ∘ g) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hb := hgLip.dist_le_mul u v
    norm_num at hb ⊢
    change dist (T (g u)) (T (g v)) ≤ 4 * dist u v
    linarith [(hdist u v).2]
  have hsep : AntilipschitzWith 16 (T ∘ g) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hp : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2, ← (hcoords v).2]
      have h := P.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    norm_num
    change dist u v ≤ 16 * dist (T (g u)) (T (g v))
    linarith [(hdist u v).1]
  have hr0 := latticeRadius_pos R hR k
  have hB : B ≤ 1 / 16 := by dsimp [B] <;> linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B] <;> positivity)
    hmodel.2.2.2.1 A (latticeRadius R (k + 1)) hD 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith)
  refine ⟨ρ, hρ, T ∘ g, hLip, hsep, ?_⟩
  intro x hx
  have hx2 : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hx2
  obtain ⟨y, hy, hTy⟩ := hx2
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le f hmodel 0 2 y hy
  change dist (T y) y ≤ (2 * B) * latticeRadius R k at hmove
  rw [hTy] at hmove
  have hyp : dist y p ≤ ρ := by
    have ht := dist_triangle y x p
    rw [dist_comm y x] at ht
    have hxp : dist x p ≤ r := hA hx.2
    dsimp [ρ]
    linarith
  have hproject := P.norm_starProjection_apply_le (y - p)
  rw [map_sub, ← dist_eq_norm (P.starProjection y) (P.starProjection p), ← dist_eq_norm y p] at hproject
  have hyg : y ∈ Set.range g := by
    rw [hgRange]
    exact ⟨hy, hproject.trans hyp⟩
  obtain ⟨u, hu⟩ := hyg
  exact ⟨u, by change T (g u) = x; rw [hu]; exact hTy⟩

theorem active_region_high_scale_local_ball_area_le_oai
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (A : Set (Ambient d)) (hA : A ⊆ closedBall p r)
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      planeChartBallAreaConstant n 4 16 * (ENNReal.ofReal r) ^ n := by
  obtain ⟨ρ, _, H, hLip, hsep, hcover⟩ :=
    exists_active_region_high_scale_local_bilipschitz_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p r hr A hA hD
  have hsub : Set.range f ∩ A ⊆ Set.range H ∩ closedBall p r :=
    fun _ hx => ⟨hcover hx, hA hx.2⟩
  exact (measure_mono hsub).trans
    (plane_chart_ball_hausdorffMeasure_le (S (supportCellRoot μ R hR k z)).direction
      (hS _).2 _ H 4 16 (by norm_num) hLip hsep p r hr)

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.active_region_high_scale_local_ball_area_le_oai := @OAI.RieszRectifiability.active_region_high_scale_local_ball_area_le_oai
