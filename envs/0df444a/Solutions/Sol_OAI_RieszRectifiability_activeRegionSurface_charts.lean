-- Prove2me | solution 1 for OAI.RieszRectifiability.activeRegionSurface_charts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:34.432786+00:00
-- url     : https://prove2.me/submissions/9496b756-9d68-45c3-9a8d-0f3ae6b24c59

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_active_surface_successor_input_chart

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

theorem finiteNormalizedWeight_sum_eq_one (F : Finset ι) (w : ι → ℝ)
    (hw : 1 ≤ ∑ i ∈ F, w i) :
    (∑ i ∈ F, finiteNormalizedWeight F w i) = 1 := by
  have hp : 0 < ∑ i ∈ F, w i := lt_of_lt_of_le zero_lt_one hw
  simp only [finiteNormalizedWeight, finiteWeightDenominator, max_eq_right hw,
    ← Finset.sum_div, div_self (ne_of_gt hp)]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_LocalImageCapture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local capture of perturbed images

A displacement bound ensures that points mapping into a given ball originate
in a controlled neighborhood. Capturing that neighborhood by a chart identifies
the image inside the ball, also after restriction by orthogonal projection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem image_inter_closedBall_eq_of_bounded_displacement {d : ℕ}
    (f : Ambient d → Ambient d) (A C : Set (Ambient d)) (c : Ambient d)
    (r B : ℝ) (hC : C ⊆ A)
    (hcapture : ∀ x ∈ A, dist x c ≤ r + B → x ∈ C)
    (hmove : ∀ x ∈ A, dist (f x) x ≤ B) :
    (f '' A) ∩ closedBall c r = (f '' C) ∩ closedBall c r := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨⟨x, hcapture x hx ?_, rfl⟩, hy⟩
    have ht := dist_triangle x (f x) c
    rw [dist_comm x (f x)] at ht
    have hm := hmove x hx
    have hb : dist (f x) c ≤ r := hy
    linarith
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨⟨x, hC hx, rfl⟩, hy⟩

theorem image_chart_captures_closedBall {d : ℕ} {U V : Type*}
    (f : Ambient d → Ambient d) (A : Set (Ambient d))
    (g : U → Ambient d) (h : V → Ambient d)
    (P : Submodule ℝ (Ambient d)) (D : Set P) (c : Ambient d) (r B : ℝ)
    (hg : Set.range g ⊆ A)
    (hcapture : ∀ x ∈ A, dist x c ≤ r + B → x ∈ Set.range g)
    (hmove : ∀ x ∈ A, dist (f x) x ≤ B)
    (hrange : Set.range h = (f '' Set.range g) ∩ P.orthogonalProjectionOnto ⁻¹' D)
    (hproject : closedBall c r ⊆ P.orthogonalProjectionOnto ⁻¹' D) :
    (f '' A) ∩ closedBall c r = Set.range h ∩ closedBall c r := by
  rw [image_inter_closedBall_eq_of_bounded_displacement f A (Set.range g) c r B
    hg hcapture hmove, hrange]
  ext y
  constructor
  · intro hy
    exact ⟨⟨hy.1, hproject hy.2⟩, hy.2⟩
  · intro hy
    exact ⟨hy.1.1, hy.2⟩

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

theorem finiteCoverCutoff_eq_one (c : X) (r : ℝ) (hr : 0 < r) (x : X)
    (hx : dist x c ≤ 3 * r) : finiteCoverCutoff c r x = 1 := by
  have hd : dist x c / r ≤ 3 := (div_le_iff₀ hr).mpr hx
  have h : (1 : ℝ) ≤ 4 - dist x c / r := by linarith
  simp only [finiteCoverCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

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

theorem finiteProjectionAverage_eq_weighted_sum (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x : Ambient d) (hθ : (∑ i ∈ F, θ i x) = 1) :
    finiteProjectionAverage F θ π x = ∑ i ∈ F, θ i x • π i x := by
  unfold finiteProjectionAverage
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hθ, one_smul]
  abel

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

theorem finiteProjectionAverage_dist_reference_le (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x p : Ambient d) (L : ℝ)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x) (hsum : (∑ i ∈ F, θ i x) = 1)
    (hπ : ∀ i ∈ F, θ i x ≠ 0 → dist (π i x) p ≤ L) :
    dist (finiteProjectionAverage F θ π x) p ≤ L := by
  have heq : finiteProjectionAverage F θ π x - p =
      ∑ i ∈ F, θ i x • (π i x - p) := by
    rw [finiteProjectionAverage_eq_weighted_sum F θ π x hsum]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  have hterm (i : ι) (hi : i ∈ F) : ‖θ i x • (π i x - p)‖ ≤ θ i x * L := by
    by_cases hz : θ i x = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i hi)]
      exact mul_le_mul_of_nonneg_left (hπ i hi hz) (hθ i hi)
  calc
    _ = ‖∑ i ∈ F, θ i x • (π i x - p)‖ := by rw [dist_eq_norm, heq]
    _ ≤ ∑ i ∈ F, ‖θ i x • (π i x - p)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ F, θ i x * L := Finset.sum_le_sum hterm
    _ = (∑ i ∈ F, θ i x) * L := (Finset.sum_mul _ _ _).symm
    _ = L := by rw [hsum, one_mul]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionAverageIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

variable {ι : Type*} {d : ℕ}

theorem finiteProjectionAverage_increment_identity (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1) :
    (finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y) =
      (∑ i ∈ F, θ i x • ((π i x - π i y) - (p x - p y))) +
      ∑ i ∈ F, (θ i x - θ i y) • (π i y - p y) := by
  rw [finiteProjectionAverage_eq_weighted_sum F θ π x hx,
    finiteProjectionAverage_eq_weighted_sum F θ π y hy]
  simp only [smul_sub, sub_smul, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hx, hy, one_smul]
  abel

theorem finiteProjectionAverage_increment_estimate (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d) (α B : ℝ)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - π i y) - (p x - p y)‖ ≤ α * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) (p y) ≤ B) :
    ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y)‖ ≤
      α * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := by
  have hfirst : ‖∑ i ∈ F, θ i x • ((π i x - π i y) - (p x - p y))‖ ≤
      α * dist x y := by
    calc
      _ ≤ ∑ i ∈ F, ‖θ i x • ((π i x - π i y) - (p x - p y))‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, θ i x * (α * dist x y) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = 0
        · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθ i hi)]
          exact mul_le_mul_of_nonneg_left (hlinear i hi hz) (hθ i hi)
      _ = _ := by rw [← Finset.sum_mul, hx, one_mul]
  have hsecond : ‖∑ i ∈ F, (θ i x - θ i y) • (π i y - p y)‖ ≤
      B * (∑ i ∈ F, |θ i x - θ i y|) := by
    calc
      _ ≤ ∑ i ∈ F, ‖(θ i x - θ i y) • (π i y - p y)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ F, |θ i x - θ i y| * B := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : θ i x = θ i y
        · simp only [hz, sub_self, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hoffset i hi hz) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  rw [finiteProjectionAverage_increment_identity F θ π p x y hx hy]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

theorem finiteProjectionAverage_increment_bound (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (p : Ambient d → Ambient d) (x y : Ambient d) (α B L : ℝ)
    (hB : 0 ≤ B) (hθ : ∀ i ∈ F, 0 ≤ θ i x)
    (hx : (∑ i ∈ F, θ i x) = 1) (hy : (∑ i ∈ F, θ i y) = 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - π i y) - (p x - p y)‖ ≤ α * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) (p y) ≤ B)
    (hvariation : (∑ i ∈ F, |θ i x - θ i y|) ≤ L * dist x y) :
    ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (p x - p y)‖ ≤
      (α + B * L) * dist x y := by
  have h := finiteProjectionAverage_increment_estimate F θ π p x y α B
    hθ hx hy hlinear hoffset
  calc
    _ ≤ α * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := h
    _ ≤ α * dist x y + B * (L * dist x y) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvariation hB)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionPerturbationCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Small errors from an orthogonal projection give quantitative bounds on the parallel and
perpendicular components, keeping perturbed vectors in a controlled cone.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem projection_perturbation_vector_bounds {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (v w : Ambient d) (η : ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hv : ‖v‖ ≤ 2 * ‖P.starProjection v‖)
    (herr : ‖w - P.starProjection v‖ ≤ η * ‖v‖) :
    ‖v‖ ≤ 4 * ‖P.starProjection w‖ ∧
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤
        (4 * η) * ‖P.starProjection w‖ ∧
      ‖w‖ ≤ (1 + η) * ‖v‖ ∧
      ‖w‖ ≤ (1 + 4 * η) * ‖P.starProjection w‖ := by
  have hPv : P.starProjection v ∈ P := (P.orthogonalProjectionOnto v).property
  have hself : P.starProjection (P.starProjection v) = P.starProjection v :=
    P.starProjection_eq_self_iff.mpr hPv
  have hperp : (Pᗮ : Submodule ℝ (Ambient d)).starProjection (P.starProjection v) = 0 := by
    rw [P.starProjection_orthogonal_val, hself, sub_self]
  have hparallel : ‖P.starProjection w - P.starProjection v‖ ≤ η * ‖v‖ := by
    have h := (P.norm_starProjection_apply_le (w - P.starProjection v)).trans herr
    rwa [map_sub, hself] at h
  have hbase : ‖P.starProjection v‖ ≤ ‖P.starProjection w‖ + η * ‖v‖ := by
    have htri := norm_sub_le (P.starProjection w)
      (P.starProjection w - P.starProjection v)
    rw [sub_sub_cancel] at htri
    linarith
  have hinverse : ‖v‖ ≤ 4 * ‖P.starProjection w‖ := by
    have hm := mul_le_mul_of_nonneg_right hηsmall (norm_nonneg v)
    linarith
  have hnormal : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤ η * ‖v‖ := by
    have h := ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le
      (w - P.starProjection v)).trans herr
    rwa [map_sub, hperp, sub_zero] at h
  have hcone : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection w‖ ≤
      (4 * η) * ‖P.starProjection w‖ := by
    have hm := mul_le_mul_of_nonneg_left hinverse hη
    nlinarith
  have hforward : ‖w‖ ≤ (1 + η) * ‖v‖ := by
    have htri := norm_add_le (w - P.starProjection v) (P.starProjection v)
    rw [sub_add_cancel] at htri
    have hproj := P.norm_starProjection_apply_le v
    nlinarith
  have himage : ‖w‖ ≤ (1 + 4 * η) * ‖P.starProjection w‖ := by
    have htri := norm_add_le (P.starProjection w)
      ((Pᗮ : Submodule ℝ (Ambient d)).starProjection w)
    rw [P.starProjection_add_starProjection_orthogonal] at htri
    nlinarith
  exact ⟨hinverse, hcone, hforward, himage⟩

theorem projection_perturbation_image_cone {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (E : Set (Ambient d)) (f : Ambient d → Ambient d)
    (η : ℝ) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4)
    (hinput : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y))
    (herr : ∀ x ∈ E, ∀ y ∈ E,
      ‖(f x - f y) - P.starProjection (x - y)‖ ≤ η * dist x y) :
    ∀ u ∈ f '' E, ∀ v ∈ f '' E,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (u - v)‖ ≤
        (4 * η) * dist (P.starProjection u) (P.starProjection v) := by
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  have hv : ‖x - y‖ ≤ 2 * ‖P.starProjection (x - y)‖ := by
    simpa only [map_sub, dist_eq_norm] using! hinput x hx y hy
  have h := (projection_perturbation_vector_bounds P (x - y) (f x - f y) η
    hη hηsmall hv (herr x hx y hy)).2.1
  simpa only [map_sub, dist_eq_norm] using! h

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

theorem plane_chart_location_of_height {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (c : Ambient d) (ρ B : ℝ)
    (g : closedBall (S.direction.orthogonalProjectionOnto c) ρ → Ambient d)
    (hcoordinates : ∀ u, S.direction.orthogonalProjectionOnto (g u) = u.val)
    (hheight : ∀ u, infDist (g u) (S : Set (Ambient d)) ≤ B) :
    ∀ u, dist (g u) c ≤ ρ + B + infDist c (S : Set (Ambient d)) := by
  intro u
  have hstar : S.direction.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : S.direction => (v : Ambient d)) (hcoordinates u)
  have h := dist_le_projection_add_plane_distances S hS (g u) c
  rw [hstar] at h
  have hu : dist (u.val : Ambient d) (S.direction.starProjection c) ≤ ρ := u.property
  linarith [hheight u]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveLevelCenterPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

theorem activeLevelWeight_sum_eq_one_near_center {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t) (x : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    (∑ i ∈ activeLevelIndex μ R hR k z Good t,
      activeLevelWeight μ R hR k z Good t i x) = 1 := by
  apply finiteNormalizedWeight_sum_eq_one
  have hone : activeLevelCutoff μ R hR k z t q x = 1 :=
    finiteCoverCutoff_eq_one q.center _ (latticeRadius_pos R hR (k + t)) x hx
  rw [← hone]
  exact Finset.single_le_sum (fun i _ => finiteCoverCutoff_nonneg i.center _ x) hq

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionLocalComparison
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
  (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (q : SupportCellDescendant μ R hR k z)
  (hq : q ∈ activeLevelIndex μ R hR k z Good t)

include hε hεsmall hfit hq hS

theorem active_level_used_plane_comparison (x y : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hy : y ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good t)
    (hn : activeLevelWeight μ R hR k z Good t i x ≠ 0 ∨
      activeLevelWeight μ R hR k z Good t i y ≠ 0) :
    ‖(S i).direction.starProjection - (S q).direction.starProjection‖ ≤ 2048 * ε ∧
    dist (nonemptyAffineProjection (S i) (hS i).1 y)
      (nonemptyAffineProjection (S q) (hS q).1 y) ≤
        (262144 * ε) * latticeRadius R (k + t) := by
  let r := latticeRadius R (k + t)
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hri : i.radius = r := by simp only [SupportCellDescendant.radius, hiA.1, r]
  have hrq : q.radius = r := by simp only [SupportCellDescendant.radius, hqA.1, r]
  have hnearAt (a : Ambient d) (ha : dist a q.center ≤ 3 * r)
      (hnz : activeLevelWeight μ R hR k z Good t i a ≠ 0) :
      dist i.center q.center ≤ 7 * r := by
    have hd := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i a).mp hnz
    have ht := dist_triangle i.center a q.center
    rw [dist_comm i.center a] at ht
    change dist a i.center < 4 * r at hd
    linarith
  have hnear : dist i.center q.center ≤ 7 * r := by
    rcases hn with hnx | hny
    · exact hnearAt x hx hnx
    · exact hnearAt y hy hny
  have hsmall : i.radius ≤ q.radius := by rw [hri, hrq]
  have hlarge : q.radius ≤ 64 * i.radius := by rw [hri, hrq]; linarith
  have hneighbor : dist i.center q.center ≤ 128 * q.radius := by rw [hrq]; linarith
  refine ⟨neighbor_cell_projection_operator_norm_le μ R hR k z i q hsmall hlarge hneighbor
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hi) (hfit q hq), ?_⟩
  have hyi : y ∈ closedBall i.center (32 * i.radius) := by
    have hy' : dist y q.center ≤ 3 * r := hy
    have ht := dist_triangle y q.center i.center
    rw [dist_comm q.center i.center] at ht
    change dist y i.center ≤ 32 * i.radius
    rw [hri]
    linarith
  have h := neighbor_cell_affine_projections_close_on_32ball μ R hR k z i q
    hsmall hlarge hneighbor ε hε hεsmall (S i) (S q) (hS i) (hS q)
    (hfit i hi) (hfit q hq) y hyi
  simpa only [hri, r] using! h

theorem activeLevelProjectionMap_reference_displacement (x : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x)
      (nonemptyAffineProjection (S q) (hS q).1 x) ≤
        (262144 * ε) * latticeRadius R (k + t) := by
  apply finiteProjectionAverage_dist_reference_le
    (activeLevelIndex μ R hR k z Good t) (activeLevelWeight μ R hR k z Good t)
    (fun i => nonemptyAffineProjection (S i) (hS i).1) x _ _
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq x hx)
  intro i hi hn
  exact (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
    q hq x x hx hx i hi (Or.inl hn)).2

theorem activeLevelProjectionMap_reference_increment (x y : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hy : y ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    ‖(activeLevelProjectionMap μ R hR k z Good t S hS x -
      activeLevelProjectionMap μ R hR k z Good t S hS y) -
      (S q).direction.starProjection (x - y)‖ ≤ activeProjectionError d ε * dist x y := by
  let r := latticeRadius R (k + t)
  let θ := activeLevelWeight μ R hR k z Good t
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  have hlinear : ∀ i ∈ activeLevelIndex μ R hR k z Good t, θ i x ≠ 0 →
      ‖(π i x - π i y) - (π q x - π q y)‖ ≤ (2048 * ε) * dist x y := by
    intro i hi hn
    have hop := (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
      q hq x y hx hy i hi (Or.inl hn)).1
    exact nonemptyAffineProjection_increment_difference_le (S i) (S q)
      (hS i).1 (hS q).1 x y (2048 * ε) hop
  have hoffset : ∀ i ∈ activeLevelIndex μ R hR k z Good t, θ i x ≠ θ i y →
      dist (π i y) (π q y) ≤ (262144 * ε) * r := by
    intro i hi hchange
    have hn : θ i x ≠ 0 ∨ θ i y ≠ 0 := by
      by_cases hz : θ i x = 0
      · right
        intro hyz
        exact hchange (hz.trans hyz.symm)
      · exact Or.inl hz
    exact (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
      q hq x y hx hy i hi hn).2
  have hvariation : (∑ i ∈ activeLevelIndex μ R hR k z Good t, |θ i x - θ i y|) ≤
      (4 * (9 : ℝ) ^ d / r) * dist x y := by
    calc
      _ ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
        activeLevelWeight_sum_abs_sub_le μ R hR k z Good t x y
      _ = _ := by ring
  have h := finiteProjectionAverage_increment_bound (activeLevelIndex μ R hR k z Good t)
    θ π (π q) x y (2048 * ε) ((262144 * ε) * r) (4 * (9 : ℝ) ^ d / r)
    (by positivity) (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq x hx)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq y hy) hlinear hoffset hvariation
  have heq : 2048 * ε + ((262144 * ε) * r) * (4 * (9 : ℝ) ^ d / r) =
      activeProjectionError d ε := by
    unfold activeProjectionError
    field_simp [ne_of_gt hr]
    ring
  rw [heq] at h
  change ‖(activeLevelProjectionMap μ R hR k z Good t S hS x -
    activeLevelProjectionMap μ R hR k z Good t S hS y) -
    (nonemptyAffineProjection (S q) (hS q).1 x -
      nonemptyAffineProjection (S q) (hS q).1 y)‖ ≤ _ at h
  rwa [nonemptyAffineProjection_sub] at h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionLocalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem activeProjectionError_small_parameters (d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4) :
    0 ≤ activeProjectionError d ε ∧ ε ≤ 1 / 1024 := by
  have hp : 0 ≤ (1048576 * (9 : ℝ) ^ d) * ε := by positivity
  constructor
  · unfold activeProjectionError
    positivity
  · unfold activeProjectionError at hsmall
    nlinarith

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

theorem activeLevelProjectionMap_covers_shrunk_disk {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (a : (S q).direction) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d)
    (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    closedBall a (ρ - (262144 * ε) * latticeRadius R (k + t)) ⊆
      Set.range (fun u : closedBall a ρ =>
        (S q).direction.orthogonalProjectionOnto
          (activeLevelProjectionMap μ R hR k z Good t S hS (g u))) := by
  let P := (S q).direction
  let r := latticeRadius R (k + t)
  let η := activeProjectionError d ε
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  let f : closedBall a ρ → P := fun u => P.orthogonalProjectionOnto (σ (g u))
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hcoord (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hdisp : ∀ u : closedBall a ρ, dist (f u) u.val ≤ (262144 * ε) * r := by
    intro u
    have ht : P.orthogonalProjectionOnto (nonemptyAffineProjection (S q) (hS q).1 (g u)) = u.val := by
      rw [nonemptyAffineProjection_tangential, hcoordinates u]
    have hdist := activeLevelProjectionMap_reference_displacement μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (hlocal u)
    calc
      _ = dist (P.orthogonalProjectionOnto (σ (g u)))
          (P.orthogonalProjectionOnto (nonemptyAffineProjection (S q) (hS q).1 (g u))) := by rw [ht]
      _ ≤ dist (σ (g u)) (nonemptyAffineProjection (S q) (hS q).1 (g u)) := by
        change ‖P.starProjection (σ (g u)) -
          P.starProjection (nonemptyAffineProjection (S q) (hS q).1 (g u))‖ ≤ _
        rw [← map_sub]
        exact P.norm_starProjection_apply_le _
      _ ≤ _ := hdist
  have herr : LipschitzWith (Real.toNNReal (2 * η))
      (fun u : closedBall a ρ => f u - u.val) := by
    apply LipschitzWith.of_dist_le'
    intro u v
    have hself : P.starProjection (P.starProjection (g u - g v)) =
        P.starProjection (g u - g v) :=
      P.starProjection_eq_self_iff.mpr (P.orthogonalProjectionOnto (g u - g v)).property
    have heq : (f u - u.val) - (f v - v.val) =
        P.orthogonalProjectionOnto ((σ (g u) - σ (g v)) - P.starProjection (g u - g v)) := by
      apply Subtype.ext
      change (P.starProjection (σ (g u)) - (u.val : Ambient d)) -
        (P.starProjection (σ (g v)) - (v.val : Ambient d)) =
        P.starProjection ((σ (g u) - σ (g v)) - P.starProjection (g u - g v))
      rw [map_sub, hself, map_sub, map_sub, hcoord u, hcoord v]
      abel
    have hinc := activeLevelProjectionMap_reference_increment μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (g v) (hlocal u) (hlocal v)
    have hLip : dist (g u) (g v) ≤ 2 * dist u v := by
      simpa only [NNReal.coe_ofNat] using! hg.dist_le_mul u v
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖(σ (g u) - σ (g v)) - P.starProjection (g u - g v)‖ :=
        P.norm_starProjection_apply_le _
      _ ≤ η * dist (g u) (g v) := hinc
      _ ≤ η * (2 * dist u v) := mul_le_mul_of_nonneg_left hLip hη
      _ = (2 * η) * dist u v := by ring
  have hcontract : Real.toNNReal (2 * η) < 1 := by
    have hreal : (Real.toNNReal (2 * η) : ℝ) < 1 := by
      rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      change η ≤ 1 / 4 at hsmall
      linarith
    exact_mod_cast hreal
  exact closedBall_covered_by_lipschitz_perturbation a ρ ((262144 * ε) * r)
    hρ (Real.toNNReal (2 * η)) hcontract f hdisp herr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionReplacementChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Replacement charts on active projection images

The active projection of a tangentially parametrized disk satisfies a quantitative cone bound
and covers a smaller disk in the reference plane. These properties produce a replacement chart
with exact tangential coordinates, Lipschitz constant at most two, and controlled normal slope.
Its range is precisely the portion of the projected image lying above the smaller disk.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_level_replacement_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (a : (S q).direction) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d) (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    let P := (S q).direction
    let δ := (262144 * ε) * latticeRadius R (k + t)
    let D := closedBall a (ρ - δ)
    let A := (activeLevelProjectionMap μ R hR k z Good t S hS) '' Set.range g
    ∃ h : D → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
        (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ A ∧ P.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = A ∩ P.orthogonalProjectionOnto ⁻¹' D := by
  let P := (S q).direction
  let η := activeProjectionError d ε
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  let δ := (262144 * ε) * latticeRadius R (k + t)
  let D := closedBall a (ρ - δ)
  let A := σ '' Set.range g
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hstar (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hinput : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      dist x y ≤ 2 * dist (P.starProjection x) (P.starProjection y) := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    rw [hstar u, hstar v]
    simpa only [NNReal.coe_ofNat] using! hg.dist_le_mul u v
  have herr : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(σ x - σ y) - P.starProjection (x - y)‖ ≤ η * dist x y := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    exact activeLevelProjectionMap_reference_increment μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (g v) (hlocal u) (hlocal v)
  have hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (Real.toNNReal (4 * η) : ℝ) * dist (P.starProjection x) (P.starProjection y) := by
    intro x hx y hy
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
    exact projection_perturbation_image_cone P (Set.range g) σ η hη hsmall hinput herr x hx y hy
  have hcover : D ⊆ P.orthogonalProjectionOnto '' A := by
    have hc := activeLevelProjectionMap_covers_shrunk_disk μ R hR k z Good t S hS
      ε hε hsmall hfit q hq a ρ hρ g hg hcoordinates hlocal
    intro b hb
    obtain ⟨u, hu⟩ := hc hb
    exact ⟨σ (g u), ⟨g u, ⟨u, rfl⟩, rfl⟩, hu⟩
  obtain ⟨h, hLip, hnLip, hcoords, hrange⟩ :=
    exists_chart_on_covered_projection P A (Real.toNNReal (4 * η)) D hcover hcone
  have hL : 1 + Real.toNNReal (4 * η) ≤ (2 : ℝ≥0) := by
    have hh : ((1 + Real.toNNReal (4 * η) : ℝ≥0) : ℝ) ≤ 2 := by
      rw [NNReal.coe_add, NNReal.coe_one,
        Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      change η ≤ 1 / 4 at hsmall
      linarith
    exact_mod_cast hh
  exact ⟨h, hLip.weaken hL, hnLip, hcoords, hrange⟩

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

theorem activeLevelProjectionMap_image_plane_height
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (E : Set (Ambient d))
    (hE : E ⊆ closedBall q.center (3 * latticeRadius R (k + t))) :
    ∀ y ∈ (activeLevelProjectionMap μ R hR k z Good t S hS) '' E,
      infDist y (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
  let : Nonempty (S q) := (hS q).1.to_subtype
  rintro y ⟨x, hx, rfl⟩
  have hp : nonemptyAffineProjection (S q) (hS q).1 x ∈ S q :=
    orthogonalProjection_mem x
  exact (infDist_le_dist_of_mem hp).trans
    (activeLevelProjectionMap_reference_displacement μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq x (hE hx))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_RecenteredDiskCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recentering disk charts

A chart whose projection is the identity restricts to any closed disk contained in
its parameter disk. The recentered chart preserves the normal Lipschitz bound and
parametrizes exactly the part of the original range over the smaller disk.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_recentered_disk_chart {d : ℕ}
    (P : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ)
    (g : closedBall a ρ → Ambient d) (L : ℝ≥0)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (b : P) (r : ℝ) (hcontain : dist b a + r ≤ ρ) :
    ∃ h : closedBall b r → Ambient d,
      LipschitzWith (1 + L) h ∧
      LipschitzWith L (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ P.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = Set.range g ∩ P.orthogonalProjectionOnto ⁻¹' closedBall b r := by
  have hcover : closedBall b r ⊆ P.orthogonalProjectionOnto '' Set.range g := by
    intro v hv
    have hnear : v ∈ closedBall a ρ := by
      have ht := dist_triangle v b a
      have hv' : dist v b ≤ r := hv
      change dist v a ≤ ρ
      linarith
    let u : closedBall a ρ := ⟨v, hnear⟩
    exact ⟨g u, ⟨u, rfl⟩, hcoordinates u⟩
  have hstar (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hcone : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y) := by
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    have h := hnormal.dist_le_mul u v
    rw [dist_eq_norm, ← map_sub] at h
    rw [hstar u, hstar v]
    exact h
  exact exists_chart_on_covered_projection P (Set.range g) L (closedBall b r) hcover hcone

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceChartStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One active surface chart step

A local chart capturing the original surface near an active cell gives a chart for its projected
image. Shrinking the tangential disk leaves room for the projection displacement while retaining
exact local image capture. The new chart has controlled normal slope, stays in the reference
plane tube, and remains inside the prescribed ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_surface_chart_step {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (A : Set (Ambient d))
    (g : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
      ((11 / 4 : ℝ) * latticeRadius R (k + t)) → Ambient d)
    (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hsubset : Set.range g ⊆ A)
    (hcapture : A ∩ closedBall q.center ((5 / 2 : ℝ) * latticeRadius R (k + t)) ⊆ Set.range g)
    (hmove : ∀ x ∈ A,
      dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤
        latticeRadius R (k + t) / 4) :
    ∃ h : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * latticeRadius R (k + t)) → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
        (fun u => ((S q).directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ (activeLevelProjectionMap μ R hR k z Good t S hS) '' A ∧
        (S q).direction.orthogonalProjectionOnto (h u) = u.val ∧
        infDist (h u) (S q : Set (Ambient d)) ≤
          (262144 * ε) * latticeRadius R (k + t) ∧
        h u ∈ closedBall q.center (3 * latticeRadius R (k + t))) ∧
      ((activeLevelProjectionMap μ R hR k z Good t S hS) '' A) ∩
          closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) =
        Set.range h ∩ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) := by
  let r := latticeRadius R (k + t)
  let P := (S q).direction
  let a := P.orthogonalProjectionOnto q.center
  let δ := (262144 * ε) * r
  let L := Real.toNNReal (4 * activeProjectionError d ε)
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hpow hε.le
  have hδcoeff : 262144 * ε ≤ 1 / 4 := by
    unfold activeProjectionError at hsmall
    nlinarith
  have hδ : δ ≤ r / 4 := by
    have h := mul_le_mul_of_nonneg_right hδcoeff hr.le
    dsimp [δ]
    linarith
  have hεfit : 1024 * ε ≤ 1 / 4 := by linarith
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hrad : q.radius = r := by simp only [SupportCellDescendant.radius, hqA.1, r]
  have hqr := q.radius_pos
  have hcenter := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) (S q) (hS q) (hfit q hq)).1
      q.center (mem_ball_self (by positivity)) q.center_mem_support
  have hcenterBound : infDist q.center (S q : Set (Ambient d)) ≤ r / 4 := by
    rw [hrad] at hcenter
    have h := mul_le_mul_of_nonneg_right hεfit hr.le
    nlinarith
  obtain ⟨j, hjLip, hjNormal, hjCoords, hjRange⟩ :=
    exists_active_level_replacement_chart μ R hR k z Good t S hS ε hε hsmall hfit q hq
      a ((11 / 4 : ℝ) * r) (by positivity) g hg hcoordinates hlocal
  obtain ⟨h, hhLip, hhNormal, hhCoords, hhRange⟩ :=
    exists_recentered_disk_chart P a (((11 / 4 : ℝ) * r) - δ) j L
      (fun u => (hjCoords u).2) hjNormal a ((5 / 2 : ℝ) * r)
      (by rw [dist_self]; linarith)
  have hL : 1 + L ≤ (2 : ℝ≥0) := by
    have hreal : ((1 + L : ℝ≥0) : ℝ) ≤ 2 := by
      change 1 + (Real.toNNReal (4 * activeProjectionError d ε) : ℝ) ≤ 2
      rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      linarith
    exact_mod_cast hreal
  have hheight : ∀ u, infDist (h u) (S q : Set (Ambient d)) ≤ δ := by
    intro u
    obtain ⟨v, hv⟩ := (hhCoords u).1
    have hin : h u ∈ σ '' Set.range g := by
      rw [← hv]
      exact (hjCoords v).1
    exact activeLevelProjectionMap_image_plane_height μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (Set.range g) (by rintro x ⟨v, rfl⟩; exact hlocal v)
      (h u) hin
  have hphysical : ∀ u, h u ∈ closedBall q.center (3 * r) := by
    intro u
    have hloc := plane_chart_location_of_height (S q) (hS q).1 q.center
      ((5 / 2 : ℝ) * r) δ h (fun v => (hhCoords v).2) hheight u
    change dist (h u) q.center ≤ 3 * r
    linarith
  have hexact : Set.range h = (σ '' Set.range g) ∩
      P.orthogonalProjectionOnto ⁻¹' closedBall a ((5 / 2 : ℝ) * r) := by
    rw [hhRange, hjRange]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      refine ⟨⟨hy.1, ?_⟩, hy.2⟩
      have hy' : dist (P.orthogonalProjectionOnto y) a ≤ (5 / 2 : ℝ) * r := hy.2
      change dist (P.orthogonalProjectionOnto y) a ≤ (11 / 4 : ℝ) * r - δ
      linarith
  refine ⟨h, hhLip.weaken hL, hhNormal, ?_, ?_⟩
  · intro u
    refine ⟨?_, (hhCoords u).2, hheight u, hphysical u⟩
    have hin : h u ∈ σ '' Set.range g := (hexact ▸ (show h u ∈ Set.range h from ⟨u, rfl⟩)).1
    exact Set.image_mono hsubset hin
  · have hpre : ∀ x ∈ A, dist x q.center ≤ (9 / 4 : ℝ) * r + r / 4 → x ∈ Set.range g := by
      intro x hx hnear
      apply hcapture
      exact ⟨hx, by change dist x q.center ≤ (5 / 2 : ℝ) * r; linarith⟩
    have hproject : closedBall q.center ((9 / 4 : ℝ) * r) ⊆
        P.orthogonalProjectionOnto ⁻¹' closedBall a ((5 / 2 : ℝ) * r) := by
      intro x hx
      have hp := P.norm_starProjection_apply_le (x - q.center)
      rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
      have hx' : dist x q.center ≤ (9 / 4 : ℝ) * r := hx
      change dist (P.orthogonalProjectionOnto x) a ≤ (5 / 2 : ℝ) * r
      change dist (P.starProjection x) (P.starProjection q.center) ≤ (5 / 2 : ℝ) * r
      linarith
    exact image_chart_captures_closedBall σ A g h P (closedBall a ((5 / 2 : ℝ) * r))
      q.center ((9 / 4 : ℝ) * r) (r / 4) hsubset hpre hmove hexact hproject

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

theorem activeLevelProjectionMap_successor_surface_displacement_small
    (hsmall : ε ≤ 1 / 68157440) :
    ∀ x ∈ A, dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x) x ≤
      latticeRadius R (k + (t + 1)) / 4 := by
  intro x hx
  have h := activeLevelProjectionMap_successor_surface_displacement μ R hR k z Good t
    S hS ε hε hεsmall hfit A hprevious x hx
  have hr := (latticeRadius_pos R hR (k + (t + 1))).le
  have hm := mul_le_mul_of_nonneg_right hsmall hr
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceChartInductionStep
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
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεtiny hsmall hfit hcharts

theorem active_surface_charts_successor :
    HasActiveSurfaceCharts μ R hR k z Good (t + 1) S ε
      ((activeLevelProjectionMap μ R hR k z Good (t + 1) S hS) '' A) := by
  have hprevious : ∀ q ∈ activeLevelIndex μ R hR k z Good t, ∀ x ∈ A,
      x ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) →
        infDist x (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
    intro q hq x hx hnear
    have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
    have hrad : q.radius = latticeRadius R (k + t) := by
      simp only [SupportCellDescendant.radius, hqA.1]
    have h := HasActiveCellSurfaceChart.height_on_inner_ball q (S q) ε A (hcharts q hq) x hx
      (by simpa only [hrad] using! hnear)
    simpa only [hrad] using! h
  have hmove := activeLevelProjectionMap_successor_surface_displacement_small μ R hR k z Good t
    S hS ε hε (by linarith) hfit A hprevious (by linarith : ε ≤ 1 / 68157440)
  intro i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hrad : i.radius = latticeRadius R (k + (t + 1)) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  have hin := active_surface_successor_input_chart μ R hR k z Good t S hS ε hε hεtiny
    hsmall hfit A hcharts i hi
  unfold HasActiveCellInputChart at hin
  rw [hrad] at hin
  obtain ⟨g, hg, hcoords, hlocal, hsubset, hcapture⟩ := hin
  have h := exists_active_surface_chart_step μ R hR k z Good (t + 1) S hS ε hε
    (by linarith) (fun j hj => hfit j ((mem_activeLevelIndex μ R hR k z Good (t + 1) j).mp hj).2)
    i hi A g hg hcoords hlocal hsubset hcapture hmove
  unfold HasActiveCellSurfaceChart
  rw [hrad]
  exact h

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_FittingPlaneInputChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Input charts on fitting planes

A small bilateral plane error bounds the offset of a support center from the fitting
plane. The located affine chart then gives the input disk, with constant normal component,
exact projected range, and image contained in the ambient ball of radius `3 * r`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_fitting_plane_input_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (c : Ambient d) (hc : c ∈ μ.support)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hεsmall : ε ≤ 1 / 2048)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hfit : bilateralPlaneError μ c (1024 * r) S < ε) :
    ∃ g : closedBall (S.direction.orthogonalProjectionOnto c) ((5 / 2 : ℝ) * r) → Ambient d,
      LipschitzWith 2 g ∧
      LipschitzWith 0 (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)) ∧
      (∀ u, g u ∈ S ∧ S.direction.orthogonalProjectionOnto (g u) = u.val ∧
        g u ∈ closedBall c (3 * r)) ∧
      Set.range g = (S : Set (Ambient d)) ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto c) ((5 / 2 : ℝ) * r) := by
  have hcenter := (bilateralPlaneError_lt_pointwise μ ⟨c, hc⟩ c (1024 * r) ε
    (by positivity) S hS hfit).1 c (mem_ball_self (by positivity)) hc
  have hoffset : infDist c (S : Set (Ambient d)) ≤ r / 2 := by
    have hm := mul_le_mul_of_nonneg_right hεsmall (show 0 ≤ 1024 * r by positivity)
    linarith
  obtain ⟨g, hLip, hnLip, hcoords, hrange⟩ :=
    exists_located_affine_plane_disk_chart S hS.1 c ((5 / 2 : ℝ) * r)
  refine ⟨g, hLip.weaken (by norm_num), hnLip, ?_, hrange⟩
  intro u
  refine ⟨(hcoords u).1, (hcoords u).2.1, ?_⟩
  have hloc := (hcoords u).2.2
  change dist (g u) c ≤ 3 * r
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveSurfaceInitialCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem active_surface_charts_initial {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 2048)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    HasActiveSurfaceCharts μ R hR k z Good 0 S ε
      (S (supportCellRoot μ R hR k z) : Set (Ambient d)) := by
  intro q hq
  have hqA := (mem_activeLevelIndex μ R hR k z Good 0 q).mp hq
  have heq := q.eq_root_of_zero_depth hqA.1
  have hplane : (S (supportCellRoot μ R hR k z) : Set (Ambient d)) = (S q : Set (Ambient d)) := by
    rw [heq]
  rw [hplane]
  obtain ⟨g, hgLip, hgNormal, hgCoords, hgRange⟩ := exists_fitting_plane_input_chart μ
    q.center q.center_mem_support q.radius q.radius_pos ε hεsmall (S q) (hS q) (hfit q hqA.2)
  refine ⟨g, hgLip, hgNormal.weaken (zero_le), ?_, ?_⟩
  · intro u
    refine ⟨(hgCoords u).1, (hgCoords u).2.1, ?_, (hgCoords u).2.2⟩
    rw [infDist_zero_of_mem (hgCoords u).1]
    exact mul_nonneg (mul_nonneg (by norm_num) hε.le) q.radius_pos.le
  · ext x
    constructor
    · intro hx
      refine ⟨?_, hx.2⟩
      rw [hgRange]
      refine ⟨hx.1, ?_⟩
      have hp := (S q).direction.norm_starProjection_apply_le (x - q.center)
      rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
      have hx' : dist x q.center ≤ (9 / 4 : ℝ) * q.radius := hx.2
      have hr := q.radius_pos
      change dist ((S q).direction.starProjection x) ((S q).direction.starProjection q.center) ≤
        (5 / 2 : ℝ) * q.radius
      linarith
    · rintro ⟨⟨u, rfl⟩, hx⟩
      exact ⟨(hgCoords u).1, hx⟩

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

theorem activeRegionSurface_charts_oai (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) (t : ℕ) :
    HasActiveSurfaceCharts μ R hR k z Good t S ε
      (activeRegionSurface μ R hR k z Good S hS t) := by
  induction t with
  | zero =>
    exact active_surface_charts_initial μ R hR k z Good S hS ε hε (by linarith) hfit
  | succ t ih =>
    exact active_surface_charts_successor μ R hR k z Good t S hS ε hε hεtiny hsmall hfit
      (activeRegionSurface μ R hR k z Good S hS t) ih

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.activeRegionSurface_charts_oai := @OAI.RieszRectifiability.activeRegionSurface_charts_oai
