-- Prove2me | solution 1 for OAI.RieszRectifiability.active_surface_successor_input_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:43.233219+00:00
-- url     : https://prove2.me/submissions/acc77bbc-c147-4066-a54e-9163743f664c

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionDiskLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection between subspace disks

Projecting a displacement orthogonally and translating its center carries a closed
disk into a disk of the same radius. The disk lift records this range constraint.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem projectionDiskLift_sub {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (u v : closedBall b ρ) :
    ((projectionDiskLift P Q a b ρ u).val : Ambient d) -
      ((projectionDiskLift P Q a b ρ v).val : Ambient d) =
        P.starProjection ((u.val : Ambient d) - (v.val : Ambient d)) := by
  change ((a : Ambient d) + P.starProjection ((u.val : Ambient d) - (b : Ambient d))) -
    ((a : Ambient d) + P.starProjection ((v.val : Ambient d) - (b : Ambient d))) = _
  calc
    _ = P.starProjection ((u.val : Ambient d) - (b : Ambient d)) -
        P.starProjection ((v.val : Ambient d) - (b : Ambient d)) := by abel
    _ = P.starProjection (((u.val : Ambient d) - (b : Ambient d)) -
        ((v.val : Ambient d) - (b : Ambient d))) := (map_sub _ _ _).symm
    _ = _ := by rw [sub_sub_sub_cancel_right]

theorem projectionDiskLift_lipschitz {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) : LipschitzWith 1 (projectionDiskLift P Q a b ρ) := by
  apply LipschitzWith.mk_one
  intro u v
  change ‖((projectionDiskLift P Q a b ρ u).val : Ambient d) -
    ((projectionDiskLift P Q a b ρ v).val : Ambient d)‖ ≤ dist u v
  rw [projectionDiskLift_sub]
  exact P.norm_starProjection_apply_le _

theorem projectionDiskLift_center {d : ℕ} (P Q : Submodule ℝ (Ambient d))
    (a : P) (b : Q) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    projectionDiskLift P Q a b ρ ⟨b, mem_closedBall_self hρ⟩ = ⟨a, mem_closedBall_self hρ⟩ := by
  apply Subtype.ext
  simp only [projectionDiskLift, sub_self, map_zero, add_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_PlaneChangeProjectedMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parameter maps under a change of plane

The disk lift and orthogonal projection transfer a parametrization to another
plane. Normal Lipschitz control and the distance between projections bound its
deviation from the identity parameter map.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem planeChangedParameterMap_error_lipschitz {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (b : Q) (ρ : ℝ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    LipschitzWith (L + α) (fun v : closedBall b ρ =>
      planeChangedParameterMap P Q a b ρ g v - v.val) := by
  let u := projectionDiskLift P Q a b ρ
  let N : closedBall b ρ → Ambient d :=
    fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g (u v))
  have hdecomp (v : closedBall a ρ) :
      g v = (v.val : Ambient d) + (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v) := by
    have hs : P.starProjection (g v) = (v.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoordinates v)
    have h := (P.starProjection_add_starProjection_orthogonal (g v)).symm
    rwa [hs] at h
  apply LipschitzWith.of_dist_le_mul
  intro v w
  let z : Ambient d := (v.val : Ambient d) - (w.val : Ambient d)
  have hQz : Q.starProjection z = z :=
    Q.starProjection_eq_self_iff.mpr (Q.sub_mem v.val.property w.val.property)
  have hPz : ‖P.starProjection z - z‖ ≤ (α : ℝ) * ‖z‖ := by
    have h := ((P.starProjection - Q.starProjection).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg z))
    change ‖P.starProjection z - Q.starProjection z‖ ≤ (α : ℝ) * ‖z‖ at h
    rwa [hQz] at h
  have hgdiff : g (u v) - g (u w) = P.starProjection z + (N v - N w) := by
    calc
      _ = (((u v).val : Ambient d) - ((u w).val : Ambient d)) + (N v - N w) := by
        rw [hdecomp (u v), hdecomp (u w)]
        dsimp only [N]
        abel
      _ = _ := by rw [projectionDiskLift_sub]
  have hN : ‖N v - N w‖ ≤ (L : ℝ) * dist v w := by
    have hn : ‖N v - N w‖ ≤ (L : ℝ) * dist (u v) (u w) := hnormal.dist_le_mul (u v) (u w)
    have hu : dist (u v) (u w) ≤ dist v w := by
      simpa only [NNReal.coe_one, one_mul] using!
        (projectionDiskLift_lipschitz P Q a b ρ).dist_le_mul v w
    exact hn.trans (mul_le_mul_of_nonneg_left hu L.coe_nonneg)
  have heq : (Q.starProjection (g (u v)) - (v.val : Ambient d)) -
      (Q.starProjection (g (u w)) - (w.val : Ambient d)) =
        Q.starProjection (P.starProjection z - z) + Q.starProjection (N v - N w) := by
    calc
      _ = Q.starProjection (g (u v) - g (u w)) - z := by
        rw [map_sub]
        dsimp only [z]
        abel
      _ = Q.starProjection (P.starProjection z + (N v - N w)) - Q.starProjection z := by
        rw [hgdiff, hQz]
      _ = _ := by simp only [map_add, map_sub]; abel
  change ‖(Q.starProjection (g (u v)) - (v.val : Ambient d)) -
    (Q.starProjection (g (u w)) - (w.val : Ambient d))‖ ≤ _
  rw [heq, NNReal.coe_add]
  calc
    _ ≤ ‖Q.starProjection (P.starProjection z - z)‖ + ‖Q.starProjection (N v - N w)‖ :=
      norm_add_le _ _
    _ ≤ (α : ℝ) * ‖z‖ + (L : ℝ) * dist v w :=
      add_le_add ((Q.norm_starProjection_apply_le _).trans hPz)
        ((Q.norm_starProjection_apply_le _).trans hN)
    _ = ((L : ℝ) + (α : ℝ)) * dist v w := by
      have hz : ‖z‖ = dist v w := rfl
      rw [hz]
      ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneChangeCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Disk coverage after changing the reference plane

A graph with small normal Lipschitz constant projects onto a smaller disk in a
nearby plane. Coverage follows from the Lipschitz perturbation bound for its
transferred parameter map.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem graph_covers_changed_plane_disk {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0) (hsmall : L + α < 1)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ⟩)
    closedBall b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) ⊆ Q.orthogonalProjectionOnto '' Set.range g := by
  let a₀ : closedBall a ρ := ⟨a, mem_closedBall_self hρ⟩
  let b := Q.orthogonalProjectionOnto (g a₀)
  let b₀ : closedBall b ρ := ⟨b, mem_closedBall_self hρ⟩
  let f := planeChangedParameterMap P Q a b ρ g
  have herror : LipschitzWith (L + α) (fun v : closedBall b ρ => f v - v.val) :=
    planeChangedParameterMap_error_lipschitz P Q a b ρ g L α hcoordinates hnormal hop
  have hzero : f b₀ - b₀.val = 0 := by
    change Q.orthogonalProjectionOnto (g (projectionDiskLift P Q a b ρ b₀)) - b = 0
    rw [projectionDiskLift_center P Q a b ρ hρ]
    exact sub_self _
  have hdisp : ∀ v : closedBall b ρ, dist (f v) v.val ≤ ((L : ℝ) + (α : ℝ)) * ρ := by
    intro v
    have h := herror.dist_le_mul v b₀
    rw [hzero, dist_zero_right, NNReal.coe_add] at h
    have hd : dist v b₀ ≤ ρ := v.property
    rw [dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left hd (add_nonneg L.coe_nonneg α.coe_nonneg))
  have hcover := closedBall_covered_by_lipschitz_perturbation b ρ
    (((L : ℝ) + (α : ℝ)) * ρ) hρ (L + α) hsmall f hdisp herror
  change closedBall b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) ⊆ Q.orthogonalProjectionOnto '' Set.range g
  intro y hy
  obtain ⟨v, hv⟩ := hcover hy
  exact ⟨g (projectionDiskLift P Q a b ρ v),
    ⟨projectionDiskLift P Q a b ρ v, rfl⟩, hv⟩

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionConeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem projection_cone_transfer_vector {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 2)
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ))
    (v : Ambient d)
    (hcone : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤ (L : ℝ) * ‖P.starProjection v‖) :
    ‖v‖ ≤ 2 * ‖Q.starProjection v‖ ∧
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
        (2 * ((L : ℝ) + (α : ℝ))) * ‖Q.starProjection v‖ := by
  have hdiff : ‖P.starProjection v - Q.starProjection v‖ ≤ (α : ℝ) * ‖v‖ :=
    ((P.starProjection - Q.starProjection).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg v))
  have hid : (Qᗮ : Submodule ℝ (Ambient d)).starProjection v =
      (Pᗮ : Submodule ℝ (Ambient d)).starProjection v +
        (P.starProjection v - Q.starProjection v) := by
    rw [Q.starProjection_orthogonal_val, P.starProjection_orthogonal_val]
    abel
  have hnormal : ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection v‖ ≤
      ((L : ℝ) + (α : ℝ)) * ‖v‖ := by
    rw [hid]
    calc
      _ ≤ ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection v‖ +
          ‖P.starProjection v - Q.starProjection v‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖P.starProjection v‖ + (α : ℝ) * ‖v‖ := add_le_add hcone hdiff
      _ ≤ (L : ℝ) * ‖v‖ + (α : ℝ) * ‖v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (P.norm_starProjection_apply_le v) L.coe_nonneg) le_rfl
      _ = _ := by ring
  have hinverse : ‖v‖ ≤ 2 * ‖Q.starProjection v‖ := by
    have htri := norm_add_le (Q.starProjection v)
      ((Qᗮ : Submodule ℝ (Ambient d)).starProjection v)
    rw [Q.starProjection_add_starProjection_orthogonal] at htri
    have hm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
    linarith
  refine ⟨hinverse, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hinverse (add_nonneg L.coe_nonneg α.coe_nonneg)
  nlinarith

theorem projection_cone_transfer {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (A : Set (Ambient d)) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 2)
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ))
    (hcone : ∀ x ∈ A, ∀ y ∈ A,
      ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (L : ℝ) * dist (P.starProjection x) (P.starProjection y)) :
    ∀ x ∈ A, ∀ y ∈ A,
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        (2 * ((L : ℝ) + (α : ℝ))) * dist (Q.starProjection x) (Q.starProjection y) := by
  intro x hx y hy
  have hp : ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      (L : ℝ) * ‖P.starProjection (x - y)‖ := by
    simpa only [map_sub, dist_eq_norm] using! hcone x hx y hy
  have h := (projection_cone_transfer_vector P Q L α hsmall hop (x - y) hp).2
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ParentChartPlaneHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring parent-chart height bounds

For adjacent cell scales, neighboring-plane projection estimates transfer a height bound
relative to the parent plane to a quantitative bound relative to the child plane.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem parent_chart_plane_height_transfer {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hscale : q.radius = 64 * i.radius)
    (hnear : dist i.center q.center ≤ 2 * q.radius)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε)
    (x : Ambient d) (hx : x ∈ closedBall q.center (3 * q.radius))
    (hheight : infDist x (W : Set (Ambient d)) ≤ (262144 * ε) * q.radius) :
    infDist x (S : Set (Ambient d)) ≤ (524288 * ε) * q.radius := by
  let : Nonempty S := hS.1.to_subtype
  let : Nonempty W := hW.1.to_subtype
  have hri := i.radius_pos
  have hrq := q.radius_pos
  have hsmall : i.radius ≤ q.radius := by rw [hscale]; linarith
  have hlarge : q.radius ≤ 64 * i.radius := hscale.le
  have hneighbor : dist i.center q.center ≤ 128 * q.radius := by linarith
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    hsmall hlarge hneighbor ε hε hεsmall S W hS hW hSi hWq
  have hScenter := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) S hS hSi).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hWcenter := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) W hW hWq).1 i.center
      (by change dist i.center q.center < 1024 * q.radius; linarith) i.center_mem_support
  have hdx : dist x i.center ≤ 5 * q.radius := by
    have ht := dist_triangle x q.center i.center
    rw [dist_comm q.center i.center] at ht
    have hx' : dist x q.center ≤ 3 * q.radius := hx
    linarith
  have hpair := affine_projection_pair_dist_bound S W i.center x (2048 * ε) hop
  have hm := mul_le_mul_of_nonneg_left hdx (show 0 ≤ 2048 * ε by positivity)
  have ht := dist_triangle (orthogonalProjection S x : Ambient d)
    (orthogonalProjection W x : Ambient d) x
  rw [dist_comm (orthogonalProjection S x : Ambient d) x,
    dist_orthogonalProjection_eq_infDist S x,
    dist_comm (orthogonalProjection W x : Ambient d) x,
    dist_orthogonalProjection_eq_infDist W x] at ht
  have hscaleError := mul_le_mul_of_nonneg_left hsmall hε.le
  nlinarith [mul_pos hε hrq]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_PlaneChangeCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reparameterizing a chart over a nearby plane

Small normal slope and a small change of projection leave a positive disk
covered in the new plane. The projection inverse defines a chart on this disk,
with quantitative Lipschitz bounds for the chart and its normal component.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_chart_over_nearby_plane {d : ℕ}
    (P Q : Submodule ℝ (Ambient d)) (a : P) (ρ : ℝ) (hρ : 0 < ρ)
    (g : closedBall a ρ → Ambient d) (L α : ℝ≥0)
    (hsmall : (L : ℝ) + (α : ℝ) ≤ 1 / 4)
    (hcoordinates : ∀ v, P.orthogonalProjectionOnto (g v) = v.val)
    (hnormal : LipschitzWith L
      (fun v => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (g v)))
    (hop : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ)) :
    let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ.le⟩)
    let r := ρ - ((L : ℝ) + (α : ℝ)) * ρ
    let D := closedBall b r
    0 < r ∧ ∃ h : D → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (2 * (L + α))
        (fun u => (Qᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ Q.orthogonalProjectionOnto (h u) = u.val) ∧
      Set.range h = Set.range g ∩ Q.orthogonalProjectionOnto ⁻¹' D := by
  let b := Q.orthogonalProjectionOnto (g ⟨a, mem_closedBall_self hρ.le⟩)
  let r := ρ - ((L : ℝ) + (α : ℝ)) * ρ
  let D := closedBall b r
  have hr : 0 < r := by
    have hm := mul_le_mul_of_nonneg_right hsmall hρ.le
    dsimp only [r]
    linarith
  have hcontract : L + α < 1 := by
    have h : ((L + α : ℝ≥0) : ℝ) < 1 := by
      rw [NNReal.coe_add]
      linarith
    exact_mod_cast h
  have hcover : D ⊆ Q.orthogonalProjectionOnto '' Set.range g :=
    graph_covers_changed_plane_disk P Q a ρ hρ.le g L α hcontract hcoordinates hnormal hop
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
  have hconeQ : ∀ x ∈ Set.range g, ∀ y ∈ Set.range g,
      ‖(Qᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
        ((2 * (L + α) : ℝ≥0) : ℝ) * dist (Q.starProjection x) (Q.starProjection y) := by
    intro x hx y hy
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add] using!
      projection_cone_transfer P Q (Set.range g) L α (hsmall.trans (by norm_num)) hop hcone x hx y hy
  obtain ⟨h, hLip, hnLip, hcoords, hrange⟩ :=
    exists_chart_on_covered_projection Q (Set.range g) (2 * (L + α)) D hcover hconeQ
  have hL : 1 + 2 * (L + α) ≤ (2 : ℝ≥0) := by
    have hh : ((1 + 2 * (L + α) : ℝ≥0) : ℝ) ≤ 2 := by
      rw [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
      linarith
    exact_mod_cast hh
  exact ⟨hr, h, hLip.weaken hL, hnLip, hcoords, hrange⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_ParentToChildInputChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Parent-to-child input charts

A parent chart is reparametrized over the nearby child plane and restricted to the child
disk. Projection and height estimates preserve the exact restricted range, the Lipschitz
and normal-component bounds, and containment in the physical child ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_parent_to_child_input_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (i q : SupportCellDescendant μ R hR k z)
    (hscale : q.radius = 64 * i.radius)
    (hnear : dist i.center q.center ≤ 2 * q.radius)
    (ε : ℝ) (hε : 0 < ε) (hεtiny : ε ≤ 1 / 268435456)
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (hSi : bilateralPlaneError μ i.center (1024 * i.radius) S < ε)
    (hWq : bilateralPlaneError μ q.center (1024 * q.radius) W < ε)
    (g : closedBall (W.direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) → Ambient d)
    (L : ℝ≥0) (hsmall : (L : ℝ) + 2048 * ε ≤ 1 / 8)
    (hcoordinates : ∀ u, W.direction.orthogonalProjectionOnto (g u) = u.val)
    (hnormal : LipschitzWith L
      (fun u => (W.directionᗮ : Submodule ℝ (Ambient d)).starProjection (g u)))
    (hheight : ∀ u, infDist (g u) (W : Set (Ambient d)) ≤ (262144 * ε) * q.radius)
    (hphysical : ∀ u, g u ∈ closedBall q.center (3 * q.radius)) :
    ∃ h : closedBall (S.direction.orthogonalProjectionOnto i.center) ((11 / 4 : ℝ) * i.radius) → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (2 * (L + Real.toNNReal (2048 * ε)))
        (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ Set.range g ∧ S.direction.orthogonalProjectionOnto (h u) = u.val ∧
        h u ∈ closedBall i.center (3 * i.radius)) ∧
      Set.range h = Set.range g ∩ S.direction.orthogonalProjectionOnto ⁻¹'
        closedBall (S.direction.orthogonalProjectionOnto i.center) ((11 / 4 : ℝ) * i.radius) := by
  let P := W.direction
  let Q := S.direction
  let a := P.orthogonalProjectionOnto q.center
  let ac := Q.orthogonalProjectionOnto i.center
  let ρ := (5 / 2 : ℝ) * q.radius
  have hri := i.radius_pos
  have hrq := q.radius_pos
  have hρ : 0 < ρ := by dsimp [ρ] <;> positivity
  let u0 : closedBall a ρ := ⟨a, mem_closedBall_self hρ.le⟩
  let b := Q.orthogonalProjectionOnto (g u0)
  let α : ℝ≥0 := ⟨2048 * ε, by positivity⟩
  have hα : α = Real.toNNReal (2048 * ε) := by
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (by positivity : 0 ≤ 2048 * ε)).symm
  have hεsmall : ε ≤ 1 / 1024 := by linarith
  have hop := neighbor_cell_projection_operator_norm_le μ R hR k z i q
    (by rw [hscale]; linarith) hscale.le (by linarith)
    ε hε hεsmall S W hS hW hSi hWq
  have hop' : ‖P.starProjection - Q.starProjection‖ ≤ (α : ℝ) := by
    rw [norm_sub_rev]
    exact hop
  have hsmall' : (L : ℝ) + (α : ℝ) ≤ 1 / 4 := by
    change (L : ℝ) + 2048 * ε ≤ 1 / 4
    linarith
  have hcq := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) W hW hWq).1 q.center
      (mem_ball_self (by positivity)) q.center_mem_support
  have hci := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) S hS hSi).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hx0 : dist (g u0) q.center ≤ (263168 * ε) * q.radius := by
    have h := dist_le_projection_add_plane_distances W hW.1 (g u0) q.center
    have hc : P.starProjection (g u0) = P.starProjection q.center :=
      congrArg (fun v : P => (v : Ambient d)) (hcoordinates u0)
    change dist (g u0) q.center ≤ dist (P.starProjection (g u0)) (P.starProjection q.center) +
      infDist (g u0) (W : Set (Ambient d)) + infDist q.center (W : Set (Ambient d)) at h
    rw [hc, dist_self, zero_add] at h
    nlinarith [hheight u0]
  have hx0small : dist (g u0) q.center ≤ q.radius / 16 := by
    have hm := mul_le_mul_of_nonneg_right hεtiny hrq.le
    nlinarith
  have hb : dist ac b ≤ 2 * q.radius + q.radius / 16 := by
    have hp := Q.norm_starProjection_apply_le (i.center - g u0)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    have ht := dist_triangle i.center q.center (g u0)
    rw [dist_comm q.center (g u0)] at ht
    change dist (Q.starProjection i.center) (Q.starProjection (g u0)) ≤ _
    linarith
  obtain ⟨hradius, j, hjLip, hjNormal, hjCoords, hjRange⟩ :=
    exists_chart_over_nearby_plane P Q a ρ hρ g L α hsmall' hcoordinates hnormal hop'
  have hcontain : dist ac b + (11 / 4 : ℝ) * i.radius ≤
      ρ - ((L : ℝ) + (α : ℝ)) * ρ := by
    have hm := mul_le_mul_of_nonneg_right hsmall hrq.le
    change dist ac b + (11 / 4 : ℝ) * i.radius ≤
      (5 / 2 : ℝ) * q.radius - ((L : ℝ) + 2048 * ε) * ((5 / 2 : ℝ) * q.radius)
    nlinarith
  obtain ⟨h, hhLip, hhNormal, hhCoords, hhRange⟩ :=
    exists_recentered_disk_chart Q b (ρ - ((L : ℝ) + (α : ℝ)) * ρ) j (2 * (L + α))
      (fun u => (hjCoords u).2) hjNormal ac ((11 / 4 : ℝ) * i.radius) hcontain
  have hL : 1 + 2 * (L + α) ≤ (2 : ℝ≥0) := by
    have hreal : ((1 + 2 * (L + α) : ℝ≥0) : ℝ) ≤ 2 := by
      change 1 + 2 * ((L : ℝ) + 2048 * ε) ≤ 2
      linarith
    exact_mod_cast hreal
  have hrange : Set.range h = Set.range g ∩ Q.orthogonalProjectionOnto ⁻¹'
      closedBall ac ((11 / 4 : ℝ) * i.radius) := by
    rw [hhRange, hjRange]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      refine ⟨⟨hy.1, ?_⟩, hy.2⟩
      have hy' : dist (Q.orthogonalProjectionOnto y) ac ≤ (11 / 4 : ℝ) * i.radius := hy.2
      have ht := dist_triangle (Q.orthogonalProjectionOnto y) ac b
      change dist (Q.orthogonalProjectionOnto y) b ≤ ρ - ((L : ℝ) + (α : ℝ)) * ρ
      linarith
  have hhg : ∀ u, h u ∈ Set.range g := by
    intro u
    exact (hrange ▸ (show h u ∈ Set.range h from ⟨u, rfl⟩)).1
  have hhheight : ∀ u, infDist (h u) (S : Set (Ambient d)) ≤ (524288 * ε) * q.radius := by
    intro u
    obtain ⟨v, hv⟩ := hhg u
    rw [← hv]
    exact parent_chart_plane_height_transfer μ R hR k z i q hscale hnear ε hε hεsmall
      S W hS hW hSi hWq (g v) (hphysical v) (hheight v)
  have hhphysical : ∀ u, h u ∈ closedBall i.center (3 * i.radius) := by
    intro u
    have hloc := plane_chart_location_of_height S hS.1 i.center ((11 / 4 : ℝ) * i.radius)
      ((524288 * ε) * q.radius) h (fun v => (hhCoords v).2) hhheight u
    have hm := mul_le_mul_of_nonneg_right hεtiny hri.le
    rw [hscale] at hloc
    change dist (h u) i.center ≤ 3 * i.radius
    nlinarith
  refine ⟨h, hhLip.weaken hL, ?_, ?_, hrange⟩
  · rwa [← hα]
  · intro u
    exact ⟨hhg u, (hhCoords u).2, hhphysical u⟩

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

theorem active_surface_successor_input_chart_oai
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
    HasActiveCellInputChart i (S i) A := by
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
  have hnear := q.dist_center_of_mem i.center hc
  obtain ⟨g, hgLip, hgNormal, hgCoords, hgCapture⟩ := hcharts q hq
  let L := Real.toNNReal (4 * activeProjectionError d ε)
  obtain ⟨hη, _⟩ := activeProjectionError_small_parameters d ε hε (by linarith)
  have hL : (L : ℝ) + 2048 * ε ≤ 1 / 8 := by
    change (Real.toNNReal (4 * activeProjectionError d ε) : ℝ) + 2048 * ε ≤ 1 / 8
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
    linarith
  obtain ⟨g', hg'Lip, _, hg'Coords, hg'Range⟩ :=
    exists_parent_to_child_input_chart μ R hR k z i q hscale hnear ε hε hεtiny
      (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA) g L hL
      (fun u => (hgCoords u).2.1) hgNormal
      (fun u => (hgCoords u).2.2.1) (fun u => (hgCoords u).2.2.2)
  refine ⟨g', hg'Lip, (fun u => (hg'Coords u).2.1),
    (fun u => (hg'Coords u).2.2), ?_, ?_⟩
  · rintro x ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := (hg'Coords u).1
    rw [← hv]
    exact (hgCoords v).1
  · intro x hx
    have hri := i.radius_pos
    have hxq : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
      have ht := dist_triangle x i.center q.center
      have hxi : dist x i.center ≤ (5 / 2 : ℝ) * i.radius := hx.2
      change dist x q.center ≤ (9 / 4 : ℝ) * q.radius
      nlinarith
    have hxg : x ∈ Set.range g := (hgCapture ▸ (show x ∈ A ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hx.1, hxq⟩)).1
    rw [hg'Range]
    refine ⟨hxg, ?_⟩
    have hp := (S i).direction.norm_starProjection_apply_le (x - i.center)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    have hxi : dist x i.center ≤ (5 / 2 : ℝ) * i.radius := hx.2
    change dist ((S i).direction.starProjection x) ((S i).direction.starProjection i.center) ≤
      (11 / 4 : ℝ) * i.radius
    linarith

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.active_surface_successor_input_chart_oai := @OAI.RieszRectifiability.active_surface_successor_input_chart_oai
