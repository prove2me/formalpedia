-- Prove2me | solution 1 for OAI.RieszRectifiability.quantitative_uniform_precision_area_models
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:34.229832+00:00
-- url     : https://prove2.me/submissions/63a3d5a9-810d-4a34-b2f8-6a23181adf30

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
import Theorems.Thm_OAI_RieszRectifiability_active_region_limit_all_radius_ball_area_ge
import Theorems.Thm_OAI_RieszRectifiability_active_region_limit_area_le_original_top
import Theorems.Thm_OAI_RieszRectifiability_active_region_limit_local_ball_area_le
import Theorems.Thm_OAI_RieszRectifiability_exists_active_region_limit_model

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_OrthogonalNormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Function

theorem exists_isometry_onto_subspace {q d : ℕ} (S : Submodule ℝ (Ambient d))
    (hdim : Module.finrank ℝ S = q) :
    ∃ N : Ambient q →ₗᵢ[ℝ] Ambient d, N.toLinearMap.range = S := by
  let b : OrthonormalBasis (Fin q) ℝ S :=
    (stdOrthonormalBasis ℝ S).reindex (finCongr hdim)
  let E : Ambient q ≃ₗᵢ[ℝ] S := b.repr.symm
  let N : Ambient q →ₗᵢ[ℝ] Ambient d :=
    { toLinearMap := S.subtype.comp E.toLinearEquiv.toLinearMap
      norm_map' := fun x => E.norm_map x }
  refine ⟨N, ?_⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (b.repr.symm y).property
  · intro hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    change ((b.repr.symm (b.repr ⟨x, hx⟩) : S) : Ambient d) = x
    simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_AffinePlaneNormalFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal coordinates for affine planes

Isometric tangent and normal frames express affine orthogonal projection and distance
to a plane in Euclidean coordinates. The frame construction chooses the point of the
plane nearest the origin as its base point.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set EuclideanGeometry

theorem exists_euclidean_isometric_embedding {n d : ℕ} (hnd : n ≤ d) :
    Nonempty (Ambient n →ₗᵢ[ℝ] Ambient d) := by
  have hdim : n ≤ Module.finrank ℝ (Ambient d) := by
    simpa only [finrank_euclideanSpace_fin] using! hnd
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  have hspan : Module.finrank ℝ (Submodule.span ℝ (range v)) = n := by
    simpa only [Fintype.card_fin] using! finrank_span_eq_card hv
  obtain ⟨L, _hL⟩ := exists_isometry_onto_subspace (Submodule.span ℝ (range v)) hspan
  exact ⟨L⟩

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ApproximatePlaneFits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_affine_n_plane {n d : ℕ} (hnd : n ≤ d) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S := by
  obtain ⟨L⟩ := exists_euclidean_isometric_embedding hnd
  refine ⟨L.toLinearMap.range.toAffineSubspace, ⟨0, ?_⟩, ?_⟩
  · exact L.toLinearMap.range.zero_mem
  · rw [Submodule.toAffineSubspace_direction, LinearMap.finrank_range_of_inj L.injective]
    exact finrank_euclideanSpace_fin

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

theorem exists_bilateral_plane_error_lt {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (a : Ambient d) (r ε : ℝ)
    (hbeta : bilateralBeta n μ a r < ε) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧ bilateralPlaneError μ a r S < ε := by
  obtain ⟨S, hS⟩ := exists_affine_n_plane hnd
  have hne : {t : ℝ | ∃ T : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n T ∧ t = bilateralPlaneError μ a r T}.Nonempty :=
    ⟨bilateralPlaneError μ a r S, S, hS, rfl⟩
  obtain ⟨t, ⟨T, hT, ht⟩, hlt⟩ := exists_lt_of_csInf_lt hne hbeta
  exact ⟨T, hT, ht ▸ hlt⟩

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

theorem finiteProjectionAverage_continuous (F : Finset ι)
    (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (hθ : ∀ i ∈ F, Continuous (θ i)) (hπ : ∀ i ∈ F, Continuous (π i)) :
    Continuous (finiteProjectionAverage F θ π) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  apply continuous_id.add
  exact continuous_finsetSum F (fun i hi => (hθ i hi).smul ((hπ i hi).sub continuous_id))

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

theorem nonemptyAffineProjection_lipschitz {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty) :
    LipschitzWith 1 (nonemptyAffineProjection S hS) := by
  let : Nonempty S := hS.to_subtype
  apply LipschitzWith.mk_one
  intro x y
  change dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S y : Ambient d) ≤ _
  rw [dist_eq_norm, affine_projection_difference S x y]
  exact S.direction.norm_starProjection_apply_le (x - y)

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

theorem activeRegionCell_good (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : activeRegionCell Good i) : Good i :=
  hi i le_rfl Subset.rfl

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

theorem cappedStoppingDistance_le_center_radius {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) (i : ι) :
    cappedStoppingDistance R c r x ≤ dist x (c i) + r i := by
  exact ciInf_le (cappedStoppingDistance_bddBelow R c r hR hr x) (some i)

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

theorem activeLevelWeight_lipschitz (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good t) :
    LipschitzWith (Real.toNNReal (4 * (9 : ℝ) ^ d / latticeRadius R (k + t)))
      (activeLevelWeight μ R hR k z Good t i) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  rw [Real.dist_eq]
  have hsingle := Finset.single_le_sum
    (s := activeLevelIndex μ R hR k z Good t)
    (f := fun j => |activeLevelWeight μ R hR k z Good t j x -
      activeLevelWeight μ R hR k z Good t j y|)
    (fun _ _ => abs_nonneg _) hi
  calc
    _ ≤ _ := hsingle
    _ ≤ (4 * (9 : ℝ) ^ d) * (dist x y / latticeRadius R (k + t)) :=
      activeLevelWeight_sum_abs_sub_le μ R hR k z Good t x y
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

theorem activeLevelProjectionMap_continuous :
    Continuous (activeLevelProjectionMap μ R hR k z Good t S hS) :=
  finiteProjectionAverage_continuous _ _ _
    (fun i hi => (activeLevelWeight_lipschitz μ R hR k z Good t i hi).continuous)
    (fun i _ => (nonemptyAffineProjection_lipschitz (S i) (hS i).1).continuous)

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

theorem activeLevelProjectionMap_support_displacement (ε : ℝ) (hε : 0 ≤ ε)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (x : Ambient d) (hx : x ∈ μ.support) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤
      (1024 * ε) * latticeRadius R (k + t) := by
  apply finiteProjectionAverage_dist_self_le _ _ _ x _
    (mul_nonneg (mul_nonneg (by norm_num) hε) (latticeRadius_pos R hR (k + t)).le)
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hrad : i.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  have hr := i.radius_pos
  have hball : x ∈ ball i.center (1024 * i.radius) := by
    change dist x i.center < 1024 * i.radius
    rw [← hrad] at hnear
    linarith
  have hdist := (bilateralPlaneError_lt_pointwise μ ⟨x, hx⟩ i.center
    (1024 * i.radius) ε (by positivity) (S i) (hS i) (hfit i hi)).1 x hball hx
  rw [nonemptyAffineProjection_dist_self]
  calc
    _ ≤ ε * (1024 * i.radius) := hdist.le
    _ = _ := by rw [hrad]; ring

theorem exists_active_level_projection_maps (hnd : n ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
      (hT : ∀ i, IsAffineNPlane n (T i)),
      (∀ i, activeRegionCell
          (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) i →
        bilateralPlaneError μ i.center (1024 * i.radius) (T i) < ε) ∧
      ∀ s : ℕ,
        Continuous (activeLevelProjectionMap μ R hR k z
          (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT) ∧
        (∀ x ∈ μ.support,
          dist (activeLevelProjectionMap μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT x) x ≤
              (1024 * ε) * latticeRadius R (k + s)) ∧
        (∀ x, 5 * latticeRadius R (k + s) ≤ cellRegionStoppingScale μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) x →
          activeLevelProjectionMap μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT x = x) := by
  classical
  let G : SupportCellDescendant μ R hR k z → Prop :=
    fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨T₀, hT₀⟩ := exists_affine_n_plane hnd
  have hex (i : SupportCellDescendant μ R hR k z) :
      ∃ T : AffineSubspace ℝ (Ambient d), IsAffineNPlane n T ∧
        (activeRegionCell G i → bilateralPlaneError μ i.center (1024 * i.radius) T < ε) := by
    by_cases hi : activeRegionCell G i
    · obtain ⟨T, hT, hf⟩ := exists_bilateral_plane_error_lt hnd μ i.center
        (1024 * i.radius) ε (activeRegionCell_good G i hi)
      exact ⟨T, hT, fun _ => hf⟩
    · exact ⟨T₀, hT₀, fun h => (hi h).elim⟩
  choose T hT hfit using hex
  refine ⟨T, hT, hfit, ?_⟩
  intro s
  refine ⟨activeLevelProjectionMap_continuous μ R hR k z G s T hT, ?_, ?_⟩
  · intro x hx
    apply activeLevelProjectionMap_support_displacement μ R hR k z G s T hT ε hε.le
      (fun i hi => hfit i ((mem_activeLevelIndex μ R hR k z G s i).mp hi).2) x hx
  · intro x hx
    exact activeLevelProjectionMap_eq_self_of_large_scale μ R hR k z G s T hT x hx

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

theorem activeRegionLargeRadiusLowerAreaConstant_pos (n : ℕ) :
    0 < activeRegionLargeRadiusLowerAreaConstant n := by
  exact ENNReal.mul_pos (planeDiskLowerAreaConstant_pos n 1).ne' (by positivity)

theorem activeRegionLargeRadiusLowerAreaConstant_lt_top (n : ℕ) :
    activeRegionLargeRadiusLowerAreaConstant n < ⊤ := by
  exact ENNReal.mul_lt_top (planeDiskLowerAreaConstant_lt_top n 1 (by norm_num)) (by finiteness)

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

theorem planeChartBallAreaConstant_lt_top (n : ℕ) (K L : ℝ≥0) :
    planeChartBallAreaConstant n K L < ⊤ := by
  exact ENNReal.mul_lt_top (by finiteness) (planeUnitHausdorffMeasure_lt_top n)

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

theorem activeRegionLowScaleAreaFactor_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionLowScaleAreaFactor n C G < ⊤ := by
  have hs := activeRegionStopMassAreaConstant_lt_top n G
  unfold activeRegionLowScaleAreaFactor
  finiteness

theorem activeRegionSmallRadiusLowerAreaConstant_pos (n : ℕ) (C G : ℝ) :
    0 < activeRegionSmallRadiusLowerAreaConstant n C G := by
  apply lt_min
  · exact ENNReal.inv_pos.mpr (activeRegionLowScaleAreaFactor_lt_top n C G).ne
  · exact ENNReal.mul_pos (activeRegionPositiveLocalLowerAreaConstant_pos n).ne' (by positivity)

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

theorem activeRegionAllRadiusLowerAreaConstant_pos (n : ℕ) (C G : ℝ) :
    0 < activeRegionAllRadiusLowerAreaConstant n C G := by
  apply lt_min
  · exact ENNReal.mul_pos (activeRegionSmallRadiusLowerAreaConstant_pos n C G).ne' (by positivity)
  · exact activeRegionLargeRadiusLowerAreaConstant_pos n

theorem activeRegionAllRadiusLowerAreaConstant_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionAllRadiusLowerAreaConstant n C G < ⊤ :=
  lt_of_le_of_lt (min_le_right _ _) (activeRegionLargeRadiusLowerAreaConstant_lt_top n)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLargeScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionLargeAreaConstant_lt_top (n d : ℕ) :
    activeRegionLargeAreaConstant n d < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) (by finiteness))
    (planeUnitHausdorffMeasure_lt_top n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLimitEmbedding
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
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hS hε hεtiny hsmall hfit hmodel

theorem active_region_limit_injective : Function.Injective f := by
  intro u v huv
  let B := (17039360 * ε) / 63
  have htail : ∀ t (w : S (supportCellRoot μ R hR k z)),
      dist (activeRegionParameterMap μ R hR k z Good S hS t w) (f w) ≤
      B * latticeRadius R (k + t) := hmodel.2.2.2.1
  have hbound : ∀ t : ℕ, dist u v ≤
      (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t := by
    intro t
    have hfinite := activeRegionParameterMap_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit t u v
    have hpair : dist (activeRegionParameterMap μ R hR k z Good S hS t u)
        (activeRegionParameterMap μ R hR k z Good S hS t v) ≤
        2 * B * latticeRadius R (k + t) := by
      have ht := dist_triangle (activeRegionParameterMap μ R hR k z Good S hS t u)
        (f u) (activeRegionParameterMap μ R hR k z Good S hS t v)
      have hv : dist (f u) (activeRegionParameterMap μ R hR k z Good S hS t v) ≤
          B * latticeRadius R (k + t) := by rw [huv, dist_comm]; exact htail t v
      linarith [htail t u]
    have hm := mul_le_mul_of_nonneg_left (hfinite.1.trans hpair)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) t)
    have hleft : (4 : ℝ) ^ t * ((1 / 4 : ℝ) ^ t * dist u v) = dist u v := by
      rw [← mul_assoc, ← mul_pow]
      norm_num
    have hright : (4 : ℝ) ^ t * (2 * B * latticeRadius R (k + t)) =
        (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t := by
      rw [latticeRadius_add]
      calc
        _ = (2 * B * latticeRadius R k) * ((4 : ℝ) ^ t * (1 / 64 : ℝ) ^ t) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    rw [hleft, hright] at hm
    exact hm
  have hlim : Tendsto (fun t : ℕ => (2 * B * latticeRadius R k) * (1 / 16 : ℝ) ^ t)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16)
        (by norm_num : (1 / 16 : ℝ) < 1)).const_mul (2 * B * latticeRadius R k)
  exact dist_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) dist_nonneg)

theorem active_region_limit_isClosedEmbedding : IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hmodel.1
    (active_region_limit_injective μ R hR k z Good S hS ε hε hεtiny hsmall hfit f hmodel)
    hmodel.2.1.isClosedMap

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive stopping-scale charts bound the local Hausdorff area of an active-region limit
surface by a finite dimensional constant times the cell radius to the power `n`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionLocalAreaConstant_lt_top (n d : ℕ) :
    activeRegionLocalAreaConstant n d < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (planeUnitHausdorffMeasure_lt_top n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSmallScaleArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionSmallScaleAreaConstant_lt_top (n d : ℕ) (C : ℝ) :
    activeRegionSmallScaleAreaConstant n d C < ⊤ := by
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (activeRegionLocalAreaConstant_lt_top n d) (by finiteness))
    ENNReal.ofReal_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionZeroSetArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem activeRegionZeroAreaConstant_lt_top (n : ℕ) (C : ℝ) :
    activeRegionZeroAreaConstant n C < ⊤ := by
  exact ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionZeroLocalArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem activeRegionZeroLocalAreaConstant_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionZeroLocalAreaConstant n C G < ⊤ := by
  unfold activeRegionZeroLocalAreaConstant
  finiteness

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLocalUpperArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionLocalUpperAreaConstant_lt_top (n d : ℕ) (C G : ℝ) :
    activeRegionLocalUpperAreaConstant n d C G < ⊤ := by
  have hz := activeRegionZeroLocalAreaConstant_lt_top n C G
  have hs := activeRegionSmallScaleAreaConstant_lt_top n d C
  have hp := planeChartBallAreaConstant_lt_top n 16 64
  have hh := planeChartBallAreaConstant_lt_top n 4 16
  unfold activeRegionLocalUpperAreaConstant
  finiteness

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_OriginalTopAreaCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem enlargedTopMassConstant_lt_top (n : ℕ) (C G : ℝ) :
    enlargedTopMassConstant n C G < ⊤ := by
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionUniformArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem activeRegionUniformAreaConstant_lt_top (n d : ℕ) (C G : ℝ) :
    activeRegionUniformAreaConstant n d C G < ⊤ := by
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨activeRegionZeroAreaConstant_lt_top n C,
      ENNReal.mul_lt_top (activeRegionSmallScaleAreaConstant_lt_top n d C)
        (enlargedTopMassConstant_lt_top n C G)⟩,
    ENNReal.mul_lt_top (activeRegionLargeAreaConstant_lt_top n d) ENNReal.ofReal_lt_top⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Uniformity_SurfacePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Class-uniform surface pieces for restart charts

Uniform upper and lower area estimates give native surface measures with common
growth and projection bounds. A geometric loss estimate then chooses a finite
chart depth for any positive deficit. The precision, Lipschitz bounds, and restart
piece parameters are selected from the fixed dimensions and regularity constants
before the original measure or its support cell is introduced.
-/

namespace RieszRectifiability
noncomputable section
open MeasureTheory Metric Set Topology
open scoped NNReal ENNReal

/-- Area comparison constants are uniform over the measure class and the allowed precision. -/
theorem quantitative_uniform_precision_area_models_oai {n d : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    (C G : ℝ) (hC : 1 ≤ C) (hG : 0 < G) :
    ∃ Ktop : ℝ≥0∞, Ktop < ⊤ ∧ ∃ Kupper : ℝ≥0∞, Kupper < ⊤ ∧
      ∃ Klower : ℝ≥0∞, 0 < Klower ∧ Klower < ⊤ ∧
      ∀ (μ : Measure (Ambient d)) [μ.Regular], ADRegularWithConstant n C μ →
      GlobalUpperGrowth n G μ → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 281474976710656 → activeProjectionError d ε ≤ 1 / 128 →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Good := fun q : SupportCellDescendant μ R hR k z =>
          bilateralBeta n μ q.center (1024 * q.radius) < ε
        ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
          (hS : ∀ i, IsAffineNPlane n (S i)),
          (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
          ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
            IsActiveRegionLimitModel μ R hR k z Good S hS ε f ∧ IsClosedEmbedding f ∧
            (μH[(n : ℝ)] : Measure (Ambient d))
              (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
                Ktop * μ (cleanSupportCell μ R hR k z) ∧
            (∀ (p : Ambient d) (r : ℝ), 0 < r →
              (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
                Kupper * (ENNReal.ofReal r) ^ n) ∧
            ∀ p ∈ Set.range f, ∀ (r : ℝ), 0 < r →
              Klower * (ENNReal.ofReal r) ^ n ≤
                (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨activeRegionUniformAreaConstant n d C G,
    activeRegionUniformAreaConstant_lt_top n d C G,
    activeRegionLocalUpperAreaConstant n d C G,
    activeRegionLocalUpperAreaConstant_lt_top n d C G,
    activeRegionAllRadiusLowerAreaConstant n C G,
    activeRegionAllRadiusLowerAreaConstant_pos n C G,
    activeRegionAllRadiusLowerAreaConstant_lt_top n C G, ?_⟩
  intro μ _hreg hAD hg ε hε hεfine hsmall R hR k z hcore
  have hballs := hAD.2
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
  obtain ⟨f, hmodel⟩ := exists_active_region_limit_model μ R hR k z Good S hS ε hε hεtiny hsmall hfit
  refine ⟨S, hS, hfit, f, hmodel,
    active_region_limit_isClosedEmbedding μ R hR k z Good S hS ε hε hεtiny hsmall hfit f hmodel,
    active_region_limit_area_le_original_top μ C G hCpos hG hg
      (fun x hx r hr => (hballs x hx r hr).1) R hR k hcore z Good S hS ε hε hεfine hsmall hfit f hmodel,
    ?_, ?_⟩
  · intro p r hr
    exact active_region_limit_local_ball_area_le μ C G hCpos hG hg
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p r hr
  · intro p hp r hr
    exact active_region_limit_all_radius_ball_area_ge hn μ C G hCpos hG hg
      (fun x hx s hs => (hballs x hx s hs).1) R hR k hcore z Good S hS
      ε hε hεfine hsmall hfit f hmodel p hp r hr

end
end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.quantitative_uniform_precision_area_models_oai := @OAI.RieszRectifiability.quantitative_uniform_precision_area_models_oai
