-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:51.539641+00:00
-- url     : https://prove2.me/submissions/e362595b-b334-48b3-96fa-1e1e2de9d393

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000
import Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_full_planar_measure_limit
import Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_source_excess_limit

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineAnchorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An affine map controlled at a base point and its basis anchors is controlled at every affine
combination by the sum of the absolute coordinates. The operator norm of the basis-coordinate
map bounds that sum in terms of the dimension and the ambient norm on the subspace.
-/

namespace RieszRectifiability

noncomputable section

open Module
open scoped BigOperators

theorem affine_map_norm_bound_from_anchors {n d q : ℕ}
    (c : Ambient q) (B : Ambient d →L[ℝ] Ambient q) (a : Ambient d)
    (v : Fin n → Ambient d) (t : Fin n → ℝ) (ε : ℝ)
    (hbase : ‖c + B a‖ ≤ ε) (hvertices : ∀ i, ‖c + B (a + v i)‖ ≤ ε) :
    ‖c + B (a + ∑ i, t i • v i)‖ ≤ ε * (1 + 2 * ∑ i, |t i|) := by
  have hv : ∀ i, ‖B (v i)‖ ≤ 2 * ε := by
    intro i
    calc
      _ = ‖(c + B (a + v i)) - (c + B a)‖ := by rw [map_add]; congr 1; abel
      _ ≤ ‖c + B (a + v i)‖ + ‖c + B a‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hvertices i]
  calc
    _ = ‖(c + B a) + ∑ i, t i • B (v i)‖ := by
      simp only [map_add, map_sum, map_smul, add_assoc]
    _ ≤ ‖c + B a‖ + ‖∑ i, t i • B (v i)‖ := norm_add_le _ _
    _ ≤ ε + ∑ i, ‖t i • B (v i)‖ :=
      add_le_add hbase (norm_sum_le _ _)
    _ ≤ ε + ∑ i, |t i| * (2 * ε) := by
      apply add_le_add (le_refl ε)
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end

end RieszRectifiability

end OAI
end

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_EuclideanBallNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_euclidean_ball_net {k : ℕ} (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ s : Finset (Ambient k),
      (∀ x ∈ s, ‖x‖ ≤ R) ∧
      (∀ x : Ambient k, ‖x‖ ≤ R → ∃ y ∈ s, dist x y < δ) ∧
      (s.card : ℝ) * (δ / 2) ^ k ≤ (R + δ / 2) ^ k := by
  classical
  let P : Finset (Ambient k) → Prop := fun s =>
    (∀ x ∈ s, ‖x‖ ≤ R) ∧ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y
  have hr : 0 < δ / 2 := by positivity
  have hcount : ∀ s, P s → (s.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ k := by
    intro s hs
    apply euclidean_separated_card_le s R (δ / 2) hR hr hs.1
    intro x hx y hy hxy
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! hs.2 x hx y hy hxy
  let cards : Set ℕ := {m | ∃ s : Finset (Ambient k), P s ∧ s.card = m}
  have hne : cards.Nonempty := ⟨0, ∅, by simp [P], rfl⟩
  obtain ⟨B, hB⟩ := exists_nat_gt (((R + δ / 2) / (δ / 2)) ^ k)
  have hbdd : BddAbove cards := by
    refine ⟨B, ?_⟩
    rintro m ⟨s, hs, rfl⟩
    exact_mod_cast (hcount s hs).trans hB.le
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ t, P t → t.card ≤ s.card := by
    intro t ht
    rw [hcard]
    exact le_csSup hbdd ⟨t, ht, rfl⟩
  refine ⟨s, hs.1, ?_, ?_⟩
  · intro x hx
    by_contra hmissing
    have hfar : ∀ y ∈ s, δ ≤ dist x y := by
      intro y hy
      exact le_of_not_gt (fun h => hmissing ⟨y, hy, h⟩)
    have hnot : x ∉ s := by
      intro hxmem
      have h := hfar x hxmem
      rw [dist_self] at h
      exact (not_le_of_gt hδ) h
    have hnew : P (insert x s) := by
      constructor
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hs.1 y hy
      · intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | hsu
        · rcases Finset.mem_insert.mp hv with rfl | hsv
          · exact (huv rfl).elim
          · exact hfar v hsv
        · rcases Finset.mem_insert.mp hv with rfl | hsv
          · simpa only [dist_comm] using! hfar u hsu
          · exact hs.2 u hsu v hsv huv
    have h := hmax (insert x s) hnew
    rw [Finset.card_insert_of_notMem hnot] at h
    omega
  · apply euclidean_separated_card_mul_radius_pow_le s R (δ / 2) hR hr hs.1
    intro x hx y hy hxy
    have h := hs.2 x hx y hy hxy
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LeastSquaredExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Least-squared approximation by affine planes

The squared excess minimizes the radius-normalized quadratic distance over affine planes
of the prescribed dimension. Local finiteness ensures that these distance integrals exist
on balls.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem squared_infDist_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (a : Ambient d) (r : ℝ)
    (s : Set (Ambient d)) (hs : s.Nonempty) :
    IntegrableOn (fun x => infDist x s ^ 2) (ball a r) μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top))
  obtain ⟨p, hp⟩ := hs
  have hm : MemLp (fun x => infDist x s) 2 (μ.restrict (ball a r)) := by
    apply MemLp.of_bound (continuous_infDist_pt s).aestronglyMeasurable (r + dist a p)
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg infDist_nonneg]
    have hx' : dist x a ≤ r := hx.le
    exact (infDist_le_dist_of_mem hp).trans ((dist_triangle x a p).trans
      (add_le_add hx' (le_refl (dist a p))))
  exact hm.integrable_sq

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

theorem normalizedNormalHeight_reconstruct {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    δ • N (normalizedNormalHeight a N δ x) = N (N.toContinuousLinearMap.adjoint (x - a)) := by
  rw [normalizedNormalHeight, map_smul, smul_smul, mul_inv_cancel₀ hδ, one_smul]

theorem normal_coordinates_decomposition {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : δ ≠ 0) (x : Ambient d) :
    x - a = L (L.toContinuousLinearMap.adjoint (x - a)) + δ • N (normalizedNormalHeight a N δ x) := by
  rw [normalizedNormalHeight_reconstruct a N δ hδ]
  exact (hsplit (x - a)).symm

theorem physical_projection_distance_eq {n q d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) + N (N.toContinuousLinearMap.adjoint y) = y)
    (δ : ℝ) (hδ : 0 < δ) (x : Ambient d) :
    dist x (tangentPlaneProjection a L x) = δ * ‖normalizedNormalHeight a N δ x‖ := by
  have h := normal_coordinates_decomposition a L N hsplit δ hδ.ne' x
  have he : x - tangentPlaneProjection a L x = δ • N (normalizedNormalHeight a N δ x) := by
    unfold tangentPlaneProjection
    rw [← sub_sub]
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, N.norm_map]

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

theorem isometric_range_starProjection {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (x : Ambient d) :
    L.toLinearMap.range.starProjection x = L (L.toContinuousLinearMap.adjoint x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (LinearMap.mem_range_self L.toLinearMap (L.toContinuousLinearMap.adjoint x))
  change x - L (L.toContinuousLinearMap.adjoint x) ∈ L.toContinuousLinearMap.rangeᗮ
  rw [L.toContinuousLinearMap.orthogonal_range]
  change L.toContinuousLinearMap.adjoint (x - L (L.toContinuousLinearMap.adjoint x)) = 0
  have hL : L.toContinuousLinearMap.adjoint (L (L.toContinuousLinearMap.adjoint x)) =
      L.toContinuousLinearMap.adjoint x :=
    DFunLike.congr_fun L.adjoint_comp_self (L.toContinuousLinearMap.adjoint x)
  rw [map_sub, hL, sub_self]

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

theorem exists_isometric_normal_embedding {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      N.toLinearMap.range = L.toLinearMap.rangeᗮ := by
  let S := L.toLinearMap.range
  have hS : Module.finrank ℝ S = n := by
    rw [LinearMap.finrank_range_of_inj L.injective]
    exact finrank_euclideanSpace_fin
  have hdim : Module.finrank ℝ Sᗮ = d - n := by
    have h := S.finrank_add_finrank_orthogonal
    rw [hS, finrank_euclideanSpace_fin] at h
    omega
  exact exists_isometry_onto_subspace Sᗮ hdim

theorem exists_complete_normal_frame {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      (∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) ∧
      ∀ x, L (L.toContinuousLinearMap.adjoint x) + N (N.toContinuousLinearMap.adjoint x) = x := by
  obtain ⟨N, hN⟩ := exists_isometric_normal_embedding L
  refine ⟨N, ?_, ?_⟩
  · intro y
    have hm : N y ∈ L.toLinearMap.rangeᗮ := by
      rw [← hN]
      exact LinearMap.mem_range_self N.toLinearMap y
    change N y ∈ L.toContinuousLinearMap.rangeᗮ at hm
    rw [L.toContinuousLinearMap.orthogonal_range] at hm
    exact hm
  · intro x
    have hL := isometric_range_starProjection L x
    have hP := isometric_range_starProjection N x
    have hP' : L.toLinearMap.rangeᗮ.starProjection x = N (N.toContinuousLinearMap.adjoint x) := by
      have heq := congrArg (fun S : Submodule ℝ (Ambient d) => S.starProjection x) hN
      exact heq.symm.trans hP
    rw [← hL, ← hP']
    exact L.toLinearMap.range.starProjection_add_starProjection_orthogonal x

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

theorem affine_plane_projection_of_frame {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (a : Ambient d) (ha : a ∈ S)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hL : L.toLinearMap.range = S.direction)
    (x : Ambient d) :
    (orthogonalProjection S x : Ambient d) = tangentPlaneProjection a L x := by
  have hproj : S.direction.starProjection (x - a) =
      L (L.toContinuousLinearMap.adjoint (x - a)) := by
    have heq := congrArg (fun T : Submodule ℝ (Ambient d) => T.starProjection (x - a)) hL
    exact heq.symm.trans (isometric_range_starProjection L (x - a))
  calc
    _ = S.direction.starProjection (x - a) + a := by
      simpa only [vsub_eq_sub, vadd_eq_add, Submodule.coe_orthogonalProjectionOnto_apply]
        using! orthogonalProjection_apply_mem S ha (p := x)
    _ = _ := by rw [hproj]; exact add_comm _ _

theorem affine_plane_distance_normal_frame {n q d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (a : Ambient d) (ha : a ∈ S)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (hL : L.toLinearMap.range = S.direction)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hsplit : ∀ y, L (L.toContinuousLinearMap.adjoint y) +
      N (N.toContinuousLinearMap.adjoint y) = y) (x : Ambient d) :
    infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖ := by
  rw [← dist_orthogonalProjection_eq_infDist S x, affine_plane_projection_of_frame S a ha L hL]
  simpa only [normalizedNormalHeight, inv_one, one_smul, one_mul]
    using! physical_projection_distance_eq a L N hsplit 1 zero_lt_one x

theorem exists_affine_plane_normal_frame {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    ∃ a : Ambient d, a ∈ S ∧ ‖a‖ = infDist (0 : Ambient d) (S : Set (Ambient d)) ∧
      ∃ L : Ambient n →ₗᵢ[ℝ] Ambient d, L.toLinearMap.range = S.direction ∧
      ∃ N : Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
        (∀ y, L.toContinuousLinearMap.adjoint (N y) = 0) ∧
        (∀ y, L (L.toContinuousLinearMap.adjoint y) +
          N (N.toContinuousLinearMap.adjoint y) = y) ∧
        ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖ := by
  let : Nonempty S := hS.1.to_subtype
  let a : Ambient d := orthogonalProjection S (0 : Ambient d)
  have ha : a ∈ S := orthogonalProjection_mem (0 : Ambient d)
  have hnorm : ‖a‖ = infDist (0 : Ambient d) (S : Set (Ambient d)) := by
    simpa only [dist_zero_left] using! dist_orthogonalProjection_eq_infDist S (0 : Ambient d)
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace S.direction hS.2
  obtain ⟨N, horth, hsplit⟩ := exists_complete_normal_frame L
  exact ⟨a, ha, hnorm, L, hL, N, horth, hsplit,
    affine_plane_distance_normal_frame S a ha L hL N hsplit⟩

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

theorem affine_projection_dist_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (x y : Ambient d) :
    dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S y : Ambient d) ≤ dist x y := by
  rw [dist_eq_norm, affine_projection_difference, dist_eq_norm]
  exact S.direction.norm_starProjection_apply_le (x - y)

theorem exists_affine_tube_ball_cover {k d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ c : Finset (Ambient d),
      (∀ x : Ambient d, ‖x‖ ≤ R → infDist x (S : Set (Ambient d)) < δ →
        ∃ y ∈ c, dist x y < 2 * δ) ∧
      (c.card : ℝ) * (δ / 2) ^ k ≤ (R + δ / 2) ^ k := by
  classical
  let : Nonempty S := hS.1.to_subtype
  let a : Ambient d := orthogonalProjection S (0 : Ambient d)
  have ha : a ∈ S := orthogonalProjection_mem (0 : Ambient d)
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace S.direction hS.2
  obtain ⟨s, _hs, hcover, hcard⟩ := exists_euclidean_ball_net (k := k) R δ hR hδ
  let f : Ambient k → Ambient d := fun t => a + L t
  have hf : Function.Injective f := by
    intro t t' h
    exact L.injective (add_left_cancel h)
  refine ⟨s.image f, ?_, ?_⟩
  · intro x hx hdist
    let p : Ambient d := orthogonalProjection S x
    have hp : p ∈ S := orthogonalProjection_mem x
    have hdir : p - a ∈ L.toLinearMap.range := by
      rw [hL]
      exact AffineSubspace.vsub_mem_direction hp ha
    obtain ⟨t, ht⟩ := hdir
    change L t = p - a at ht
    have hpt : a + L t = p := by rw [ht]; abel
    have htR : ‖t‖ ≤ R := by
      calc
        _ = ‖L t‖ := (L.norm_map t).symm
        _ = dist p a := by rw [ht, dist_eq_norm]
        _ ≤ dist x 0 := affine_projection_dist_le S x 0
        _ = ‖x‖ := dist_zero_right x
        _ ≤ R := hx
    obtain ⟨y, hy, hty⟩ := hcover t htR
    refine ⟨f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    have hpdist : dist p (f y) = dist t y := by
      change dist p (a + L y) = dist t y
      rw [← hpt, dist_add_left, L.isometry.dist_eq]
    have hxp : dist x p < δ := by
      simpa only [p, dist_orthogonalProjection_eq_infDist] using! hdist
    have htri := dist_triangle x p (f y)
    rw [hpdist] at htri
    linarith
  · rw [Finset.card_image_of_injective s hf]
    exact hcard

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AffineTubeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem affineTube_measure_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    μ (affineTube S R δ) ≤
      ENNReal.ofReal (C * (2 * δ) ^ n * (((R + δ / 2) / (δ / 2)) ^ k)) := by
  obtain ⟨c, hcover, hcard⟩ := exists_affine_tube_ball_cover S hS R δ hR hδ
  have hsub : affineTube S R δ ⊆ ⋃ y ∈ c, ball y (2 * δ) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
    obtain ⟨y, hy, hxy⟩ := hcover x hxR hx.2
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, by simpa only [mem_ball, dist_comm] using! hxy⟩⟩
  have hB : 0 ≤ C * (2 * δ) ^ n := mul_nonneg hg.1 (pow_nonneg (by positivity) n)
  have hbound : μ (affineTube S R δ) ≤ ENNReal.ofReal ((c.card : ℝ) * (C * (2 * δ) ^ n)) := by
    calc
      _ ≤ μ (⋃ y ∈ c, ball y (2 * δ)) := measure_mono hsub
      _ ≤ ∑ y ∈ c, μ (ball y (2 * δ)) := measure_biUnion_finset_le c _
      _ ≤ ∑ _y ∈ c, ENNReal.ofReal (C * (2 * δ) ^ n) := by
        apply Finset.sum_le_sum
        intro y _hy
        exact hg.2 y (2 * δ) (by positivity)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul
          (Nat.cast_nonneg c.card : (0 : ℝ) ≤ c.card), ENNReal.ofReal_natCast]
  have hc : (c.card : ℝ) ≤ ((R + δ / 2) / (δ / 2)) ^ k := by
    rw [div_pow]
    exact (le_div_iff₀ (pow_pos (by positivity : 0 < δ / 2) k)).mpr hcard
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_comm] using! mul_le_mul_of_nonneg_right hc hB

theorem affineTube_real_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S)
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    μ.real (affineTube S R δ) ≤ C * (2 * δ) ^ n * (((R + δ / 2) / (δ / 2)) ^ k) := by
  have hC := hg.1
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (affineTube_measure_bound μ C hg S hS R δ hR hδ)

theorem lower_dimensional_affineTube_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    μ.real (affineTube S R (τ * R)) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ * R ^ n := by
  have hC := hg.1
  have hδ : 0 < τ * R := mul_pos hτ hR
  have hratio : (R + τ * R / 2) / (τ * R / 2) ≤ 3 / τ := by
    have heq : (R + τ * R / 2) / (τ * R / 2) = (2 + τ) / τ := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) hτ.le
  have hpow : τ ^ (n - k) ≤ τ := by
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - k ≠ 0)
    rw [hl, pow_succ]
    simpa only [one_mul] using!
      mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.le hτ1 : τ ^ l ≤ 1) hτ.le
  have hp : τ ^ n = τ ^ (n - k) * τ ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn.le]
  calc
    _ ≤ C * (2 * (τ * R)) ^ n * (((R + τ * R / 2) / (τ * R / 2)) ^ k) :=
      affineTube_real_bound μ C hg S hS R (τ * R) hR.le hδ
    _ ≤ C * (2 * (τ * R)) ^ n * ((3 / τ) ^ k) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hratio k)
      positivity
    _ = (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * R ^ n * τ ^ (n - k) := by
      simp only [mul_pow, div_pow, hp]
      field_simp
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * R ^ n * τ :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

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

theorem exists_approximate_plane_fit {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (a : Ambient d) (r ε : ℝ) (hε : 0 < ε) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      quadraticPlaneError n μ a r S < squaredExcess n μ a r + ε := by
  obtain ⟨S, hS⟩ := exists_affine_n_plane hnd
  have hne : {t : ℝ | ∃ T : AffineSubspace ℝ (Ambient d),
      IsAffineNPlane n T ∧ t = quadraticPlaneError n μ a r T}.Nonempty :=
    ⟨quadraticPlaneError n μ a r S, S, hS, rfl⟩
  obtain ⟨t, ⟨T, hT, ht⟩, hlt⟩ := exists_lt_of_csInf_lt hne
    (show squaredExcess n μ a r < squaredExcess n μ a r + ε from lt_add_of_pos_right _ hε)
  exact ⟨T, hT, ht ▸ hlt⟩

theorem quadraticPlaneError_integral_identity {n d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : r ≠ 0)
    (S : AffineSubspace ℝ (Ambient d)) :
    r ^ (n + 2) * quadraticPlaneError n μ a r S =
      ∫ x in ball a r, infDist x (S : Set (Ambient d)) ^ 2 ∂μ := by
  rw [quadraticPlaneError, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr), one_mul]

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

theorem directedBallDeviation_nonneg {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r : ℝ) : 0 ≤ directedBallDeviation s t a r := by
  apply Real.sSup_nonneg
  rintro v ⟨x, _, rfl⟩
  exact infDist_nonneg

theorem directedBallDeviation_le {d : ℕ} (s t : Set (Ambient d))
    (a : Ambient d) (r η : ℝ) (hη : 0 ≤ η)
    (hpoint : ∀ x ∈ ball a r, x ∈ s → infDist x t ≤ η) :
    directedBallDeviation s t a r ≤ η := by
  apply Real.sSup_le _ hη
  rintro v ⟨x, hx, rfl⟩
  exact hpoint x hx.1 hx.2

theorem bilateralPlaneError_nonneg {d : ℕ} (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) (S : AffineSubspace ℝ (Ambient d)) :
    0 ≤ bilateralPlaneError μ a r S :=
  div_nonneg (add_nonneg (directedBallDeviation_nonneg _ _ a r)
    (directedBallDeviation_nonneg _ _ a r)) hr

theorem bilateralBeta_nonneg {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r) : 0 ≤ bilateralBeta n μ a r := by
  apply Real.sInf_nonneg
  rintro v ⟨S, _, rfl⟩
  exact bilateralPlaneError_nonneg μ a r hr S

theorem bilateralBeta_le_planeError {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 ≤ r)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) :
    bilateralBeta n μ a r ≤ bilateralPlaneError μ a r S := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨T, _, rfl⟩
    exact bilateralPlaneError_nonneg μ a r hr T
  · exact ⟨S, hS, rfl⟩

theorem bilateralBeta_lt_of_support_tubes {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a r, x ∈ μ.support → infDist x (S : Set (Ambient d)) < ε * r / 4)
    (hreverse : ∀ x ∈ ball a r, x ∈ S → infDist x μ.support < ε * r / 4) :
    bilateralBeta n μ a r < ε := by
  apply (bilateralBeta_le_planeError n μ a r hr.le S hS).trans_lt
  have h1 := directedBallDeviation_le μ.support (S : Set (Ambient d)) a r (ε * r / 4)
    (by positivity) (fun x hx hs => (hforward x hx hs).le)
  have h2 := directedBallDeviation_le (S : Set (Ambient d)) μ.support a r (ε * r / 4)
    (by positivity) (fun x hx hs => (hreverse x hx hs).le)
  apply (div_lt_iff₀ hr).mpr
  nlinarith

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rescaled measures and their growth bounds

The blowup at a center and positive scale pushes a measure forward by translation
and dilation, then normalizes by the scale to the power `n`. Exact ball formulas
transport the support and preserve global upper and lower growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_preimage_ball {d : ℕ} (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' ball x R = ball (a + r • x) (r * R) := by
  ext y
  have hvec : y - (a + r • x) = r • (r⁻¹ • (y - a) - x) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hdist : dist y (a + r • x) = r * dist (r⁻¹ • (y - a)) x := by
    simp only [dist_eq_norm]
    rw [hvec, norm_smul, Real.norm_of_nonneg hr.le]
  simp only [mem_preimage, mem_ball, hdist]
  exact (mul_lt_mul_iff_right₀ hr).symm

theorem blowupMeasure_ball {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    blowupMeasure n μ a r (ball x R) =
      ENNReal.ofReal ((r ^ n)⁻¹) * μ (ball (a + r • x) (r * R)) := by
  have hblowup : Measurable (fun y : Ambient d => r⁻¹ • (y - a)) :=
    ((continuous_id.sub continuous_const).const_smul r⁻¹).measurable
  rw [blowupMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hblowup measurableSet_ball, blowup_preimage_ball a x r R hr]

theorem blowupMeasure_growth {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r) (hg : GlobalUpperGrowth n C μ) :
    GlobalUpperGrowth n C (blowupMeasure n μ a r) := by
  refine ⟨hg.1, ?_⟩
  intro x R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  calc
    _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal (C * (r * R) ^ n) :=
      mul_le_mul_right (hg.2 (a + r • x) (r * R) (by positivity)) _
    _ = ENNReal.ofReal (C * R ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp

theorem blowupMeasure_support_iff {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r : ℝ) (hr : 0 < r) :
    x ∈ (blowupMeasure n μ a r).support ↔ a + r • x ∈ μ.support := by
  rw [Metric.nhds_basis_ball.mem_measureSupport, Metric.nhds_basis_ball.mem_measureSupport]
  have hcoef : 0 < ENNReal.ofReal ((r ^ n)⁻¹) := ENNReal.ofReal_pos.mpr (by positivity)
  constructor
  · intro hx R hR
    have h := hx (R / r) (by positivity)
    rw [blowupMeasure_ball n μ a x r (R / r) hr,
      mul_div_cancel₀ R hr.ne'] at h
    exact (ENNReal.mul_pos_iff.mp h).2
  · intro hx R hR
    rw [blowupMeasure_ball n μ a x r R hr]
    exact ENNReal.mul_pos_iff.mpr ⟨hcoef, hx (r * R) (by positivity)⟩

theorem blowupMeasure_origin_mem_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (ha : a ∈ μ.support) :
    (0 : Ambient d) ∈ (blowupMeasure n μ a r).support := by
  apply (blowupMeasure_support_iff n μ a 0 r hr).mpr
  simpa only [smul_zero, add_zero] using! ha

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_BlowupRadiusGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem blowupMeasure_support_image {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    (blowupMeasure n μ a r).support = (fun y => r⁻¹ • (y - a)) '' μ.support := by
  ext x
  constructor
  · intro hx
    refine ⟨a + r • x, (blowupMeasure_support_iff n μ a x r hr).mp hx, ?_⟩
    change r⁻¹ • ((a + r • x) - a) = x
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩
    apply (blowupMeasure_support_iff n μ a _ r hr).mpr
    have heq : a + r • (r⁻¹ • (y - a)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [heq]
    exact hy

theorem blowupMeasure_ediam_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ediam (blowupMeasure n μ a r).support = ENNReal.ofReal r⁻¹ * ediam μ.support := by
  have himage : (fun y : Ambient d => r⁻¹ • (y - a)) '' μ.support =
      r⁻¹ • ((fun y : Ambient d => y - a) '' μ.support) := by
    rw [← Set.image_smul, Set.image_image]
  have htranslate : Isometry (fun y : Ambient d => y - a) := by
    apply Isometry.of_dist_eq
    intro x y
    exact dist_sub_right x y a
  rw [blowupMeasure_support_image n μ a r hr, himage, ediam_smul₀,
    htranslate.ediam_image μ.support]
  change (‖r⁻¹‖₊ : ℝ≥0∞) * ediam μ.support = _
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [coe_nnnorm, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]

theorem blowupMeasure_ediam_support_mul {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal r * ediam (blowupMeasure n μ a r).support = ediam μ.support := by
  rw [blowupMeasure_ediam_support n μ a r hr, ← mul_assoc,
    ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul]

theorem blowupMeasure_admissibleRadius_iff {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    AdmissibleRadius (blowupMeasure n μ a r) R ↔ AdmissibleRadius μ (r * R) := by
  constructor
  · intro hR
    refine ⟨mul_pos hr hR.1, ?_⟩
    calc
      ENNReal.ofReal (r * R) = ENNReal.ofReal r * ENNReal.ofReal R := ENNReal.ofReal_mul hr.le
      _ ≤ ENNReal.ofReal r * ediam (blowupMeasure n μ a r).support := mul_le_mul_right hR.2 _
      _ = ediam μ.support := blowupMeasure_ediam_support_mul n μ a r hr
  · intro hR
    refine ⟨(mul_pos_iff_of_pos_left hr).mp hR.1, ?_⟩
    rw [blowupMeasure_ediam_support n μ a r hr]
    calc
      ENNReal.ofReal R = ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r * R) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal r⁻¹ * ediam μ.support := mul_le_mul_right hR.2 _

theorem blowupMeasure_lower_admissible {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, AdmissibleRadius μ R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R)) :
    ∀ x ∈ (blowupMeasure n μ a r).support, ∀ R : ℝ, AdmissibleRadius (blowupMeasure n μ a r) R →
      ENNReal.ofReal (R ^ n / C) ≤ blowupMeasure n μ a r (ball x R) := by
  intro x hx R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  have h := hlower (a + r • x) ((blowupMeasure_support_iff n μ a x r hr).mp hx)
    (r * R) ((blowupMeasure_admissibleRadius_iff n μ a r R hr).mp hR)
  calc
    _ = ENNReal.ofReal ((r ^ n)⁻¹) * ENNReal.ofReal ((r * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (r ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right h _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BlowupAffineGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem physicalAffine_apply {d : ℕ} (a x : Ambient d) (r : ℝ) (hr : 0 < r) :
    physicalAffine a r hr x = a + r • x := rfl

theorem physicalAffine_symm_apply {d : ℕ} (a y : Ambient d) (r : ℝ) (hr : 0 < r) :
    (physicalAffine a r hr).symm y = r⁻¹ • (y - a) := rfl

theorem isAffineNPlane_map_equiv {d : ℕ} (n : ℕ)
    (e : Ambient d ≃ᵃ[ℝ] Ambient d) (S : AffineSubspace ℝ (Ambient d))
    (hS : IsAffineNPlane n S) : IsAffineNPlane n (S.map e.toAffineMap) := by
  refine ⟨hS.1.image e, ?_⟩
  rw [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap,
    e.linear.finrank_map_eq, hS.2]

theorem affineSubspace_map_equiv_symm {d : ℕ}
    (e : Ambient d ≃ᵃ[ℝ] Ambient d) (S : AffineSubspace ℝ (Ambient d)) :
    (S.map e.symm.toAffineMap).map e.toAffineMap = S := by
  apply SetLike.coe_injective
  change e '' (e.symm '' (S : Set (Ambient d))) = (S : Set (Ambient d))
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa only [e.apply_symm_apply] using! hz
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

theorem physicalAffine_infDist {d : ℕ} (a x : Ambient d) (r : ℝ) (hr : 0 < r)
    (s : Set (Ambient d)) :
    infDist (physicalAffine a r hr x) (physicalAffine a r hr '' s) = r * infDist x s := by
  have himage : physicalAffine a r hr '' s = (fun y : Ambient d => a + y) '' (r • s) := by
    rw [← Set.image_smul, Set.image_image]
    rfl
  have htranslate : Isometry (fun y : Ambient d => a + y) := by
    apply Isometry.of_dist_eq
    intro x y
    exact dist_add_left a x y
  rw [physicalAffine_apply, himage, Metric.infDist_image htranslate,
    infDist_smul₀ hr.ne', Real.norm_of_nonneg hr.le]

theorem physicalAffine_preimage_ball {d : ℕ} (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    physicalAffine a r hr ⁻¹' ball (physicalAffine a r hr x) (r * R) = ball x R := by
  ext y
  have hd : dist (physicalAffine a r hr y) (physicalAffine a r hr x) = r * dist y x := by
    simp only [physicalAffine_apply, dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le]
  simp only [mem_preimage, mem_ball, hd, mul_lt_mul_iff_right₀ hr]

theorem blowupMeasure_setIntegral_ball {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) (f : Ambient d → E) :
    (∫ y in ball x R, f y ∂blowupMeasure n μ a r) =
      (r ^ n)⁻¹ • ∫ y in ball (a + r • x) (r * R), f (r⁻¹ • (y - a)) ∂μ := by
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹)]
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [he.setIntegral_map, blowup_preimage_ball a x r R hr]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_BlowupBilateralBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem physicalAffine_image_blowup_support {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    physicalAffine a r hr '' (blowupMeasure n μ a r).support = μ.support := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (blowupMeasure_support_iff n μ a x r hr).mp hx
  · intro hy
    refine ⟨(physicalAffine a r hr).symm y, ?_, (physicalAffine a r hr).apply_symm_apply y⟩
    apply (blowupMeasure_support_iff n μ a _ r hr).mpr
    change physicalAffine a r hr ((physicalAffine a r hr).symm y) ∈ μ.support
    simpa only [(physicalAffine a r hr).apply_symm_apply] using! hy

theorem directedBallDeviation_physical {d : ℕ} (s t : Set (Ambient d))
    (a x : Ambient d) (r R : ℝ) (hr : 0 < r) :
    directedBallDeviation (physicalAffine a r hr '' s) (physicalAffine a r hr '' t)
      (physicalAffine a r hr x) (r * R) = r * directedBallDeviation s t x R := by
  have hset : ball (physicalAffine a r hr x) (r * R) ∩ physicalAffine a r hr '' s =
      physicalAffine a r hr '' (ball x R ∩ s) := by
    ext y
    constructor
    · rintro ⟨hy, z, hz, rfl⟩
      refine ⟨z, ⟨?_, hz⟩, rfl⟩
      have hzball : z ∈ physicalAffine a r hr ⁻¹'
          ball (physicalAffine a r hr x) (r * R) := hy
      rwa [physicalAffine_preimage_ball a x r R hr] at hzball
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ⟨z, hz.2, rfl⟩⟩
      have hzball : z ∈ physicalAffine a r hr ⁻¹'
          ball (physicalAffine a r hr x) (r * R) := by
        rw [physicalAffine_preimage_ball a x r R hr]
        exact hz.1
      exact hzball
  unfold directedBallDeviation
  rw [hset, Set.image_image]
  simp_rw [physicalAffine_infDist a _ r hr t]
  calc
    _ = sSup (r • ((fun z => infDist z t) '' (ball x R ∩ s))) := by
      congr 1
      rw [← Set.image_smul, Set.image_image]
      rfl
    _ = _ := Real.sSup_smul_of_nonneg hr.le _

theorem bilateralPlaneError_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) :
    bilateralPlaneError (blowupMeasure n μ a r) 0 R S =
      bilateralPlaneError μ a (r * R) (S.map (physicalAffine a r hr).toAffineMap) := by
  have hforward := directedBallDeviation_physical (blowupMeasure n μ a r).support
    (S : Set (Ambient d)) a 0 r R hr
  have hreverse := directedBallDeviation_physical (S : Set (Ambient d))
    (blowupMeasure n μ a r).support a 0 r R hr
  rw [physicalAffine_image_blowup_support n μ a r hr] at hforward hreverse
  have hzero : physicalAffine a r hr 0 = a := by
    rw [physicalAffine_apply, smul_zero, add_zero]
  rw [hzero] at hforward hreverse
  unfold bilateralPlaneError
  rw [AffineSubspace.coe_map]
  change _ = (directedBallDeviation μ.support
    (physicalAffine a r hr '' (S : Set (Ambient d))) a (r * R) +
    directedBallDeviation (physicalAffine a r hr '' (S : Set (Ambient d)))
      μ.support a (r * R)) / (r * R)
  rw [hforward, hreverse, ← mul_add, mul_div_mul_left _ _ hr.ne']

theorem bilateralBeta_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    bilateralBeta n (blowupMeasure n μ a r) 0 R = bilateralBeta n μ a (r * R) := by
  unfold bilateralBeta
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a r hr).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, bilateralPlaneError_blowup n μ a r R hr S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a r hr).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [bilateralPlaneError_blowup n μ a r R hr, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneAnchorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem infDist_projection_le_sum {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (W : Set (Ambient d)) (x : Ambient d) :
    infDist (orthogonalProjection S x : Ambient d) W ≤
      infDist x (S : Set (Ambient d)) + infDist x W := by
  calc
    _ ≤ infDist x W + dist (orthogonalProjection S x : Ambient d) x :=
      infDist_le_infDist_add_dist
    _ = _ := by
      rw [dist_comm, dist_orthogonalProjection_eq_infDist]
      exact add_comm _ _

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

theorem euclidean_starProjection_norm_le {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (x : Ambient d) : ‖S.starProjection x‖ ≤ ‖x‖ :=
  S.norm_starProjection_apply_le x

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

theorem coefficient_bound_of_span_distance {d : ℕ}
    (S : Submodule ℝ (Ambient d)) (p u : Ambient d) (hp : p ∈ S)
    (r : ℝ) (hr : 0 < r) (hu : r ≤ infDist u (S : Set (Ambient d))) (s : ℝ) :
    |s| ≤ ‖p + s • u‖ / r := by
  have hself : S.starProjection p = p := S.starProjection_eq_self_iff.mpr hp
  have hz : Sᗮ.starProjection p = 0 := by
    have h := S.starProjection_add_starProjection_orthogonal p
    rw [hself, add_eq_left] at h
    exact h
  apply (le_div_iff₀ hr).mpr
  calc
    |s| * r ≤ |s| * infDist u (S : Set (Ambient d)) :=
      mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ = ‖Sᗮ.starProjection (p + s • u)‖ := by
      rw [submodule_infDist_eq_normal_projection, map_add, map_smul, hz, zero_add,
        norm_smul, Real.norm_eq_abs]
    _ ≤ _ := euclidean_starProjection_norm_le Sᗮ (p + s • u)

theorem coordinate_bound_extend {n d : ℕ} (v : Fin n → Ambient d) (u : Ambient d)
    (C M r : ℝ) (hC : 0 ≤ C) (hM : ‖u‖ ≤ M) (hr : 0 < r)
    (hsep : r ≤ infDist u (Submodule.span ℝ (range v) : Set (Ambient d)))
    (hprefix : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖)
    (t : Fin n → ℝ) (s : ℝ) :
    (∑ i, |t i|) + |s| ≤
      (C * (1 + M / r) + 1 / r) * ‖(∑ i, t i • v i) + s • u‖ := by
  let p : Ambient d := ∑ i, t i • v i
  have hp : p ∈ Submodule.span ℝ (range v) := by
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (mem_range_self i)))
  have hs : |s| ≤ ‖p + s • u‖ / r :=
    coefficient_bound_of_span_distance (Submodule.span ℝ (range v)) p u hp r hr hsep s
  have hM0 : 0 ≤ M := (norm_nonneg u).trans hM
  have hpnorm : ‖p‖ ≤ (1 + M / r) * ‖p + s • u‖ := by
    calc
      _ = ‖(p + s • u) - s • u‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖p + s • u‖ + ‖s • u‖ := norm_sub_le _ _
      _ = ‖p + s • u‖ + |s| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖p + s • u‖ + (‖p + s • u‖ / r) * M := by
        apply add_le_add le_rfl
        exact (mul_le_mul_of_nonneg_left hM (abs_nonneg s)).trans
          (mul_le_mul_of_nonneg_right hs hM0)
      _ = _ := by ring
  calc
    _ ≤ C * ‖p‖ + |s| := add_le_add (hprefix t) le_rfl
    _ ≤ C * ((1 + M / r) * ‖p + s • u‖) + ‖p + s • u‖ / r :=
      add_le_add (mul_le_mul_of_nonneg_left hpnorm hC) hs
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OrderedSpanConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped BigOperators

theorem spanConditionConstant_nonneg (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) (n : ℕ) :
    0 ≤ spanConditionConstant M r n := by
  induction n with
  | zero => simp [spanConditionConstant]
  | succ n ih =>
    simp only [spanConditionConstant]
    positivity

theorem ordered_span_coefficient_bound {n d : ℕ}
    (v : Fin n → Ambient d) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r)
    (hv : ∀ i, ‖v i‖ ≤ M) (hsep : OrderedSpanSeparated n v r) (t : Fin n → ℝ) :
    (∑ i, |t i|) ≤ spanConditionConstant M r n * ‖∑ i, t i • v i‖ := by
  induction n with
  | zero => simp [spanConditionConstant]
  | succ n ih =>
    have hp : ∀ s : Fin n → ℝ, (∑ i, |s i|) ≤
        spanConditionConstant M r n * ‖∑ i, s i • Fin.init v i‖ :=
      fun s => ih (Fin.init v) (fun i => hv i.castSucc) hsep.1 s
    have h := coordinate_bound_extend (Fin.init v) (v (Fin.last n))
      (spanConditionConstant M r n) M r (spanConditionConstant_nonneg M r hM hr n)
      (hv (Fin.last n)) hr hsep.2 hp (Fin.init t) (t (Fin.last n))
    simpa only [spanConditionConstant, Fin.sum_univ_castSucc, Fin.init] using! h

theorem linearIndependent_of_coordinate_bound {n d : ℕ}
    (v : Fin n → Ambient d) (C : ℝ)
    (hbound : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖) :
    LinearIndependent ℝ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  have h := hbound t
  rw [ht, norm_zero, mul_zero] at h
  have hi : |t i| ≤ ∑ j, |t j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem ordered_span_linearIndependent {n d : ℕ}
    (v : Fin n → Ambient d) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r)
    (hv : ∀ i, ‖v i‖ ≤ M) (hsep : OrderedSpanSeparated n v r) :
    LinearIndependent ℝ v :=
  linearIndependent_of_coordinate_bound v (spanConditionConstant M r n)
    (ordered_span_coefficient_bound v M r hM hr hv hsep)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_AnchorPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped BigOperators

theorem linear_combination_perturbation_bound {n d : ℕ}
    (v w : Fin n → Ambient d) (η : ℝ) (hclose : ∀ i, ‖w i - v i‖ ≤ η)
    (t : Fin n → ℝ) :
    ‖(∑ i, t i • v i) - ∑ i, t i • w i‖ ≤ η * ∑ i, |t i| := by
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ i, ‖t i • (v i - w i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |t i| * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left (hclose i) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem coordinate_bound_under_perturbation {n d : ℕ}
    (v w : Fin n → Ambient d) (C η : ℝ) (hC : 0 ≤ C)
    (hsmall : C * η ≤ 1 / 2) (hclose : ∀ i, ‖w i - v i‖ ≤ η)
    (hbound : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖)
    (t : Fin n → ℝ) :
    (∑ i, |t i|) ≤ (2 * C) * ‖∑ i, t i • w i‖ := by
  have hnorm : ‖∑ i, t i • v i‖ ≤
      ‖∑ i, t i • w i‖ + η * ∑ i, |t i| := by
    calc
      _ = ‖(∑ i, t i • w i) + ((∑ i, t i • v i) - ∑ i, t i • w i)‖ := by
        congr 1
        abel
      _ ≤ ‖∑ i, t i • w i‖ + ‖(∑ i, t i • v i) - ∑ i, t i • w i‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (linear_combination_perturbation_bound v w η hclose t)
  have h := (hbound t).trans (mul_le_mul_of_nonneg_left hnorm hC)
  have hs : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg (fun i _ => abs_nonneg (t i))
  have hp := mul_le_mul_of_nonneg_right hsmall hs
  nlinarith

theorem projected_anchor_perturbation_bound {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (p₀ p : Ambient d) :
    ‖((orthogonalProjection S p : Ambient d) - (orthogonalProjection S p₀ : Ambient d)) -
      (p - p₀)‖ ≤ infDist p (S : Set (Ambient d)) + infDist p₀ (S : Set (Ambient d)) := by
  calc
    _ = ‖((orthogonalProjection S p : Ambient d) - p) -
      ((orthogonalProjection S p₀ : Ambient d) - p₀)‖ := by congr 1; abel
    _ ≤ ‖(orthogonalProjection S p : Ambient d) - p‖ +
      ‖(orthogonalProjection S p₀ : Ambient d) - p₀‖ := norm_sub_le _ _
    _ = _ := by
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (orthogonalProjection S p : Ambient d) p,
        dist_comm (orthogonalProjection S p₀ : Ambient d) p₀,
        dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_infDist]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ConditionedPlaneComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module EuclideanGeometry
open scoped BigOperators

theorem plane_distance_bound_from_conditioned_generators {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (a : Ambient d) (ha : a ∈ S) (v : Fin n → Ambient d)
    (hv : ∀ i, v i ∈ S.direction) (K ε : ℝ) (hε : 0 ≤ ε)
    (hcoeff : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ K * ‖∑ i, t i • v i‖)
    (hbase : infDist a (W : Set (Ambient d)) ≤ ε)
    (hvertices : ∀ i, infDist (a + v i) (W : Set (Ambient d)) ≤ ε)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤ ε * (1 + 2 * (K * ‖x - a‖)) := by
  have hlin := linearIndependent_of_coordinate_bound v K hcoeff
  have hsub : Submodule.span ℝ (range v) ≤ S.direction := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hv i
  have hdim : finrank ℝ (Submodule.span ℝ (range v)) = n := by
    simpa only [Fintype.card_fin] using! finrank_span_eq_card hlin
  have hspan : Submodule.span ℝ (range v) = S.direction :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdim.trans hS.2.symm)
  have hxspan : x - a ∈ Submodule.span ℝ (range v) := by
    rw [hspan]
    exact AffineSubspace.vsub_mem_direction hx ha
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxspan
  have hxa : x = a + ∑ i, t i • v i := by rw [ht]; abel
  obtain ⟨aw, _haw, _hnorm, _Lw, _hLw, Nw, _horth, _hsplit, hdist⟩ :=
    exists_affine_plane_normal_frame W hW
  let F := Nw.toContinuousLinearMap.adjoint
  have hF : ∀ y, ‖-F aw + F y‖ = infDist y (W : Set (Ambient d)) := by
    intro y
    rw [hdist y]
    change ‖-F aw + F y‖ = ‖F (y - aw)‖
    rw [map_sub]
    congr 1
    abel
  have hb := affine_map_norm_bound_from_anchors (-F aw) F a v t ε
    (by simpa only [hF] using! hbase) (by intro i; simpa only [hF] using! hvertices i)
  rw [← hxa, hF] at hb
  have hc := hcoeff t
  rw [ht] at hc
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))) hε)

theorem plane_distance_bound_from_conditioned_support_anchors {n d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (hS : IsAffineNPlane n S) (hW : IsAffineNPlane n W)
    (p0 : Ambient d) (p : Fin n → Ambient d) (K η : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hsmall : K * (2 * η) ≤ 1 / 2)
    (hcoeff : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ K * ‖∑ i, t i • (p i - p0)‖)
    (hbase : infDist p0 (S : Set (Ambient d)) ≤ η ∧ infDist p0 (W : Set (Ambient d)) ≤ η)
    (hpoints : ∀ i, infDist (p i) (S : Set (Ambient d)) ≤ η ∧
      infDist (p i) (W : Set (Ambient d)) ≤ η)
    (x : Ambient d) (hx : x ∈ S) :
    infDist x (W : Set (Ambient d)) ≤
      2 * η * (1 + 4 * K * ‖x - (orthogonalProjection S p0 : Ambient d)‖) := by
  let a : Ambient d := orthogonalProjection S p0
  let v : Fin n → Ambient d := fun i => (orthogonalProjection S (p i) : Ambient d) - a
  have hclose : ∀ i, ‖v i - (p i - p0)‖ ≤ 2 * η := by
    intro i
    exact (projected_anchor_perturbation_bound S p0 (p i)).trans
      (by linarith [(hpoints i).1, hbase.1])
  have hc : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ (2 * K) * ‖∑ i, t i • v i‖ :=
    coordinate_bound_under_perturbation (fun i => p i - p0) v K (2 * η) hK hsmall hclose hcoeff
  have hv : ∀ i, v i ∈ S.direction := fun i =>
    AffineSubspace.vsub_mem_direction (orthogonalProjection_mem (p i)) (orthogonalProjection_mem p0)
  have hb : infDist a (W : Set (Ambient d)) ≤ 2 * η :=
    (infDist_projection_le_sum S (W : Set (Ambient d)) p0).trans (by linarith [hbase.1, hbase.2])
  have hvfit : ∀ i, infDist (a + v i) (W : Set (Ambient d)) ≤ 2 * η := by
    intro i
    have heq : a + v i = (orthogonalProjection S (p i) : Ambient d) := by dsimp only [v]; abel
    rw [heq]
    exact (infDist_projection_le_sum S (W : Set (Ambient d)) (p i)).trans
      (by linarith [(hpoints i).1, (hpoints i).2])
  have h := plane_distance_bound_from_conditioned_generators S W hS hW a
    (orthogonalProjection_mem p0) v hv (2 * K) (2 * η) (by positivity) hc hb hvfit x hx
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneMomentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transfer of squared plane-distance moments

A pointwise comparison of distances to two affine planes yields a comparison
of their second moments on a ball. The additive distance error contributes its
square times the ball mass, using local finiteness to justify integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem plane_distance_second_moment_transfer {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R t : ℝ) (ht : 0 ≤ t)
    (hpoint : ∀ x ∈ ball (0 : Ambient d) R,
      infDist x (S : Set (Ambient d)) ≤ infDist x (W : Set (Ambient d)) + t) :
    (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) +
        2 * t ^ 2 * μ.real (ball (0 : Ambient d) R) := by
  have : IsFiniteMeasure (μ.restrict (ball (0 : Ambient d) R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top))
  have hSi := squared_infDist_integrableOn_ball μ 0 R S hS
  have hWi := squared_infDist_integrableOn_ball μ 0 R W hW
  have hbound : (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) R, 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2 ∂μ := by
    apply integral_mono_ae hSi ((hWi.const_mul 2).add (integrable_const _))
    filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
    change infDist x (S : Set (Ambient d)) ^ 2 ≤ 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2
    have hsq := (sq_le_sq₀ infDist_nonneg (add_nonneg infDist_nonneg ht)).mpr (hpoint x hx)
    nlinarith [sq_nonneg (infDist x (W : Set (Ambient d)) - t)]
  calc
    _ ≤ ∫ x in ball (0 : Ambient d) R, 2 * infDist x (W : Set (Ambient d)) ^ 2 + 2 * t ^ 2 ∂μ := hbound
    _ = _ := by
      rw [integral_add (hWi.const_mul 2) (integrable_const _), integral_const_mul, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      ring

theorem plane_second_moment_bound_from_distance_transfer {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R E K D : ℝ) (hR : 0 < R) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hfit : (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      D * E ^ 2 * R ^ (n + 2))
    (hpoint : ∀ x ∈ ball (0 : Ambient d) R,
      infDist x (S : Set (Ambient d)) ≤ infDist x (W : Set (Ambient d)) + K * E * R) :
    (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      (2 * D + 2 * C * K ^ 2) * E ^ 2 * R ^ (n + 2) := by
  have hm : μ.real (ball (0 : Ambient d) R) ≤ C * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) (hg.2 0 R hR)
  calc
    _ ≤ 2 * (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) +
        2 * (K * E * R) ^ 2 * μ.real (ball (0 : Ambient d) R) :=
      plane_distance_second_moment_transfer μ S W hS hW R (K * E * R) (by positivity) hpoint
    _ ≤ 2 * (D * E ^ 2 * R ^ (n + 2)) + 2 * (K * E * R) ^ 2 * (C * R ^ n) :=
      add_le_add (mul_le_mul_of_nonneg_left hfit (by norm_num))
        (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by rw [pow_add R n 2]; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicApproximateFits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_dyadic_approximate_fits {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b) (N : ℕ)
    (hexcess : ∀ i ≤ N, squaredExcess n μ 0 ((2 : ℝ) ^ i) ≤ (δ * b ^ i) ^ 2) :
    ∃ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) ∧
      ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
        infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
          2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) := by
  have hfit : ∀ i : ℕ, ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) S <
        squaredExcess n μ 0 ((2 : ℝ) ^ i) + (δ * b ^ i) ^ 2 := by
    intro i
    exact exists_approximate_plane_fit hnd μ 0 ((2 : ℝ) ^ i) ((δ * b ^ i) ^ 2)
      (sq_pos_of_pos (mul_pos hδ (pow_pos hb i)))
  choose P hP herr using hfit
  refine ⟨P, hP, ?_⟩
  intro i hi
  have hnorm : quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) (P i) ≤ 2 * (δ * b ^ i) ^ 2 :=
    (herr i).le.trans (by linarith [hexcess i hi])
  rw [← quadraticPlaneError_integral_identity μ 0 ((2 : ℝ) ^ i) (by positivity) (P i)]
  calc
    ((2 : ℝ) ^ i) ^ (n + 2) * quadraticPlaneError n μ 0 ((2 : ℝ) ^ i) (P i) ≤
        ((2 : ℝ) ^ i) ^ (n + 2) * (2 * (δ * b ^ i) ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_JointPlaneGoodSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simultaneous approximation by two affine planes

The joint squared-distance error defines a good set close to both planes. Its
continuity gives local integrability, and an integral error bound yields a lower
mass estimate for the good set by controlling the complementary bad set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem jointPlaneFitError_continuous {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) : Continuous (jointPlaneFitError S W) :=
  ((continuous_infDist_pt (S : Set (Ambient d))).pow 2).add
    ((continuous_infDist_pt (W : Set (Ambient d))).pow 2)

theorem jointPlaneFitError_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R : ℝ) : IntegrableOn (jointPlaneFitError S W) (ball 0 R) μ :=
  (squared_infDist_integrableOn_ball μ 0 R S hS).add
    (squared_infDist_integrableOn_ball μ 0 R W hW)

theorem jointPlaneGoodSet_distance_bounds {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) (R η : ℝ) (hη : 0 < η)
    (x : Ambient d) (hx : x ∈ jointPlaneGoodSet S W R η) :
    x ∈ ball (0 : Ambient d) R ∧
      infDist x (S : Set (Ambient d)) < η ∧ infDist x (W : Set (Ambient d)) < η := by
  refine ⟨hx.1, ?_, ?_⟩
  · apply (sq_lt_sq₀ infDist_nonneg hη.le).mp
    exact (le_add_of_nonneg_right (sq_nonneg (infDist x (W : Set (Ambient d))))).trans_lt hx.2
  · apply (sq_lt_sq₀ infDist_nonneg hη.le).mp
    exact (le_add_of_nonneg_left (sq_nonneg (infDist x (S : Set (Ambient d))))).trans_lt hx.2

theorem jointPlaneGoodSet_mass_lower {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R η c : ℝ) (hη : 0 < η)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (herr : (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      η ^ 2 * ((c / 2) * R ^ n)) :
    (c / 2) * R ^ n ≤ μ.real (jointPlaneGoodSet S W R η) := by
  let bad : Set (Ambient d) := ball 0 R ∩ {x | η ^ 2 ≤ jointPlaneFitError S W x}
  have hmeas : MeasurableSet {x | η ^ 2 ≤ jointPlaneFitError S W x} :=
    isClosed_le continuous_const (jointPlaneFitError_continuous S W) |>.measurableSet
  have hbadmeas : MeasurableSet bad := measurableSet_ball.inter hmeas
  have hf := jointPlaneFitError_integrableOn_ball μ S W hS hW R
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (f := jointPlaneFitError S W)
    (μ := μ.restrict (ball (0 : Ambient d) R))
    (Filter.Eventually.of_forall (fun x =>
      add_nonneg (sq_nonneg (infDist x (S : Set (Ambient d))))
        (sq_nonneg (infDist x (W : Set (Ambient d)))))) hf (η ^ 2)
  rw [measureReal_restrict_apply hmeas, inter_comm] at hmarkov
  have hb : μ.real bad ≤ (c / 2) * R ^ n :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hη)).mp (hmarkov.trans herr)
  have hfinite : μ (ball (0 : Ambient d) R) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top)
  have hset : jointPlaneGoodSet S W R η = ball (0 : Ambient d) R \ bad := by
    ext x
    simp only [jointPlaneGoodSet, bad, mem_inter_iff, mem_ofPred_eq, mem_sdiff]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, fun hb => (not_le_of_gt hlt) hb.2⟩
    · rintro ⟨hx, hout⟩
      exact ⟨hx, lt_of_not_ge (fun hle => hout ⟨hx, hle⟩)⟩
  rw [hset, measureReal_sdiff inter_subset_left hbadmeas hfinite]
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NeighboringFitErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem dyadicFitErrorConstant_pos (n : ℕ) (b : ℝ) : 0 < dyadicFitErrorConstant n b := by
  dsimp only [dyadicFitErrorConstant]
  positivity

theorem neighboring_joint_fit_error_bound {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R E b : ℝ) (hR : 0 ≤ R)
    (hleft : (∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * E ^ 2 * R ^ (n + 2))
    (hright : (∫ x in ball (0 : Ambient d) (2 * R), infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      2 * (b * E) ^ 2 * (2 * R) ^ (n + 2)) :
    (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      dyadicFitErrorConstant n b * E ^ 2 * R ^ (n + 2) := by
  have hSi := squared_infDist_integrableOn_ball μ 0 R S hS
  have hWi := squared_infDist_integrableOn_ball μ 0 R W hW
  have hWlarge := squared_infDist_integrableOn_ball μ 0 (2 * R) W hW
  have hrestrict : (∫ x in ball (0 : Ambient d) R, infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) (2 * R), infDist x (W : Set (Ambient d)) ^ 2 ∂μ :=
    integral_mono_measure (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl)
      (Filter.Eventually.of_forall (fun x => sq_nonneg (infDist x (W : Set (Ambient d))))) hWlarge
  change (∫ x in ball (0 : Ambient d) R,
    infDist x (S : Set (Ambient d)) ^ 2 + infDist x (W : Set (Ambient d)) ^ 2 ∂μ) ≤ _
  rw [integral_add hSi hWi]
  calc
    _ ≤ 2 * E ^ 2 * R ^ (n + 2) + 2 * (b * E) ^ 2 * (2 * R) ^ (n + 2) :=
      add_le_add hleft (hrestrict.trans hright)
    _ = _ := by simp only [dyadicFitErrorConstant, mul_pow] <;> ring

theorem dyadic_neighboring_joint_fit_error_bound {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (P : ℕ → AffineSubspace ℝ (Ambient d)) (hP : ∀ i, IsAffineNPlane n (P i))
    (δ b : ℝ) (N : ℕ)
    (hfit : ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
        2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) (i : ℕ) (hi : i < N) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i), jointPlaneFitError (P i) (P (i + 1)) x ∂μ) ≤
      dyadicFitErrorConstant n b * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) := by
  apply neighboring_joint_fit_error_bound μ (P i) (P (i + 1)) (hP i).1 (hP (i + 1)).1
    ((2 : ℝ) ^ i) (δ * b ^ i) b (by positivity) (hfit i hi.le)
  have hright := hfit (i + 1) (Nat.succ_le_of_lt hi)
  have hr : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
  have he : δ * b ^ (i + 1) = b * (δ * b ^ i) := by rw [pow_succ]; ring
  rw [hr, he] at hright
  exact hright

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicFitCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_dyadic_fit_calibration (n : ℕ) (b c : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ dyadicFitErrorConstant n b ≤ L ^ 2 * (c / 2) := by
  let q := 2 * dyadicFitErrorConstant n b / c
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg (by norm_num) (dyadicFitErrorConstant_pos n b).le) hc.le
  let L := 1 + Real.sqrt q
  have hL : 0 < L := by dsimp only [L] <;> positivity
  have hs : q ≤ L ^ 2 := by
    dsimp only [L]
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  refine ⟨L, hL, ?_⟩
  calc
    dyadicFitErrorConstant n b = q * (c / 2) := by dsimp only [q]; field_simp
    _ ≤ L ^ 2 * (c / 2) := mul_le_mul_of_nonneg_right hs (by positivity)

theorem calibrated_dyadic_joint_fit_error {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (P : ℕ → AffineSubspace ℝ (Ambient d)) (hP : ∀ i, IsAffineNPlane n (P i))
    (δ b L c : ℝ) (hcal : dyadicFitErrorConstant n b ≤ L ^ 2 * (c / 2)) (N : ℕ)
    (hfit : ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
        2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) (i : ℕ) (hi : i < N) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i), jointPlaneFitError (P i) (P (i + 1)) x ∂μ) ≤
      (L * δ * (2 : ℝ) ^ i * b ^ i) ^ 2 * ((c / 2) * ((2 : ℝ) ^ i) ^ n) := by
  calc
    _ ≤ dyadicFitErrorConstant n b * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) :=
      dyadic_neighboring_joint_fit_error_bound μ P hP δ b N hfit i hi
    _ ≤ (L ^ 2 * (c / 2)) * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcal (sq_nonneg _)) (by positivity)
    _ = _ := by rw [pow_add ((2 : ℝ) ^ i) n 2]; ring

theorem calibrated_dyadic_threshold_small (L δ b ε : ℝ)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hb : 1 ≤ b) (N i : ℕ) (hi : i ≤ N)
    (hsmall : L * δ * b ^ N ≤ ε) :
    L * δ * (2 : ℝ) ^ i * b ^ i ≤ ε * (2 : ℝ) ^ i := by
  have hbpow : b ^ i ≤ b ^ N := pow_le_pow_right₀ hb hi
  calc
    L * δ * (2 : ℝ) ^ i * b ^ i = (L * δ * b ^ i) * (2 : ℝ) ^ i := by ring
    _ ≤ (L * δ * b ^ N) * (2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbpow (mul_nonneg hL hδ)) (by positivity)
    _ ≤ ε * (2 : ℝ) ^ i := mul_le_mul_of_nonneg_right hsmall (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneDistanceTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped BigOperators

theorem affine_projection_norm_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (a : Ambient d) (ha : a ∈ S) (x : Ambient d) :
    ‖(orthogonalProjection S x : Ambient d)‖ ≤ ‖x‖ + ‖a‖ := by
  have hdist : dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S 0 : Ambient d) ≤
      ‖x‖ := by simpa only [dist_zero_right] using! affine_projection_dist_le S x 0
  have hzero : ‖(orthogonalProjection S 0 : Ambient d)‖ ≤ ‖a‖ := by
    calc
      ‖(orthogonalProjection S 0 : Ambient d)‖ = dist (0 : Ambient d) (orthogonalProjection S 0) :=
        (dist_zero_left _).symm
      _ = infDist (0 : Ambient d) (S : Set (Ambient d)) := dist_orthogonalProjection_eq_infDist S 0
      _ ≤ dist (0 : Ambient d) a := infDist_le_dist_of_mem ha
      _ = ‖a‖ := dist_zero_left a
  calc
    ‖(orthogonalProjection S x : Ambient d)‖ = dist (orthogonalProjection S x : Ambient d) 0 :=
      (dist_zero_right _).symm
    _ ≤ dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S 0 : Ambient d) +
        dist (orthogonalProjection S 0 : Ambient d) 0 := dist_triangle _ _ _
    _ ≤ ‖x‖ + ‖a‖ := add_le_add hdist (by simpa only [dist_zero_right] using! hzero)

theorem plane_distance_transfer {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (W : Set (Ambient d))
    (a : Ambient d) (ha : a ∈ S) (B C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (haB : ‖a‖ ≤ B)
    (hcompare : ∀ p ∈ S, infDist p W ≤ C * (1 + ‖p‖ / R)) (x : Ambient d) :
    infDist x W ≤ infDist x (S : Set (Ambient d)) + C * (1 + (‖x‖ + B) / R) := by
  let p : Ambient d := orthogonalProjection S x
  have hp : p ∈ S := orthogonalProjection_mem x
  have hnorm : ‖p‖ ≤ ‖x‖ + B :=
    (affine_projection_norm_le S a ha x).trans (add_le_add le_rfl haB)
  have hfit : infDist p W ≤ C * (1 + (‖x‖ + B) / R) :=
    (hcompare p hp).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right hnorm hR.le)) hC)
  calc
    infDist x W ≤ infDist p W + dist x p := infDist_le_infDist_add_dist
    _ = infDist p W + infDist x (S : Set (Ambient d)) := by
      rw [dist_orthogonalProjection_eq_infDist]
    _ ≤ C * (1 + (‖x‖ + B) / R) + infDist x (S : Set (Ambient d)) := add_le_add hfit le_rfl
    _ = _ := add_comm _ _

theorem upper_bound_by_last_and_step_sum (d e : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ i < k, d i ≤ d (i + 1) + e i) :
    d 0 ≤ d k + ∑ i ∈ Finset.range k, e i := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ k ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hk := hstep k (Nat.lt_succ_self k)
    rw [Finset.sum_range_succ]
    linarith

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

theorem exists_ordered_separated_anchors_from_escape {n d : ℕ}
    (good : Set (Ambient d)) (p0 : Ambient d) (r : ℝ)
    (hescape : ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
      ∃ x ∈ good, r ≤ infDist x (S : Set (Ambient d))) :
    ∃ p : Fin n → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated n (fun i => p i - p0) r := by
  have hbuild : ∀ m : ℕ, m ≤ n → ∃ p : Fin m → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated m (fun i => p i - p0) r := by
    intro m
    induction m with
    | zero =>
      intro _hm
      refine ⟨Fin.elim0, ?_, trivial⟩
      intro i
      exact Fin.elim0 i
    | succ m ih =>
      intro hm
      obtain ⟨p, hp, hsep⟩ := ih (by omega)
      let U := Submodule.span ℝ (range (fun i => p i - p0))
      let S := AffineSubspace.mk' p0 U
      have hdim : finrank ℝ U ≤ m := by
        simpa only [Fintype.card_fin] using! (finrank_range_le_card (R := ℝ) (fun i => p i - p0))
      have hS : IsAffineNPlane (finrank ℝ U) S :=
        ⟨AffineSubspace.mk'_nonempty p0 U,
          congrArg (fun V : Submodule ℝ (Ambient d) => finrank ℝ V)
            (AffineSubspace.direction_mk' p0 U)⟩
      obtain ⟨x, hx, hxr⟩ := hescape (finrank ℝ U) (lt_of_le_of_lt hdim (by omega)) S hS
      have hxU : r ≤ infDist (x - p0) (U : Set (Ambient d)) := by
        rw [← infDist_affine_translate p0 x U]
        exact hxr
      have hinit : Fin.init (fun i : Fin (m + 1) =>
          Fin.snoc (α := fun _ => Ambient d) p x i - p0) =
          (fun i : Fin m => p i - p0) := by
        funext i
        simp only [Fin.init, Fin.snoc_castSucc]
      refine ⟨Fin.snoc p x, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using! hx
        · simpa only [Fin.snoc_castSucc] using! hp j
      · constructor
        · change OrderedSpanSeparated m (Fin.init (fun i =>
            Fin.snoc (α := fun _ => Ambient d) p x i - p0)) r
          rw [hinit]
          exact hsep
        · change r ≤ infDist (Fin.snoc (α := fun _ => Ambient d) p x (Fin.last m) - p0)
            (Submodule.span ℝ (range (Fin.init (fun i =>
              Fin.snoc (α := fun _ => Ambient d) p x i - p0))) : Set (Ambient d))
          rw [hinit, Fin.snoc_last]
          exact hxU
  exact hbuild n le_rfl

theorem exists_conditioned_anchors_from_escape {n d : ℕ}
    (good : Set (Ambient d)) (p0 : Ambient d) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hgood : good ⊆ ball (0 : Ambient d) R) (hp0 : p0 ∈ good)
    (hescape : ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
      ∃ x ∈ good, r ≤ infDist x (S : Set (Ambient d))) :
    ∃ p : Fin n → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated n (fun i => p i - p0) r ∧
      LinearIndependent ℝ (fun i => p i - p0) ∧
      ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤
        spanConditionConstant (2 * R) r n * ‖∑ i, t i • (p i - p0)‖ := by
  obtain ⟨p, hp, hsep⟩ := exists_ordered_separated_anchors_from_escape good p0 r hescape
  have hnorm : ∀ i, ‖p i - p0‖ ≤ 2 * R := by
    intro i
    have hi : ‖p i‖ < R := by simpa only [mem_ball, dist_zero_right] using! hgood (hp i)
    have h0 : ‖p0‖ < R := by simpa only [mem_ball, dist_zero_right] using! hgood hp0
    exact (norm_sub_le (p i) p0).trans (by linarith)
  exact ⟨p, hp, hsep,
    ordered_span_linearIndependent (fun i => p i - p0) (2 * R) r (by positivity) hr hnorm hsep,
    ordered_span_coefficient_bound (fun i => p i - p0) (2 * R) r (by positivity) hr hnorm hsep⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NonconcentrationPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_support_point_outside_small_set {d : ℕ}
    (μ : Measure (Ambient d)) (s bad : Set (Ambient d)) (hbad : μ bad ≠ ∞)
    (hlt : μ.real bad < μ.real s) :
    ∃ x ∈ s, x ∈ μ.support ∧ x ∉ bad := by
  by_contra hnone
  have hsub : s ≤ᵐ[μ] bad := by
    filter_upwards [μ.support_mem_ae] with x hx
    intro hxs
    by_contra hxb
    exact hnone ⟨x, hxs, hx, hxb⟩
  have h := ENNReal.toReal_mono hbad (measure_mono_ae hsub)
  exact (not_le_of_gt hlt) h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_LargeSubsetEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_support_point_in_subset_away_from_plane {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ c : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (s : Set (Ambient d)) (hs : s ⊆ ball (0 : Ambient d) R)
    (hmass : c * R ^ n ≤ μ.real s)
    (hsmall : (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ < c) :
    ∃ x ∈ s, x ∈ μ.support ∧ τ * R ≤ infDist x (S : Set (Ambient d)) := by
  have htube : μ.real (affineTube S R (τ * R)) < μ.real s :=
    (lower_dimensional_affineTube_bound μ C hg S hS hkn R τ hR hτ hτ1).trans_lt
      ((mul_lt_mul_of_pos_right hsmall (pow_pos hR n)).trans_le hmass)
  have hfinite : μ (affineTube S R (τ * R)) ≠ ∞ :=
    ne_of_lt ((affineTube_measure_bound μ C hg S hS R (τ * R) hR.le (mul_pos hτ hR)).trans_lt
      ENNReal.ofReal_lt_top)
  obtain ⟨x, hx, hsupport, hout⟩ := exists_support_point_outside_small_set μ s
    (affineTube S R (τ * R)) hfinite htube
  refine ⟨x, hx, hsupport, le_of_not_gt ?_⟩
  intro hnear
  exact hout ⟨ball_subset_closedBall (hs hx), hnear⟩

theorem exists_uniform_affine_escape_width_for_subsets (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → ∀ s : Set (Ambient d), s ⊆ ball (0 : Ambient d) R →
      c * R ^ n ≤ μ.real s →
      ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
        ∃ x ∈ s, x ∈ μ.support ∧ τ * R ≤ infDist x (S : Set (Ambient d)) := by
  let D : ℝ := C * (2 : ℝ) ^ n * (3 : ℝ) ^ n
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  let τ := min 1 (c / (2 * (D + 1)))
  have hden : 0 < 2 * (D + 1) := by positivity
  have hτ : 0 < τ := lt_min zero_lt_one (div_pos hc hden)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτb : τ * (2 * (D + 1)) ≤ c := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : D * τ < c := by nlinarith [mul_nonneg hD hτ.le]
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hg R hR s hs hmass k hkn S hS
  apply exists_support_point_in_subset_away_from_plane μ C hg S hS hkn R τ c hR hτ hτ1
    s hs hmass
  have hK : C * (2 : ℝ) ^ n * (3 : ℝ) ^ k ≤ D := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkn.le)
      (mul_nonneg hC (by positivity))
  exact (mul_le_mul_of_nonneg_right hK hτ.le).trans_lt hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_JointSupportAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Joint plane-fit control and uniform affine escape produce support anchors with quantitative
spanning bounds. The separation parameter is chosen uniformly before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

theorem exists_uniform_joint_support_anchors (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), (S : Set (Ambient d)).Nonempty →
      (W : Set (Ambient d)).Nonempty → ∀ η : ℝ, 0 < η →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∃ p0 ∈ jointPlaneGoodSet S W R η, p0 ∈ μ.support ∧
        ∃ p : Fin n → Ambient d,
          (∀ i, p i ∈ jointPlaneGoodSet S W R η ∧ p i ∈ μ.support) ∧
          OrderedSpanSeparated n (fun i => p i - p0) (τ * R) ∧
          LinearIndependent ℝ (fun i => p i - p0) ∧
          ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤
            spanConditionConstant (2 * R) (τ * R) n * ‖∑ i, t i • (p i - p0)‖ := by
  obtain ⟨τ, hτ, hτ1, hescape⟩ := exists_uniform_affine_escape_width_for_subsets
    n d C (c / 2) hC (by positivity)
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη herr
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let s := jointPlaneGoodSet S W R η
  have hs : s ⊆ ball (0 : Ambient d) R := inter_subset_left
  have hsmass : (c / 2) * R ^ n ≤ μ.real s :=
    jointPlaneGoodSet_mass_lower μ S W hS hW R η c hη hmass herr
  have hpos : 0 < μ.real s := (mul_pos (by positivity : 0 < c / 2) (pow_pos hR n)).trans_le hsmass
  obtain ⟨p0, hp0, hp0support, _hout⟩ := exists_support_point_outside_small_set μ s ∅
    (by simp) (by simpa only [measureReal_empty] using! hpos)
  let good := s ∩ μ.support
  have hgood : good ⊆ ball (0 : Ambient d) R := fun _ hx => hs hx.1
  have he : ∀ k : ℕ, k < n → ∀ T : AffineSubspace ℝ (Ambient d), IsAffineNPlane k T →
      ∃ x ∈ good, τ * R ≤ infDist x (T : Set (Ambient d)) := by
    intro k hkn T hT
    obtain ⟨x, hx, hxsupport, hxr⟩ := hescape μ hg R hR s hs hsmass k hkn T hT
    exact ⟨x, ⟨hx, hxsupport⟩, hxr⟩
  obtain ⟨p, hp, hsep, hlin, hcoeff⟩ := exists_conditioned_anchors_from_escape
    good p0 R (τ * R) hR.le (mul_pos hτ hR) hgood ⟨hp0, hp0support⟩ he
  exact ⟨p0, hp0, hp0support, p, hp, hsep, hlin, hcoeff⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_MeasuredPlaneComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Upper growth and a lower ball-mass bound provide uniformly separated joint support anchors for
two affine planes. A small joint squared fitting error then yields a quantitative comparison of
the planes, with distortion controlled by the anchor span-condition constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem exists_measured_plane_comparison_width (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      spanConditionConstant (2 * R) (τ * R) n * (2 * η) ≤ 1 / 2 →
      ∃ a ∈ S, ‖a‖ ≤ R + η ∧ ∀ x ∈ S,
        infDist x (W : Set (Ambient d)) ≤
          2 * η * (1 + 4 * spanConditionConstant (2 * R) (τ * R) n * ‖x - a‖) := by
  obtain ⟨τ, hτ, hτ1, hanchors⟩ := exists_uniform_joint_support_anchors n d C c hC hc
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη herr hsmall
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let : Nonempty S := hS.1.to_subtype
  obtain ⟨p0, hp0, _hsupport0, p, hp, _hsep, _hlin, hcoeff⟩ :=
    hanchors μ hfinite hg R hR hmass S W hS.1 hW.1 η hη herr
  have h0 := jointPlaneGoodSet_distance_bounds S W R η hη p0 hp0
  have hbase : infDist p0 (S : Set (Ambient d)) ≤ η ∧
      infDist p0 (W : Set (Ambient d)) ≤ η := ⟨h0.2.1.le, h0.2.2.le⟩
  have hpoints : ∀ i, infDist (p i) (S : Set (Ambient d)) ≤ η ∧
      infDist (p i) (W : Set (Ambient d)) ≤ η := by
    intro i
    have hi := jointPlaneGoodSet_distance_bounds S W R η hη (p i) (hp i).1
    exact ⟨hi.2.1.le, hi.2.2.le⟩
  let a : Ambient d := orthogonalProjection S p0
  have ha : a ∈ S := orthogonalProjection_mem p0
  have hnorm0 : ‖p0‖ ≤ R := by
    have hlt : ‖p0‖ < R := by simpa only [mem_ball, dist_zero_right] using! h0.1
    exact hlt.le
  have hnormdist : ‖p0 - a‖ ≤ η := by
    rw [← dist_eq_norm, dist_orthogonalProjection_eq_infDist]
    exact hbase.1
  have hanorm : ‖a‖ ≤ R + η :=
    (norm_le_norm_add_norm_sub p0 a).trans (add_le_add hnorm0 hnormdist)
  refine ⟨a, ha, hanorm, ?_⟩
  intro x hx
  exact plane_distance_bound_from_conditioned_support_anchors S W hS hW p0 p
    (spanConditionConstant (2 * R) (τ * R) n) η
    (spanConditionConstant_nonneg (2 * R) (τ * R) (by positivity) (mul_pos hτ hR) n)
    hη.le hsmall hcoeff hbase hpoints x hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaleAnchorConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem spanConditionConstant_rescale (M τ R : ℝ) (hτ : τ ≠ 0) (hR : R ≠ 0) (n : ℕ) :
    spanConditionConstant (M * R) (τ * R) n = spanConditionConstant M τ n / R := by
  induction n with
  | zero => simp only [spanConditionConstant, zero_div]
  | succ n ih =>
    simp only [spanConditionConstant, ih]
    field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_UniformMeasuredPlaneComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_measured_plane_comparison (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η → η ≤ ε * R →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∀ x ∈ S, infDist x (W : Set (Ambient d)) ≤ A * η * (1 + ‖x‖ / R) := by
  obtain ⟨τ, hτ, _hτ1, hcompare⟩ := exists_measured_plane_comparison_width n d C c hC hc
  let K := spanConditionConstant 2 τ n
  have hK : 0 ≤ K := spanConditionConstant_nonneg 2 τ (by norm_num) hτ n
  let ε := min 1 (1 / (4 * (K + 1)))
  have hden : 0 < 4 * (K + 1) := by positivity
  have hε : 0 < ε := lt_min zero_lt_one (div_pos zero_lt_one hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεb : ε * (4 * (K + 1)) ≤ 1 := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmallK : K * (2 * ε) ≤ 1 / 2 := by nlinarith
  let A := 2 * (1 + 8 * K)
  have hA : 0 < A := by dsimp only [A] <;> positivity
  refine ⟨A, ε, hA, hε, hε1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr x hx
  have hscale : spanConditionConstant (2 * R) (τ * R) n = K / R :=
    spanConditionConstant_rescale 2 τ R hτ.ne' hR.ne' n
  have hratio : η / R ≤ ε := (div_le_iff₀ hR).mpr hηsmall
  have hsmall : spanConditionConstant (2 * R) (τ * R) n * (2 * η) ≤ 1 / 2 := by
    rw [hscale]
    calc
      (K / R) * (2 * η) = K * (2 * (η / R)) := by ring
      _ ≤ K * (2 * ε) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)) hK
      _ ≤ 1 / 2 := hsmallK
  obtain ⟨a, _ha, hanorm, hcomp⟩ := hcompare μ hfinite hg R hR hmass S W hS hW η hη herr hsmall
  have hηR : η ≤ R := hηsmall.trans
    ((mul_le_mul_of_nonneg_right hε1 hR.le).trans_eq (one_mul R))
  have hxa : ‖x - a‖ ≤ ‖x‖ + 2 * R := (norm_sub_le x a).trans (by linarith)
  have hn : ‖x - a‖ / R ≤ ‖x‖ / R + 2 := by
    apply (div_le_iff₀ hR).mpr
    calc
      ‖x - a‖ ≤ ‖x‖ + 2 * R := hxa
      _ = (‖x‖ / R + 2) * R := by field_simp
  have hq : 0 ≤ ‖x‖ / R := div_nonneg (norm_nonneg x) hR.le
  have hfactor : 1 + 4 * K * (‖x‖ / R + 2) ≤ (1 + 8 * K) * (1 + ‖x‖ / R) := by
    nlinarith [mul_nonneg hK hq]
  calc
    infDist x (W : Set (Ambient d)) ≤
        2 * η * (1 + 4 * spanConditionConstant (2 * R) (τ * R) n * ‖x - a‖) := hcomp x hx
    _ = 2 * η * (1 + 4 * K * (‖x - a‖ / R)) := by rw [hscale]; ring
    _ ≤ 2 * η * (1 + 4 * K * (‖x‖ / R + 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 4 * K))) (by positivity)
    _ ≤ 2 * η * ((1 + 8 * K) * (1 + ‖x‖ / R)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = A * η * (1 + ‖x‖ / R) := by dsimp only [A] <;> ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_JointFitBasePoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded base points for jointly fitting planes

A lower mass bound and a small integral joint-fit error produce a point close
to both affine planes. Orthogonal projection of that point supplies base points
on each plane with norm bounded by the ball radius plus the fitting tolerance.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped ENNReal

theorem exists_small_norm_points_on_joint_fits {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R η c : ℝ) (hR : 0 < R) (hη : 0 < η) (hc : 0 < c)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (herr : (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      η ^ 2 * ((c / 2) * R ^ n)) :
    (∃ a ∈ S, ‖a‖ ≤ R + η) ∧ (∃ b ∈ W, ‖b‖ ≤ R + η) := by
  have hm := jointPlaneGoodSet_mass_lower μ S W hS hW R η c hη hmass herr
  have hpos : 0 < μ.real (jointPlaneGoodSet S W R η) :=
    (mul_pos (by positivity : 0 < c / 2) (pow_pos hR n)).trans_le hm
  obtain ⟨x, hx, _hsupport, _hout⟩ := exists_support_point_outside_small_set μ
    (jointPlaneGoodSet S W R η) ∅ (by simp) (by simpa only [measureReal_empty] using! hpos)
  have hbounds := jointPlaneGoodSet_distance_bounds S W R η hη x hx
  have hxnorm : ‖x‖ ≤ R := by
    have hlt : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using! hbounds.1
    exact hlt.le
  have hpoint : ∀ T : AffineSubspace ℝ (Ambient d), (T : Set (Ambient d)).Nonempty →
      infDist x (T : Set (Ambient d)) ≤ η → ∃ a ∈ T, ‖a‖ ≤ R + η := by
    intro T hT hfit
    let : Nonempty T := hT.to_subtype
    let a : Ambient d := orthogonalProjection T x
    have herror : ‖x - a‖ ≤ η := by
      rw [← dist_eq_norm, dist_orthogonalProjection_eq_infDist]
      exact hfit
    exact ⟨a, orthogonalProjection_mem x,
      (norm_le_norm_add_norm_sub x a).trans (add_le_add hxnorm herror)⟩
  exact ⟨hpoint S hS hbounds.2.1.le, hpoint W hW hbounds.2.2.le⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_UniformDistanceTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform measured plane comparison transfers distance estimates from one affine plane to
another. A small-norm point on the joint fits anchors the comparison, giving an additive error
controlled by the fit scale and the normalized distance from the origin.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_measured_distance_transfer (n d : ℕ)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ A ε : ℝ, 0 < A ∧ 0 < ε ∧ ε ≤ 1 ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ R : ℝ, 0 < R → c * R ^ n ≤ μ.real (ball (0 : Ambient d) R) →
      ∀ S W : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S → IsAffineNPlane n W →
      ∀ η : ℝ, 0 < η → η ≤ ε * R →
      (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
        η ^ 2 * ((c / 2) * R ^ n) →
      ∀ x : Ambient d, infDist x (W : Set (Ambient d)) ≤
        infDist x (S : Set (Ambient d)) + A * η * (3 + ‖x‖ / R) := by
  obtain ⟨A, ε, hA, hε, hε1, hcompare⟩ := exists_uniform_measured_plane_comparison n d C c hC hc
  refine ⟨A, ε, hA, hε, hε1, ?_⟩
  intro μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr x
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let : Nonempty S := hS.1.to_subtype
  obtain ⟨⟨a, ha, hanorm⟩, _hb⟩ := exists_small_norm_points_on_joint_fits
    μ S W hS.1 hW.1 R η c hR hη hc hmass herr
  have hηR : η ≤ R := hηsmall.trans
    ((mul_le_mul_of_nonneg_right hε1 hR.le).trans_eq (one_mul R))
  have haB : ‖a‖ ≤ 2 * R := by linarith
  have hfit := hcompare μ hfinite hg R hR hmass S W hS hW η hη hηsmall herr
  have h := plane_distance_transfer S (W : Set (Ambient d)) a ha (2 * R) (A * η) R
    (mul_nonneg hA.le hη.le) hR haB hfit x
  have heq : 1 + (‖x‖ + 2 * R) / R = 3 + ‖x‖ / R := by
    rw [add_div, mul_div_cancel_right₀ 2 hR.ne']
    ring
  simpa only [heq] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicDistanceSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Distance transfer between adjacent dyadic plane fits

Calibrated fitting errors and lower mass bounds give distance comparisons between
successive affine planes. A uniform smallness threshold on the final dyadic error
controls every adjacent step, with constants chosen before the measure and planes.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_dyadic_distance_steps (n d : ℕ)
    (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hb : 1 < b) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ * b ^ N ≤ κ →
      ∀ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) →
      (∀ i ≤ N, c * ((2 : ℝ) ^ i) ^ n ≤ μ.real (ball (0 : Ambient d) ((2 : ℝ) ^ i))) →
      (∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
        infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
          2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) →
      ∀ i < N, ∀ x : Ambient d,
        infDist x (P i : Set (Ambient d)) ≤ infDist x (P (i + 1) : Set (Ambient d)) +
          B * δ * (2 : ℝ) ^ i * b ^ i * (3 + ‖x‖ / (2 : ℝ) ^ i) := by
  obtain ⟨A, ε, hA, hε, _hε1, htransfer⟩ := exists_uniform_measured_distance_transfer n d C c hC hc
  obtain ⟨L, hL, hcal⟩ := exists_dyadic_fit_calibration n b c hc
  let B := A * L
  let κ := ε / L
  refine ⟨B, κ, mul_pos hA hL, div_pos hε hL, ?_⟩
  intro μ hfinite hg N δ hδ hsmall P hP hmass hfit i hi x
  let : IsFiniteMeasureOnCompacts μ := hfinite
  let η := L * δ * (2 : ℝ) ^ i * b ^ i
  have hη : 0 < η := by dsimp only [η] <;> positivity
  have hsmallL : L * δ * b ^ N ≤ ε := by
    have h := (le_div_iff₀ hL).mp hsmall
    nlinarith
  have hηsmall : η ≤ ε * (2 : ℝ) ^ i :=
    calibrated_dyadic_threshold_small L δ b ε hL.le hδ.le hb.le N i hi.le hsmallL
  have hjoint := calibrated_dyadic_joint_fit_error μ P hP δ b L c hcal N hfit i hi
  have hreverse : (∫ y in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      jointPlaneFitError (P (i + 1)) (P i) y ∂μ) ≤ η ^ 2 * ((c / 2) * ((2 : ℝ) ^ i) ^ n) := by
    simpa only [jointPlaneFitError, add_comm] using! hjoint
  have h := htransfer μ hfinite hg ((2 : ℝ) ^ i) (by positivity) (hmass i hi.le)
    (P (i + 1)) (P i) (hP (i + 1)) (hP i) η hη hηsmall hreverse x
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [B, η]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicDistanceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open scoped BigOperators

theorem geom_sum_le_pow_div (b : ℝ) (hb : 1 < b) (l : ℕ) :
    (∑ i ∈ Finset.range l, b ^ i) ≤ b ^ l / (b - 1) := by
  rw [geom_sum_eq (ne_of_gt hb) l]
  exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hb.le)

theorem dyadic_distance_error_sum_le (B δ b X : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hb : 1 < b) (hX : 0 ≤ X)
    (l : ℕ) (hXl : X ≤ (2 : ℝ) ^ l) :
    (∑ i ∈ Finset.range l, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) ≤
      B * δ * (2 : ℝ) ^ l * b ^ l * (3 / (2 * b - 1) + 1 / (b - 1)) := by
  have hterm : ∀ i : ℕ, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i) =
      B * δ * (3 * (2 * b) ^ i + X * b ^ i) := by
    intro i
    rw [mul_pow]
    field_simp
  have hsum : (∑ i ∈ Finset.range l, B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) =
      B * δ * (3 * (∑ i ∈ Finset.range l, (2 * b) ^ i) +
        X * (∑ i ∈ Finset.range l, b ^ i)) := by
    simp only [hterm, Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  have htwo : 1 < 2 * b := by linarith
  have hinner : 3 * (∑ i ∈ Finset.range l, (2 * b) ^ i) + X * (∑ i ∈ Finset.range l, b ^ i) ≤
      3 * ((2 * b) ^ l / (2 * b - 1)) + (2 : ℝ) ^ l * (b ^ l / (b - 1)) := by
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (geom_sum_le_pow_div (2 * b) htwo l) (by norm_num)
    · exact (mul_le_mul_of_nonneg_left (geom_sum_le_pow_div b hb l) hX).trans
        (mul_le_mul_of_nonneg_right hXl (div_nonneg (pow_nonneg (by linarith) l)
          (sub_nonneg.mpr hb.le)))
  rw [hsum]
  calc
    _ ≤ B * δ * (3 * ((2 * b) ^ l / (2 * b - 1)) + (2 : ℝ) ^ l * (b ^ l / (b - 1))) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg hB hδ)
    _ = _ := by rw [mul_pow]; ring

theorem dyadic_distance_chain_bound (d : ℕ → ℝ) (B δ b X : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hb : 1 < b) (hX : 0 ≤ X)
    (l : ℕ) (hXl : X ≤ (2 : ℝ) ^ l)
    (hstep : ∀ i < l, d i ≤ d (i + 1) +
      B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) :
    d 0 ≤ d l + B * δ * (2 : ℝ) ^ l * b ^ l * (3 / (2 * b - 1) + 1 / (b - 1)) := by
  exact (upper_bound_by_last_and_step_sum d
    (fun i => B * δ * (2 : ℝ) ^ i * b ^ i * (3 + X / (2 : ℝ) ^ i)) l hstep).trans
      (add_le_add le_rfl (dyadic_distance_error_sum_le B δ b X hB hδ hb hX l hXl))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FixedPlaneDyadicMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic moments relative to one fixed plane

Approximate excess minimizers provide an affine plane at each dyadic radius.
Summing the adjacent distance-transfer estimates controls the squared distance to
the initial plane on every larger ball, uniformly in the measure and number of scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_fixed_plane_dyadic_moments {n d : ℕ} (hnd : n ≤ d)
    (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (hb : 1 < b) :
    ∃ M κ : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ μ : Measure (Ambient d), IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth n C μ →
      ∀ N : ℕ, ∀ δ : ℝ, 0 < δ → δ * b ^ N ≤ κ →
      (∀ i ≤ N, c * ((2 : ℝ) ^ i) ^ n ≤ μ.real (ball (0 : Ambient d) ((2 : ℝ) ^ i))) →
      (∀ i ≤ N, squaredExcess n μ 0 ((2 : ℝ) ^ i) ≤ (δ * b ^ i) ^ 2) →
      ∃ P : ℕ → AffineSubspace ℝ (Ambient d), (∀ i, IsAffineNPlane n (P i)) ∧
        (∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
          infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
            2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) ∧
        ∀ l ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
          infDist x (P 0 : Set (Ambient d)) ^ 2 ∂μ) ≤
            M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := by
  obtain ⟨B, κ, hB, hκ, hsteps⟩ := exists_uniform_dyadic_distance_steps n d C c b hC hc hb
  let K := B * (3 / (2 * b - 1) + 1 / (b - 1))
  have hden1 : 0 < b - 1 := sub_pos.mpr hb
  have hden2 : 0 < 2 * b - 1 := by linarith
  have hK : 0 < K := by dsimp only [K] <;> positivity
  let M := 4 + 2 * C * K ^ 2
  have hM : 0 < M := by dsimp only [M] <;> positivity
  refine ⟨M, κ, hM, hκ, ?_⟩
  intro μ hfinite hg N δ hδ hsmall hmass hexcess
  let : IsFiniteMeasureOnCompacts μ := hfinite
  obtain ⟨P, hP, hfit⟩ := exists_dyadic_approximate_fits hnd μ δ b hδ (by linarith) N hexcess
  have hstep := hsteps μ hfinite hg N δ hδ hsmall P hP hmass hfit
  refine ⟨P, hP, hfit, ?_⟩
  intro l hl
  have hpoint : ∀ x ∈ ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (P 0 : Set (Ambient d)) ≤ infDist x (P l : Set (Ambient d)) +
        K * (δ * b ^ l) * (2 : ℝ) ^ l := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ l := by
      have hlt : ‖x‖ < (2 : ℝ) ^ l := by simpa only [mem_ball, dist_zero_right] using! hx
      exact hlt.le
    have h := dyadic_distance_chain_bound (fun i => infDist x (P i : Set (Ambient d)))
      B δ b ‖x‖ hB.le hδ.le hb (norm_nonneg x) l hxnorm
      (fun i hi => hstep i (lt_of_lt_of_le hi hl) x)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [K]
    ring
  have h := plane_second_moment_bound_from_distance_transfer μ C hg (P 0) (P l)
    (hP 0).1 (hP l).1 ((2 : ℝ) ^ l) (δ * b ^ l) K 2 (by positivity)
    (by positivity) hK.le (hfit l hl) hpoint
  simpa only [M, show (2 : ℝ) * 2 = 4 by norm_num] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_AdmissibleDyadicHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem dyadic_admissibleRadius_of_horizon {d : ℕ} (μ : Measure (Ambient d))
    (T : ℕ) (hT : AdmissibleRadius μ ((2 : ℝ) ^ T)) (l : ℕ) (hl : l ≤ T) :
    AdmissibleRadius μ ((2 : ℝ) ^ l) := by
  refine ⟨by positivity, ?_⟩
  exact (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hl)).trans hT.2

theorem dyadic_lower_real_mass_of_admissible_horizon {d : ℕ} (n : ℕ) (C G : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball 0 r))
    (T : ℕ) (hT : AdmissibleRadius μ ((2 : ℝ) ^ T)) (l : ℕ) (hl : l ≤ T) :
    C⁻¹ * ((2 : ℝ) ^ l) ^ n ≤ μ.real (ball 0 ((2 : ℝ) ^ l)) := by
  have hpos : 0 < (2 : ℝ) ^ l := by positivity
  have hfin : μ (ball 0 ((2 : ℝ) ^ l)) ≠ ∞ := ne_of_lt
    ((hg.2 0 ((2 : ℝ) ^ l) hpos).trans_lt ENNReal.ofReal_lt_top)
  have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr
    (hlower _ (dyadic_admissibleRadius_of_horizon μ T hT l hl))
  have hn : 0 ≤ ((2 : ℝ) ^ l) ^ n / C := by positivity
  rw [ENNReal.toReal_ofReal hn] at h
  simpa only [Measure.real, div_eq_mul_inv, mul_comm] using! h

theorem support_diameters_grow_of_admissible_dyadic_horizon {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (T : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support := by
  have hp : Tendsto (fun j => (2 : ℝ) ^ T j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hT
  intro r _hr
  filter_upwards [hp.eventually (eventually_ge_atTop r)] with j hj
  exact (ENNReal.ofReal_le_ofReal hj).trans (horizon j).2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ExcessSourcePlaneMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_shifted_fixed_plane_source_moments {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball 0 r))
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (T : ℕ → ℕ)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb : 1 < b) (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j → squaredExcess n (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2) :
    ∃ J : ℕ, ∃ M : ℝ, 0 < M ∧ ∃ S : ℕ → AffineSubspace ℝ (Ambient d),
      (∀ j, IsAffineNPlane n (S j)) ∧ ∀ j l, l ≤ T (j + J) →
        (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2
          ∂μ (j + J)) ≤ M * (δ (j + J) * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := by
  obtain ⟨M, κ, hM, hκ, hfit⟩ := exists_uniform_fixed_plane_dyadic_moments hnd G C⁻¹ b
    (hg 0).1 (inv_pos.mpr hC) hb
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hsmall.eventually (gt_mem_nhds hκ))
  have hfits (j : ℕ) := hfit (μ (j + J)) inferInstance (hg (j + J)) (T (j + J)) (δ (j + J))
    (hδ (j + J)) (hJ (j + J) (by omega)).le
    (fun l hl => dyadic_lower_real_mass_of_admissible_horizon n C G (μ (j + J)) hC
      (hg (j + J)) (hlower (j + J)) (T (j + J)) (horizon (j + J)) l hl)
    (hexcess (j + J))
  choose P hP _hfit hfixed using hfits
  exact ⟨J, M, hM, (fun j => P j 0), (fun j => hP j 0), hfixed⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupExcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem blowup_infDist_plane {d : ℕ} (a y : Ambient d) (r : ℝ) (hr : 0 < r)
    (S : AffineSubspace ℝ (Ambient d)) :
    infDist (r⁻¹ • (y - a)) (S : Set (Ambient d)) =
      r⁻¹ * infDist y (S.map (physicalAffine a r hr).toAffineMap : Set (Ambient d)) := by
  have h := physicalAffine_infDist a ((physicalAffine a r hr).symm y) r hr
    (S : Set (Ambient d))
  rw [(physicalAffine a r hr).apply_symm_apply] at h
  change infDist y (S.map (physicalAffine a r hr).toAffineMap : Set (Ambient d)) =
    r * infDist (r⁻¹ • (y - a)) (S : Set (Ambient d)) at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

theorem quadraticPlaneError_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (S : AffineSubspace ℝ (Ambient d)) :
    quadraticPlaneError n (blowupMeasure n μ a r) 0 R S =
      quadraticPlaneError n μ a (r * R) (S.map (physicalAffine a r hr).toAffineMap) := by
  unfold quadraticPlaneError
  rw [blowupMeasure_setIntegral_ball n μ a 0 r R hr]
  simp only [smul_zero, add_zero, smul_eq_mul]
  simp_rw [blowup_infDist_plane a _ r hr S, mul_pow, integral_const_mul]
  simp only [mul_inv_rev, pow_add, inv_pow]
  ring

theorem squaredExcess_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    squaredExcess n (blowupMeasure n μ a r) 0 R = squaredExcess n μ a (r * R) := by
  unfold squaredExcess
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a r hr).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, quadraticPlaneError_blowup n μ a r R hr S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a r hr).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [quadraticPlaneError_blowup n μ a r R hr, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupRieszOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Riesz operators under affine blowup

Affine dilation rescales distances, the Riesz kernel, and the hard truncation radius.
The corresponding change of measure gives the square-seminorm scaling identity and
transports uniform Riesz bounds to blowups. The seminorm identity also covers functions
that are not almost everywhere strongly measurable, since its exponent is positive and finite.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem physicalAffine_dist {d : ℕ} (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    dist (physicalAffine a r hr x) (physicalAffine a r hr y) = r * dist x y := by
  simp only [physicalAffine_apply, dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le]

theorem kernel_physicalAffine {d : ℕ} (n : ℕ) (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    kernel n (physicalAffine a r hr x) (physicalAffine a r hr y) =
      (r ^ n)⁻¹ • kernel n x y := by
  have hsub : physicalAffine a r hr x - physicalAffine a r hr y = r • (x - y) := by
    simp only [physicalAffine_apply, smul_sub]
    abel
  simp only [kernel, hsub, norm_smul, Real.norm_of_nonneg hr.le, mul_pow, mul_inv_rev,
    smul_smul]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem truncated_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r ε : ℝ) (hr : 0 < r) (f : Ambient d → ℝ) :
    truncated n (blowupMeasure n μ a r) ε f x =
      truncated n μ (r * ε) (fun y => f (r⁻¹ • (y - a))) (physicalAffine a r hr x) := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  have hdist (y : Ambient d) : dist (physicalAffine a r hr x) y =
      r * dist x (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a x ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    exact h
  have hset : (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' {y | ε < dist x y} =
      {y | r * ε < dist (physicalAffine a r hr x) y} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hdist, mul_lt_mul_iff_right₀ hr]
  have hk (y : Ambient d) : kernel n (physicalAffine a r hr x) y =
      (r ^ n)⁻¹ • kernel n x (r⁻¹ • (y - a)) := by
    have h := kernel_physicalAffine n a x ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    exact h
  unfold truncated
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), he.setIntegral_map, hset,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hk, smul_smul, smul_smul, mul_comm]

theorem memLp_blowup_iff {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (f : Ambient d → E) (p : ℝ≥0∞) :
    MemLp f p (blowupMeasure n μ a r) ↔ MemLp (fun y => f (r⁻¹ • (y - a))) p μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  have hcancel : ENNReal.ofReal (r ^ n) • blowupMeasure n μ a r =
      μ.map (fun y => r⁻¹ • (y - a)) := by
    rw [blowupMeasure, smul_smul, ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ n),
      mul_inv_cancel₀ (pow_ne_zero n hr.ne'), ENNReal.ofReal_one, one_smul]
  constructor
  · intro hf
    have hm := hf.smul_measure (ENNReal.ofReal_ne_top : ENNReal.ofReal (r ^ n) ≠ ⊤)
    rw [hcancel] at hm
    exact he.memLp_map_measure_iff.mp hm
  · intro hf
    have hm : MemLp f p (μ.map (fun y => r⁻¹ • (y - a))) := he.memLp_map_measure_iff.mpr hf
    exact hm.smul_measure ENNReal.ofReal_ne_top

theorem eLpNorm_blowup {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (f : Ambient d → E) :
    eLpNorm f 2 (blowupMeasure n μ a r) =
      (ENNReal.ofReal ((r ^ n)⁻¹)) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm (fun y => f (r⁻¹ • (y - a))) 2 μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [blowupMeasure, eLpNorm_smul_measure_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    he.eLpNorm_map_measure]
  rfl

theorem uniform_riesz_bound_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (D : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧ eLpNorm (truncated n μ ε f) 2 μ ≤
        (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (blowupMeasure n μ a r) →
      MemLp (truncated n (blowupMeasure n μ a r) ε f) 2 (blowupMeasure n μ a r) ∧
      eLpNorm (truncated n (blowupMeasure n μ a r) ε f) 2 (blowupMeasure n μ a r) ≤
        (D : ℝ≥0∞) * eLpNorm f 2 (blowupMeasure n μ a r) := by
  intro ε hε f hf
  obtain ⟨hm, hn⟩ := hB (r * ε) (mul_pos hr hε) (fun y => f (r⁻¹ • (y - a)))
    ((memLp_blowup_iff n μ a r hr f 2).mp hf)
  have ht : (fun y => truncated n (blowupMeasure n μ a r) ε f (r⁻¹ • (y - a))) =
      truncated n μ (r * ε) (fun y => f (r⁻¹ • (y - a))) := by
    funext y
    rw [truncated_blowup n μ a _ r ε hr]
    change truncated n μ (r * ε) _
      (physicalAffine a r hr ((physicalAffine a r hr).symm y)) = _
    rw [(physicalAffine a r hr).apply_symm_apply]
  constructor
  · apply (memLp_blowup_iff n μ a r hr _ 2).mpr
    rw [ht]
    exact hm
  · rw [eLpNorm_blowup n μ a r hr, ht, eLpNorm_blowup n μ a r hr]
    calc
      _ ≤ _ * ((D : ℝ≥0∞) * eLpNorm (fun y => f (r⁻¹ • (y - a))) 2 μ) := mul_le_mul_right hn _
      _ = _ := by ac_rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupScalarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings under blowup

Change of variables for normalized blowup measures transfers the near and far parts
of the scalar Riesz pairing. Rescaling the localization ball and pulling back the test
function gives the exact factor `(r ^ n)⁻¹` in the pairing identity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem blowupMeasure_integral {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (f : Ambient d → E) :
    (∫ y, f y ∂blowupMeasure n μ a r) =
      (r ^ n)⁻¹ • ∫ y, f (r⁻¹ • (y - a)) ∂μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [blowupMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), he.integral_map]

theorem blowupMeasure_integral_prod_restrict {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    [SFinite μ] (a : Ambient d) (r : ℝ) (hr : 0 < r) (s t : Set (Ambient d))
    (f : Ambient d × Ambient d → ℝ) :
    (∫ q, f q ∂((blowupMeasure n μ a r).restrict s).prod
      ((blowupMeasure n μ a r).restrict t)) =
      ((r ^ n)⁻¹) ^ 2 * ∫ q, f (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a))
        ∂(μ.restrict ((fun y => r⁻¹ • (y - a)) ⁻¹' s)).prod
          (μ.restrict ((fun y => r⁻¹ • (y - a)) ⁻¹' t)) := by
  let e := (physicalHomeomorph a r hr).symm.toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) := e.measurableEmbedding
  have heprod : MeasurableEmbedding (Prod.map (fun y : Ambient d => r⁻¹ • (y - a))
      (fun y : Ambient d => r⁻¹ • (y - a))) := (e.prodCongr e).measurableEmbedding
  simp only [blowupMeasure, Measure.restrict_smul, he.restrict_map]
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, integral_smul_measure,
    Measure.map_prod_map _ _ he.measurable he.measurable, heprod.integral_map]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹),
    smul_eq_mul, pow_two]
  rfl

theorem kernel_normalized {d : ℕ} (n : ℕ) (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    kernel n (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) = r ^ n • kernel n x y := by
  have h := kernel_physicalAffine n a ((physicalAffine a r hr).symm x)
    ((physicalAffine a r hr).symm y) r hr
  rw [(physicalAffine a r hr).apply_symm_apply, (physicalAffine a r hr).apply_symm_apply] at h
  rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hr.ne'), one_smul]
  rfl

theorem blowup_preimage_closedExterior {d : ℕ} (a : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' closedExterior 0 R = closedExterior a (r * R) := by
  ext y
  have hdist : dist a y = r * dist (0 : Ambient d) (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a 0 ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    simpa only [physicalAffine_apply, smul_zero, add_zero, physicalAffine_symm_apply] using! h
  simp only [closedExterior, mem_preimage, mem_ofPred_eq, hdist, mul_le_mul_iff_right₀ hr]

theorem rieszScalarPairing_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) [SFinite μ]
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing n (blowupMeasure n μ a r) 0 R e φ =
      (r ^ n)⁻¹ * rieszScalarPairing n μ a (r * R) e (fun y => φ (r⁻¹ • (y - a))) := by
  have hi (q : Ambient d × Ambient d) :
      rieszInteriorIntegrand n e φ (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a)) =
        r ^ n * rieszInteriorIntegrand n e (fun y => φ (r⁻¹ • (y - a))) q := by
    unfold rieszInteriorIntegrand
    dsimp only
    rw [kernel_normalized n a q.1 q.2 r hr, real_inner_smul_right]
    ring
  have hf (q : Ambient d × Ambient d) :
      rieszFarIntegrand n e φ 0 (r⁻¹ • (q.1 - a), r⁻¹ • (q.2 - a)) =
        r ^ n * rieszFarIntegrand n e (fun y => φ (r⁻¹ • (y - a))) a q := by
    unfold rieszFarIntegrand
    dsimp only
    have hzero : r⁻¹ • (a - a) = (0 : Ambient d) := by simp
    rw [← hzero, kernel_normalized n a q.1 q.2 r hr, kernel_normalized n a a q.2 r hr,
      ← smul_sub, real_inner_smul_right]
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [blowupMeasure_integral_prod_restrict n μ a r hr,
    blowupMeasure_integral_prod_restrict n μ a r hr,
    blowup_preimage_ball a 0 r R hr, blowup_preimage_closedExterior a r R hr]
  simp only [smul_zero, add_zero]
  simp_rw [hi, hf, integral_const_mul]
  have hcancel : ((r ^ n)⁻¹) ^ 2 * r ^ n = (r ^ n)⁻¹ := by
    field_simp
  have hscale (z : ℝ) : ((r ^ n)⁻¹) ^ 2 * (r ^ n * z) = (r ^ n)⁻¹ * z := by
    rw [← mul_assoc, hcancel]
  simp_rw [hscale]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem physical_test_lipschitz {d : ℕ} (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (hφ : LipschitzWith 1 φ) :
    LipschitzWith 1 (fun y => r * φ (r⁻¹ • (y - a))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hd : dist x y = r * dist (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a ((physicalAffine a r hr).symm x)
      ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply, (physicalAffine a r hr).apply_symm_apply] at h
    exact h
  simp only [NNReal.coe_one, one_mul]
  calc
    _ = r * dist (φ (r⁻¹ • (x - a))) (φ (r⁻¹ • (y - a))) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hr]
    _ ≤ r * dist (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      simpa only [NNReal.coe_one, one_mul] using! hφ.dist_le_mul (r⁻¹ • (x - a)) (r⁻¹ • (y - a))
    _ = _ := hd.symm

theorem physical_test_tsupport {d : ℕ} (a : Ambient d) (r A : ℝ) (hr : 0 < r)
    (φ : Ambient d → ℝ) (hs : tsupport φ ⊆ ball 0 A) :
    tsupport (fun y => r * φ (r⁻¹ • (y - a))) ⊆ ball a (r * A) := by
  intro y hy
  have hcomp : r⁻¹ • (y - a) ∈ tsupport φ :=
    tsupport_comp_subset_preimage (f := fun y : Ambient d => r⁻¹ • (y - a)) φ
      (by fun_prop) (tsupport_mul_subset_right hy)
  have hyball : y ∈ (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' ball 0 A := hs hcomp
  simpa only [blowup_preimage_ball a 0 r A hr, smul_zero, add_zero] using! hyball

theorem ScalarOscillationBound.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) [SFinite μ]
    (a : Ambient d) (r A v : ℝ) (hr : 0 < r)
    (hosc : ScalarOscillationBound n μ a (r * A) (r ^ (n + 1) * v)) :
    ScalarOscillationBound n (blowupMeasure n μ a r) 0 A v := by
  intro e he φ hφ hs hzero
  have hmean : (∫ y, φ (r⁻¹ • (y - a)) ∂μ) = 0 := by
    rw [blowupMeasure_integral n μ a r hr, smul_eq_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero (pow_ne_zero n hr.ne'))
  have hmean' : (∫ y, r * φ (r⁻¹ • (y - a)) ∂μ) = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  have hp := hosc e he (fun y => r * φ (r⁻¹ • (y - a)))
    (physical_test_lipschitz a r hr φ hφ) (physical_test_tsupport a r A hr φ hs) hmean'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos hr] at hp
  have hbound : |rieszScalarPairing n μ a (2 * (r * A)) e
      (fun y => φ (r⁻¹ • (y - a)))| ≤ r ^ n * v := by
    apply (mul_le_mul_iff_right₀ hr).mp
    simpa only [pow_succ, mul_assoc, mul_comm r] using! hp
  rw [rieszScalarPairing_blowup n μ a r (2 * A) hr, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (r ^ n)⁻¹)]
  have hrad : r * (2 * A) = 2 * (r * A) := by ring
  rw [hrad]
  calc
    _ ≤ (r ^ n)⁻¹ * (r ^ n * v) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = v := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hr.ne'), one_mul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedTailDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem normalized_last_radius_dyadic_identity (R : ℝ) (hR : 0 < R) (j : ℕ) :
    (R * (2 : ℝ) ^ (2 * j + 3))⁻¹ / (1 / 2 : ℝ) ^ j =
      (R * 8)⁻¹ * (1 / 2 : ℝ) ^ j := by
  rw [pow_add, pow_mul, div_pow]
  norm_num
  field_simp
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
  norm_num

theorem normalized_last_radius_dyadic_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j : ℕ => (R * (2 : ℝ) ^ (2 * j + 3))⁻¹ / (1 / 2 : ℝ) ^ j) atTop (𝓝 0) := by
  simp only [normalized_last_radius_dyadic_identity R hR]
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((R * 8)⁻¹)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicExcessSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem dyadic_excess_horizon_identity (b : ℝ) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * b ^ (2 * j + 3) = b ^ 3 * (b ^ 2 / 2) ^ j := by
  rw [pow_add b (2 * j) 3, pow_mul b 2 j]
  have hp : (1 / 2 : ℝ) ^ j * (b ^ 2) ^ j = (b ^ 2 / 2) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    (1 / 2 : ℝ) ^ j * ((b ^ 2) ^ j * b ^ 3) =
        b ^ 3 * ((1 / 2 : ℝ) ^ j * (b ^ 2) ^ j) := by ring
    _ = _ := by rw [hp]

theorem dyadic_excess_horizon_tendsto_zero (b : ℝ) (hb : b ^ 2 < 2) :
    Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j * b ^ (2 * j + 3)) atTop (𝓝 0) := by
  simp only [dyadic_excess_horizon_identity]
  simpa only [mul_zero] using!
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ b ^ 2 / 2)
      (by linarith : b ^ 2 / 2 < 1)).const_mul (b ^ 3)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ExcessPropagationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Filter Topology

theorem propagationScale_pos (j : ℕ) : 0 < propagationScale j := by
  unfold propagationScale
  positivity

theorem propagationScale_tendsto_zero : Tendsto propagationScale atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)

theorem propagationHorizon_tendsto_atTop : Tendsto propagationHorizon atTop atTop := by
  have h : StrictMono propagationHorizon := by
    intro i j hij
    dsimp [propagationHorizon]
    omega
  exact h.tendsto_atTop

theorem propagationTestRadius_tendsto_atTop : Tendsto propagationTestRadius atTop atTop := by
  exact Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 8)
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      propagationHorizon_tendsto_atTop)

theorem propagation_horizon_product_tendsto_zero (b : ℝ) (hb : b ^ 2 < 2) :
    Tendsto (fun j => propagationScale j * b ^ propagationHorizon j) atTop (𝓝 0) :=
  dyadic_excess_horizon_tendsto_zero b hb

theorem propagation_last_error_tendsto_zero :
    Tendsto (fun j => ((2 : ℝ) ^ propagationHorizon j)⁻¹ / propagationScale j) atTop (𝓝 0) := by
  simpa only [one_mul] using! normalized_last_radius_dyadic_tendsto 1 zero_lt_one

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X] [Nonempty X]

theorem finiteMeasure_cell_mass_tendsto (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s : Set X) (hboundary : (ν : Measure X) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure X).real s) atTop (𝓝 ((ν : Measure X).real s)) := by
  have hn : Tendsto (fun j => (μ j).normalize) atTop (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hweak hν
  have hb : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν]
    rw [(ν.null_iff_toMeasure_null _).mpr hboundary, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
  have hmass : Tendsto (fun j => (μ j) s) atTop (𝓝 (ν s)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using! hweak.mass.mul hp
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmass

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_WeakRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak convergence on continuity sets

Weak convergence of finite measures controls the masses of sets with null boundary.
Weighting by bounded continuous nonnegative functions transfers this control to restricted
integrals, providing continuity-set versions of the weak convergence estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction

theorem finiteMeasure_continuitySet_mass_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (s : Set (Ambient d))
    (hboundary : (ν : Measure (Ambient d)) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure (Ambient d)).real s) atTop
      (𝓝 ((ν : Measure (Ambient d)).real s)) := by
  by_cases hν : ν = 0
  · subst ν
    have ht : Tendsto (fun j => (μ j : Measure (Ambient d)).real univ) atTop (𝓝 0) := by
      simpa using! NNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
    simpa using! squeeze_zero (fun _ => measureReal_nonneg)
      (fun j => measureReal_mono (μ := (μ j : Measure (Ambient d))) (subset_univ s)) ht
  · exact finiteMeasure_cell_mass_tendsto μ ν hweak hν s hboundary

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactWeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal BoundedContinuousFunction CompactlySupported

theorem compactWeightedFiniteMeasure_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0)) (g : Ambient d → ℝ) :
    (∫ x, g x ∂(compactWeightedFiniteMeasure μ f : Measure (Ambient d))) =
      ∫ x, (f x : ℝ) * g x ∂μ := by
  exact integral_withDensity_eq_integral_smul f.continuous.measurable g

theorem compactWeightedFiniteMeasure_tendsto {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : C_c(Ambient d, ℝ≥0)) :
    Tendsto (fun j => compactWeightedFiniteMeasure (μ j) f) atTop
      (𝓝 (compactWeightedFiniteMeasure ν f)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => f.toReal x * g x, f.toReal.continuous.mul g.continuous⟩,
      f.toReal.hasCompactSupport.mul_right⟩
  have ht := hlocal test
  change Tendsto (fun j => ∫ x, f.toReal x * g x ∂μ j) atTop
    (𝓝 (∫ x, f.toReal x * g x ∂ν)) at ht
  simpa only [compactWeightedFiniteMeasure_integral,
    CompactlySupportedContinuousMap.toReal_apply] using! ht

theorem exists_compact_nonneg_cutoff {d : ℕ} (s : Set (Ambient d)) (hs : IsCompact s) :
    ∃ f : C_c(Ambient d, ℝ≥0), (∀ x ∈ s, f x = 1) ∧ ∀ x, f x ≤ 1 := by
  obtain ⟨g, hgs, _, hgc, hg⟩ :=
    exists_continuous_one_zero_of_isCompact hs isClosed_empty (disjoint_empty s)
  let g₀ : C_c(Ambient d, ℝ) := ⟨g, hgc⟩
  refine ⟨g₀.nnrealPart, ?_, ?_⟩
  · intro x hx
    change Real.toNNReal (g x) = 1
    rw [show g x = 1 from hgs hx]
    simp
  · intro x
    change Real.toNNReal (g x) ≤ 1
    simpa using! Real.toNNReal_le_toNNReal (hg x).2

theorem compactWeightedFiniteMeasure_restrict {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)).restrict s = μ.restrict s := by
  change (μ.withDensity (fun x => (f x : ℝ≥0∞))).restrict s = _
  rw [restrict_withDensity hs]
  calc
    _ = (μ.restrict s).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hs] with x hx
      simp only [hf x hx, ENNReal.coe_one, Pi.one_apply]
    _ = _ := withDensity_one

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_LocalSupportConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactWeightedFiniteMeasure_apply_eq {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ≥0))
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hf : ∀ x ∈ s, f x = 1) :
    (compactWeightedFiniteMeasure μ f : Measure (Ambient d)) s = μ s := by
  have h := congrArg (fun ρ : Measure (Ambient d) => ρ univ)
    (compactWeightedFiniteMeasure_restrict μ f s hs hf)
  simpa using! h

theorem compactTestConvergence_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν)
    (q : Ambient d → ℝ) (K : ℝ≥0) (hq : LipschitzWith K q)
    (hzero : ∀ᵐ x ∂ν, q x = 0) (a : Ambient d) (R ε r c : ℝ)
    (hε : 0 < ε) (hc : 0 < c) (hr : (K : ℝ) * r ≤ ε / 2)
    (hball : ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r)) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → q x < ε := by
  obtain ⟨f, hf, _⟩ := exists_compact_nonneg_cutoff (closedBall a (R + r))
    (isCompact_closedBall a (R + r))
  let νf := compactWeightedFiniteMeasure ν f
  let μf := fun j => compactWeightedFiniteMeasure (μ j) f
  let bad : Set (Ambient d) := {x | ε / 2 ≤ q x}
  have hclosed : IsClosed bad := isClosed_le continuous_const hq.continuous
  have hzero' : ∀ᵐ x ∂(νf : Measure (Ambient d)), q x = 0 :=
    (withDensity_absolutelyContinuous ν (fun x => (f x : ℝ≥0∞))).ae_le hzero
  have hbad : (νf : Measure (Ambient d)) bad = 0 := by
    have hnot : ∀ᵐ x ∂(νf : Measure (Ambient d)), x ∉ bad := by
      filter_upwards [hzero'] with x hx
      change ¬ ε / 2 ≤ q x
      rw [hx]
      linarith
    simpa only [ae_iff, not_not] using! hnot
  have hfront : (νf : Measure (Ambient d)) (frontier bad) = 0 :=
    measure_mono_null hclosed.frontier_subset hbad
  have hmass : Tendsto (fun j => (μf j : Measure (Ambient d)).real bad) atTop (𝓝 0) := by
    simpa only [Measure.real, hbad, ENNReal.toReal_zero] using!
      finiteMeasure_continuitySet_mass_tendsto μf νf
        (compactWeightedFiniteMeasure_tendsto μ ν hlocal f) bad hfront
  filter_upwards [hball, hmass.eventually (gt_mem_nhds hc)] with j hj hsmall
  intro x hx hxsupport
  by_contra hlarge
  have hlarge' : ε ≤ q x := le_of_not_gt hlarge
  have hsub : ball x r ⊆ bad := by
    intro y hy
    have hd : dist x y ≤ r := by
      simpa only [dist_comm] using! (show dist y x < r from hy).le
    have hdiff : q x - q y ≤ (K : ℝ) * dist x y := by
      have h := hq.dist_le_mul x y
      rw [Real.dist_eq] at h
      exact (le_abs_self _).trans h
    have hmul := mul_le_mul_of_nonneg_left hd K.coe_nonneg
    change ε / 2 ≤ q y
    linarith
  have hfone : ∀ y ∈ ball x r, f y = 1 := by
    intro y hy
    apply hf y
    apply mem_closedBall.mpr
    have hd := dist_triangle y x a
    have hy' : dist y x < r := hy
    have hx' : dist x a < R := hx
    linarith
  have heq : (μf j : Measure (Ambient d)).real (ball x r) = (μ j).real (ball x r) := by
    unfold Measure.real
    rw [show (μf j : Measure (Ambient d)) (ball x r) = (μ j) (ball x r) from
      compactWeightedFiniteMeasure_apply_eq (μ j) f (ball x r) measurableSet_ball hfone]
  have hmassge : c ≤ (μf j : Measure (Ambient d)).real bad := by
    calc
      c ≤ (μ j).real (ball x r) := hj x hx hxsupport
      _ = (μf j : Measure (Ambient d)).real (ball x r) := heq.symm
      _ ≤ _ := measureReal_mono hsub
  exact (not_lt_of_ge hmassge) hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedBoxHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection-height control on bounded boxes

Convergence to a coordinate-plane measure, together with local lower mass bounds, forces
the restricted measures into arbitrarily thin tubes about the coordinate plane. The height
estimate is stated almost everywhere for the bounded projection measures used in boxwise
kernel comparisons.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem eventual_lower_ball_mass_of_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, ∀ x ∈ (μ j).support, c ≤ (μ j).real (ball x r) := by
  have hc : 0 < r ^ n / C := div_pos (pow_pos hr n) hC
  refine ⟨r ^ n / C, hc, ?_⟩
  filter_upwards [hdiam r hr] with j hj
  intro x hx
  have hfinite : (μ j) (ball x r) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top)
  have h := ENNReal.toReal_mono hfinite (hlower j x hx r ⟨hr, hj⟩)
  simpa only [ENNReal.toReal_ofReal hc.le, Measure.real] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ball-mass bounds through compact test functions

Compactly supported continuous cutoffs compare test integrals with ball masses from above
and below. These comparisons pass uniform growth bounds through convergence against
compact test functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem ball_mass_le_compact_test_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (r : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hone : ∀ x ∈ ball a r, f x = 1) :
    μ.real (ball a r) ≤ ∫ x, f x ∂μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  have hi : Integrable ((ball a r).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono hi (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (fun x => by
      by_cases hx : x ∈ ball a r
      · simpa only [indicator_of_mem hx] using! (hone x hx).ge
      · simpa only [indicator_of_notMem hx] using! hf x)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_nearby_support {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ y, y ∈ (μ j).support ∧ y ∈ ball x r := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hmass : 0 < ν.real (ball x (r / 2)) := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((ν.mem_support_iff_forall x).mp hx (ball x (r / 2))
        (ball_mem_nhds x (by positivity)))
    · exact ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall x (r / 2)).measure_lt_top).ne
  have hpos : 0 < ∫ y, F y ∂ν := hmass.trans_le
    (ball_mass_le_compact_test_integral ν F x (r / 2) (fun y => (hbounds y).1)
      (fun _ hy => hone (ball_subset_closedBall hy)))
  filter_upwards [(hlocal F).eventually (lt_mem_nhds hpos)] with j hj
  by_contra hnone
  have hzeroae : ∀ᵐ y ∂μ j, F y = 0 := by
    filter_upwards [(μ j).support_mem_ae] with y hy
    exact hzero (show y ∈ (ball x r)ᶜ from fun hball => hnone ⟨y, hy, hball⟩)
  have heq : (∫ y, F y ∂μ j) = 0 := integral_eq_zero_of_ae hzeroae
  rw [heq] at hj
  exact (lt_irrefl 0) hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalExcessSequenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vanishing normalized excess for the original sequence

Dyadic excess bounds yield fixed-plane source moments after a finite index shift.
Applying the source-excess limit theorem to that tail, then restoring the shift,
produces a strictly increasing subsequence with vanishing normalized excess at
every nonnegative radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_original_excess_sequence_limit {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (hδpos : ∀ j, 0 < δ j)
    (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb1 : 1 < b) (hb2 : b < 2)
    (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j →
      squaredExcess (p + 1) (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0) := by
  obtain ⟨J, M, _hM, S, hS, hmoment⟩ := exists_shifted_fixed_plane_source_moments hnd
    μ C G hC hg (fun j r hr => hlower j 0 (hzero j) r hr)
    δ hδpos T horizon b hb1 hsmall hexcess
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  have hdiam := support_diameters_grow_of_admissible_dyadic_horizon μ T hT horizon
  obtain ⟨ρ, hρ, hlim⟩ := exists_dyadic_source_excess_limit (fun j => μ (j + J)) C G hC
    (fun j => hg (j + J)) (fun j => hlower (j + J))
    (fun r hr => hshift.eventually (hdiam r hr)) (fun j => hzero (j + J)) S hS
    (fun j => δ (j + J)) (fun j => T (j + J)) (hδ.comp hshift) (hT.comp hshift)
    M b hmoment (fun j => A (j + J)) (hA.comp hshift) (fun j => hosc (j + J))
    D (fun j => hB (j + J)) (fun j => hδpos (j + J)) hb1.le hb2 (hlast.comp hshift)
  refine ⟨fun j => ρ j + J, ?_, hlim⟩
  intro i j hij
  exact Nat.add_lt_add_right (hρ hij) J

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactReverseSupportTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_compact_reverse_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (K : Set (Ambient d)) (hK : IsCompact K)
    (hsub : K ⊆ ν.support) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ K, infDist x (μ j).support < ε := by
  classical
  have hh : 0 < ε / 2 := half_pos hε
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun y : K => ball (y : Ambient d) (ε / 2))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hh⟩)
  have hnear : ∀ᶠ j in atTop, ∀ y ∈ s,
      ∃ z, z ∈ (μ j).support ∧ z ∈ ball (y : Ambient d) (ε / 2) := by
    apply (Filter.eventually_all_finset s).mpr
    intro y _hy
    exact compactTestConvergence_nearby_support μ ν hlocal y (hsub y.property) (ε / 2) hh
  filter_upwards [hnear] with j hj
  intro x hx
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
  obtain ⟨z, hz, hzy⟩ := hj y hys
  have hdist : dist x z < ε := by
    have h1 : dist x (y : Ambient d) < ε / 2 := hxy
    have h2 : dist (y : Ambient d) z < ε / 2 := by simpa only [dist_comm] using! hzy
    exact (dist_triangle x (y : Ambient d) z).trans_lt (by linarith)
  exact (infDist_le_dist_of_mem hz).trans_lt hdist

theorem compactTestConvergence_reverse_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε := by
  have hK : IsCompact (ν.support ∩ closedBall a R) :=
    (isCompact_closedBall a R).inter_left ν.isClosed_support
  filter_upwards [compactTestConvergence_compact_reverse_support_tube μ ν hlocal
    (ν.support ∩ closedBall a R) hK inter_subset_left ε hε] with j hj
  intro x hx hs
  exact hj x ⟨hs, ball_subset_closedBall hx⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BilateralSupportConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_support_tube_of_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε := by
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam
    (ε / 2) (half_pos hε)
  have hzero : ∀ᵐ x ∂ν, infDist x ν.support = 0 := by
    filter_upwards [ν.support_mem_ae] with x hx
    exact infDist_zero_of_mem hx
  apply compactTestConvergence_support_tube μ ν hlocal (fun x => infDist x ν.support)
    1 (lipschitz_infDist_pt ν.support) hzero a R ε (ε / 2) c hε hc (by simp)
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

theorem compactTestConvergence_bilateral_support_tubes {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε) ∧
      (∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε) :=
  (compactTestConvergence_support_tube_of_AD_lower n μ ν hlocal C hC hlower hdiam a R ε hε).and
    (compactTestConvergence_reverse_support_tube μ ν hlocal a R ε hε)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BilateralFlatLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem isAffineNPlane_isometric_range {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d) :
    IsAffineNPlane n L.toLinearMap.range.toAffineSubspace := by
  refine ⟨⟨0, L.toLinearMap.range.zero_mem⟩, ?_⟩
  rw [Submodule.toAffineSubspace_direction, LinearMap.finrank_range_of_inj L.injective]
  exact finrank_euclideanSpace_fin

theorem compactTestConvergence_bilateralBeta_tendsto_zero {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hsupport : ν.support = (S : Set (Ambient d))) (a : Ambient d) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun j => bilateralBeta n (μ j) a r) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro t ht
    exact Eventually.of_forall fun j => ht.trans_le (bilateralBeta_nonneg n (μ j) a r hr.le)
  · intro ε hε
    filter_upwards [compactTestConvergence_bilateral_support_tubes n μ ν hlocal C hC
      hlower hdiam a r (ε * r / 4) (by positivity)] with j hj
    exact bilateralBeta_lt_of_support_tubes n (μ j) a r ε hr hε S hS
      (by simpa only [hsupport] using! hj.1) (by simpa only [hsupport] using! hj.2)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalBilateralSequenceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bilateral flatness along a subsequence

Vanishing dyadic excess and scalar oscillation yield a planar weak limit after
shifting and extracting a subsequence. Lower mass bounds then turn this planar
limit into convergence of the original measures' bilateral beta numbers at every
fixed positive radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_original_bilateral_sequence_limit {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (hδpos : ∀ j, 0 < δ j) (horizon : ∀ j, AdmissibleRadius (μ j) ((2 : ℝ) ^ T j))
    (b : ℝ) (hb : 1 < b) (hsmall : Tendsto (fun j => δ j * b ^ T j) atTop (𝓝 0))
    (hexcess : ∀ j l, l ≤ T j →
      squaredExcess (p + 1) (μ j) 0 ((2 : ℝ) ^ l) ≤ (δ j * b ^ l) ^ 2)
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 < r →
      Tendsto (fun j => bilateralBeta (p + 1) (μ (ρ j)) 0 r) atTop (𝓝 0) := by
  obtain ⟨J, M, _, S, hS, hmoment⟩ := exists_shifted_fixed_plane_source_moments hnd
    μ C G hC hg (fun j r hr => hlower j 0 (hzero j) r hr)
    δ hδpos T horizon b hb hsmall hexcess
  have hshift : Tendsto (fun j : ℕ => j + J) atTop atTop := tendsto_add_atTop_nat J
  have hdiam := support_diameters_grow_of_admissible_dyadic_horizon μ T hT horizon
  have hv : Tendsto (fun j => δ (j + J) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0)] using! (hδ.comp hshift).pow 3
  obtain ⟨ρ, hρ, ν, _, _, _, Llim, hfinite, _, hweak, _, _, hsupport, _⟩ :=
    exists_dyadic_full_planar_measure_limit (fun j => μ (j + J)) C G hC
      (fun j => hg (j + J)) (fun j => hlower (j + J))
      (fun r hr => hshift.eventually (hdiam r hr)) (fun j => hzero (j + J)) S hS
      (fun j => δ (j + J)) (fun j => T (j + J)) (hδ.comp hshift) (hT.comp hshift)
      M b hmoment (fun j => A (j + J)) (fun j => δ (j + J) ^ 3)
      (hA.comp hshift) hv (fun j => hosc (j + J))
  let : IsFiniteMeasureOnCompacts ν := hfinite
  refine ⟨fun j => ρ j + J, (fun _ _ hij => Nat.add_lt_add_right (hρ hij) J), ?_⟩
  intro r hr
  exact compactTestConvergence_bilateralBeta_tendsto_zero (p + 1) (fun j => μ (ρ j + J)) ν
    hweak C hC (fun j => hlower (ρ j + J))
    (fun s hs => hρ.tendsto_atTop.eventually (hshift.eventually (hdiam s hs)))
    Llim.toLinearMap.range.toAffineSubspace (isAffineNPlane_isometric_range Llim) hsupport 0 r hr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_UniformBilateralExcessPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bilateral excess propagation

The conclusion combines a squared-excess estimate with bilateral beta smallness.
A contradiction sequence first yields bilateral convergence and then a further
subsequence with vanishing normalized excess, producing one propagation index
that works uniformly for all measures satisfying the stated bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_uniform_bilateral_excess_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      IsFiniteMeasureOnCompacts μ → GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      (0 : Ambient d) ∈ μ.support →
      AdmissibleRadius μ ((2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ 0 ((2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      ScalarOscillationBound (p + 1) μ 0 (propagationTestRadius J) (propagationScale J ^ 3) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ExcessBilateralConclusion (p + 1) μ r (propagationScale J) ε := by
  classical
  by_contra h
  push Not at h
  have hbad (j : ℕ) := h (j + J₀) (by omega)
  choose μ hfinite hg hlower hzero horizon hexcess hosc hB hfail using hbad
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := hfinite j
  have hshift : Tendsto (fun j : ℕ => j + J₀) atTop atTop := tendsto_add_atTop_nat J₀
  obtain ⟨ρ, hρ, hbilateral⟩ := exists_original_bilateral_sequence_limit hnd μ C G hC hg hlower hzero
    (fun j => propagationScale (j + J₀)) (fun j => propagationHorizon (j + J₀))
    (propagationScale_tendsto_zero.comp hshift) (propagationHorizon_tendsto_atTop.comp hshift)
    (fun j => propagationScale_pos (j + J₀)) horizon b hb1
    ((propagation_horizon_product_tendsto_zero b hb2).comp hshift) hexcess
    (fun j => propagationTestRadius (j + J₀)) (propagationTestRadius_tendsto_atTop.comp hshift) hosc
  have hindices : Tendsto (fun j => ρ j + J₀) atTop atTop := hshift.comp hρ.tendsto_atTop
  obtain ⟨τ, hτ, hlim⟩ := exists_original_excess_sequence_limit hnd (fun j => μ (ρ j)) C G hC
    (fun j => hg (ρ j)) (fun j => hlower (ρ j)) (fun j => hzero (ρ j))
    (fun j => propagationScale (ρ j + J₀)) (fun j => propagationHorizon (ρ j + J₀))
    (propagationScale_tendsto_zero.comp hindices) (propagationHorizon_tendsto_atTop.comp hindices)
    (fun j => propagationScale_pos (ρ j + J₀)) (fun j => horizon (ρ j)) b hb1 (by nlinarith)
    ((propagation_horizon_product_tendsto_zero b hb2).comp hindices) (fun j => hexcess (ρ j))
    (fun j => propagationTestRadius (ρ j + J₀)) (propagationTestRadius_tendsto_atTop.comp hindices)
    (fun j => hosc (ρ j)) D (fun j => hB (ρ j))
    (propagation_last_error_tendsto_zero.comp hindices)
  have he := (hlim r hr.le).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hb := ((hbilateral r hr).comp hτ.tendsto_atTop).eventually (gt_mem_nhds hε)
  obtain ⟨j, hj, hjb⟩ := (he.and hb).exists
  apply hfail (ρ (τ j))
  refine ⟨?_, hjb⟩
  have heq := (div_lt_iff₀ (sq_pos_of_pos (propagationScale_pos (ρ (τ j) + J₀)))).mp hj
  simpa only [one_mul] using! heq.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ScaleInvariantExcessPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scale-invariant bilateral excess propagation

Blowing up at a support point and a positive radius reduces excess propagation to its
normalized form. Growth, admissibility, oscillation, and the uniform Riesz bound transfer to
the blowup, while excess and bilateral beta transform back to the original scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_scale_invariant_bilateral_excess_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      ScalarOscillationBound (p + 1) μ a (r * propagationTestRadius J)
        (r ^ (p + 2) * propagationScale J ^ 3) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      squaredExcess (p + 1) μ a (r * R) ≤ propagationScale J ^ 2 ∧
        bilateralBeta (p + 1) μ a (r * R) < ε := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_uniform_bilateral_excess_propagation hnd C G hC b hb1 hb2
    D R ε hR hε J₀
  refine ⟨J, hJ₀, ?_⟩
  intro μ hg hlower a ha r hr horizon hexcess hosc hB
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let ν := blowupMeasure (p + 1) μ a r
  have hνg : GlobalUpperGrowth (p + 1) G ν := blowupMeasure_growth (p + 1) μ a r G hr hg
  let : IsFiniteMeasureOnCompacts ν := globalGrowth_finite_on_compacts G ν hνg
  have hνlower := blowupMeasure_lower_admissible (p + 1) μ a r C hr hlower
  have hνzero := blowupMeasure_origin_mem_support (p + 1) μ a r hr ha
  have hνhorizon := (blowupMeasure_admissibleRadius_iff (p + 1) μ a r
    ((2 : ℝ) ^ propagationHorizon J) hr).mpr horizon
  have hνexcess : ∀ l ≤ propagationHorizon J,
      squaredExcess (p + 1) ν 0 ((2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2 := by
    intro l hl
    rw [squaredExcess_blowup (p + 1) μ a r _ hr]
    exact hexcess l hl
  have hνosc := hosc.blowup (p + 1) μ a r (propagationTestRadius J) (propagationScale J ^ 3) hr
  have hνB := uniform_riesz_bound_blowup (p + 1) μ a r hr D hB
  have hresult := hJ ν inferInstance hνg hνlower hνzero hνhorizon hνexcess hνosc hνB
  change squaredExcess (p + 1) (blowupMeasure (p + 1) μ a r) 0 R ≤ propagationScale J ^ 2 ∧
    bilateralBeta (p + 1) (blowupMeasure (p + 1) μ a r) 0 R < ε at hresult
  rwa [squaredExcess_blowup (p + 1) μ a r R hr, bilateralBeta_blowup (p + 1) μ a r R hr] at hresult

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicPropagationRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic descendant radii

The radius at depth `j` is the original radius divided by `2 ^ j`. Rescaling by
another dyadic power either returns to a shallower descendant or passes to a
larger original scale. Positivity and the support-diameter bound ensure that an
admissible dyadic horizon remains admissible for every descendant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem descendantRadius_pos (r : ℝ) (hr : 0 < r) (j : ℕ) : 0 < descendantRadius r j := by
  unfold descendantRadius
  positivity

theorem descendantRadius_zero (r : ℝ) : descendantRadius r 0 = r := by
  simp [descendantRadius]

theorem descendantRadius_half (r : ℝ) (j : ℕ) :
    descendantRadius r j * (1 / 2 : ℝ) = descendantRadius r (j + 1) := by
  simp only [descendantRadius, pow_succ]
  ring

theorem descendantRadius_mul_dyadic_small (r : ℝ) (j l : ℕ) (hl : l ≤ j) :
    descendantRadius r j * (2 : ℝ) ^ l = descendantRadius r (j - l) := by
  have hp : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - l) * (2 : ℝ) ^ l := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  simp only [descendantRadius, hp]
  field_simp

theorem descendantRadius_mul_dyadic_large (r : ℝ) (j l : ℕ) (hl : j ≤ l) :
    descendantRadius r j * (2 : ℝ) ^ l = r * (2 : ℝ) ^ (l - j) := by
  have hp : (2 : ℝ) ^ l = (2 : ℝ) ^ j * (2 : ℝ) ^ (l - j) := by
    rw [← pow_add, Nat.add_sub_of_le hl]
  simp only [descendantRadius, hp]
  field_simp

theorem descendantRadius_admissible_horizon {d : ℕ} (μ : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (j K : ℕ) (h : AdmissibleRadius μ (r * (2 : ℝ) ^ K)) :
    AdmissibleRadius μ (descendantRadius r j * (2 : ℝ) ^ K) := by
  have hpow : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hle : descendantRadius r j ≤ r := by
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).mpr
      (le_mul_of_one_le_right hr.le hpow)
  refine ⟨mul_pos (descendantRadius_pos r hr j) (by positivity), ?_⟩
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))).trans h.2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicChainPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform propagation along dyadic descendant chains

A single propagation scale, chosen before the measure, controls squared excess
throughout a finite descendant chain. Scalar oscillation bounds at its preceding
scales also give bilateral flatness at every positive descendant depth.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_dyadic_chain_propagation_oai {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ,
      (∀ j < L, ScalarOscillationBound (p + 1) μ a
        (descendantRadius r j * propagationTestRadius J)
        (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
      ∀ j ≤ L,
        squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
        (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε) := by
  obtain ⟨J, hJ₀, hJ⟩ := exists_scale_invariant_bilateral_excess_propagation hnd C G hC b hb1 hb2
    D (1 / 2) ε (by norm_num) hε J₀
  refine ⟨J, hJ₀, ?_⟩
  intro μ hg hlower a ha r hr horizon hinit hB L hosc j
  have hweight (i l : ℕ) (hil : i ≤ l) :
      (propagationScale J * b ^ i) ^ 2 ≤ (propagationScale J * b ^ l) ^ 2 := by
    apply pow_le_pow_left₀ (mul_nonneg (propagationScale_pos J).le
      (pow_nonneg (zero_lt_one.trans hb1).le i))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1.le hil) (propagationScale_pos J).le
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hjL
    cases j with
    | zero =>
      refine ⟨?_, by omega⟩
      simpa only [descendantRadius_zero, pow_zero, mul_one] using! hinit 0 (by omega)
    | succ k =>
      have hkL : k < L := by omega
      have hlocal : ∀ l ≤ propagationHorizon J,
          squaredExcess (p + 1) μ a (descendantRadius r k * (2 : ℝ) ^ l) ≤
            (propagationScale J * b ^ l) ^ 2 := by
        intro l hl
        by_cases hlk : l ≤ k
        · rw [descendantRadius_mul_dyadic_small r k l hlk]
          have hprev := (ih (k - l) (by omega) (by omega)).1
          have hw := hweight 0 l (by omega)
          simp only [pow_zero, mul_one] at hw
          exact hprev.trans hw
        · rw [descendantRadius_mul_dyadic_large r k l (by omega)]
          exact (hinit (l - k) (by omega)).trans (hweight (l - k) l (Nat.sub_le l k))
      have hout := hJ μ hg hlower a ha (descendantRadius r k) (descendantRadius_pos r hr k)
        (descendantRadius_admissible_horizon μ r hr k (propagationHorizon J) horizon)
        hlocal (hosc k hkL) hB
      rw [descendantRadius_half] at hout
      exact ⟨hout.1, fun _ => hout.2⟩

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation_oai := @OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation_oai
