-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:18.628038+00:00
-- url     : https://prove2.me/submissions/c9262116-01f1-4cfb-adfb-86ff979fc059

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

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

theorem blowupMeasure_lower_global {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r C : ℝ) (hr : 0 < r)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R)) :
    ∀ x ∈ (blowupMeasure n μ a r).support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ blowupMeasure n μ a r (ball x R) := by
  intro x hx R hR
  rw [blowupMeasure_ball n μ a x r R hr]
  have h := hlower (a + r • x) ((blowupMeasure_support_iff n μ a x r hr).mp hx)
    (r * R) (by positivity)
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

theorem compact_test_integral_le_ball_mass {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (R : ℝ)
    (hf : ∀ x, f x ≤ 1) (hz : ∀ x, x ∉ ball a R → f x = 0) :
    (∫ x, f x ∂μ) ≤ μ.real (ball a R) := by
  have : IsFiniteMeasure (μ.restrict (ball a R)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top).ne
  have hi : Integrable ((ball a R).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hi
    (fun x => by
      by_cases hx : x ∈ ball a R
      · simpa only [indicator_of_mem hx] using! hf x
      · simpa only [indicator_of_notMem hx] using! (hz x hx).le)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

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

theorem compactTestConvergence_upper_growth {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) :
    GlobalUpperGrowth n (C * 2 ^ n) ν := by
  have hC : 0 ≤ C := (hg 0).1
  refine ⟨mul_nonneg hC (by positivity), ?_⟩
  intro a r hr
  have hsub : closedBall a r ⊆ ball a (2 * r) := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall a r) isOpen_ball.isClosed_compl (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hfi : ∀ j, (∫ x, F x ∂μ j) ≤ C * (2 * r) ^ n := by
    intro j
    apply (compact_test_integral_le_ball_mass (μ j) F a (2 * r)
      (fun x => (hbounds x).2) (fun x hx => hzero hx)).trans
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (by positivity))
      ((hg j).2 a (2 * r) (by positivity))
  have hlim : (∫ x, F x ∂ν) ≤ C * (2 * r) ^ n :=
    le_of_tendsto (hlocal F) (Eventually.of_forall hfi)
  have hball : ν.real (ball a r) ≤ C * (2 * r) ^ n :=
    (ball_mass_le_compact_test_integral ν F a r (fun x => (hbounds x).1)
      (fun _ hx => hone (ball_subset_closedBall hx))).trans hlim
  have hfinite : ν (ball a r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mpr
  simpa only [mul_pow, mul_assoc] using! hball

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

theorem compactTestConvergence_support_zero_of_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → q x < ε) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  by_contra hne
  have hpos : 0 < q x := lt_of_le_of_ne (hqnn x) (Ne.symm hne)
  let ε := q x / 2
  have hε : 0 < ε := by dsimp only [ε] <;> positivity
  have hnhds : {y | ε < q y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const hq).mem_nhds (show ε < q x by dsimp only [ε] <;> linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hR : 0 < ‖x‖ + r := by linarith [norm_nonneg x]
  obtain ⟨j, hjnear, hjtube⟩ := ((compactTestConvergence_nearby_support μ ν hlocal x hx r hr).and
    (htube (‖x‖ + r) ε hR hε)).exists
  obtain ⟨y, hysupport, hyball⟩ := hjnear
  have hy0 : y ∈ ball (0 : Ambient d) (‖x‖ + r) := by
    have htri := dist_triangle y x (0 : Ambient d)
    have hyr : dist y x < r := hyball
    simp only [mem_ball, dist_zero_right] at htri ⊢
    linarith
  exact (not_lt_of_ge (hball hyball).le) (hjtube y hy0 hysupport)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitLowerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_lower_ball_mass {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r b : ℝ) (hr : 0 < r)
    (hlower : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support, b ≤ (μ j).real (ball y (r / 4))) :
    b ≤ ν.real (ball x r) := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hbound : ∀ᶠ j in atTop, b ≤ ∫ z, F z ∂μ j := by
    filter_upwards [hlower, compactTestConvergence_nearby_support μ ν hlocal x hx
      (r / 4) (by positivity)] with j hj hnear
    obtain ⟨y, hysupp, hyball⟩ := hnear
    apply (hj y hysupp).trans
    apply ball_mass_le_compact_test_integral (μ j) F y (r / 4) (fun z => (hbounds z).1)
    intro z hz
    apply hone
    have htri := dist_triangle z y x
    have hzy : dist z y < r / 4 := hz
    have hyx : dist y x < r / 4 := hyball
    exact mem_closedBall.mpr (by linarith)
  have hlimit : b ≤ ∫ z, F z ∂ν := ge_of_tendsto (hlocal F) hbound
  exact hlimit.trans (compact_test_integral_le_ball_mass ν F x r
    (fun z => (hbounds z).2) (fun _ hz => hzero hz))

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_mem_support_of_ball_masses {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d)
    (hmass : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, c ≤ (μ j).real (ball x r)) : x ∈ ν.support := by
  have hball : ∀ r : ℝ, 0 < r → 0 < ν (ball x r) := by
    intro r hr
    have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
    obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
        (disjoint_compl_right_iff_subset.mpr hsub)
    let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
    obtain ⟨c, hc, hmassc⟩ := hmass (r / 2) (by positivity)
    have hbound : ∀ᶠ j in atTop, c ≤ ∫ y, F y ∂μ j := by
      filter_upwards [hmassc] with j hj
      exact hj.trans (ball_mass_le_compact_test_integral (μ j) F x (r / 2)
        (fun y => (hbounds y).1) (fun _ hy => hone (ball_subset_closedBall hy)))
    have hlimit : c ≤ ∫ y, F y ∂ν := ge_of_tendsto (hlocal F) hbound
    have hpos : 0 < ν.real (ball x r) := hc.trans_le (hlimit.trans
      (compact_test_integral_le_ball_mass ν F x r (fun y => (hbounds y).2) (fun _ hy => hzero hy)))
    exact (ENNReal.toReal_pos_iff.mp hpos).1
  apply (ν.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  exact (hball r hr).trans_le (measure_mono hsub)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedLowerGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem CappedLowerGrowth.real_bound {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (hC : 0 < C) (hlower : CappedLowerGrowth n C H μ)
    (x : Ambient d) (hx : x ∈ μ.support) (r : ℝ) (hr : 0 < r) (hrH : r ≤ H) :
    r ^ n / C ≤ μ.real (ball x r) := by
  have hfinite : μ (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  have h := ENNReal.toReal_mono hfinite (hlower x hx r hr hrH)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ n / C)] using! h

theorem CappedLowerGrowth.blowup {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    CappedLowerGrowth n C (H / s) (blowupMeasure n μ a s) := by
  intro x hx R hR hRH
  rw [blowupMeasure_ball n μ a x s R hs]
  have hscaled : s * R ≤ H := by
    have h := (le_div_iff₀ hs).mp hRH
    simpa only [mul_comm] using! h
  have hl := hlower (a + s • x) ((blowupMeasure_support_iff n μ a x s hs).mp hx)
    (s * R) (mul_pos hs hR) hscaled
  calc
    _ = ENNReal.ofReal ((s ^ n)⁻¹) * ENNReal.ofReal ((s * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (s ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right hl _

theorem CappedLowerGrowth.compact_limit {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) : CappedLowerGrowth n (C * 4 ^ n) H ν := by
  intro x hx r hr hrH
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by rw [div_pow]; ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    apply Eventually.of_forall
    intro j y hy
    rw [← heq]
    exact CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) y hy (r / 4)
      (by positivity) (by linarith)
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

theorem CappedLowerGrowth.limit_origin {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hH : 0 < H) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    (0 : Ambient d) ∈ ν.support := by
  apply compactTestConvergence_mem_support_of_ball_masses μ ν hlocal 0
  intro r hr
  let t := min r H
  have ht : 0 < t := lt_min hr hH
  refine ⟨t ^ n / C, by positivity, Eventually.of_forall fun j => ?_⟩
  have hl := CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) 0 (hzero j) t ht (min_le_right _ _)
  apply hl.trans
  exact ENNReal.toReal_mono
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) r).measure_lt_top).ne
    (measure_mono (ball_subset_ball (min_le_left r H)))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_exterior_integral_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (x : Ambient d) (r : ℝ) (hr : 0 < r) :
    (∫ y in {y | r < dist x y}, inverseDistancePow (m + 1) x y ∂μ) ≤ 2 * (C * 2 ^ m / r) := by
  have hgeo : Summable (fun k : ℕ => (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun k : ℕ =>
      ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
      (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k) hgeo
  have hiu : IntegrableOn (inverseDistancePow (m + 1) x) (⋃ k, dyadicAnnulus x r k) μ :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun k => inverseDistancePow_integrableOn_annulus m (m + 1) C μ hg x r hr k) hs
  have hsub := exterior_subset_iUnion_dyadicAnnulus x r hr
  calc
    _ ≤ ∫ y in ⋃ k, dyadicAnnulus x r k, inverseDistancePow (m + 1) x y ∂μ :=
      setIntegral_mono_set hiu (Filter.Eventually.of_forall fun y => inverseDistancePow_nonneg _ _ _)
        (Filter.Eventually.of_forall fun y hy => hsub hy)
    _ = ∑' k, ∫ y in dyadicAnnulus x r k, ‖inverseDistancePow (m + 1) x y‖ ∂μ := by
      rw [integral_iUnion (dyadicAnnulus_measurable x r) (dyadicAnnulus_disjoint x r hr) hiu]
      simp only [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)]
    _ ≤ ∑' k : ℕ, (C * 2 ^ m / r) * (1 / 2 : ℝ) ^ k :=
      Summable.tsum_le_tsum (fun k => inverseDistancePow_annular_integral_bound m C μ hg x r hr k)
        hs hgeo
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      norm_num
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of the compactness weight

Local finiteness controls the weight on closed balls, while polynomial upper growth controls
its exterior integral. Together these give global integrability and a quantitative mass bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeight_exterior_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R : ℝ) (hR : 0 < R) :
    (∫ x in {x | R < dist (0 : Ambient d) x}, compactnessWeight n x ∂μ) ≤
      2 * (C * 2 ^ n / R) := by
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  apply le_trans _ (inverseDistancePow_exterior_integral_bound n C μ hg 0 R hR)
  apply integral_mono_ae (compactnessWeight_integrableOn_exterior n μ C hg R hR)
    (inverseDistancePow_integrableOn_exterior n C μ hg 0 R hR)
  filter_upwards [ae_restrict_mem (μ := μ) hs] with x hx
  exact compactnessWeight_le_inverseDistance n x (dist_pos.mp (hR.trans hx)).symm

theorem compactnessWeight_integral_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    (∫ x, compactnessWeight n x ∂μ) ≤ 3 * C * 2 ^ n := by
  have hglobal := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top)
  have hm : μ.real (closedBall (0 : Ambient d) 1) ≤ C * 2 ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
      ((measure_mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))).trans
        (hg.2 0 2 (by norm_num)))
  have hi : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤ C * 2 ^ n := by
    have h := integral_mono (μ := μ.restrict (closedBall (0 : Ambient d) 1))
      hglobal.integrableOn (integrable_const (1 : ℝ))
      (compactnessWeight_le_one n)
    have h' : (∫ x in closedBall (0 : Ambient d) 1, compactnessWeight n x ∂μ) ≤
        μ.real (closedBall (0 : Ambient d) 1) := by
      simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_one] using! h
    exact h'.trans hm
  have heq : (closedBall (0 : Ambient d) 1)ᶜ = {x | (1 : ℝ) < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  rw [← integral_add_compl (s := closedBall (0 : Ambient d) 1) measurableSet_closedBall hglobal, heq]
  calc
    _ ≤ C * 2 ^ n + 2 * (C * 2 ^ n / 1) :=
      add_le_add hi (compactnessWeight_exterior_integral_bound n μ C hg 1 zero_lt_one)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessWeightedMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite measures obtained from the compactness weight

The positive decaying compactness weight turns a globally growing measure into a finite
measure. Integral formulas give quantitative tail control and transfer a lower mass bound
on the unit ball to a lower bound for the weighted total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal

theorem compactnessWeightedMeasure_real {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    {s : Set (Ambient d)} (hs : MeasurableSet s)
    (hi : IntegrableOn (compactnessWeight n) s μ) :
    (compactnessWeightedMeasure n μ).real s = ∫ x in s, compactnessWeight n x ∂μ := by
  rw [Measure.real, compactnessWeightedMeasure_apply n μ hs hi,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (compactnessWeight_pos n x).le))]

theorem compactnessFiniteMeasure_mass_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) :
    ((compactnessFiniteMeasure n μ C hg).mass : ℝ) ≤ 3 * C * 2 ^ n := by
  change (compactnessWeightedMeasure n μ).real univ ≤ _
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_bound n μ C hg

theorem compactnessFiniteMeasure_tail_bound {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ) (R : ℝ) (hR : 0 < R) :
    ((compactnessFiniteMeasure n μ C hg) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      2 * (C * 2 ^ n / R) := by
  have heq : (closedBall (0 : Ambient d) R)ᶜ = {x | R < dist (0 : Ambient d) x} := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, not_le]
    rw [dist_comm]
  change (compactnessWeightedMeasure n μ).real (closedBall (0 : Ambient d) R)ᶜ ≤ _
  have hs : MeasurableSet {x | R < dist (0 : Ambient d) x} :=
    (isOpen_lt continuous_const (continuous_const.dist continuous_id)).measurableSet
  rw [heq, compactnessWeightedMeasure_real n μ hs
    (compactnessWeight_integrableOn_exterior n μ C hg R hR)]
  exact compactnessWeight_exterior_integral_bound n μ C hg R hR

theorem compactnessWeight_lower_on_unit_ball {d : ℕ} (n : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) 1) : (2 : ℝ)⁻¹ ^ (n + 1) ≤ compactnessWeight n x := by
  have hn : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using! hx
  have hpow : (1 + ‖x‖) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (n + 1)
  simpa only [compactnessWeight, one_div, inv_pow] using!
    one_div_le_one_div_of_le (by positivity : 0 < (1 + ‖x‖) ^ (n + 1)) hpow

theorem compactnessWeight_integral_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ∫ x, compactnessWeight n x ∂μ := by
  have hi := compactnessWeight_integrable n μ C hg
  have : IsFiniteMeasure (μ.restrict (ball (0 : Ambient d) 1)) :=
    isFiniteMeasure_restrict.mpr
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
  have hlocal : μ.real (ball (0 : Ambient d) 1) * (2 : ℝ)⁻¹ ^ (n + 1) ≤
      ∫ x in ball (0 : Ambient d) 1, compactnessWeight n x ∂μ := by
    have h := integral_mono_ae (μ := μ.restrict (ball (0 : Ambient d) 1))
      (integrable_const ((2 : ℝ)⁻¹ ^ (n + 1))) hi.integrableOn
      (by
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_ball] with x hx
        exact compactnessWeight_lower_on_unit_ball n x hx)
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using! h
  exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans
    (hlocal.trans (setIntegral_le_integral hi (Eventually.of_forall
      (fun x => (compactnessWeight_pos n x).le))))

theorem compactnessFiniteMeasure_mass_lower {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C c : ℝ) (hg : GlobalUpperGrowth n C μ)
    (hm : c ≤ μ.real (ball (0 : Ambient d) 1)) :
    c * (2 : ℝ)⁻¹ ^ (n + 1) ≤ ((compactnessFiniteMeasure n μ C hg).mass : ℝ) := by
  change _ ≤ (compactnessWeightedMeasure n μ).real univ
  rw [compactnessWeightedMeasure_real n μ MeasurableSet.univ
    (compactnessWeight_integrable n μ C hg).integrableOn, Measure.restrict_univ]
  exact compactnessWeight_integral_lower n μ C c hg hm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactnessUnweighting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactnessWeight_inv_continuous {d : ℕ} (n : ℕ) :
    Continuous (fun x : Ambient d => (compactnessWeight n x)⁻¹) :=
  (compactnessWeight_continuous n).inv₀ (fun x => ne_of_gt (compactnessWeight_pos n x))

theorem compactnessUnweightedMeasure_locally_finite {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (compactnessUnweightedMeasure n ν) := by
  constructor
  intro K hK
  have hi : IntegrableOn (fun x => (compactnessWeight n x)⁻¹) K ν :=
    ContinuousOn.integrableOn_compact hK (compactnessWeight_inv_continuous n).continuousOn
  rw [compactnessUnweightedMeasure, withDensity_apply _ hK.measurableSet,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x =>
      inv_nonneg.mpr (compactnessWeight_pos n x).le))]
  exact ENNReal.ofReal_lt_top

theorem compactness_unweight_weight {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) :
    compactnessUnweightedMeasure n (compactnessWeightedMeasure n μ) = μ := by
  rw [compactnessUnweightedMeasure, compactnessWeightedMeasure,
    ← withDensity_mul μ (compactnessWeight_continuous n).measurable.ennreal_ofReal
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal]
  have heq : (fun x : Ambient d => ENNReal.ofReal (compactnessWeight n x)) *
      (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) = 1 := by
    funext x
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (compactnessWeight_pos n x).le,
      mul_inv_cancel₀ (ne_of_gt (compactnessWeight_pos n x)), ENNReal.ofReal_one, Pi.one_apply]
  rw [heq, withDensity_one]

theorem compactnessUnweightedMeasure_integral {d : ℕ} (n : ℕ)
    (ν : Measure (Ambient d)) (f : Ambient d → ℝ) :
    (∫ x, f x ∂compactnessUnweightedMeasure n ν) =
      ∫ x, (compactnessWeight n x)⁻¹ * f x ∂ν := by
  rw [compactnessUnweightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (compactnessWeight_inv_continuous n).measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change (ENNReal.ofReal ((compactnessWeight n x)⁻¹)).toReal • f x =
      (compactnessWeight n x)⁻¹ * f x
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (compactnessWeight_pos n x).le), smul_eq_mul])

theorem compactness_unweight_weak_convergence {d : ℕ} (n : ℕ)
    (νj : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto νj atTop (𝓝 ν)) :
    CompactTestConvergence (fun j => compactnessUnweightedMeasure n (νj j : Measure (Ambient d)))
      (compactnessUnweightedMeasure n (ν : Measure (Ambient d))) := by
  intro f
  let test : C_c(Ambient d, ℝ) :=
    ⟨⟨fun x => (compactnessWeight n x)⁻¹ * f x,
      (compactnessWeight_inv_continuous n).mul f.continuous⟩, f.hasCompactSupport.mul_left⟩
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν test.toBoundedContinuousFunction
  change Tendsto (fun j => ∫ x, (compactnessWeight n x)⁻¹ * f x ∂(νj j : Measure (Ambient d)))
    atTop (𝓝 (∫ x, (compactnessWeight n x)⁻¹ * f x ∂(ν : Measure (Ambient d)))) at h
  simpa only [compactnessUnweightedMeasure_integral] using! h

theorem compactness_weighted_limit_gives_original_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) (ν : FiniteMeasure (Ambient d))
    (hν : Tendsto (fun j => compactnessFiniteMeasure n (μ j) C (hg j)) atTop (𝓝 ν)) :
    CompactTestConvergence μ (compactnessUnweightedMeasure n ν) := by
  have h := compactness_unweight_weak_convergence n _ ν hν
  simpa only [compactnessFiniteMeasure, FiniteMeasure.toMeasure_mk, compactness_unweight_weight] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FiniteMeasureSequentialCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sequential compactness of finite measures

Normalization converts uniform tail estimates and a positive mass lower bound into
tightness of probability measures. A further subsequence of the masses recovers a
finite-measure limit while preserving the uniform mass bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

theorem finiteMeasure_normalize_set_bound {d : ℕ} (μ : FiniteMeasure (Ambient d))
    (a b : ℝ) (ha : 0 < a) (hm : a ≤ (μ.mass : ℝ))
    (s : Set (Ambient d)) (hs : (μ s : ℝ) ≤ b) : (μ.normalize s : ℝ) ≤ b / a := by
  have heq : (μ s : ℝ) = (μ.mass : ℝ) * (μ.normalize s : ℝ) := by
    exact_mod_cast μ.self_eq_mass_mul_normalize s
  apply (le_div_iff₀ ha).mpr
  calc
    (μ.normalize s : ℝ) * a ≤ (μ.normalize s : ℝ) * (μ.mass : ℝ) :=
      mul_le_mul_of_nonneg_left hm (μ.normalize s).coe_nonneg
    _ = (μ s : ℝ) := by linarith only [heq]
    _ ≤ b := hs

theorem exists_normalized_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ))
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ P : ProbabilityMeasure (Ambient d),
      Tendsto (fun j => (μ (ρ j)).normalize) atTop (𝓝 P) := by
  let u : ℕ → ℝ≥0 := fun k => Real.toNNReal (B / a) * (1 / 2) ^ k
  let K : ℕ → Set (Ambient d) := fun k => closedBall 0 ((2 : ℝ) ^ k)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u, mul_zero] using!
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1)).const_mul
        (Real.toNNReal (B / a))
  have hc : IsCompact {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le hu
      (fun k => isCompact_closedBall 0 _) (Or.inl inferInstance)
  have hin : ∀ j, (μ j).normalize ∈ {P : ProbabilityMeasure (Ambient d) | ∀ k, P (K k)ᶜ ≤ u k} := by
    intro j k
    have hreal : ((μ j).normalize (K k)ᶜ : ℝ) ≤ (u k : ℝ) := by
      calc
        _ ≤ (B / (2 : ℝ) ^ k) / a := finiteMeasure_normalize_set_bound
          (μ j) a _ ha (hm j) (K k)ᶜ (ht j _ (by positivity))
        _ = (u k : ℝ) := by
          simp only [u, NNReal.coe_mul, Real.coe_toNNReal _ (div_nonneg hB ha.le), NNReal.coe_pow, NNReal.coe_div,
            NNReal.coe_one, NNReal.coe_ofNat, div_pow, one_pow]
          ring
    exact_mod_cast hreal
  obtain ⟨P, _hP, ρ, hρ, hlim⟩ := hc.tendsto_subseq hin
  exact ⟨ρ, hρ, P, hlim⟩

theorem exists_finite_measure_subsequence {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (a A B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hm : ∀ j, a ≤ ((μ j).mass : ℝ) ∧ ((μ j).mass : ℝ) ≤ A)
    (ht : ∀ j R, 0 < R → ((μ j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤ B / R) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : FiniteMeasure (Ambient d),
      Tendsto (fun j => μ (ρ j)) atTop (𝓝 ν) ∧ a ≤ (ν.mass : ℝ) ∧ (ν.mass : ℝ) ≤ A := by
  obtain ⟨ρ, hρ, P, hP⟩ := exists_normalized_measure_subsequence μ a B ha hB
    (fun j => (hm j).1) ht
  have hbounded : ∀ j, ((μ (ρ j)).mass : ℝ) ∈ Icc a A := fun j => hm (ρ j)
  obtain ⟨m, hmI, σ, hσ, hmass⟩ := isCompact_Icc.tendsto_subseq hbounded
  let m' : ℝ≥0 := ⟨m, ha.le.trans hmI.1⟩
  have hmass' : Tendsto (fun j => (μ (ρ (σ j))).mass) atTop (𝓝 m') :=
    NNReal.tendsto_coe.mp hmass
  have hP' : Tendsto (fun j => (μ (ρ (σ j))).normalize.toFiniteMeasure) atTop
      (𝓝 P.toFiniteMeasure) :=
    (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto P).comp
      (hP.comp hσ.tendsto_atTop)
  have hmasslim : (m' • P.toFiniteMeasure).mass = m' := by
    change (m' • P.toFiniteMeasure) univ = m'
    rw [FiniteMeasure.smul_apply]
    change m' * P.toFiniteMeasure.mass = m'
    rw [ProbabilityMeasure.mass_toFiniteMeasure, mul_one]
  refine ⟨ρ ∘ σ, hρ.comp hσ, m' • P.toFiniteMeasure, ?_, ?_, ?_⟩
  · have h := hmass'.smul hP'
    simpa only [← FiniteMeasure.self_eq_mass_smul_normalize, comp_apply] using! h
  · rw [hmasslim]
    exact hmI.1
  · rw [hmasslim]
    exact hmI.2

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalMeasureCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem le_compactnessUnweightedMeasure {d : ℕ} (n : ℕ) (ν : Measure (Ambient d)) :
    ν ≤ compactnessUnweightedMeasure n ν := by
  have h : ν.withDensity 1 ≤ ν.withDensity (fun x => ENNReal.ofReal ((compactnessWeight n x)⁻¹)) := by
    apply withDensity_mono
    exact Eventually.of_forall (fun x => by
      change (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((compactnessWeight n x)⁻¹)
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [compactnessWeight, inv_inv]
      exact one_le_pow₀ (by linarith [norm_nonneg x]))
  simpa only [withDensity_one, compactnessUnweightedMeasure] using! h

theorem compactnessUnweightedMeasure_ne_zero {d : ℕ} (n : ℕ)
    (ν : FiniteMeasure (Ambient d)) (hν : ν ≠ 0) :
    compactnessUnweightedMeasure n (ν : Measure (Ambient d)) ≠ 0 := by
  intro hzero
  have h : (ν : Measure (Ambient d)) = 0 := by
    apply le_antisymm _ bot_le
    simpa only [hzero] using! le_compactnessUnweightedMeasure n (ν : Measure (Ambient d))
  apply hν
  apply FiniteMeasure.toMeasure_injective
  exact h

theorem exists_original_measure_compact_subsequence {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧ CompactTestConvergence (fun j => μ (ρ j)) ν := by
  let μw : ℕ → FiniteMeasure (Ambient d) := fun j => compactnessFiniteMeasure n (μ j) C (hg j)
  let a : ℝ := c * (2 : ℝ)⁻¹ ^ (n + 1)
  have ha : 0 < a := by dsimp only [a] <;> positivity
  have hC : 0 ≤ C := (hg 0).1
  have hmass : ∀ j, a ≤ ((μw j).mass : ℝ) ∧ ((μw j).mass : ℝ) ≤ 3 * C * 2 ^ n := by
    intro j
    exact ⟨compactnessFiniteMeasure_mass_lower n (μ j) C c (hg j) (hm j),
      compactnessFiniteMeasure_mass_bound n (μ j) C (hg j)⟩
  have htail : ∀ j R, 0 < R → ((μw j) (closedBall (0 : Ambient d) R)ᶜ : ℝ) ≤
      (2 * C * 2 ^ n) / R := by
    intro j R hR
    calc
      _ ≤ 2 * (C * 2 ^ n / R) := compactnessFiniteMeasure_tail_bound n (μ j) C (hg j) R hR
      _ = _ := by ring
  obtain ⟨ρ, hρ, νw, hweak, hlow, _hupp⟩ := exists_finite_measure_subsequence μw
    a (3 * C * 2 ^ n) (2 * C * 2 ^ n) ha (by positivity) hmass htail
  have hνw : νw ≠ 0 := by
    apply νw.mass_nonzero_iff.mp
    intro hz
    rw [hz, NNReal.coe_zero] at hlow
    exact (not_le_of_gt ha) hlow
  refine ⟨ρ, hρ, compactnessUnweightedMeasure n (νw : Measure (Ambient d)),
    compactnessUnweightedMeasure_locally_finite n _, compactnessUnweightedMeasure_ne_zero n νw hνw, ?_⟩
  exact compactness_weighted_limit_gives_original_limit n (fun j => μ (ρ j)) C
    (fun j => hg (ρ j)) νw hweak

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalGrowthLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonzero compact-test limits with upper growth

A uniform lower bound on unit-ball mass prevents the compact-test subsequential
limit from vanishing. The upper growth estimate passes to this limit with the
explicit factor `2 ^ n` in its constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_original_growth_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (C * 2 ^ n) ν := by
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlimit⟩ :=
    exists_original_measure_compact_subsequence n μ C c hc hg hm
  let := hfinite
  exact ⟨ρ, hρ, ν, hfinite, hne, hlimit,
    compactTestConvergence_upper_growth n (fun j => μ (ρ j)) ν hlimit C (fun j => hg (ρ j))⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedMeasureCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactness under capped lower growth

Uniform upper growth and capped lower growth yield a nonzero compact-test limit.
The limit retains the origin in its support and quantitative growth bounds, with
the upper and lower constants enlarged by `2 ^ n` and `4 ^ n` respectively.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_capped_lower_measure_limit {d : ℕ} (n : ℕ) (C G H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H)
    (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      CappedLowerGrowth n (C * 4 ^ n) H ν ∧ (0 : Ambient d) ∈ ν.support := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  let t := min 1 H
  have ht : 0 < t := lt_min zero_lt_one hH
  have hmass (j : ℕ) : t ^ n / C ≤ (μ j).real (ball (0 : Ambient d) 1) := by
    apply (CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) 0 (hzero j) t ht (min_le_right _ _)).trans
    exact measureReal_mono (ball_subset_ball (min_le_left 1 H))
      ((hg j).2 0 1 zero_lt_one |>.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν⟩ :=
    exists_original_growth_limit n μ G (t ^ n / C) (by positivity) hg hmass
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, ?_, ?_⟩
  · exact CappedLowerGrowth.compact_limit n C H (fun j => μ (ρ j)) ν hC hlocal (fun j => hlower (ρ j))
  · exact CappedLowerGrowth.limit_origin n C H (fun j => μ (ρ j)) ν hC hH hlocal
      (fun j => hlower (ρ j)) (fun j => hzero (ρ j))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_EventualGlobalLowerLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_eventual_global_lower {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ∀ x ∈ (μ j).support,
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r)) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r → ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by rw [div_pow]; ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    filter_upwards [hlower (r / 4) (by positivity)] with j hj
    intro y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hj y hy)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), heq] at h
    exact h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedLowerTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Blowups turn capped lower growth into eventual global lower growth as their scales vanish.
Compact-test convergence then preserves these lower bounds in a tangent measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem capped_blowup_lower_unit_cap {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (s : ℝ) (hs : 0 < s) (hsH : s ≤ H) :
    CappedLowerGrowth n C 1 (blowupMeasure n μ a s) := by
  intro x hx r hr hr1
  apply CappedLowerGrowth.blowup n C H μ hlower a s hs x hx r hr
  apply hr1.trans
  exact (one_le_div hs).mpr hsH

theorem capped_blowup_eventual_global_lower {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hH : 0 < H) (hlower : CappedLowerGrowth n C H μ) (a : Ambient d)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ∀ x ∈ (blowupMeasure n μ a (s j)).support,
      ENNReal.ofReal (r ^ n / C) ≤ blowupMeasure n μ a (s j) (ball x r) := by
  intro r hr
  have hsr : Tendsto (fun j => s j * r) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const r
  filter_upwards [hsr.eventually (gt_mem_nhds hH)] with j hj
  intro x hx
  apply CappedLowerGrowth.blowup n C H μ hlower a (s j) (hs j) x hx r hr
  exact (le_div_iff₀ (hs j)).mpr (by simpa only [mul_comm] using! hj.le)

theorem exists_capped_lower_tangent {d : ℕ} (n : ℕ) (C G H : ℝ)
    (μ : Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H) (hg : GlobalUpperGrowth n G μ)
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (ha : a ∈ μ.support)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hsH : ∀ j, s j ≤ H) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ a (s (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r → ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  have hgj (j : ℕ) : GlobalUpperGrowth n G (μj j) := blowupMeasure_growth n μ a (s j) G (hs j) hg
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _, hzeroν⟩ :=
    exists_capped_lower_measure_limit n C G 1 μj hC zero_lt_one hgj
      (fun j => capped_blowup_lower_unit_cap n C H μ hlower a (s j) (hs j) (hsH j))
      (fun j => blowupMeasure_origin_mem_support n μ a (s j) (hs j) ha)
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (μj (ρ j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (hgj (ρ j))
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, ?_⟩
  apply compactTestConvergence_eventual_global_lower n C (fun j => μj (ρ j)) ν hC hlocal
  exact capped_blowup_eventual_global_lower n C H μ hH hlower a
    (fun j => s (ρ j)) (fun j => hs (ρ j)) (hs0.comp hρ.tendsto_atTop)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_LocalFlatBallTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem local_bilateral_tube_transfer {d : ℕ} (A B S : Set (Ambient d)) (hA : A.Nonempty)
    (a b : Ambient d) (r δ η : ℝ) (hr : 0 < r) (hδ : δ ≤ r / 4) (hη : η ≤ r / 4)
    (hab : dist b a ≤ r / 4)
    (hBA : ∀ x ∈ ball a (2 * r), x ∈ B → infDist x A < δ)
    (hAB : ∀ x ∈ ball a (2 * r), x ∈ A → infDist x B < δ)
    (hAS : ∀ x ∈ ball a (2 * r), x ∈ A → infDist x S < η)
    (hSA : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x A < η) :
    (∀ x ∈ ball b r, x ∈ B → infDist x S < η + δ) ∧
    (∀ x ∈ ball b r, x ∈ S → infDist x B < η + δ) := by
  have hxlarge (x : Ambient d) (hx : x ∈ ball b r) : x ∈ ball a (2 * r) := by
    have ht := dist_triangle x b a
    have hx' : dist x b < r := hx
    change dist x a < 2 * r
    linarith
  have hylarge (x y : Ambient d) (hx : x ∈ ball b r) (hxy : dist x y < r / 4) :
      y ∈ ball a (2 * r) := by
    have ht := dist_triangle y x a
    have ht' := dist_triangle x b a
    have hx' : dist x b < r := hx
    rw [dist_comm y x] at ht
    change dist y a < 2 * r
    linarith
  constructor
  · intro x hx hxB
    obtain ⟨y, hyA, hxy⟩ := (infDist_lt_iff hA).mp (hBA x (hxlarge x hx) hxB)
    have hyS := hAS y (hylarge x y hx (hxy.trans_le hδ)) hyA
    exact infDist_le_infDist_add_dist.trans_lt (by linarith : infDist y S + dist x y < η + δ)
  · intro x hx hxS
    obtain ⟨y, hyA, hxy⟩ := (infDist_lt_iff hA).mp (hSA x (hxlarge x hx) hxS)
    have hyB := hAB y (hylarge x y hx (hxy.trans_le hη)) hyA
    exact infDist_le_infDist_add_dist.trans_lt (by linarith : infDist y B + dist x y < η + δ)

theorem compactTestConvergence_local_flat_ball {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (a : Ambient d) (ha : a ∈ ν.support) (b : ℕ → Ambient d) (hb : Tendsto b atTop (𝓝 a))
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support →
      infDist x (S : Set (Ambient d)) < ε * r / 16)
    (hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) :
    ∀ᶠ j in atTop, bilateralBeta n (μ j) (b j) r < ε := by
  have hmargin : ε * r / 16 ≤ r / 4 := by nlinarith [mul_le_mul_of_nonneg_right hε1 hr.le]
  filter_upwards [compactTestConvergence_bilateral_support_tubes n μ ν hlocal C hC hlower hdiam
    a (2 * r) (ε * r / 16) (by positivity),
    Metric.tendsto_nhds.mp hb (r / 4) (by positivity)] with j hj hjb
  have ht := local_bilateral_tube_transfer ν.support (μ j).support (S : Set (Ambient d))
    ⟨a, ha⟩ a (b j) r (ε * r / 16) (ε * r / 16) hr hmargin hmargin hjb.le
    hj.1 hj.2 hforward hreverse
  apply bilateralBeta_lt_of_support_tubes n (μ j) (b j) r ε hr hε S hS
  · intro x hx hxs
    have hp := ht.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have hp := ht.2 x hx hxs
    nlinarith [mul_pos hε hr]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_CappedLowerSupportTubes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_capped_support_tube {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (a : Ambient d)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε := by
  let r := min (ε / 2) H
  have hr : 0 < r := lt_min (half_pos hε) hH
  have hzero : ∀ᵐ x ∂ν, infDist x ν.support = 0 := by
    filter_upwards [ν.support_mem_ae] with x hx
    exact infDist_zero_of_mem hx
  apply compactTestConvergence_support_tube μ ν hlocal (fun x => infDist x ν.support)
    1 (lipschitz_infDist_pt ν.support) hzero a R ε r (r ^ n / C) hε (by positivity)
    (by simpa only [NNReal.coe_one, one_mul] using! min_le_left (ε / 2) H)
  exact Eventually.of_forall fun j x _ hx =>
    CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) x hx r hr (min_le_right _ _)

theorem compactTestConvergence_capped_bilateral_tubes {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (a : Ambient d)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε) ∧
      (∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε) :=
  (compactTestConvergence_capped_support_tube n C H μ ν hlocal hC hH hlower a R ε hε).and
    (compactTestConvergence_reverse_support_tube μ ν hlocal a R ε hε)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactSupportApproximants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_support_approximants {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (b : Ambient d) (hb : b ∈ ν.support) :
    ∃ (φ : ℕ → ℕ) (a : ℕ → Ambient d),
      (∀ j, j ≤ φ j) ∧ Tendsto φ atTop atTop ∧
      (∀ j, a j ∈ (μ (φ j)).support) ∧ Tendsto a atTop (𝓝 b) := by
  have hex (k : ℕ) : ∃ j, k ≤ j ∧ ∃ x, x ∈ (μ j).support ∧
      dist x b < (1 / 2 : ℝ) ^ k := by
    obtain ⟨j, hjnear, hjlarge⟩ := ((compactTestConvergence_nearby_support μ ν hlocal b hb
      ((1 / 2 : ℝ) ^ k) (by positivity)).and (eventually_ge_atTop k)).exists
    exact ⟨j, hjlarge, hjnear⟩
  choose φ hφ a ha hd using hex
  have htop : Tendsto φ atTop atTop := tendsto_atTop_mono hφ tendsto_id
  refine ⟨φ, a, hφ, htop, ha, ?_⟩
  have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hpow.eventually (gt_mem_nhds hε)] with j hj
  exact (hd j).trans hj

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CappedFlatBallLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Flat balls under compact-test convergence

Capped lower growth supplies local support control along a converging sequence of measures.
Bilateral approximation by an affine plane then transfers flat balls to nearby centers of
the approximating measures, and persistent bad balls impose a lower beta bound on the limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_capped_flat_ball {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j))
    (a : Ambient d) (ha : a ∈ ν.support) (b : ℕ → Ambient d) (hb : Tendsto b atTop (𝓝 a))
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support → infDist x (S : Set (Ambient d)) < ε * r / 16)
    (hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) :
    ∀ᶠ j in atTop, bilateralBeta n (μ j) (b j) r < ε := by
  have hmargin : ε * r / 16 ≤ r / 4 := by nlinarith [mul_le_mul_of_nonneg_right hε1 hr.le]
  filter_upwards [compactTestConvergence_capped_bilateral_tubes n C H μ ν hlocal hC hH hlower
    a (2 * r) (ε * r / 16) (by positivity),
    Metric.tendsto_nhds.mp hb (r / 4) (by positivity)] with j hj hjb
  have ht := local_bilateral_tube_transfer ν.support (μ j).support (S : Set (Ambient d))
    ⟨a, ha⟩ a (b j) r (ε * r / 16) (ε * r / 16) hr hmargin hmargin hjb.le
    hj.1 hj.2 hforward hreverse
  apply bilateralBeta_lt_of_support_tubes n (μ j) (b j) r ε hr hε S hS
  · intro x hx hxs
    have hp := ht.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have hp := ht.2 x hx hxs
    nlinarith [mul_pos hε hr]

theorem compactTestConvergence_capped_beta_lower {n d : ℕ} (hnd : n ≤ d) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (hC : 0 < C) (hH : 0 < H)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j))
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ε / 64 ≤ bilateralBeta n ν a (2 * r) := by
  by_contra hnot
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd ν a (2 * r) (ε / 64) (lt_of_not_ge hnot)
  have hp := bilateralPlaneError_lt_pointwise ν ⟨a, ha⟩ a (2 * r) (ε / 64) (by positivity) S hS he
  have hforward : ∀ x ∈ ball a (2 * r), x ∈ ν.support →
      infDist x (S : Set (Ambient d)) < ε * r / 16 := by
    intro x hx hxs
    have ht := hp.1 x hx hxs
    nlinarith [mul_pos hε hr]
  have hreverse : ∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16 := by
    intro x hx hxs
    have ht := hp.2 x hx hxs
    nlinarith [mul_pos hε hr]
  obtain ⟨φ, b, _, hφ, hbs, hb⟩ := compactTestConvergence_support_approximants μ ν hlocal a ha
  let : ∀ j, IsFiniteMeasureOnCompacts ((μ ∘ φ) j) :=
    fun j => inferInstanceAs (IsFiniteMeasureOnCompacts (μ (φ j)))
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  have ht := compactTestConvergence_capped_flat_ball n C H (μ ∘ φ) ν hc hC hH
    (fun j => hlower (φ j)) a ha b hb r ε hr hε hε1 S hS hforward hreverse
  obtain ⟨j, hjflat, hjbad, hjU⟩ :=
    (ht.and ((hφ.eventually hbad).and (hb.eventually (hU.mem_nhds haU)))).exists
  exact (not_lt_of_ge (hjbad (b j) (hbs j) hjU)) hjflat

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BlowupBilateralCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem bilateralPlaneError_blowup_at {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s R : ℝ) (hs : 0 < s) (S : AffineSubspace ℝ (Ambient d)) :
    bilateralPlaneError (blowupMeasure n μ a s) b R S =
      bilateralPlaneError μ (a + s • b) (s * R) (S.map (physicalAffine a s hs).toAffineMap) := by
  have hforward := directedBallDeviation_physical (blowupMeasure n μ a s).support
    (S : Set (Ambient d)) a b s R hs
  have hreverse := directedBallDeviation_physical (S : Set (Ambient d))
    (blowupMeasure n μ a s).support a b s R hs
  rw [physicalAffine_image_blowup_support n μ a s hs, physicalAffine_apply] at hforward hreverse
  unfold bilateralPlaneError
  rw [AffineSubspace.coe_map]
  change _ = (directedBallDeviation μ.support
    (physicalAffine a s hs '' (S : Set (Ambient d))) (a + s • b) (s * R) +
    directedBallDeviation (physicalAffine a s hs '' (S : Set (Ambient d)))
      μ.support (a + s • b) (s * R)) / (s * R)
  rw [hforward, hreverse, ← mul_add, mul_div_mul_left _ _ hs.ne']

theorem bilateralBeta_blowup_at {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s R : ℝ) (hs : 0 < s) :
    bilateralBeta n (blowupMeasure n μ a s) b R = bilateralBeta n μ (a + s • b) (s * R) := by
  unfold bilateralBeta
  congr 1
  ext t
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S.map (physicalAffine a s hs).toAffineMap,
      isAffineNPlane_map_equiv n _ S hS, bilateralPlaneError_blowup_at n μ a b s R hs S⟩
  · rintro ⟨T, hT, rfl⟩
    refine ⟨T.map (physicalAffine a s hs).symm.toAffineMap,
      isAffineNPlane_map_equiv n _ T hT, ?_⟩
    rw [bilateralPlaneError_blowup_at n μ a b s R hs, affineSubspace_map_equiv_symm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_LocalFlatBallExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Local bilateral flatness in a compact-test limit transfers to nearby support points of the
approximating measures, contradicting an eventual lower bound on their local flatness error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_excludes_local_flat_ball {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ¬ ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      (∀ x ∈ ball a (2 * r), x ∈ ν.support → infDist x (S : Set (Ambient d)) < ε * r / 16) ∧
      (∀ x ∈ ball a (2 * r), x ∈ S → infDist x ν.support < ε * r / 16) := by
  rintro ⟨S, hS, hforward, hreverse⟩
  obtain ⟨φ, b, _, hφ, hbs, hb⟩ := compactTestConvergence_support_approximants μ ν hlocal a ha
  let : ∀ j, IsFiniteMeasureOnCompacts ((μ ∘ φ) j) :=
    fun j => inferInstanceAs (IsFiniteMeasureOnCompacts (μ (φ j)))
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  have ht := compactTestConvergence_local_flat_ball n (μ ∘ φ) ν hc C hC
    (fun j => hlower (φ j)) (fun t ht => hφ.eventually (hdiam t ht))
    a ha b hb r ε hr hε hε1 S hS hforward hreverse
  obtain ⟨j, hjflat, hjbad, hjU⟩ :=
    (ht.and ((hφ.eventually hbad).and (hb.eventually (hU.mem_nhds haU)))).exists
  exact (not_lt_of_ge (hjbad (b j) (hbs j) hjU)) hjflat

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_BilateralLowerLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_bilateralBeta_lower {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ε / 64 ≤ bilateralBeta n ν a (2 * r) := by
  by_contra hnot
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd ν a (2 * r) (ε / 64) (lt_of_not_ge hnot)
  have hp := bilateralPlaneError_lt_pointwise ν ⟨a, ha⟩ a (2 * r) (ε / 64) (by positivity) S hS he
  apply compactTestConvergence_excludes_local_flat_ball n μ ν hlocal C hC hlower hdiam
    U hU ε hε hε1 r hr hbad a ha haU
  refine ⟨S, hS, ?_, ?_⟩
  · intro x hx hxs
    have ht := hp.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have ht := hp.2 x hx hxs
    nlinarith [mul_pos hε hr]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_UniformNonflatLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem GlobalBilateralLower.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) (hε : GlobalBilateralLower n μ ε) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    GlobalBilateralLower n (blowupMeasure n μ a s) ε := by
  intro b hb R hR
  rw [bilateralBeta_blowup_at n μ a b s R hs]
  exact hε _ ((blowupMeasure_support_iff n μ a b s hs).mp hb) _ (mul_pos hs hR)

theorem GlobalBilateralLower.compact_limit {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ᶠ j in atTop, GlobalBilateralLower n (μ j) ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  intro a ha R hR
  have hb : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ (univ : Set (Ambient d)) →
      ε ≤ bilateralBeta n (μ j) b (R / 2) := by
    filter_upwards [hbad] with j hj
    exact fun b hb _ => hj b hb (R / 2) (by positivity)
  have ht := compactTestConvergence_bilateralBeta_lower hnd μ ν hlocal C hC hlower hdiam
    univ isOpen_univ ε hε hε1 (R / 2) (by positivity) hb a ha (mem_univ a)
  simpa only [mul_div_cancel₀ R (by norm_num : (2 : ℝ) ≠ 0)] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_CappedNonflatTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bounded rescaled centers eventually remain in any open neighborhood of the blowup center.
This transfers local capped nonflatness to a global bilateral lower bound for tangent limits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem scaled_bounded_centers_eventually_mem_open {d : ℕ}
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (ha : a ∈ U)
    (s : ℕ → ℝ) (hs : ∀ j, 0 ≤ s j) (hs0 : Tendsto s atTop (𝓝 0)) (M : ℝ) :
    ∀ᶠ j in atTop, ∀ x : Ambient d, ‖x‖ ≤ M → a + s j • x ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have ht : Tendsto (fun j => s j * M) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const M
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with j hj
  intro x hx
  apply hball
  change dist (a + s j • x) a < δ
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hs j)]
  exact (mul_le_mul_of_nonneg_left hx (hs j)).trans_lt hj

theorem global_bilateral_lower_of_capped_tangent {n d : ℕ} (hnd : n ≤ d)
    (C G H cap ε : ℝ) (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hg : GlobalUpperGrowth n G μ) (hlower : CappedLowerGrowth n C H μ)
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (haU : a ∈ U)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hsH : ∀ j, s j ≤ H) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hcap : 0 < cap) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ x ∈ μ.support, x ∈ U → ∀ r : ℝ, 0 < r → r < cap → ε ≤ bilateralBeta n μ x r) :
    GlobalBilateralLower n ν (ε / 64) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  let : ∀ j, IsFiniteMeasureOnCompacts (μj j) := fun j =>
    globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  have hl (j : ℕ) : CappedLowerGrowth n C 1 (μj j) :=
    capped_blowup_lower_unit_cap n C H μ hlower a (s j) (hs j) (hsH j)
  intro b hb R hR
  have hscale : Tendsto (fun j => s j * (R / 2)) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hs0.mul_const (R / 2)
  have hbadj : ∀ᶠ j in atTop, ∀ x ∈ (μj j).support, x ∈ ball b 1 →
      ε ≤ bilateralBeta n (μj j) x (R / 2) := by
    filter_upwards [scaled_bounded_centers_eventually_mem_open U hU a haU s
      (fun j => (hs j).le) hs0 (‖b‖ + 1), hscale.eventually (gt_mem_nhds hcap)] with j hjU hjR
    intro x hx hxb
    have hxM : ‖x‖ ≤ ‖b‖ + 1 := by
      have ht := dist_triangle x b (0 : Ambient d)
      have hxb' : dist x b < 1 := hxb
      simp only [dist_zero_right] at ht
      linarith
    change ε ≤ bilateralBeta n (blowupMeasure n μ a (s j)) x (R / 2)
    rw [bilateralBeta_blowup_at n μ a x (s j) (R / 2) (hs j)]
    exact hbad _ ((blowupMeasure_support_iff n μ a x (s j) (hs j)).mp hx)
      (hjU x hxM) _ (mul_pos (hs j) (by positivity)) hjR
  have ht := compactTestConvergence_capped_beta_lower hnd C 1 μj ν hlocal hC zero_lt_one hl
    (ball b 1) isOpen_ball ε hε hε1 (R / 2) (by positivity) hbadj b hb (mem_ball_self zero_lt_one)
  simpa only [mul_div_cancel₀ R (by norm_num : (2 : ℝ) ≠ 0)] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedEuclideanCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem exists_separated_euclidean_closedBall_cover {k : ℕ} (R δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Finset (Ambient k),
      (∀ x ∈ s, ‖x‖ ≤ R) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) ∧
      (∀ x : Ambient k, ‖x‖ ≤ R → ∃ y ∈ s, dist x y < δ) := by
  classical
  obtain ⟨N, _, hNE, hsep, hcover⟩ := exists_separated_cover_extension
    (closedBall (0 : Ambient k) R) ∅ δ hδ (empty_subset _) (by simp)
  have hfinite : N.Finite := by
    have h := separated_set_finite_inter_compact N (closedBall (0 : Ambient k) R) δ hδ hsep
      (isCompact_closedBall 0 R)
    simpa only [inter_eq_left.mpr hNE] using! h
  refine ⟨hfinite.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have hm := hNE (hfinite.mem_toFinset.mp hx)
    simpa only [mem_closedBall, dist_zero_right] using! hm
  · intro x hx y hy hxy
    exact hsep (hfinite.mem_toFinset.mp hx) (hfinite.mem_toFinset.mp hy) hxy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x (by simpa only [mem_closedBall, dist_zero_right] using! hx)
    exact ⟨y, hfinite.mem_toFinset.mpr hy, hxy⟩

theorem euclidean_unit_ball_cover_card_lower {k : ℕ} (s : Finset (Ambient k))
    (δ : ℝ) (hδ : 0 < δ)
    (hcover : ∀ x : Ambient k, ‖x‖ < 1 → ∃ y ∈ s, dist x y < δ) :
    1 ≤ (s.card : ℝ) * δ ^ k := by
  let v : Measure (Ambient k) := volume
  have hsub : ball (0 : Ambient k) 1 ⊆ ⋃ y ∈ s, ball y δ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x (by simpa only [mem_ball, dist_zero_right] using! hx)
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy⟩⟩
  have hb : v (ball 0 1) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) * v (ball 0 1) := by
    calc
      _ ≤ v (⋃ y ∈ s, ball y δ) := measure_mono hsub
      _ ≤ ∑ y ∈ s, v (ball y δ) := measure_biUnion_finset_le s _
      _ = _ := by
        simp only [v.addHaar_ball_of_pos _ hδ, finrank_euclideanSpace_fin,
          Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hi : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) := by
    apply (ENNReal.mul_le_mul_iff_left (measure_ball_pos v 0 zero_lt_one).ne'
      (measure_ball_lt_top (μ := v) (x := 0) (r := 1)).ne).mp
    simpa only [one_mul] using! hb
  have hfin : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ k) ≠ ∞ := by finiteness
  have hreal := ENNReal.toReal_mono hfin hi
  simpa only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le k)] using! hreal

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADCoreMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Function

theorem finite_disjoint_core_mass_bound {ι : Type*} {d : ℕ}
    (n : ℕ) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (s : Finset ι) (z : ι → Ambient d) (ρ mass : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, ENNReal.ofReal (mass i) ≤ μ (ball (z i) (ρ i)))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hsub : ∀ i ∈ s, ball (z i) (ρ i) ⊆ ball a R)
    (hdisjoint : Set.PairwiseDisjoint (s : Set ι) (fun i => ball (z i) (ρ i))) :
    ∑ i ∈ s, mass i ≤ G * R ^ n := by
  have hs : ENNReal.ofReal (∑ i ∈ s, mass i) ≤ ENNReal.ofReal (G * R ^ n) := by
    calc
      _ = ∑ i ∈ s, ENNReal.ofReal (mass i) := ENNReal.ofReal_sum_of_nonneg hmass
      _ ≤ ∑ i ∈ s, μ (ball (z i) (ρ i)) := Finset.sum_le_sum hlower
      _ = μ (⋃ i ∈ s, ball (z i) (ρ i)) :=
        (measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)).symm
      _ ≤ μ (ball a R) := measure_mono (iUnion₂_subset hsub)
      _ ≤ _ := hg.2 a R hR
  have hr := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) hs
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg hmass)] using! hr

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FullPlaneLowerDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem isometric_separated_AD_card_bound {n k d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (L : Ambient k →ₗᵢ[ℝ] Ambient d) (s : Finset (Ambient k))
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1) (hsupp : ∀ x ∈ s, L x ∈ μ.support)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) :
    (s.card : ℝ) * δ ^ n ≤ (G * 2 ^ n) * (2 ^ n * C) := by
  have hsub : ∀ x ∈ s, ball (L x) (δ / 2) ⊆ ball (0 : Ambient d) 2 := by
    intro x hx
    apply ball_subset_ball'
    rw [dist_zero_right, L.norm_map]
    linarith [hs x hx]
  have hd : Set.PairwiseDisjoint (s : Set (Ambient k)) (fun x => ball (L x) (δ / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [L.dist_map]
    linarith [hsep x hx y hy hxy]
  have hb := finite_disjoint_core_mass_bound n G μ hg s L (fun _ => δ / 2)
    (fun _ => (δ / 2) ^ n / C) (fun _ _ => by positivity)
    (fun x hx => hlower (L x) (hsupp x hx) (δ / 2) (by positivity))
    0 2 (by norm_num) hsub hd
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  have hbdiv : (s.card : ℝ) * δ ^ n / (2 ^ n * C) ≤ G * 2 ^ n := by
    convert! hb using 1
    all_goals try with_reducible_and_instances rfl
    rw [div_pow]
    field_simp
  exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n * C)).mp hbdiv

theorem isometric_ball_in_support_dimension_le {n k d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (L : Ambient k →ₗᵢ[ℝ] Ambient d)
    (hsupp : ∀ x : Ambient k, ‖x‖ ≤ 1 → L x ∈ μ.support) : k ≤ n := by
  by_contra hnot
  have hnk : n < k := lt_of_not_ge hnot
  let M : ℝ := (G * 2 ^ n) * (2 ^ n * C)
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hg.1]
  let δ : ℝ := min 1 (1 / (2 * (M + 1)))
  have hden : 0 < 2 * (M + 1) := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos zero_lt_one hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδsmall : M * δ < 1 := by
    have ht : δ * (2 * (M + 1)) ≤ 1 := (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  obtain ⟨s, hs, hsep, hcover⟩ := exists_separated_euclidean_closedBall_cover (k := k) 1 δ hδ
  have hcard := isometric_separated_AD_card_bound μ C G hC hg hlower L s hs
    (fun x hx => hsupp x (hs x hx)) δ hδ hδ1 hsep
  have hvol := euclidean_unit_ball_cover_card_lower s δ hδ (fun x hx => hcover x hx.le)
  have hp : δ ^ (k - n) ≤ δ := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k - n ≠ 0)
    rw [hq, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hδ.le hδ1) hδ.le).trans_eq (one_mul δ)
  have hid : δ ^ k = δ ^ n * δ ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_of_le hnk.le]
  have hupper : (s.card : ℝ) * δ ^ k ≤ M * δ := by
    rw [hid, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hcard (pow_nonneg hδ.le (k - n))).trans
      (mul_le_mul_of_nonneg_left hp hM)
  exact (not_lt_of_ge (hvol.trans hupper)) hδsmall

theorem full_support_submodule_finrank_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support = (P : Set (Ambient d))) :
    Module.finrank ℝ P ≤ n := by
  obtain ⟨L, hL⟩ := exists_isometry_onto_subspace P rfl
  apply isometric_ball_in_support_dimension_le μ C G hC hg hlower L
  intro x _
  rw [hP]
  have hx : L x ∈ L.toLinearMap.range := LinearMap.mem_range_self L.toLinearMap x
  simpa only [hL] using! hx

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

theorem exists_support_point_away_from_plane {n k d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane k S) (hkn : k < n)
    (R τ c : ℝ) (hR : 0 < R) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (hsmall : (C * (2 : ℝ) ^ n * (3 : ℝ) ^ k) * τ < c) :
    ∃ x ∈ ball (0 : Ambient d) R, x ∈ μ.support ∧
      τ * R ≤ infDist x (S : Set (Ambient d)) := by
  have htube : μ.real (affineTube S R (τ * R)) < μ.real (ball (0 : Ambient d) R) :=
    (lower_dimensional_affineTube_bound μ C hg S hS hkn R τ hR hτ hτ1).trans_lt
      ((mul_lt_mul_of_pos_right hsmall (pow_pos hR n)).trans_le hmass)
  have hfinite : μ (affineTube S R (τ * R)) ≠ ∞ :=
    ne_of_lt ((affineTube_measure_bound μ C hg S hS R (τ * R) hR.le (mul_pos hτ hR)).trans_lt
      ENNReal.ofReal_lt_top)
  obtain ⟨x, hx, hsupport, hout⟩ :=
    exists_support_point_outside_small_set μ (ball (0 : Ambient d) R)
      (affineTube S R (τ * R)) hfinite htube
  refine ⟨x, hx, hsupport, ?_⟩
  apply le_of_not_gt
  intro hnear
  exact hout ⟨ball_subset_closedBall hx, hnear⟩

theorem exists_uniform_affine_escape_width {n d : ℕ}
    (μ : Measure (Ambient d)) (C c : ℝ) (hg : GlobalUpperGrowth n C μ) (hc : 0 < c)
    (R : ℝ) (hR : 0 < R) (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R)) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
        ∃ x ∈ ball (0 : Ambient d) R, x ∈ μ.support ∧
          τ * R ≤ infDist x (S : Set (Ambient d)) := by
  let D : ℝ := C * (2 : ℝ) ^ n * (3 : ℝ) ^ n
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hg.1 (by positivity)) (by positivity)
  let τ := min 1 (c / (2 * (D + 1)))
  have hden : 0 < 2 * (D + 1) := by positivity
  have hτ : 0 < τ := lt_min zero_lt_one (div_pos hc hden)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτb : τ * (2 * (D + 1)) ≤ c := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : D * τ < c := by nlinarith [mul_nonneg hD hτ.le]
  refine ⟨τ, hτ, hτ1, ?_⟩
  intro k hkn S hS
  apply exists_support_point_away_from_plane μ C hg S hS hkn R τ c hR hτ hτ1 hmass
  have hK : C * (2 : ℝ) ^ n * (3 : ℝ) ^ k ≤ D := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkn.le)
      (mul_nonneg hg.1 (by positivity))
  exact (mul_le_mul_of_nonneg_right hK hτ.le).trans_lt hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FullPlaneDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem support_submodule_finrank_ge {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d))) :
    n ≤ Module.finrank ℝ P := by
  by_contra hnot
  have hkn : Module.finrank ℝ P < n := lt_of_not_ge hnot
  have hfinite : μ (ball (0 : Ambient d) 1) ≠ ∞ :=
    ((hg.2 0 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top).ne
  have hmass := ENNReal.toReal_mono hfinite (hlower 0 hzero 1 zero_lt_one)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 : ℝ) ^ n / C)] at hmass
  have hm : (1 / C) * (1 : ℝ) ^ n ≤ μ.real (ball (0 : Ambient d) 1) := by
    simpa only [one_pow, mul_one] using! hmass
  obtain ⟨τ, hτ, _, hescape⟩ := exists_uniform_affine_escape_width μ G (1 / C) hg
    (by positivity) 1 zero_lt_one hm
  have hS : IsAffineNPlane (Module.finrank ℝ P) P.toAffineSubspace := by
    refine ⟨⟨0, P.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction]
  obtain ⟨x, _, hxs, hxaway⟩ := hescape _ hkn P.toAffineSubspace hS
  have hxP : x ∈ (P.toAffineSubspace : Set (Ambient d)) := hP hxs
  rw [infDist_zero_of_mem hxP, mul_one] at hxaway
  exact (not_le_of_gt hτ) hxaway

theorem full_support_submodule_finrank_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support = (P : Set (Ambient d))) :
    Module.finrank ℝ P = n := by
  apply Nat.le_antisymm (full_support_submodule_finrank_le μ C G hC hg hlower P hP)
  apply support_submodule_finrank_ge μ C G hC hg hlower _ P hP.subset
  rw [hP]
  exact P.zero_mem

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NonflatSupportHole
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem directedBallDeviation_self {d : ℕ} (S : Set (Ambient d)) (a : Ambient d) (r : ℝ) :
    directedBallDeviation S S a r = 0 := by
  apply le_antisymm _ (directedBallDeviation_nonneg S S a r)
  exact directedBallDeviation_le S S a r 0 le_rfl
    (fun _ _ hx => (infDist_zero_of_mem hx).le)

theorem bilateralBeta_zero_of_plane_support {n d : ℕ} (μ : Measure (Ambient d))
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (hsupport : μ.support = (S : Set (Ambient d))) (a : Ambient d)
    (r : ℝ) (hr : 0 ≤ r) : bilateralBeta n μ a r = 0 := by
  apply le_antisymm _ (bilateralBeta_nonneg n μ a r hr)
  apply (bilateralBeta_le_planeError n μ a r hr S hS).trans
  simp only [bilateralPlaneError, hsupport, directedBallDeviation_self, add_zero, zero_div, le_refl]

theorem GlobalBilateralLower.exists_relative_hole {n d : ℕ}
    (μ : Measure (Ambient d)) (C G ε : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hε : 0 < ε) (hbad : GlobalBilateralLower n μ ε)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d))) :
    ∃ c : Ambient d, c ∈ P ∧ c ∉ μ.support := by
  by_contra hnone
  have hfull : μ.support = (P : Set (Ambient d)) := by
    apply Set.Subset.antisymm hP
    intro x hx
    by_contra hxs
    exact hnone ⟨x, hx, hxs⟩
  have hdim := full_support_submodule_finrank_eq μ C G hC hg hlower P hfull
  have hS : IsAffineNPlane n P.toAffineSubspace := by
    refine ⟨⟨0, P.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction, hdim]
  have hzero : (0 : Ambient d) ∈ μ.support := by rw [hfull]; exact P.zero_mem
  have hb := hbad 0 hzero 1 zero_lt_one
  rw [bilateralBeta_zero_of_plane_support μ P.toAffineSubspace hS hfull 0 1 zero_le_one] at hb
  exact (not_le_of_gt hε) hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TruncationIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of hard Riesz truncations

Global upper growth makes the Riesz kernel square-integrable outside each positive-radius
ball. Pairing this exterior estimate with an L² input proves integrability of the hard
truncation. For finite measures, integrability instead follows from the bounded exterior
kernel and the inclusion of L² in L¹.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_sq_norm_le_tail_weight {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (x y : Ambient d) (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ^ 2 ≤ (ε ^ (n - 1))⁻¹ * inverseDistancePow (n + 1) x y := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd), inv_pow, ← pow_mul,
    show n * 2 = (n - 1) + (n + 1) by omega, pow_add, mul_inv]
  apply mul_le_mul_of_nonneg_right
  · simpa only [one_div] using! one_div_le_one_div_of_le
      (pow_pos hε (n - 1)) (pow_le_pow_left₀ hε.le hy (n - 1))
  · positivity

theorem kernel_memLp_two_on_exterior {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    MemLp (kernel n x) 2 (μ.restrict {y | ε < dist x y}) := by
  have hmeas : AEStronglyMeasurable (kernel n x) (μ.restrict {y | ε < dist x y}) :=
    (kernel_measurable_right n x).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hi := (inverseDistancePow_integrableOn_exterior n C μ hg x ε hε).const_mul
    ((ε ^ (n - 1))⁻¹)
  apply hi.mono' ((kernel_measurable_right n x).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact kernel_sq_norm_le_tail_weight n hn x y ε hε hy.le

theorem truncation_integrable_of_globalGrowth {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n C μ)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply memLp_one_iff_integrable.mp
  exact MemLp.smul (hf := kernel_memLp_two_on_exterior n hn C μ hg x ε hε) (hφ := hf.restrict _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ADTruncations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hard truncations for AD-regular measures

For support of infinite diameter, AD regularity yields global upper growth. For bounded
support, the measure is finite. These two cases establish integrability of every positive
hard truncation against an L² input without imposing boundedness on the support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem finiteMeasure_of_bounded_support {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (hdiam : Metric.ediam μ.support ≠ ∞) :
    IsFiniteMeasure μ := by
  have hc : IsCompact μ.support :=
    isCompact_iff_isClosed_bounded.mpr
      ⟨μ.isClosed_support, Metric.isBounded_iff_ediam_ne_top.mpr hdiam⟩
  constructor
  have heq : μ μ.support = μ univ := by
    simpa only [univ_inter] using!
      (measure_inter_conull (μ := μ) (s := univ) μ.measure_compl_support)
  rw [← heq]
  exact hc.measure_lt_top

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GlobalLowerDiameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A nonzero measure finite on compact sets cannot have bounded support if a positive-dimensional
lower growth bound holds at every positive radius: bounded support would force finite total mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem global_lower_growth_support_ediam_top {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (hne : μ ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) : ediam μ.support = ∞ := by
  by_contra hdiam
  let : IsFiniteMeasure μ := finiteMeasure_of_bounded_support μ hdiam
  obtain ⟨a, ha⟩ := μ.nonempty_support hne
  let R : ℝ := C * μ.real univ + 1
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    have hm : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
    nlinarith
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hp : R ≤ R ^ n := le_self_pow₀ hR1 (by omega)
  have hl := (hlower a ha R hR).trans (measure_mono (subset_univ _))
  have hreal := ENNReal.toReal_mono (measure_ne_top μ univ) hl
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ n / C)] at hreal
  have hpow : R ^ n ≤ μ.real univ * C := (div_le_iff₀ hC).mp hreal
  dsimp only [R] at hp
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_UniformNonflatTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform bilateral nonflatness persists, with a fixed loss, under compact-test limits and blowups.
Global lower growth supplies infinite support diameter for the limiting argument.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem GlobalBilateralLower.compact_limit_global {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hne : ∀ j, μ j ≠ 0) (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ᶠ j in atTop, GlobalBilateralLower n (μ j) ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  apply GlobalBilateralLower.compact_limit hnd μ ν hlocal C hC
    (fun j x hx t ht => hlower j x hx t ht.1) _ ε hε hε1 hbad
  intro t _
  apply Eventually.of_forall
  intro j
  rw [global_lower_growth_support_ediam_top n hn (μ j) (hne j) C hC (hlower j)]
  exact le_top

theorem GlobalBilateralLower.tangent {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ n / C) ≤ μ (ball x t))
    (a : Ambient d) (ha : a ∈ μ.support) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hbad : GlobalBilateralLower n μ ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  let : ∀ j, IsFiniteMeasureOnCompacts (μj j) := fun j =>
    globalGrowth_finite_on_compacts G (μj j) (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  have hne (j : ℕ) : μj j ≠ 0 := by
    have hz := blowupMeasure_origin_mem_support n μ a (s j) (hs j) ha
    intro hj
    change (0 : Ambient d) ∈ (μj j).support at hz
    rw [hj] at hz
    simp only [Measure.support_zero, mem_empty_iff_false] at hz
  apply GlobalBilateralLower.compact_limit_global hn hnd μj ν hne hlocal C hC
    (fun j => blowupMeasure_lower_global n μ a (s j) C (hs j) hlower) ε hε hε1
  exact Eventually.of_forall fun j => GlobalBilateralLower.blowup n μ ε hbad a (s j) (hs j)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_EmptyBallHalfspace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_nearest_point_to_hole {d : ℕ} (E : Set (Ambient d))
    (hclosed : IsClosed E) (hne : E.Nonempty) (c : Ambient d) (hc : c ∉ E) :
    ∃ a ∈ E, a ≠ c ∧ ∀ y ∈ E, dist a c ≤ dist y c := by
  obtain ⟨a, ha, heq⟩ := hclosed.exists_infDist_eq_dist hne c
  refine ⟨a, ha, (fun hac => hc (hac ▸ ha)), ?_⟩
  intro y hy
  rw [dist_comm a c, ← heq, dist_comm y c]
  exact infDist_le_dist_of_mem hy

theorem nearest_point_quadratic_constraint {d : ℕ} (a c y : Ambient d)
    (hmin : dist a c ≤ dist y c) :
    0 ≤ 2 * inner ℝ (a - c) (y - a) + ‖y - a‖ ^ 2 := by
  have hs := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist a c) hmin 2
  have heq : y - c = (a - c) + (y - a) := by abel
  simp only [dist_eq_norm] at hs
  rw [heq, norm_add_sq_real] at hs
  linarith

theorem nearest_point_rescaled_constraint {d : ℕ} (a c x : Ambient d)
    (r : ℝ) (hr : 0 < r) (hmin : dist a c ≤ dist (a + r • x) c) :
    0 ≤ 2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2 := by
  have h := nearest_point_quadratic_constraint a c (a + r • x) hmin
  have heq : a + r • x - a = r • x := by abel
  rw [heq, inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le] at h
  have hp : 0 ≤ r * (2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2) := by nlinarith
  exact nonneg_of_mul_nonneg_right hp hr

theorem compactTestConvergence_halfspace_of_quadratic_constraint {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (e : Ambient d)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hside : ∀ j x, x ∈ (μ j).support → 0 ≤ 2 * inner ℝ e x + r j * ‖x‖ ^ 2) :
    ∀ x ∈ ν.support, 0 ≤ inner ℝ e x := by
  have hzero : ∀ x ∈ ν.support, max 0 (-inner ℝ e x) = 0 := by
    apply compactTestConvergence_support_zero_of_tubes μ ν hlocal
      (fun x => max 0 (-inner ℝ e x)) (by fun_prop) (fun _ => le_max_left _ _)
    intro R ε hR hε
    have hconv : Tendsto (fun j => r j * R ^ 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using! hr0.mul_const (R ^ 2)
    filter_upwards [hconv.eventually (gt_mem_nhds (by linarith : 0 < 2 * ε))] with j hj
    intro x hx hxsupport
    have hxR : ‖x‖ ≤ R := (mem_ball_zero_iff.mp hx).le
    have hs : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
    have hp := mul_le_mul_of_nonneg_left hs (hr j)
    have h := hside j x hxsupport
    apply max_lt_iff.mpr
    exact ⟨hε, by linarith⟩
  intro x hx
  have h := le_max_right (0 : ℝ) (-inner ℝ e x)
  rw [hzero x hx] at h
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_GlobalLowerMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Global lower growth in measure limits

Compact-test convergence transfers lower ball-mass bounds to support points of the
limit, with the explicit factor `4 ^ n`. Combined with global upper growth and an origin
normalization, this produces a nonzero subsequential limit with both growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_global_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r)) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have hquarter : 0 < r / 4 := by positivity
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by
    rw [div_pow]
    ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    apply Filter.Eventually.of_forall
    intro j y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hlower j y hy (r / 4) hquarter)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C)] at h
    simpa only [heq, Measure.real] using! h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

theorem exists_global_growth_measure_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  have hmass : ∀ j, C⁻¹ ≤ (μ j).real (ball (0 : Ambient d) 1) := by
    intro j
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
      (hlower j 0 (hzero j) 1 zero_lt_one)
    simpa only [one_pow, one_div, ENNReal.toReal_ofReal (inv_nonneg.mpr hC.le), Measure.real] using! h
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν⟩ :=
    exists_original_growth_limit n μ G C⁻¹ (inv_pos.mpr hC) hg hmass
  let := hfinite
  have horigin : (0 : Ambient d) ∈ ν.support := by
    apply compactTestConvergence_mem_support_of_ball_masses (fun j => μ (ρ j)) ν hlocal 0
    intro r hr
    refine ⟨r ^ n / C, by positivity, Filter.Eventually.of_forall fun j => ?_⟩
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) r).measure_lt_top).ne
      (hlower (ρ j) 0 (hzero (ρ j)) r hr)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ n / C), Measure.real] using! h
  exact ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, horigin,
    compactTestConvergence_global_lower n (fun j => μ (ρ j)) ν hlocal C hC
      (fun j => hlower (ρ j))⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_HoleTangentMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tangent measures at a nearest point to a hole

Uniform growth bounds yield a nonzero subsequential blowup limit with inherited
two-sided growth. At a point nearest to a hole, the rescaled quadratic constraint
converges to a half-space constraint on the tangent measure's support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_blowup_measure_limit {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (a : Ambient d) (ha : a ∈ μ.support) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ a (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R) := by
  have hg' : ∀ j, GlobalUpperGrowth n G (blowupMeasure n μ a (r j)) :=
    fun j => blowupMeasure_growth n μ a (r j) G (hr j) hg
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (hg' j)
  exact exists_global_growth_measure_limit n (fun j => blowupMeasure n μ a (r j)) C G hC hg'
    (fun j => blowupMeasure_lower_global n μ a (r j) C (hr j) hlower)
    (fun j => blowupMeasure_origin_mem_support n μ a (r j) (hr j) ha)

theorem exists_nonzero_halfspace_tangent_of_hole {d : ℕ}
    (n : ℕ) (μ : Measure (Ambient d)) (hne : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (c : Ambient d) (hc : c ∉ μ.support)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ a ∈ μ.support, a ≠ c ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∃ ν : Measure (Ambient d), IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => blowupMeasure n μ a (r (ρ j))) ν ∧
        GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
        (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
          ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
        ∀ x ∈ ν.support, 0 ≤ inner ℝ (a - c) x := by
  obtain ⟨a, ha, hac, hmin⟩ := exists_nearest_point_to_hole μ.support μ.isClosed_support
    (μ.nonempty_support hne) c hc
  obtain ⟨ρ, hρ, ν, hfinite, hneν, hlocal, hgν, hzero, hlowerν⟩ :=
    exists_blowup_measure_limit n μ C G hC hg hlower a ha r hr
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (r (ρ j))) :=
    fun j => globalGrowth_finite_on_compacts G _
      (blowupMeasure_growth n μ a (r (ρ j)) G (hr (ρ j)) hg)
  refine ⟨a, ha, hac, ρ, hρ, ν, hfinite, hneν, hlocal, hgν, hzero, hlowerν, ?_⟩
  apply compactTestConvergence_halfspace_of_quadratic_constraint
    (fun j => blowupMeasure n μ a (r (ρ j))) ν hlocal (a - c)
    (fun j => r (ρ j)) (fun j => (hr (ρ j)).le) (hr0.comp hρ.tendsto_atTop)
  intro j x hx
  apply nearest_point_rescaled_constraint a c x (r (ρ j)) (hr (ρ j))
  exact hmin (a + r (ρ j) • x)
    ((blowupMeasure_support_iff n μ a x (r (ρ j)) (hr (ρ j))).mp hx)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ShrinkingBallIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem measure_ball_tendsto_zero_of_growth {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (x : Ambient d) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0) := by
  have hbound : Tendsto (fun j => ENNReal.ofReal (C * r j ^ n)) atTop (𝓝 0) := by
    simpa only [zero_pow hn.ne', mul_zero, ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hr0.pow n).const_mul C)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun j => hg.2 x (r j) (hr j))

theorem local_integral_tendsto_zero_on_shrinking_balls {d : ℕ}
    (μ : Measure (Ambient d)) (f : Ambient d → ℝ) (x : Ambient d) (R : ℝ) (hR : 0 < R)
    (hi : IntegrableOn f (ball x R) μ) (r : ℕ → ℝ) (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun j => μ (ball x (r j))) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ y in ball x (r j), f y ∂μ) atTop (𝓝 0) := by
  have hrestrict : Tendsto (fun j => (μ.restrict (ball x R)) (ball x (r j))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass
      (fun _ => bot_le) (fun j => Measure.restrict_le_self (ball x (r j)))
  have hlim := hi.tendsto_setIntegral_nhds_zero hrestrict
  apply hlim.congr'
  filter_upwards [hr0.eventually (gt_mem_nhds hR)] with j hj
  rw [Measure.restrict_restrict measurableSet_ball,
    inter_eq_left.mpr (ball_subset_ball hj.le)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyFromTruncations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ENNReal

theorem nonnegative_integrable_of_exhaustion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (s : ℕ → Set X) (hs : ∀ k, MeasurableSet (s k)) (hmono : Monotone s)
    (hcover : Function.support f ⊆ ⋃ k, s k)
    (hI : ∀ k, IntegrableOn f (s k) μ) (B : ℝ)
    (hB : ∀ k, (∫ x in s k, f x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hpos
  have hfull : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (f x) ∂μ := by
    rw [← lintegral_indicator (MeasurableSet.iUnion hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ⋃ k, s k
    · rw [indicator_of_mem hx]
    · have hfx : f x = 0 := by
        by_contra h
        exact hx (hcover h)
      rw [indicator_of_notMem hx, hfx, ENNReal.ofReal_zero]
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [hfull, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k) (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hfin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hint : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnn).mp hfin
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg hpos).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hbound

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PositiveNormalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped ENNReal

theorem positiveNormalHeight_nonneg {d : ℕ} (e x : Ambient d) :
    0 ≤ positiveNormalHeight e x := le_max_left _ _

theorem positiveNormalHeight_le_norm {d : ℕ} (e x : Ambient d) :
    positiveNormalHeight e x ≤ ‖e‖ * ‖x‖ := by
  exact max_le (by positivity) (real_inner_le_norm e x)

theorem positiveNormalPotential_nonneg {d : ℕ} (n : ℕ) (e x : Ambient d) :
    0 ≤ positiveNormalPotential n e x :=
  div_nonneg (positiveNormalHeight_nonneg e x) (by positivity)

theorem positiveNormalPotential_zero {d : ℕ} (n : ℕ) (e : Ambient d) :
    positiveNormalPotential n e 0 = 0 := by
  simp [positiveNormalPotential, positiveNormalHeight]

theorem positiveNormalPotential_measurable {d : ℕ} (n : ℕ) (e : Ambient d) :
    Measurable (positiveNormalPotential n e) := by
  unfold positiveNormalPotential positiveNormalHeight
  fun_prop

theorem positiveNormalPotential_truncated_bound {d : ℕ} (n : ℕ) (e x : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) (hsmall : ε ≤ ‖x‖) (hlarge : ‖x‖ ≤ R) :
    positiveNormalPotential n e x ≤ (‖e‖ * R) * (ε ^ (n + 1))⁻¹ := by
  have hnum : positiveNormalHeight e x ≤ ‖e‖ * R :=
    (positiveNormalHeight_le_norm e x).trans (mul_le_mul_of_nonneg_left hlarge (norm_nonneg e))
  have hinv : (‖x‖ ^ (n + 1))⁻¹ ≤ (ε ^ (n + 1))⁻¹ := by
    simpa only [one_div] using! one_div_le_one_div_of_le (pow_pos hε (n + 1))
      (pow_le_pow_left₀ hε.le hsmall (n + 1))
  exact mul_le_mul hnum hinv (by positivity)
    (mul_nonneg (norm_nonneg e) ((norm_nonneg x).trans hlarge))

theorem positiveNormalPotential_integrableOn_truncated {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (ε R : ℝ) (hε : 0 < ε) :
    IntegrableOn (positiveNormalPotential n e)
      (ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}) μ := by
  apply Measure.integrableOn_of_bounded
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top).ne
    (positiveNormalPotential_measurable n e).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
  rw [Real.norm_of_nonneg (positiveNormalPotential_nonneg n e x)]
  exact positiveNormalPotential_truncated_bound n e x ε R hε hx.2.le
    (mem_ball_zero_iff.mp hx.1).le

theorem positiveNormalPotential_integrable_of_truncated_bounds {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (e : Ambient d) (R B : ℝ)
    (hB : ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ B) :
    IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R) μ ∧
      (∫ x in ball (0 : Ambient d) R, positiveNormalPotential n e x ∂μ) ≤ B := by
  apply nonnegative_integrable_of_exhaustion (μ.restrict (ball (0 : Ambient d) R))
    (positiveNormalPotential n e) (positiveNormalPotential_measurable n e)
    (positiveNormalPotential_nonneg n e)
    (fun k : ℕ => {x : Ambient d | (1 / 2 : ℝ) ^ k < ‖x‖})
    (fun _ => measurableSet_lt measurable_const continuous_norm.measurable)
  · intro k l hkl x hx
    have hp : (1 / 2 : ℝ) ^ l ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkl
    exact lt_of_le_of_lt hp hx
  · intro x hx
    have hne : x ≠ 0 := by
      intro h
      exact hx (h ▸ positiveNormalPotential_zero n e)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hne)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro k
    simpa only [IntegrableOn, Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      positiveNormalPotential_integrableOn_truncated n μ e ((1 / 2 : ℝ) ^ k) R (by positivity)
  · intro k
    simpa only [Measure.restrict_restrict
      (measurableSet_lt measurable_const continuous_norm.measurable), inter_comm] using!
      hB ((1 / 2 : ℝ) ^ k) (by positivity)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupNormalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal-height moments under blowup

Positive normal height is homogeneous of degree one. Combining this with the measure's
blowup normalization gives the moment scaling identity and bounds the rescaled height
integral by the positive normal potential on the original ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem positiveNormalHeight_continuous {d : ℕ} (e : Ambient d) :
    Continuous (positiveNormalHeight e) := by
  unfold positiveNormalHeight
  fun_prop

theorem positiveNormalHeight_smul {d : ℕ} (e x : Ambient d) (r : ℝ) (hr : 0 ≤ r) :
    positiveNormalHeight e (r • x) = r * positiveNormalHeight e x := by
  simp only [positiveNormalHeight, inner_smul_right, mul_max_of_nonneg _ _ hr, mul_zero]

theorem positiveNormalHeight_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (e : Ambient d) (R : ℝ) :
    IntegrableOn (positiveNormalHeight e) (ball (0 : Ambient d) R) μ :=
  ((positiveNormalHeight_continuous e).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Ambient d) R)).mono_set ball_subset_closedBall

theorem blowup_positiveNormalHeight_integral {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (r R : ℝ) (hr : 0 < r) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) =
      (r ^ (n + 1))⁻¹ * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), smul_eq_mul,
    setIntegral_map measurableSet_ball (positiveNormalHeight_continuous e).aestronglyMeasurable
      (by fun_prop), blowup_preimage_ball 0 0 r R hr]
  simp only [smul_zero, add_zero, sub_zero]
  simp_rw [positiveNormalHeight_smul e _ r⁻¹ (inv_nonneg.mpr hr.le)]
  rw [integral_const_mul, pow_succ, mul_inv]
  ring

theorem positiveNormalHeight_eq_potential_weight {d : ℕ} (n : ℕ) (e x : Ambient d) :
    positiveNormalHeight e x = ‖x‖ ^ (n + 1) * positiveNormalPotential n e x := by
  by_cases hx : x = 0
  · subst x
    simp [positiveNormalHeight, positiveNormalPotential]
  · have hn : ‖x‖ ^ (n + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    unfold positiveNormalPotential
    field_simp

theorem blowup_positiveNormalHeight_le_potential_integral {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] (e : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) (r * R)) μ) :
    (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 r) ≤
      R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
  have hbound : (∫ y in ball (0 : Ambient d) (r * R), positiveNormalHeight e y ∂μ) ≤
      (r * R) ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (positiveNormalHeight_integrableOn_ball μ e (r * R))
      (hi.const_mul ((r * R) ^ (n + 1)))
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [positiveNormalHeight_eq_potential_weight n e y]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg y) (mem_ball_zero_iff.mp hy).le (n + 1))
      (positiveNormalPotential_nonneg n e y)
  rw [blowup_positiveNormalHeight_integral n μ e r R hr]
  calc
    _ ≤ (r ^ (n + 1))⁻¹ * ((r * R) ^ (n + 1) *
        ∫ y in ball (0 : Ambient d) (r * R), positiveNormalPotential n e y ∂μ) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by
      rw [mul_pow]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BlowupNormalMomentDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem blowup_positiveNormalHeight_moments_tendsto_zero {d : ℕ}
    (n : ℕ) (hn : 0 < n) (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) atTop (𝓝 0) := by
  have hscale : Tendsto (fun j => r j * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using! hr0.mul_const R
  have hpot := local_integral_tendsto_zero_on_shrinking_balls μ (positiveNormalPotential n e)
    0 R₀ hR₀ hi (fun j => r j * R) hscale
      (measure_ball_tendsto_zero_of_growth n hn μ G hg 0 (fun j => r j * R)
        (fun j => mul_pos (hr j) hR) hscale)
  have hbound : ∀ᶠ j in atTop,
      (∫ x in ball (0 : Ambient d) R, positiveNormalHeight e x ∂blowupMeasure n μ 0 (r j)) ≤
        R ^ (n + 1) * ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ := by
    filter_upwards [hscale.eventually (gt_mem_nhds hR₀)] with j hj
    exact blowup_positiveNormalHeight_le_potential_integral n μ e (r j) R (hr j) hR
      (hi.mono_set (ball_subset_ball hj.le))
  have hright : Tendsto (fun j => R ^ (n + 1) *
      ∫ y in ball (0 : Ambient d) (r j * R), positiveNormalPotential n e y ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using! hpot.const_mul (R ^ (n + 1))
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    integral_nonneg (positiveNormalHeight_nonneg e)) hbound hright

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactLimitZeroMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported

theorem compactTestConvergence_support_zero_of_first_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (hmoment : ∀ R : ℝ, 0 < R →
      Tendsto (fun j => ∫ x in ball (0 : Ambient d) R, q x ∂μ j) atTop (𝓝 0)) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  have hR : 0 < ‖x‖ + 2 := by positivity
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall (0 : Ambient d) (‖x‖ + 1)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (by linarith : ‖x‖ + 1 < ‖x‖ + 2)))
  let F : C_c(Ambient d, ℝ) := ⟨⟨fun y => f y * q y, f.continuous.mul hq⟩, hcomp.mul_right⟩
  have hFnn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hbounds y).1 (hqnn y)
  have hbound : ∀ j, (∫ y, F y ∂μ j) ≤ ∫ y in ball (0 : Ambient d) (‖x‖ + 2), q y ∂μ j := by
    intro j
    have hi : IntegrableOn q (ball (0 : Ambient d) (‖x‖ + 2)) (μ j) :=
      (hq.continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Ambient d) (‖x‖ + 2))).mono_set ball_subset_closedBall
    rw [← integral_indicator measurableSet_ball]
    apply integral_mono (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)
      (hi.integrable_indicator measurableSet_ball)
    intro y
    by_cases hy : y ∈ ball (0 : Ambient d) (‖x‖ + 2)
    · simpa only [indicator_of_mem hy, one_mul] using!
        mul_le_mul_of_nonneg_right (hbounds y).2 (hqnn y)
    · change f y * q y ≤ _
      rw [hzero hy, Pi.zero_apply, zero_mul, indicator_of_notMem hy]
  have hle : (∫ y, F y ∂ν) ≤ 0 := le_of_tendsto_of_tendsto
    (hlocal F) (hmoment (‖x‖ + 2) hR) (Filter.Eventually.of_forall hbound)
  have heq : (∫ y, F y ∂ν) = 0 := le_antisymm hle (integral_nonneg hFnn)
  have hae : F =ᵐ[ν] (fun _ => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hFnn)
      (F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport)).mp heq
  have hpoint := ν.support_subset_of_isClosed (isClosed_eq F.continuous continuous_const) hae hx
  change f x * q x = 0 at hpoint
  rw [hone (show x ∈ closedBall (0 : Ambient d) (‖x‖ + 1) by
    simp only [mem_closedBall, dist_zero_right] <;> linarith), Pi.one_apply, one_mul] at hpoint
  exact hpoint

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NormalHyperplaneTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tangent measures supported on a normal hyperplane

Half-space support is preserved by centered blowups. Decay of positive normal moments
forces the limiting support onto the boundary hyperplane; growth compactness then
produces a nonzero tangent measure with this constraint and two-sided growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem blowup_support_in_halfspace {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ (blowupMeasure n μ 0 r).support, 0 ≤ inner ℝ e x := by
  intro x hx
  have hsource : r • x ∈ μ.support := by
    simpa only [zero_add] using! (blowupMeasure_support_iff n μ 0 x r hr).mp hx
  have h := hside (r • x) hsource
  rw [inner_smul_right] at h
  exact nonneg_of_mul_nonneg_right h hr

theorem blowup_limit_support_in_normal_hyperplane {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (e : Ambient d)
    (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hi : IntegrableOn (positiveNormalPotential n e) (ball (0 : Ambient d) R₀) μ)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ 0 (r j)) ν) :
    ∀ x ∈ ν.support, inner ℝ e x = 0 := by
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ 0 (r j)) :=
    fun j => globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ 0 (r j) G (hr j) hg)
  have hpositive := compactTestConvergence_support_zero_of_first_moments
    (fun j => blowupMeasure n μ 0 (r j)) ν hlocal (positiveNormalHeight e)
    (positiveNormalHeight_continuous e) (positiveNormalHeight_nonneg e)
    (blowup_positiveNormalHeight_moments_tendsto_zero n hn μ G hg e R₀ hR₀ hi r hr hr0)
  have hnegative : ∀ x ∈ ν.support, positiveNormalHeight (-e) x = 0 := by
    apply compactTestConvergence_support_zero_of_first_moments
      (fun j => blowupMeasure n μ 0 (r j)) ν hlocal (positiveNormalHeight (-e))
      (positiveNormalHeight_continuous (-e)) (positiveNormalHeight_nonneg (-e))
    intro R _hR
    have hzero : ∀ j, (∫ x in ball (0 : Ambient d) R,
        positiveNormalHeight (-e) x ∂blowupMeasure n μ 0 (r j)) = 0 := by
      intro j
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_of_ae (blowupMeasure n μ 0 (r j)).support_mem_ae] with x hx
      have h := blowup_support_in_halfspace n μ e hside (r j) (hr j) x hx
      simp only [positiveNormalHeight, inner_neg_left, max_eq_left (neg_nonpos.mpr h), Pi.zero_apply]
    simpa only [hzero] using! (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  intro x hx
  have hp := le_max_right (0 : ℝ) (inner ℝ e x)
  have hm := le_max_right (0 : ℝ) (inner ℝ (-e) x)
  change inner ℝ e x ≤ positiveNormalHeight e x at hp
  change inner ℝ (-e) x ≤ positiveNormalHeight (-e) x at hm
  rw [hpositive x hx] at hp
  rw [hnegative x hx, inner_neg_left] at hm
  linarith

theorem exists_nonzero_normal_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 0 < n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R₀ B : ℝ) (hR₀ : 0 < R₀)
    (hB : ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R₀ ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ B)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      ∀ x ∈ ν.support, inner ℝ e x = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hi := (positiveNormalPotential_integrable_of_truncated_bounds n μ e R₀ B hB).1
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν⟩ :=
    exists_blowup_measure_limit n μ C G hC hg hlower 0 hzero r hr
  let := hfinite
  exact ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν,
    blowup_limit_support_in_normal_hyperplane n hn μ ν G hg e hside R₀ hR₀ hi
      (fun j => r (ρ j)) (fun j => hr (ρ j)) (hr0.comp hρ.tendsto_atTop) hlocal⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BoundedSupportEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Energy of bounded functions with finite-measure support

Comparison with a constant indicator gives square integrability and an explicit
energy bound in terms of the uniform bound and the measure of the support set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem bounded_support_memLp_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfm : Measurable f)
    (S : Set X) (hS : MeasurableSet S) (hfin : μ S < ∞)
    (M : ℝ) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M) (hs : ∀ x, x ∉ S → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * μ.real S := by
  let g : X → ℝ := S.indicator (fun _ => M)
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa only [Measure.restrict_apply_univ] using! hfin⟩
  have hg : MemLp g 2 μ := (memLp_indicator_iff_restrict hS).mpr (memLp_const M)
  have hpoint (x : X) : |f x| ≤ |g x| := by
    by_cases hx : x ∈ S
    · simpa only [g, indicator_of_mem hx, abs_of_nonneg hM] using! hfM x
    · simp only [hs x hx, g, indicator_of_notMem hx, abs_zero, le_refl]
  have hf : MemLp f 2 μ := hg.of_le hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hpoint x)
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, g x ^ 2 ∂μ := integral_mono hf.integrable_sq hg.integrable_sq (fun x => by
      have hb := mul_self_le_mul_self (abs_nonneg (f x)) (hpoint x)
      simpa only [← pow_two, sq_abs] using! hb)
    _ = M ^ 2 * μ.real S := by
      have heq : (fun x => g x ^ 2) = S.indicator (fun _ => M ^ 2) := by
        funext x
        by_cases hx : x ∈ S <;> simp [g, hx]
      rw [heq, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]

theorem bounded_ball_support_energy {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (f : Ambient d → ℝ) (hfm : Measurable f) (a : Ambient d) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hfM : ∀ x, |f x| ≤ M)
    (hs : ∀ x, r ≤ dist x a → f x = 0) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ M ^ 2 * (G * r ^ n) := by
  have hm := hg.2 a r hr
  have hfin := lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  have hf := bounded_support_memLp_energy μ f hfm (ball a r) measurableSet_ball hfin M hM hfM
    (fun x hx => hs x (le_of_not_gt hx))
  refine ⟨hf.1, hf.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
  exact ENNReal.toReal_le_of_le_ofReal (by positivity [hg.1]) hm

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth annular and exterior weights

Differences of smooth ball cutoffs localize functions to annular regions.
Subtracting a cutoff from a finite-measure set indicator gives an exterior
weight with controlled size, square integrability, and distance from the center.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem smoothAnnularWeight_properties {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    MemLp (smoothAnnularWeight a r R hr (hr.trans_le hrR)) 2 μ ∧
    (∀ x, |smoothAnnularWeight a r R hr (hr.trans_le hrR) x| ≤ 1) ∧
    (∀ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ≠ 0 → r ≤ dist a x) ∧
    (∫ x, smoothAnnularWeight a r R hr (hr.trans_le hrR) x ^ 2 ∂μ) ≤ G * (2 * R) ^ n := by
  have hR := hr.trans_le hrR
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  have hm : Measurable (smoothAnnularWeight a r R hr hR) := hB.1.sub hb.1
  have hbound (x : Ambient d) : |smoothAnnularWeight a r R hr hR x| ≤ 1 := by
    have hl := (annularSmoothBallCutoff a r hr).nonneg (x := x)
    have hu := (annularSmoothBallCutoff a r hr).le_one (x := x)
    have hL := (annularSmoothBallCutoff a R hR).nonneg (x := x)
    have hU := (annularSmoothBallCutoff a R hR).le_one (x := x)
    unfold smoothAnnularWeight
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hs (x : Ambient d) (hx : 2 * R ≤ dist x a) : smoothAnnularWeight a r R hr hR x = 0 := by
    rw [smoothAnnularWeight, hB.2.2.2 x hx, hb.2.2.2 x (by linarith), sub_self]
  have he := bounded_ball_support_energy n G μ hg _ hm a (2 * R) 1 (by positivity)
    (by norm_num) hbound hs
  refine ⟨he.1, hbound, ?_, by simpa only [one_pow, one_mul] using! he.2⟩
  intro x hx
  by_contra hdist
  have hd : dist x a ≤ r := by rw [dist_comm]; exact (lt_of_not_ge hdist).le
  apply hx
  rw [smoothAnnularWeight, hB.2.2.1 x (hd.trans hrR), hb.2.2.1 x hd, sub_self]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SeparatedSmoothAnnuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric

theorem smoothAnnularWeight_nonneg_of_separated {d : ℕ}
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hsep : 2 * r ≤ R)
    (x : Ambient d) : 0 ≤ smoothAnnularWeight a r R hr hR x := by
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  unfold smoothAnnularWeight
  by_cases hx : dist x a ≤ R
  · rw [hB.2.2.1 x hx]
    exact sub_nonneg.mpr (annularSmoothBallCutoff a r hr).le_one
  · rw [hb.2.2.2 x (hsep.trans (le_of_not_ge hx))]
    simpa only [sub_zero] using! (annularSmoothBallCutoff a R hR).nonneg (x := x)

theorem smoothAnnularWeight_eq_one_on_middle {d : ℕ}
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (x : Ambient d) (hinner : 2 * r ≤ dist x a) (houter : dist x a ≤ R) :
    smoothAnnularWeight a r R hr hR x = 1 := by
  have hb := annularSmoothBallCutoff_basic a r hr
  have hB := annularSmoothBallCutoff_basic a R hR
  rw [smoothAnnularWeight, hB.2.2.1 x houter, hb.2.2.2 x hinner, sub_zero]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem smoothAnnularTransform_integrable {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Integrable (fun y => smoothAnnularWeight a r R hr (hr.trans_le hrR) y • kernel n a y) μ := by
  let g := smoothAnnularWeight a r R hr (hr.trans_le hrR)
  have hgp := smoothAnnularWeight_properties n G μ hg a r R hr hrR
  have hi := truncation_integrable_of_globalGrowth n hn G μ hg g hgp.1 a (r / 2) (by positivity)
  have hE : MeasurableSet {y | r / 2 < dist a y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : {y | r / 2 < dist a y}.indicator (fun y => g y • kernel n a y) =
      (fun y => g y • kernel n a y) := by
    funext y
    by_cases hy : r / 2 < dist a y
    · have hyE : y ∈ {y : Ambient d | r / 2 < dist a y} := hy
      exact indicator_of_mem hyE _
    · have hzero : g y = 0 := by
        by_contra hne
        have hd := hgp.2.2.1 y hne
        linarith
      have hyE : y ∉ {y : Ambient d | r / 2 < dist a y} := hy
      rw [indicator_of_notMem hyE, hzero, zero_smul]
  rw [← heq]
  exact hi.integrable_indicator hE

theorem exists_unit_bounded_norm_direction {d : ℕ} (v : Ambient d) :
    ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ inner ℝ e v = ‖v‖ := by
  by_cases hv : v = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ hn]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two]
      field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalAnnularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal components of annular kernel integrals

Away from the origin the Riesz kernel is integrable on bounded annuli. For measures
supported in a nonnegative half-space, its normal component equals the positive
normal potential, so vector integral bounds control the scalar potential integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem positiveNormalPotential_eq_kernel_component {d : ℕ} (n : ℕ) (e x : Ambient d)
    (hside : 0 ≤ inner ℝ e x) :
    positiveNormalPotential n e x = inner ℝ e (kernel n x 0) := by
  rw [positiveNormalPotential, positiveNormalHeight, max_eq_right hside,
    kernel, sub_zero, inner_smul_right]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularNormalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal potentials from smooth annular bounds

For a measure supported in a halfspace, pairing the smooth annular Riesz transform
with the normal identifies the weighted positive normal potential. Uniform bounds
on these transforms control truncated potential integrals and yield integrability
on the limiting ball, with bound `‖e‖ * B`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem smooth_annular_normal_pairing {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R) :
    Integrable (fun x => smoothAnnularWeight (0 : Ambient d) r R hr hR x * positiveNormalPotential n e x) μ ∧
    (∫ x, smoothAnnularWeight (0 : Ambient d) r R hr hR x * positiveNormalPotential n e x ∂μ) =
      -inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR) := by
  let g := smoothAnnularWeight (0 : Ambient d) r R hr hR
  have hk : Integrable (fun x => g x • kernel n 0 x) μ :=
    smoothAnnularTransform_integrable n hn G μ hg 0 r R hr hrR
  have hi : Integrable (fun x => inner ℝ e (g x • kernel n 0 x)) μ :=
    (innerSL ℝ e).integrable_comp hk
  have heq : (fun x => g x * positiveNormalPotential n e x) =ᵐ[μ]
      (fun x => -inner ℝ e (g x • kernel n 0 x)) := by
    filter_upwards [μ.support_mem_ae] with x hx
    rw [positiveNormalPotential_eq_kernel_component n e x (hside x hx),
      kernel_antisymm n x 0, smul_neg, inner_neg_right, neg_neg, real_inner_smul_right]
  refine ⟨hi.neg.congr heq.symm, ?_⟩
  calc
    _ = ∫ x, -inner ℝ e (g x • kernel n 0 x) ∂μ := integral_congr_ae heq
    _ = -inner ℝ e (∫ x, g x • kernel n 0 x ∂μ) := by
      rw [integral_neg]
      congr 1
      exact (innerSL ℝ e).integral_comp_comm hk
    _ = _ := rfl

theorem positiveNormalPotential_truncated_bound_of_smooth_annuli {d : ℕ}
    (n : ℕ) (hn : 1 ≤ n) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (e : Ambient d) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R B : ℝ) (hR : 0 < R)
    (hB : ∀ (r : ℝ) (hr : 0 < r), 2 * r ≤ R →
      ‖smoothAnnularTransform n μ 0 r R hr hR‖ ≤ B) :
    ∀ ε : ℝ, 0 < ε →
      (∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, positiveNormalPotential n e x ∂μ) ≤ ‖e‖ * B := by
  intro ε hε
  let r := min ε R / 4
  have hr : 0 < r := div_pos (lt_min hε hR) (by norm_num)
  have hsep : 2 * r ≤ R := by have hm := min_le_right ε R; dsimp [r] <;> linarith
  have heps : 2 * r ≤ ε := by have hm := min_le_left ε R; dsimp [r] <;> linarith
  let g := smoothAnnularWeight (0 : Ambient d) r R hr hR
  have hpair := smooth_annular_normal_pairing n hn G μ hg e hside r R hr hR (by linarith)
  have hnonneg (x : Ambient d) : 0 ≤ g x * positiveNormalPotential n e x :=
    mul_nonneg (smoothAnnularWeight_nonneg_of_separated 0 r R hr hR hsep x)
      (positiveNormalPotential_nonneg n e x)
  calc
    _ = ∫ x in ball (0 : Ambient d) R ∩ {x | ε < ‖x‖}, g x * positiveNormalPotential n e x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_ball.inter (measurableSet_lt measurable_const continuous_norm.measurable))] with x hx
      have hinner : 2 * r ≤ dist x (0 : Ambient d) := by simpa only [dist_zero_right] using! heps.trans hx.2.le
      have houter : dist x (0 : Ambient d) ≤ R := (mem_ball.mp hx.1).le
      have hg1 : g x = 1 := smoothAnnularWeight_eq_one_on_middle 0 r R hr hR x hinner houter
      rw [hg1, one_mul]
    _ ≤ ∫ x, g x * positiveNormalPotential n e x ∂μ :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hnonneg) hpair.1
    _ = -inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR) := hpair.2
    _ ≤ |inner ℝ e (smoothAnnularTransform n μ 0 r R hr hR)| := neg_le_abs _
    _ ≤ ‖e‖ * ‖smoothAnnularTransform n μ 0 r R hr hR‖ := by
      simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (smoothAnnularTransform n μ 0 r R hr hR)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB r hr hsep) (norm_nonneg e)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_SmoothAnnularHyperplaneTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_nonzero_smooth_annular_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (R₀ B : ℝ) (hR₀ : 0 < R₀)
    (hB : ∀ (r : ℝ) (hr : 0 < r), 2 * r ≤ R₀ →
      ‖smoothAnnularTransform n μ 0 r R₀ hr hR₀‖ ≤ B)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support := by
  have hpotential := positiveNormalPotential_truncated_bound_of_smooth_annuli n hn G μ hg
    e hside R₀ B hR₀ hB
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane⟩ :=
    exists_nonzero_normal_hyperplane_tangent n (by omega) μ C G hC hg hlower hzero e hside
      R₀ (‖e‖ * B) hR₀ hpotential r hr hr0
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, ?_⟩
  intro hesupp
  have hz := hplane e hesupp
  rw [real_inner_self_eq_norm_sq] at hz
  have hp := norm_pos_iff.mpr he
  nlinarith

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

theorem kernel_normalized {d : ℕ} (n : ℕ) (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    kernel n (r⁻¹ • (x - a)) (r⁻¹ • (y - a)) = r ^ n • kernel n x y := by
  have h := kernel_physicalAffine n a ((physicalAffine a r hr).symm x)
    ((physicalAffine a r hr).symm y) r hr
  rw [(physicalAffine a r hr).apply_symm_apply, (physicalAffine a r hr).apply_symm_apply] at h
  rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero n hr.ne'), one_smul]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactSmoothAnnularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported smooth annular kernel tests

Annular cutoffs remove the Riesz singularity and give compact support. Agreement
with a capped kernel proves continuity, so pairing with a fixed normal produces
a compactly supported continuous scalar test for weak limits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped CompactlySupported

theorem annularSmoothBallCutoff_translate {d : ℕ} (a : Ambient d)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    annularSmoothBallCutoff a r hr x =
      annularSmoothBallCutoff (0 : Ambient d) r hr (x - a) := by
  simp only [ContDiffBump.apply, annularSmoothBallCutoff, sub_zero]

theorem smoothAnnularWeight_translate {d : ℕ} (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (x : Ambient d) :
    smoothAnnularWeight a r R hr hR x = smoothAnnularWeight 0 r R hr hR (x - a) := by
  simp only [smoothAnnularWeight, annularSmoothBallCutoff_translate a]

theorem smoothAnnularKernel_translate {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (x : Ambient d) :
    smoothAnnularKernel n a r R hr hR x = smoothAnnularKernel n 0 r R hr hR (x - a) := by
  rw [smoothAnnularKernel, smoothAnnularKernel, smoothAnnularWeight_translate]
  congr 1
  simp only [kernel, zero_sub, neg_sub]

theorem smoothAnnularKernel_zero_far {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (x : Ambient d) (hx : 2 * R ≤ dist x a) :
    smoothAnnularKernel n a r R hr (hr.trans_le hrR) x = 0 := by
  rw [smoothAnnularKernel, smoothAnnularWeight,
    (annularSmoothBallCutoff_basic a R (hr.trans_le hrR)).2.2.2 x hx,
    (annularSmoothBallCutoff_basic a r hr).2.2.2 x (by linarith), sub_self, zero_smul]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem annularSmoothBallCutoff_physical {d : ℕ} (a b x : Ambient d)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    annularSmoothBallCutoff (a + s • b) (s * r) (mul_pos hs hr) (a + s • x) =
      annularSmoothBallCutoff b r hr x := by
  simp only [ContDiffBump.apply, annularSmoothBallCutoff, add_sub_add_left_eq_sub,
    ← smul_sub, smul_smul]
  have hratio : 2 * (s * r) / (s * r) = 2 * r / r := by field_simp
  have hcoef : (s * r)⁻¹ * s = r⁻¹ := by field_simp
  rw [hratio, hcoef]

theorem annularSmoothBallCutoff_normalized {d : ℕ} (a b x : Ambient d)
    (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    annularSmoothBallCutoff b r hr (s⁻¹ • (x - a)) =
      annularSmoothBallCutoff (a + s • b) (s * r) (mul_pos hs hr) x := by
  have hx : a + s • (s⁻¹ • (x - a)) = x := by
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    abel
  simpa only [hx] using!
    (annularSmoothBallCutoff_physical a b (s⁻¹ • (x - a)) s r hs hr).symm

theorem smoothAnnularWeight_normalized {d : ℕ} (a b x : Ambient d)
    (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularWeight b r R hr hR (s⁻¹ • (x - a)) =
      smoothAnnularWeight (a + s • b) (s * r) (s * R) (mul_pos hs hr) (mul_pos hs hR) x := by
  rw [smoothAnnularWeight, smoothAnnularWeight,
    annularSmoothBallCutoff_normalized a b x s R hs hR,
    annularSmoothBallCutoff_normalized a b x s r hs hr]

theorem smoothAnnularKernel_normalized {d : ℕ} (n : ℕ) (a b x : Ambient d)
    (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularKernel n b r R hr hR (s⁻¹ • (x - a)) =
      s ^ n • smoothAnnularKernel n (a + s • b) (s * r) (s * R)
        (mul_pos hs hr) (mul_pos hs hR) x := by
  have hc : s⁻¹ • ((a + s • b) - a) = b := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  have hk := kernel_normalized n a (a + s • b) x s hs
  rw [hc] at hk
  rw [smoothAnnularKernel, smoothAnnularKernel, smoothAnnularWeight_normalized a b x s r R hs hr hR, hk,
    smul_smul, smul_smul, mul_comm]

theorem smoothAnnularTransform_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a b : Ambient d) (s r R : ℝ) (hs : 0 < s) (hr : 0 < r) (hR : 0 < R) :
    smoothAnnularTransform n (blowupMeasure n μ a s) b r R hr hR =
      smoothAnnularTransform n μ (a + s • b) (s * r) (s * R)
        (mul_pos hs hr) (mul_pos hs hR) := by
  change (∫ x, smoothAnnularKernel n b r R hr hR x ∂blowupMeasure n μ a s) = _
  rw [blowupMeasure_integral n μ a s hs]
  simp_rw [smoothAnnularKernel_normalized n a b _ s r R hs hr hR]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero n hs.ne'), one_smul]
  rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_VaryingCompactTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ENNReal

theorem compactTest_integral_difference_bound {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f g : C_c(Ambient d, ℝ)) (S : Set (Ambient d))
    (hfin : μ S < ∞) (hzero : ∀ x, x ∉ S → f x = 0 ∧ g x = 0)
    (δ : ℝ) (hdiff : ∀ x, |f x - g x| ≤ δ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ δ * μ.real S := by
  have hf : Integrable (fun x => f x) μ :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (fun x => g x) μ :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  rw [← integral_sub hf hg]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
    (fun x hx => by rw [(hzero x hx).1, (hzero x hx).2, sub_self])]
  simpa only [Real.norm_eq_abs] using! norm_setIntegral_le_of_norm_le_const
    (f := fun x => f x - g x) (C := δ) hfin
    (fun x _ => by simpa only [Real.norm_eq_abs] using! hdiff x)

theorem compactTestConvergence_varying_tests {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] (hlocal : CompactTestConvergence μ ν)
    (f : ℕ → C_c(Ambient d, ℝ)) (g : C_c(Ambient d, ℝ))
    (S : Set (Ambient d)) (M : ℝ) (hM : 0 ≤ M)
    (hsupport : ∀ᶠ j in atTop, (μ j) S < ∞ ∧ (μ j).real S ≤ M ∧
      ∀ x, x ∉ S → f j x = 0 ∧ g x = 0)
    (huniform : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |f j x - g x| < ε) :
    Tendsto (fun j => ∫ x, f j x ∂μ j) atTop (𝓝 (∫ x, g x ∂ν)) := by
  have hdiff : Tendsto (fun j => (∫ x, f j x ∂μ j) - ∫ x, g x ∂μ j) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hMp : 0 < M + 1 := by linarith
    let δ := ε / (M + 1)
    have hδ : 0 < δ := div_pos hε hMp
    have hδM : δ * M < ε := by
      have heq : δ * (M + 1) = ε := div_mul_cancel₀ ε hMp.ne'
      nlinarith
    filter_upwards [hsupport, huniform δ hδ] with j hj hfj
    have hb := compactTest_integral_difference_bound (μ j) (f j) g S hj.1 hj.2.2 δ
      (fun x => (hfj x).le)
    have hbound := hb.trans (mul_le_mul_of_nonneg_left hj.2.1 hδ.le)
    simpa only [Real.dist_eq, sub_zero] using! hbound.trans_lt hδM
  have ht := hdiff.add (hlocal g)
  simpa only [sub_add_cancel, zero_add] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SmoothAnnularCenterLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth annular transforms with varying centers

Converging centers yield uniform convergence of the scalar annular tests and an
eventual common compact support. Together with uniform growth, these estimates
pass the smooth annular transform through weak limits of measures.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped CompactlySupported ENNReal

theorem scalarSmoothAnnularTest_center_uniform {d : ℕ} (n : ℕ) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x,
      |scalarSmoothAnnularTest n e (a j) r R hr hrR x -
        scalarSmoothAnnularTest n e b r R hr hrR x| < ε := by
  let F := scalarSmoothAnnularTest n e (0 : Ambient d) r R hr hrR
  have hF := F.hasCompactSupport.uniformContinuous_of_continuous F.continuous
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hF ε hε
  filter_upwards [Metric.tendsto_nhds.mp ha δ hδ] with j hj
  intro x
  have hd : dist (x - a j) (x - b) < δ := by
    simpa only [dist_sub_left] using! hj
  have ht := hmod hd
  change |inner ℝ e (smoothAnnularKernel n (a j) r R hr (hr.trans_le hrR) x) -
    inner ℝ e (smoothAnnularKernel n b r R hr (hr.trans_le hrR) x)| < ε
  rw [smoothAnnularKernel_translate n (a j), smoothAnnularKernel_translate n b]
  exact ht

theorem scalarSmoothAnnularTest_common_support {d : ℕ} (n : ℕ) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ᶠ j in atTop, ∀ x, x ∉ ball b (2 * R + 2) →
      scalarSmoothAnnularTest n e (a j) r R hr hrR x = 0 ∧
        scalarSmoothAnnularTest n e b r R hr hrR x = 0 := by
  filter_upwards [Metric.tendsto_nhds.mp ha 1 zero_lt_one] with j hj
  intro x hx
  have hxb : 2 * R + 2 ≤ dist x b := le_of_not_gt hx
  have hxa : 2 * R ≤ dist x (a j) := by
    have ht := dist_triangle x (a j) b
    linarith
  constructor
  · change inner ℝ e (smoothAnnularKernel n (a j) r R hr (hr.trans_le hrR) x) = 0
    rw [smoothAnnularKernel_zero_far n (a j) r R hr hrR x hxa, inner_zero_right]
  · change inner ℝ e (smoothAnnularKernel n b r R hr (hr.trans_le hrR) x) = 0
    rw [smoothAnnularKernel_zero_far n b r R hr hrR x (by linarith), inner_zero_right]

theorem scalarSmoothAnnularTest_integral {d : ℕ} (n : ℕ) (e a : Ambient d)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    (∫ x, scalarSmoothAnnularTest n e a r R hr hrR x ∂μ) =
      inner ℝ e (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)) := by
  have hi := (smoothAnnularKernel_continuous n a r R hr hrR).integrable_of_hasCompactSupport
    (smoothAnnularKernel_hasCompactSupport n a r R hr (hr.trans_le hrR)) (μ := μ)
  exact (innerSL ℝ e).integral_comp_comm hi

theorem smoothAnnularTransform_directional_tendsto {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (e : Ambient d)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Tendsto (fun j => inner ℝ e
      (smoothAnnularTransform n (μ j) (a j) r R hr (hr.trans_le hrR))) atTop
      (𝓝 (inner ℝ e (smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)))) := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  have hR : 0 < 2 * R + 2 := by linarith
  have hG : 0 ≤ G := (hg 0).1
  have hs : ∀ᶠ j in atTop, (μ j) (ball b (2 * R + 2)) < ∞ ∧
      (μ j).real (ball b (2 * R + 2)) ≤ G * (2 * R + 2) ^ n ∧
      ∀ x, x ∉ ball b (2 * R + 2) →
        scalarSmoothAnnularTest n e (a j) r R hr hrR x = 0 ∧
          scalarSmoothAnnularTest n e b r R hr hrR x = 0 := by
    filter_upwards [scalarSmoothAnnularTest_common_support n e a b ha r R hr hrR] with j hj
    have hm := (hg j).2 b (2 * R + 2) hR
    exact ⟨hm.trans_lt ENNReal.ofReal_lt_top,
      ENNReal.toReal_le_of_le_ofReal (by positivity) hm, hj⟩
  have ht := compactTestConvergence_varying_tests μ ν hlocal
    (fun j => scalarSmoothAnnularTest n e (a j) r R hr hrR)
    (scalarSmoothAnnularTest n e b r R hr hrR) (ball b (2 * R + 2))
    (G * (2 * R + 2) ^ n) (by positivity) hs
    (scalarSmoothAnnularTest_center_uniform n e a b ha r R hr hrR)
  simpa only [scalarSmoothAnnularTest_integral] using! ht

theorem smoothAnnularTransform_bound_of_center_limit {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν)
    (a : ℕ → Ambient d) (b : Ambient d) (ha : Tendsto a atTop (𝓝 b))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ᶠ j in atTop, ‖smoothAnnularTransform n (μ j) (a j) r R hr (hr.trans_le hrR)‖ ≤ B) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  obtain ⟨e, he, heq⟩ := exists_unit_bounded_norm_direction
    (smoothAnnularTransform n ν b r R hr (hr.trans_le hrR))
  rw [← heq]
  apply le_of_tendsto (smoothAnnularTransform_directional_tendsto n G μ ν hg hlocal e a b ha r R hr hrR)
  filter_upwards [hb] with j hj
  exact (real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa only [one_mul] using! hj))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_SmoothAnnularLimitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular transform bounds on limiting supports

Support-point approximants and moving-center convergence transfer eventual
uniform smooth annular bounds to support points of a weak limit inside an open set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem smoothAnnularTransform_bound_at_limit_support {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (U : Set (Ambient d)) (hU : IsOpen U)
    (b : Ambient d) (hbs : b ∈ ν.support) (hbU : b ∈ U)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hb : ∀ᶠ j in atTop, ∀ x ∈ (μ j).support, x ∈ U →
      ‖smoothAnnularTransform n (μ j) x r R hr (hr.trans_le hrR)‖ ≤ B) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  obtain ⟨φ, a, _, hφ, has, ha⟩ := compactTestConvergence_support_approximants μ ν hlocal b hbs
  have hc : CompactTestConvergence (μ ∘ φ) ν := fun f => (hlocal f).comp hφ
  apply smoothAnnularTransform_bound_of_center_limit n G B (μ ∘ φ) ν
    (fun j => hg (φ j)) hc a b ha r R hr hrR
  filter_upwards [hφ.eventually hb, ha.eventually (hU.mem_nhds hbU)] with j hj hja
  exact hj (a j) (has j) hja

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SmoothAnnularTangentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth annular bounds on tangent measures

Local bounds near the blowup center pass to every support point of a tangent measure.
Support approximants rescale into the original neighborhood, while their outer annular
radii shrink below the prescribed cap, allowing the moving-center limit bound to apply.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem smoothAnnularTransform_bound_on_tangent {d : ℕ} (n : ℕ) (G B cap : ℝ)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hg : GlobalUpperGrowth n G μ) (U : Set (Ambient d)) (hU : IsOpen U)
    (a : Ambient d) (ha : a ∈ U) (hcap : 0 < cap)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B)
    (b : Ambient d) (hbs : b ∈ ν.support) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  let μj := fun j => blowupMeasure n μ a (s j)
  have hgj (j : ℕ) : GlobalUpperGrowth n G (μj j) :=
    blowupMeasure_growth n μ a (s j) G (hs j) hg
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μj j) := globalGrowth_finite_on_compacts G (μj j) (hgj j)
  obtain ⟨φ, x, _, hφ, hxs, hx⟩ := compactTestConvergence_support_approximants μj ν hlocal b hbs
  have hscaled : Tendsto (fun j => a + s (φ j) • x j) atTop (𝓝 a) := by
    simpa only [zero_smul, add_zero] using!
      (tendsto_const_nhds (x := a)).add ((hs0.comp hφ).smul hx)
  have hscaledR : Tendsto (fun j => s (φ j) * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using! (hs0.comp hφ).mul_const R
  have hc : CompactTestConvergence (μj ∘ φ) ν := fun f => (hlocal f).comp hφ
  apply smoothAnnularTransform_bound_of_center_limit n G B (μj ∘ φ) ν
    (fun j => hgj (φ j)) hc x b hx r R hr hrR
  filter_upwards [hscaled.eventually (hU.mem_nhds ha),
    hscaledR.eventually (gt_mem_nhds hcap)] with j hjU hjR
  have hsupport : a + s (φ j) • x j ∈ μ.support :=
    (blowupMeasure_support_iff n μ a (x j) (s (φ j)) (hs (φ j))).mp (hxs j)
  change ‖smoothAnnularTransform n (blowupMeasure n μ a (s (φ j))) (x j)
    r R hr (hr.trans_le hrR)‖ ≤ B
  rw [smoothAnnularTransform_blowup n μ a (x j) (s (φ j)) r R (hs (φ j)) hr (hr.trans_le hrR)]
  exact hbound _ hsupport hjU _ _ (mul_pos (hs (φ j)) hr)
    (mul_le_mul_of_nonneg_left hrR (hs (φ j)).le) hjR

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_AnnularBoundedTangents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tangents with global smooth annular bounds

The global smooth annular bound is stable under blowups and compact-test limits.
This stability preserves the bound when extracting a nonzero tangent supported on a
proper hyperplane, so that the dimension-reduction argument can be iterated.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem GlobalSmoothAnnularBound.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (B : ℝ) (hB : GlobalSmoothAnnularBound n μ B) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    GlobalSmoothAnnularBound n (blowupMeasure n μ a s) B := by
  intro b hb r R hr hrR
  rw [smoothAnnularTransform_blowup n μ a b s r R hs hr (hr.trans_le hrR)]
  exact hB (a + s • b) ((blowupMeasure_support_iff n μ a b s hs).mp hb)
    (s * r) (s * R) (mul_pos hs hr) (mul_le_mul_of_nonneg_left hrR hs.le)

theorem GlobalSmoothAnnularBound.compact_limit {d : ℕ} (n : ℕ) (G B : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlocal : CompactTestConvergence μ ν) (hB : ∀ᶠ j in atTop, GlobalSmoothAnnularBound n (μ j) B) :
    GlobalSmoothAnnularBound n ν B := by
  intro b hb r R hr hrR
  apply smoothAnnularTransform_bound_at_limit_support n G B μ ν hg hlocal univ isOpen_univ
    b hb (mem_univ b) r R hr hrR
  filter_upwards [hB] with j hj
  intro x hx _
  exact hj x hx r R hr hrR

theorem GlobalSmoothAnnularBound.of_local_tangent {d : ℕ} (n : ℕ) (G B cap : ℝ)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hg : GlobalUpperGrowth n G μ) (U : Set (Ambient d)) (hU : IsOpen U)
    (a : Ambient d) (ha : a ∈ U) (hcap : 0 < cap)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B) :
    GlobalSmoothAnnularBound n ν B := by
  exact smoothAnnularTransform_bound_on_tangent n G B cap μ ν hg U hU a ha hcap
    s hs hs0 hlocal hbound

theorem exists_annular_bounded_hyperplane_tangent {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (μ : Measure (Ambient d)) (C G B : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support) (hB : GlobalSmoothAnnularBound n μ B)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support ∧
      GlobalSmoothAnnularBound n ν B := by
  have horigin : ∀ (t : ℝ) (ht : 0 < t), 2 * t ≤ 1 →
      ‖smoothAnnularTransform n μ 0 t 1 ht zero_lt_one‖ ≤ B := by
    intro t ht hsep
    exact hB 0 hzero t 1 ht (by linarith)
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper⟩ :=
    exists_nonzero_smooth_annular_hyperplane_tangent n hn μ C G hC hg hlower hzero e he hside
      1 B zero_lt_one horigin r hr hr0
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, ?_⟩
  apply GlobalSmoothAnnularBound.compact_limit n G B
    (fun j => blowupMeasure n μ 0 (r (ρ j))) ν
    (fun j => blowupMeasure_growth n μ 0 (r (ρ j)) G (hr (ρ j)) hg) hlocal
  exact Eventually.of_forall fun j => GlobalSmoothAnnularBound.blowup n μ B hB 0 (r (ρ j)) (hr (ρ j))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NonflatAnnularHyperplaneTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonflat hyperplane tangents with annular bounds

The hyperplane tangent construction retains both the global smooth annular bound and
a quantitative bilateral nonflatness bound. The latter passes through tangent formation
with the explicit loss from `ε` to `ε / 64`.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_nonflat_annular_hyperplane_tangent {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (C G B ε : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hzero : (0 : Ambient d) ∈ μ.support) (hB : GlobalSmoothAnnularBound n μ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hbad : GlobalBilateralLower n μ ε)
    (e : Ambient d) (he : e ≠ 0) (hside : ∀ x ∈ μ.support, 0 ≤ inner ℝ e x)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => blowupMeasure n μ 0 (r (ρ j))) ν ∧
      GlobalUpperGrowth n (G * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
      (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
        ENNReal.ofReal (R ^ n / (C * 4 ^ n)) ≤ ν (ball x R)) ∧
      (∀ x ∈ ν.support, inner ℝ e x = 0) ∧ e ∉ ν.support ∧
      GlobalSmoothAnnularBound n ν B ∧ GlobalBilateralLower n ν (ε / 64) := by
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, hBν⟩ :=
    exists_annular_bounded_hyperplane_tangent n hn μ C G B hC hg hlower hzero hB
      e he hside r hr hr0
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, hzeroν, hlowerν, hplane, hproper, hBν, ?_⟩
  exact GlobalBilateralLower.tangent hn hnd μ ν C G hC hg hlower 0 hzero
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocal ε hε hε1 hbad

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SubspaceTangentSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Subspace support of tangent measures

Compact-test convergence preserves containment of supports in a fixed closed set.
Blowups centered in a linear subspace stay in that subspace, so their limits inherit
the same support constraint. Intersecting with the normal hyperplane of a nonzero
subspace vector strictly reduces the dimension, as needed for dimension reduction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_support_subset_closed {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (E : Set (Ambient d)) (hE : IsClosed E)
    (hsub : ∀ j, (μ j).support ⊆ E) : ν.support ⊆ E := by
  intro b hb
  obtain ⟨φ, a, _, _, has, ha⟩ := compactTestConvergence_support_approximants μ ν hlocal b hb
  exact hE.mem_of_tendsto ha (Eventually.of_forall fun j => hsub (φ j) (has j))

theorem blowupMeasure_support_submodule {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (a : Ambient d) (ha : a ∈ P) (s : ℝ) (hs : 0 < s) :
    (blowupMeasure n μ a s).support ⊆ (P : Set (Ambient d)) := by
  intro x hx
  have hy := hP ((blowupMeasure_support_iff n μ a x s hs).mp hx)
  have hz := P.smul_mem s⁻¹ (P.sub_mem hy ha)
  simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using! hz

theorem blowup_limit_support_submodule {d : ℕ} (n : ℕ) (μ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (G : ℝ) (hg : GlobalUpperGrowth n G μ)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (a : Ambient d) (ha : a ∈ P) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν) :
    ν.support ⊆ (P : Set (Ambient d)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (s j)) := fun j =>
    globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  exact compactTestConvergence_support_subset_closed _ ν hlocal P P.closed_of_finiteDimensional
    (fun j => blowupMeasure_support_submodule n μ P hP a ha (s j) (hs j))

theorem normal_section_finrank_lt {d : ℕ} (P : Submodule ℝ (Ambient d))
    (e : Ambient d) (heP : e ∈ P) (he : e ≠ 0) :
    Module.finrank ℝ ↥(P ⊓ (innerSL ℝ e).toLinearMap.ker) < Module.finrank ℝ P := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply (lt_iff_le_not_ge).mpr
  refine ⟨inf_le_left, ?_⟩
  intro hle
  have hz := (hle heP).2
  change inner ℝ e e = 0 at hz
  rw [real_inner_self_eq_norm_sq] at hz
  have hp := norm_pos_iff.mpr he
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_RelativePlaneDimensionDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension drop inside a supporting plane

A hole in the support within a linear subspace gives a halfspace tangent and then a
hyperplane tangent. Their support lies in a strictly smaller subspace while retaining
growth, lower mass, annular bounds, and quantitative bilateral nonflatness.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_relative_plane_dimension_drop {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (hne : μ ≠ 0) (C G B ε : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hB : GlobalSmoothAnnularBound n μ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : GlobalBilateralLower n μ ε)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (c : Ambient d) (hcP : c ∈ P) (hc : c ∉ μ.support) :
    ∃ Q : Submodule ℝ (Ambient d), Module.finrank ℝ Q < Module.finrank ℝ P ∧
      ∃ ν : Measure (Ambient d), IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        GlobalUpperGrowth n ((G * 2 ^ n) * 2 ^ n) ν ∧ (0 : Ambient d) ∈ ν.support ∧
        (∀ x ∈ ν.support, ∀ R : ℝ, 0 < R →
          ENNReal.ofReal (R ^ n / ((C * 4 ^ n) * 4 ^ n)) ≤ ν (ball x R)) ∧
        ν.support ⊆ (Q : Set (Ambient d)) ∧ GlobalSmoothAnnularBound n ν B ∧
        GlobalBilateralLower n ν (ε / 4096) := by
  let r := fun j : ℕ => (1 / 2 : ℝ) ^ j
  have hr (j : ℕ) : 0 < r j := by dsimp only [r] <;> positivity
  have hr0 : Tendsto r atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨a, ha, hac, ρ, hρ, η, hfiniteη, hneη, hlocalη, hgη, hzeroη, hlowerη, hsideη⟩ :=
    exists_nonzero_halfspace_tangent_of_hole n μ hne C G hC hg hlower c hc r hr hr0
  let := hfiniteη
  have hηP := blowup_limit_support_submodule n μ η G hg P hP a (hP ha)
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocalη
  have hBη : GlobalSmoothAnnularBound n η B := by
    apply GlobalSmoothAnnularBound.compact_limit n G B
      (fun j => blowupMeasure n μ a (r (ρ j))) η
      (fun j => blowupMeasure_growth n μ a (r (ρ j)) G (hr (ρ j)) hg) hlocalη
    exact Eventually.of_forall fun j => GlobalSmoothAnnularBound.blowup n μ B hB a (r (ρ j)) (hr (ρ j))
  have hbadη := GlobalBilateralLower.tangent hn hnd μ η C G hC hg hlower a ha
    (fun j => r (ρ j)) (fun j => hr (ρ j)) hlocalη ε hε hε1 hbad
  have he : a - c ≠ 0 := sub_ne_zero.mpr hac
  have heP : a - c ∈ P := P.sub_mem (hP ha) hcP
  have hεη : 0 < ε / 64 := by positivity
  have hεη1 : ε / 64 ≤ 1 := by linarith
  obtain ⟨σ, _, ν, hfiniteν, hneν, hlocalν, hgν, hzeroν, hlowerν, hplaneν, _, hBν, hbadν⟩ :=
    exists_nonflat_annular_hyperplane_tangent hn hnd η (C * 4 ^ n) (G * 2 ^ n) B (ε / 64)
      (by positivity) hgη hlowerη hzeroη hBη hεη hεη1 hbadη (a - c) he hsideη r hr hr0
  let := hfiniteν
  have hνP := blowup_limit_support_submodule n η ν (G * 2 ^ n) hgη P hηP 0 P.zero_mem
    (fun j => r (σ j)) (fun j => hr (σ j)) hlocalν
  refine ⟨P ⊓ (innerSL ℝ (a - c)).toLinearMap.ker, normal_section_finrank_lt P (a - c) heP he,
    ν, hfiniteν, hneν, hgν, hzeroν, hlowerν, ?_, hBν, ?_⟩
  · intro x hx
    exact ⟨hνP hx, hplaneν x hx⟩
  · convert! hbadν using 1
    all_goals try with_reducible_and_instances rfl
    ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_AnnularDimensionTermination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem not_global_nonflat_annular_measure {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (hne : μ ≠ 0) (C G B ε : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hB : GlobalSmoothAnnularBound n μ B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ GlobalBilateralLower n μ ε := by
  have hmain : ∀ k : ℕ, ∀ (P : Submodule ℝ (Ambient d)) (σ : Measure (Ambient d))
      (A H η : ℝ), Module.finrank ℝ P = k → σ ≠ 0 → 0 < A →
      GlobalUpperGrowth n H σ →
      (∀ x ∈ σ.support, ∀ R : ℝ, 0 < R → ENNReal.ofReal (R ^ n / A) ≤ σ (ball x R)) →
      GlobalSmoothAnnularBound n σ B → 0 < η → η ≤ 1 → GlobalBilateralLower n σ η →
      σ.support ⊆ (P : Set (Ambient d)) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P σ A H η hdim hσ hA hH hl hAnn hη hη1 hbad hP
      obtain ⟨c, hcP, hc⟩ := GlobalBilateralLower.exists_relative_hole σ A H η hA hH hl hη hbad P hP
      obtain ⟨Q, hQ, ν, _, hν, hgν, _, hlν, hνQ, hAnnν, hbadν⟩ :=
        exists_relative_plane_dimension_drop hn hnd σ hσ A H B η hA hH hl hAnn hη hη1 hbad P hP c hcP hc
      exact ih (Module.finrank ℝ Q) (hQ.trans_eq hdim) Q ν
        ((A * 4 ^ n) * 4 ^ n) ((H * 2 ^ n) * 2 ^ n) (η / 4096) rfl hν
        (by positivity) hgν hlν hAnnν (by positivity) (by linarith) hbadν hνQ
  intro hbad
  exact hmain (Module.finrank ℝ (⊤ : Submodule ℝ (Ambient d))) ⊤ μ C G ε rfl
    hne hC hg hlower hB hε hε1 hbad (fun _ _ => Submodule.mem_top)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_LocalAnnularFlatBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local flat balls from annular bounds

Local smooth annular control and capped lower growth force arbitrarily small balls
with small bilateral beta number. Otherwise a tangent inherits global nonflatness and
annular control, contradicting termination of the supporting-plane dimension drop.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_local_flat_ball_of_annular_bound {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G H B annCap : ℝ) (μ : Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H)
    (hg : GlobalUpperGrowth n G μ) (hlower : CappedLowerGrowth n C H μ)
    (U : Set (Ambient d)) (hU : IsOpen U) (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U)
    (hAnnCap : 0 < annCap)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < annCap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B)
    (flatCap ε : ℝ) (hflatCap : 0 < flatCap) (hε : 0 < ε) :
    ∃ b ∈ μ.support, b ∈ U ∧ ∃ r : ℝ, 0 < r ∧ r < flatCap ∧ bilateralBeta n μ b r < ε := by
  by_contra hnone
  let s := fun j : ℕ => H * (1 / 2 : ℝ) ^ j
  have hs (j : ℕ) : 0 < s j := by dsimp only [s] <;> positivity
  have hsH (j : ℕ) : s j ≤ H := by
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) hH.le).trans_eq (mul_one H)
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul H
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, _, hlowerν⟩ :=
    exists_capped_lower_tangent n C G H μ hC hH hg hlower a ha s hs hsH hs0
  let := hfinite
  have hBν : GlobalSmoothAnnularBound n ν B :=
    GlobalSmoothAnnularBound.of_local_tangent n G B annCap μ ν hg U hU a haU hAnnCap
      (fun j => s (ρ j)) (fun j => hs (ρ j)) (hs0.comp hρ.tendsto_atTop) hlocal hbound
  have hbad : ∀ x ∈ μ.support, x ∈ U → ∀ r : ℝ, 0 < r → r < flatCap →
      min ε 1 ≤ bilateralBeta n μ x r := by
    intro x hx hxU r hr hrcap
    apply (min_le_left ε 1).trans
    exact le_of_not_gt (fun hb => hnone ⟨x, hx, hxU, r, hr, hrcap, hb⟩)
  have hbadν := global_bilateral_lower_of_capped_tangent hnd C G H flatCap (min ε 1) μ ν
    hC hg hlower U hU a haU (fun j => s (ρ j)) (fun j => hs (ρ j)) (fun j => hsH (ρ j))
    (hs0.comp hρ.tendsto_atTop) hlocal hflatCap (lt_min hε zero_lt_one) (min_le_right _ _) hbad
  exact not_global_nonflat_annular_measure hn hnd ν hne (C * 4 ^ n) (G * 2 ^ n) B
    (min ε 1 / 64) (by positivity) hgν hlowerν hBν
    (by positivity) (by linarith [min_le_right ε 1]) hbadν

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_FlatAnnularAlternativeEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem not_flat_ball_above_beta_lower {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap ε : ℝ) (hnot : ¬ HasFlatBallAbove n μ U ρ cap ε)
    (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U) (r : ℝ)
    (hr : 0 < r) (hρ : ρ ≤ r) (hcap : r < cap) : ε ≤ bilateralBeta n μ a r :=
  le_of_not_gt (fun h => hnot ⟨a, ha, haU, r, hr, hρ, hcap, h⟩)

theorem not_large_smooth_annulus_above_bound {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (U : Set (Ambient d)) (ρ cap B : ℝ) (hnot : ¬ HasLargeSmoothAnnulusAbove n μ U ρ cap B)
    (a : Ambient d) (ha : a ∈ μ.support) (haU : a ∈ U) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hρ : ρ ≤ r) (hcap : R < cap) :
    ‖smoothAnnularTransform n μ a r R hr (hr.trans_le hrR)‖ ≤ B :=
  le_of_not_gt (fun h => hnot ⟨a, ha, haU, r, R, hr, hrR, hρ, hcap, h⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_QuantitativeFlatAnnularAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform flat-ball or large-annulus alternative

Compactness upgrades the local annular flat-ball theorem to a radius chosen uniformly
before the measure. A counterexample sequence would converge to a measure with bounded
annular transforms but no admissible flat ball, contradicting the local theorem.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_uniform_flat_annular_radius {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G H B cap ε : ℝ) (hC : 0 < C) (hH : 0 < H) (hcap : 0 < cap) (hε : 0 < ε)
    (U : Set (Ambient d)) (hU : IsOpen U) (hzeroU : (0 : Ambient d) ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < cap ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ → CappedLowerGrowth n C H μ → (0 : Ambient d) ∈ μ.support →
      HasFlatBallAbove n μ U ρ cap ε ∨ HasLargeSmoothAnnulusAbove n μ U ρ cap B := by
  by_contra hnone
  have hcounter (ρ : ℝ) (hρ : 0 < ρ) (hρcap : ρ < cap) :
      ∃ μ : Measure (Ambient d), GlobalUpperGrowth n G μ ∧ CappedLowerGrowth n C H μ ∧
        (0 : Ambient d) ∈ μ.support ∧ ¬ HasFlatBallAbove n μ U ρ cap ε ∧
          ¬ HasLargeSmoothAnnulusAbove n μ U ρ cap B := by
    by_contra hno
    apply hnone
    refine ⟨ρ, hρ, hρcap, ?_⟩
    intro μ hg hl hz
    by_contra hneither
    exact hno ⟨μ, hg, hl, hz, (not_or.mp hneither).1, (not_or.mp hneither).2⟩
  let rseq := fun j : ℕ => (cap / 2) * (1 / 2 : ℝ) ^ j
  have hrseq (j : ℕ) : 0 < rseq j := by dsimp only [rseq] <;> positivity
  have hrseqcap (j : ℕ) : rseq j < cap := by
    have hhalf : rseq j ≤ cap / 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)).trans_eq
        (mul_one (cap / 2))
    linarith
  have hrseq0 : Tendsto rseq atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (cap / 2)
  choose μ hg hl hz hflat hann using fun j => hcounter (rseq j) (hrseq j) (hrseqcap j)
  obtain ⟨τ, hτ, ν, hfinite, _, hlocal, hgν, hlν, hzν⟩ :=
    exists_capped_lower_measure_limit n C G H μ hC hH hg hl hz
  let := hfinite
  let : ∀ j, IsFiniteMeasureOnCompacts (μ (τ j)) := fun j =>
    globalGrowth_finite_on_compacts G _ (hg (τ j))
  have hrseqτ : Tendsto (fun j => rseq (τ j)) atTop (𝓝 0) := hrseq0.comp hτ.tendsto_atTop
  have hannν : ∀ x ∈ ν.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n ν x r R hr (hr.trans_le hrR)‖ ≤ B := by
    intro x hx hxU r R hr hrR hRcap
    apply smoothAnnularTransform_bound_at_limit_support n G B (fun j => μ (τ j)) ν
      (fun j => hg (τ j)) hlocal U hU x hx hxU r R hr hrR
    filter_upwards [hrseqτ.eventually (gt_mem_nhds hr)] with j hj
    intro y hy hyU
    exact not_large_smooth_annulus_above_bound n (μ (τ j)) U (rseq (τ j)) cap B (hann (τ j))
      y hy hyU r R hr hrR hj.le hRcap
  have hbadν : ∀ x ∈ ν.support, x ∈ U → ∀ r : ℝ, 0 < r → r < cap →
      min ε 1 / 64 ≤ bilateralBeta n ν x r := by
    intro x hx hxU r hr hrcap
    have hbadj : ∀ᶠ j in atTop, ∀ y ∈ (μ (τ j)).support, y ∈ U →
        min ε 1 ≤ bilateralBeta n (μ (τ j)) y (r / 2) := by
      filter_upwards [hrseqτ.eventually (gt_mem_nhds (by positivity : 0 < r / 2))] with j hj
      intro y hy hyU
      exact (min_le_left ε 1).trans
        (not_flat_ball_above_beta_lower n (μ (τ j)) U (rseq (τ j)) cap ε (hflat (τ j))
          y hy hyU (r / 2) (by positivity) hj.le (by linarith))
    have ht := compactTestConvergence_capped_beta_lower hnd C H (fun j => μ (τ j)) ν
      hlocal hC hH (fun j => hl (τ j)) U hU (min ε 1) (lt_min hε zero_lt_one) (min_le_right _ _)
      (r / 2) (by positivity) hbadj x hx hxU
    simpa only [mul_div_cancel₀ r (by norm_num : (2 : ℝ) ≠ 0)] using! ht
  obtain ⟨b, hb, hbU, r, hr, hrcap, hsmall⟩ :=
    exists_local_flat_ball_of_annular_bound hn hnd (C * 4 ^ n) (G * 2 ^ n) H B cap ν
      (by positivity) hH hgν hlν U hU 0 hzν hzeroU hcap hannν cap (min ε 1 / 64) hcap (by positivity)
  exact (not_lt_of_ge (hbadν b hb hbU r hr hrcap)) hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PhysicalFlatAnnularAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem HasFlatBallAbove.to_physical {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s ρ cap ε : ℝ) (hs : 0 < s)
    (hflat : HasFlatBallAbove n (blowupMeasure n μ a s) (ball 0 cap) ρ cap ε) :
    HasFlatBallAbove n μ (ball a (s * cap)) (s * ρ) (s * cap) ε := by
  obtain ⟨b, hb, hbU, r, hr, hρr, hrcap, hbeta⟩ := hflat
  refine ⟨a + s • b, (blowupMeasure_support_iff n μ a b s hs).mp hb, ?_,
    s * r, mul_pos hs hr, mul_le_mul_of_nonneg_left hρr hs.le,
    mul_lt_mul_of_pos_left hrcap hs, ?_⟩
  · change dist (a + s • b) a < s * cap
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    apply mul_lt_mul_of_pos_left _ hs
    simpa only [mem_ball, dist_zero_right] using! hbU
  · rwa [← bilateralBeta_blowup_at n μ a b s r hs]

theorem HasLargeSmoothAnnulusAbove.to_physical {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (s ρ cap B : ℝ) (hs : 0 < s)
    (hann : HasLargeSmoothAnnulusAbove n (blowupMeasure n μ a s) (ball 0 cap) ρ cap B) :
    HasLargeSmoothAnnulusAbove n μ (ball a (s * cap)) (s * ρ) (s * cap) B := by
  obtain ⟨b, hb, hbU, r, R, hr, hrR, hρr, hRcap, hnorm⟩ := hann
  refine ⟨a + s • b, (blowupMeasure_support_iff n μ a b s hs).mp hb, ?_,
    s * r, s * R, mul_pos hs hr, mul_le_mul_of_nonneg_left hrR hs.le,
    mul_le_mul_of_nonneg_left hρr hs.le, mul_lt_mul_of_pos_left hRcap hs, ?_⟩
  · change dist (a + s • b) a < s * cap
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    apply mul_lt_mul_of_pos_left _ hs
    simpa only [mem_ball, dist_zero_right] using! hbU
  · rwa [smoothAnnularTransform_blowup n μ a b s r R hs hr (hr.trans_le hrR)] at hnorm

theorem exists_uniform_physical_flat_annular_radius {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ a ∈ μ.support, ∀ s : ℝ, 0 < s → AdmissibleRadius μ (s / 8) →
      HasFlatBallAbove n μ (ball a (s / 16)) (ρ * s) (s / 16) ε ∨
        HasLargeSmoothAnnulusAbove n μ (ball a (s / 16)) (ρ * s) (s / 16) B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_flat_annular_radius hn hnd C G (1 / 8) B (1 / 16) ε
    hC (by norm_num) (by norm_num) hε (ball (0 : Ambient d) (1 / 16)) isOpen_ball
    (mem_ball_self (by norm_num))
  refine ⟨ρ, hρ, hρcap, ?_⟩
  intro μ hg hlower a ha s hs hcore
  have hl : CappedLowerGrowth n C (s / 8) μ := by
    intro x hx r hr hrs
    exact hlower x hx r ⟨hr, (ENNReal.ofReal_le_ofReal hrs).trans hcore.2⟩
  have hlscaled : CappedLowerGrowth n C (1 / 8) (blowupMeasure n μ a s) := by
    have ht := CappedLowerGrowth.blowup n C (s / 8) μ hl a s hs
    have heq : (s / 8) / s = (1 / 8 : ℝ) := by field_simp
    simpa only [heq] using! ht
  rcases hchoose (blowupMeasure n μ a s) (blowupMeasure_growth n μ a s G hs hg) hlscaled
    (blowupMeasure_origin_mem_support n μ a s hs ha) with hflat | hann
  · left
    simpa only [mul_one_div, mul_comm s ρ] using! HasFlatBallAbove.to_physical n μ a s ρ (1 / 16) ε hs hflat
  · right
    simpa only [mul_one_div, mul_comm s ρ] using!
      HasLargeSmoothAnnulusAbove.to_physical n μ a s ρ (1 / 16) B hs hann

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_CellFlatAnnularAlternative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_cell_flat_annular_alternative_oai {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
        (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) ε ∨
        HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_physical_flat_annular_radius hn hnd C G B ε hC hε
  refine ⟨ρ, hρ, hρcap, ?_⟩
  intro μ hg hlower R₀ hR₀ k z hcore
  have hs := latticeRadius_pos R₀ hR₀ k
  rcases hchoose μ hg hlower z (supportLatticeCenter μ R₀ hR₀ k z).property
    (latticeRadius R₀ k) hs hcore with hflat | hann
  · exact Or.inl hflat
  · right
    obtain ⟨a, ha, hanear, r, R, hr, hrR, hρr, hRcap, hnorm⟩ := hann
    have hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8 := by
      have ht : dist a (z : Ambient d) < latticeRadius R₀ k / 16 := hanear
      linarith
    let W : CellAnnulus μ R₀ hR₀ k z ρ :=
      { center := a, center_mem := ha, center_dist := hnear,
        innerRadius := r, outerRadius := R, inner_pos := hr, inner_le_outer := hrR,
        inner_lower := hρr, outer_upper := by linarith }
    exact ⟨W, hnorm.le⟩

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative_oai := @OAI.RieszRectifiability.exists_uniform_cell_flat_annular_alternative_oai
