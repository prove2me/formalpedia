-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:49.262402+00:00
-- url     : https://prove2.me/submissions/df1d6cc6-87b2-465d-ba6b-ed639f1e925e

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_RegularLatticeScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Filter Topology

theorem latticeRadius_zero (R : ℝ) : latticeRadius R 0 = R := by simp [latticeRadius]

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

theorem supportLatticeExceptional_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) : MeasurableSet (supportLatticeExceptional μ R hR) :=
  MeasurableSet.iUnion (supportLatticeOverlap_measurable μ R hR)

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    MeasurableSet (cleanSupportCell μ R hR k z) :=
  (supportLatticeCell_closed μ R hR k z).measurableSet.diff
    (supportLatticeExceptional_measurable μ R hR)

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

theorem cleanSupportCell_measure_pos_finite {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    0 < μ (cleanSupportCell μ R hR k z) ∧ μ (cleanSupportCell μ R hR k z) < ∞ := by
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  exact ⟨(ENNReal.ofReal_pos.mpr (div_pos (pow_pos hcore.1 n) hC)).trans_le hb.1,
    hb.2.trans_lt ENNReal.ofReal_lt_top⟩

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

theorem annularLatticeDepth_radius_lower (R : ℝ) (hR : 0 < R) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ 8 * latticeRadius R k) :
    r ≤ 512 * latticeRadius R (k + annularLatticeDepth R k r hr) := by
  generalize hd : annularLatticeDepth R k r hr = t
  cases t with
  | zero =>
    simp only [Nat.add_zero]
    have hp := latticeRadius_pos R hR k
    linarith
  | succ t =>
    have hp : r / 8 < latticeRadius R (k + t) := by
      by_contra hbad
      have hm := annularLatticeDepth_minimal R k r hr t (le_of_not_gt hbad)
      rw [hd] at hm
      omega
    rw [← Nat.add_assoc, latticeRadius_succ]
    linarith

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

theorem cleanSupportCell_pair_distance_le {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x y : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hy : y ∈ cleanSupportCell μ R hR k z) :
    dist x y ≤ 4 * latticeRadius R k := by
  have hxz := (supportLatticeCell_bounds μ R hR k z).2 hx.1
  have hyz := (supportLatticeCell_bounds μ R hR k z).2 hy.1
  change dist x (z : Ambient d) ≤ 2 * latticeRadius R k at hxz
  change dist y (z : Ambient d) ≤ 2 * latticeRadius R k at hyz
  have ht := dist_triangle_right x y (z : Ambient d)
  linarith

theorem exists_pair_scale_support_descendant {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (x y : Ambient d)
    (hx : x ∈ cleanSupportCell μ R hR k z)
    (hy : y ∈ cleanSupportCell μ R hR k z) (hne : x ≠ y) :
    ∃ i : SupportCellDescendant μ R hR k z,
      x ∈ i.cell ∧ i.radius ≤ dist x y / 8 ∧ dist x y ≤ 512 * i.radius ∧
        x ∈ ball i.center (1024 * i.radius) ∧
        y ∈ ball i.center (1024 * i.radius) := by
  have hdist : 0 < dist x y := dist_pos.mpr hne
  let t := annularLatticeDepth R k (dist x y) hdist
  obtain ⟨i, hi, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx t
  have hu : i.radius ≤ dist x y / 8 := by
    simpa only [SupportCellDescendant.radius, hi.1, t] using!
      annularLatticeDepth_radius_upper R k (dist x y) hdist
  have htop : dist x y ≤ 8 * latticeRadius R k := by
    have hb := cleanSupportCell_pair_distance_le μ R hR k z x y hx hy
    have hr := latticeRadius_pos R hR k
    linarith
  have hl : dist x y ≤ 512 * i.radius := by
    simpa only [SupportCellDescendant.radius, hi.1, t] using!
      annularLatticeDepth_radius_lower R hR k (dist x y) hdist htop
  have hxcenter := i.dist_center_of_mem x hi.2
  have hxycenter := dist_triangle y x i.center
  rw [dist_comm y x] at hxycenter
  have hr := i.radius_pos
  refine ⟨i, hi.2, hu, hl, ?_, ?_⟩
  · rw [mem_ball]
    linarith
  · rw [mem_ball]
    linarith

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

theorem cellRegionLimit_measurable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    MeasurableSet (cellRegionLimit μ R hR k z Good) := by
  let := supportCellDescendant_countable μ R hR k z
  have heq : cellRegionLimit μ R hR k z Good =
      cleanSupportCell μ R hR k z \ ⋃ i : {i // ¬Good i}, i.val.cell := by
    ext x
    simp only [cellRegionLimit, mem_ofPred_eq, mem_sdiff, mem_iUnion, not_exists]
    constructor
    · rintro ⟨hx, hall⟩
      exact ⟨hx, fun i hi => i.property (hall i.val hi)⟩
    · rintro ⟨hx, hbad⟩
      refine ⟨hx, ?_⟩
      intro i hi
      by_contra hnot
      exact hbad ⟨i, hnot⟩ hi
  rw [heq]
  exact (cleanSupportCell_measurable μ R hR k z).diff
    (MeasurableSet.iUnion fun i => cleanSupportCell_measurable μ R hR
      (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩)

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

theorem cellRegionLimit_disjoint_stops {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good) :
    Disjoint (cellRegionLimit μ R hR k z Good) i.cell := by
  apply Set.disjoint_left.mpr
  intro x hx hxi
  exact hi.1 (hx.2 i hxi)

theorem cleanSupportCell_eq_region_limit_union_stops {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    cleanSupportCell μ R hR k z = cellRegionLimit μ R hR k z Good ∪
      ⋃ i : cellRegionStops μ R hR k z Good, i.val.cell := by
  ext x
  constructor
  · intro hx
    by_cases hgood : x ∈ cellRegionLimit μ R hR k z Good
    · exact Or.inl hgood
    · obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell μ R hR k z Good x hx hgood
      exact Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  · rintro (hx | hx)
    · exact hx.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact i.val.cell_subset_top hi

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellRegionMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass decomposition for a cell region

The clean root cell splits into the region limit and the pairwise disjoint stopping
cells. Countability of descendants and measurability of the cells turn this partition
into an exact identity between the root mass, the limit mass, and the sum of stop masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem cellRegion_mass_identity {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    μ (cleanSupportCell μ R hR k z) = μ (cellRegionLimit μ R hR k z Good) +
      ∑' i : cellRegionStops μ R hR k z Good, μ i.val.cell := by
  let := supportCellDescendant_countable μ R hR k z
  have hd : Pairwise (fun i j : cellRegionStops μ R hR k z Good => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    exact cellRegionStops_pairwise_disjoint μ R hR k z Good i.property j.property
      (fun heq => hij (Subtype.ext heq))
  have hm : ∀ i : cellRegionStops μ R hR k z Good, MeasurableSet i.val.cell :=
    fun i => cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hs : Disjoint (cellRegionLimit μ R hR k z Good)
      (⋃ i : cellRegionStops μ R hR k z Good, i.val.cell) := by
    apply Set.disjoint_left.mpr
    intro x hx hstop
    obtain ⟨i, hi⟩ := mem_iUnion.mp hstop
    exact Set.disjoint_left.mp
      (cellRegionLimit_disjoint_stops μ R hR k z Good i.val i.property) hx hi
  conv_lhs => rw [cleanSupportCell_eq_region_limit_union_stops μ R hR k z Good]
  rw [measure_union hs (MeasurableSet.iUnion hm), measure_iUnion hd hm]

theorem cellRegion_stopping_mass_le_top {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (∑' i : cellRegionStops μ R hR k z Good, μ i.val.cell) ≤ μ (cleanSupportCell μ R hR k z) := by
  rw [cellRegion_mass_identity μ R hR k z Good]
  exact le_add_left le_rfl

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_AdjacentCellPlaneDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing planes at adjacent cell scales

The factor of sixty-four between parent and child radii allows bilateral approximation
to transfer plane tubes across adjacent cells. A local plane comparison then bounds the
component of each child-plane direction orthogonal to the parent-plane direction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem SupportCellDescendant.radius_parent_eq_64 {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hdepth : i.depth = q.depth + 1) :
    q.radius = 64 * i.radius := by
  change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
  rw [hdepth, ← Nat.add_assoc, latticeRadius_succ]
  ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ContractedDirectionTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A linear map that contracts a unit direction sends vectors close to a lower-dimensional subspace.
Orthogonal projection extends this estimate to the image of a tube around a subspace.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem contracted_direction_image_near_lower_subspace
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →ₗ[ℝ] F) (u : E) (hu : ‖u‖ = 1)
    (κ : ℝ) (hκ : 0 ≤ κ) (hTu : ‖T u‖ ≤ κ) :
    ∃ Q : Submodule ℝ F, Module.finrank ℝ Q < Module.finrank ℝ E ∧
      ∀ x : E, ∃ y ∈ Q, dist (T x) y ≤ κ * ‖x‖ := by
  let W : Submodule ℝ E := (ℝ ∙ u)ᗮ
  let Q := W.map T
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W < Module.finrank ℝ E := by
    have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton hu0] at h
    change 1 + Module.finrank ℝ W = Module.finrank ℝ E at h
    omega
  refine ⟨Q, (Submodule.finrank_map_le T W).trans_lt hdim, ?_⟩
  intro x
  let v := x - inner ℝ u x • u
  have hv : v ∈ W := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    dsimp [v]
    simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      hu, one_pow, mul_one, sub_self]
  have hinner : |inner ℝ u x| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs, hu, one_mul] using! norm_inner_le_norm (𝕜 := ℝ) u x
  refine ⟨T v, ⟨v, hv, rfl⟩, ?_⟩
  calc
    dist (T x) (T v) = ‖inner ℝ u x • T u‖ := by
      rw [dist_eq_norm, ← map_sub]
      have hsub : x - v = inner ℝ u x • u := by dsimp [v]; abel
      rw [hsub, map_smul]
    _ = |inner ℝ u x| * ‖T u‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |inner ℝ u x| * κ := mul_le_mul_of_nonneg_left hTu (abs_nonneg _)
    _ ≤ ‖x‖ * κ := mul_le_mul_of_nonneg_right hinner hκ
    _ = κ * ‖x‖ := mul_comm _ _

theorem contracted_plane_tube_image_subset {n d : ℕ}
    (S : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ S = n)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ) (R δ : ℝ) :
    ∃ Q : Submodule ℝ (Ambient n), Module.finrank ℝ Q < n ∧
      T '' affineTube S.toAffineSubspace R δ ⊆
        affineTube Q.toAffineSubspace R (δ + κ * R) := by
  obtain ⟨Q, hQ, hnear⟩ := contracted_direction_image_near_lower_subspace
    (T.comp S.subtype) u hu κ hκ hTu
  refine ⟨Q, hdim ▸ hQ, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
  let p : S := S.orthogonalProjectionOnto x
  have hpx : dist x (p : Ambient d) < δ := by
    change ‖x - S.starProjection x‖ < δ
    have heq : x - S.starProjection x = Sᗮ.starProjection x := by
      have h := S.starProjection_add_starProjection_orthogonal x
      exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
    rw [heq, ← submodule_infDist_eq_normal_projection S x]
    exact hx.2
  have hpR : ‖p‖ ≤ R := (S.norm_starProjection_apply_le x).trans hxR
  obtain ⟨y, hy, hpy⟩ := hnear p
  have hTxp : dist (T x) (T (p : Ambient d)) ≤ dist x (p : Ambient d) := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hT _
  have hTxy : dist (T x) y < δ + κ * R := by
    have ht := dist_triangle (T x) (T (p : Ambient d)) y
    have hb : dist (T (p : Ambient d)) y ≤ κ * R :=
      hpy.trans (mul_le_mul_of_nonneg_left hpR hκ)
    linarith
  refine ⟨?_, (infDist_le_dist_of_mem hy).trans_lt hTxy⟩
  change dist (T x) 0 ≤ R
  simpa only [dist_zero_right] using! (hT x).trans hxR

theorem contracted_plane_tube_image_real_measure_bound {n d : ℕ}
    (S : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ S = n)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (μ : Measure (Ambient n)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    μ.real (T '' affineTube S.toAffineSubspace R δ) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * ((δ + κ * R) / R) * R ^ n := by
  obtain ⟨Q, hQ, hsub⟩ := contracted_plane_tube_image_subset S hdim T hT u hu κ hκ hTu R δ
  let τ := (δ + κ * R) / R
  have hτ : 0 < τ := div_pos (by positivity) hR
  have hτ1 : τ ≤ 1 := (div_le_one hR).mpr hwidth
  have hw : τ * R = δ + κ * R := div_mul_cancel₀ _ hR.ne'
  have hplane : IsAffineNPlane (Module.finrank ℝ Q) Q.toAffineSubspace := by
    refine ⟨⟨0, Q.zero_mem⟩, ?_⟩
    rw [Submodule.toAffineSubspace_direction]
  have hbound := lower_dimensional_affineTube_bound μ C hg Q.toAffineSubspace
    hplane hQ R τ hR hτ hτ1
  have hfinite : μ (affineTube Q.toAffineSubspace R (δ + κ * R)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact affineTube_measure_bound μ C hg Q.toAffineSubspace hplane R (δ + κ * R)
      hR.le (by positivity)
  calc
    _ ≤ μ.real (affineTube Q.toAffineSubspace R (δ + κ * R)) :=
      ENNReal.toReal_mono hfinite (measure_mono hsub)
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ (Module.finrank ℝ Q)) * τ * R ^ n := by
      simpa only [hw] using! hbound
    _ ≤ (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * τ * R ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR.le n)
      apply mul_le_mul_of_nonneg_right _ hτ.le
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hQ.le)
        (mul_nonneg hg.1 (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ContractedAffinePatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Failure of a lower norm bound produces a contracted unit direction. Translating an affine patch
into a linear tube then gives a mass estimate for its image under the contracting map.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem exists_contracted_unit_direction_of_not_lower {d e : ℕ}
    (S : Submodule ℝ (Ambient d)) (T : Ambient d →ₗ[ℝ] Ambient e) (κ : ℝ)
    (hnot : ¬ ∀ v : S, κ * ‖v‖ ≤ ‖T (v : Ambient d)‖) :
    ∃ u : S, ‖u‖ = 1 ∧ ‖T (u : Ambient d)‖ < κ := by
  push Not at hnot
  obtain ⟨v, hv⟩ := hnot
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let u : S := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs]
    change |‖v‖⁻¹| * ‖v‖ = 1
    rw [abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  refine ⟨u, hu, ?_⟩
  change ‖T (‖v‖⁻¹ • (v : Ambient d))‖ < κ
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have h := mul_lt_mul_of_pos_left hv (inv_pos.mpr hn)
  simpa only [← mul_assoc, inv_mul_cancel_left₀ hn.ne', mul_comm κ] using! h

theorem infDist_translated_affine_direction {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (b : Ambient d) (hb : b ∈ S) (x : Ambient d) :
    infDist (x - b) (S.direction : Set (Ambient d)) = infDist x (S : Set (Ambient d)) := by
  have hp := affine_projection_difference S x b
  rw [orthogonalProjection_eq_self_iff.mpr hb] at hp
  have hn : (x - b) - S.direction.starProjection (x - b) =
      (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - b) := by
    have h := S.direction.starProjection_add_starProjection_orthogonal (x - b)
    exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
  rw [submodule_infDist_eq_normal_projection, ← hn, ← hp, sub_sub_sub_cancel_right]
  exact (dist_orthogonalProjection_eq_infDist S x)

theorem translated_affine_patch_subset_tube {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ) :
    (fun x => x - b) '' A ⊆ affineTube S.direction.toAffineSubspace R δ := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · change dist (x - b) 0 ≤ R
    rw [dist_zero_right, ← dist_eq_norm]
    exact (dist_triangle x c b).trans ((add_le_add (hA hx) hcenter).trans hrad)
  · change infDist (x - b) (S.direction : Set (Ambient d)) < δ
    rw [infDist_translated_affine_direction S b hb x]
    exact hheight x hx

theorem contracted_affine_patch_translated_real_measure_bound {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (μ : Measure (Ambient n)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ)
    (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    μ.real ((fun x => T (x - b)) '' A) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * ((δ + κ * R) / R) * R ^ n := by
  let : Nonempty S := hS.1.to_subtype
  have hsub : (fun x => T (x - b)) '' A ⊆
      T '' affineTube S.direction.toAffineSubspace R δ := by
    rw [← Set.image_image]
    exact Set.image_mono (translated_affine_patch_subset_tube S b c hb A r a R δ
      hA hcenter hrad hheight)
  have hball : T '' affineTube S.direction.toAffineSubspace R δ ⊆ ball 0 (2 * R) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
    rw [mem_ball, dist_zero_right]
    exact (hT x).trans_lt (by linarith)
  have hfinite : μ (T '' affineTube S.direction.toAffineSubspace R δ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hball).trans (hg.2 0 (2 * R) (by positivity)))
  exact (ENNReal.toReal_mono hfinite (measure_mono hsub)).trans
    (contracted_plane_tube_image_real_measure_bound S.direction hS.2 T hT u hu
      κ hκ hTu μ C hg R δ hR hδ hwidth)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NativeHausdorffGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal Pointwise

theorem ambient_closedBall_hausdorffMeasure (n : ℕ) (a : Ambient n)
    (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall a r) =
      (ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n := by
  have hd : 0 ≤ (n : ℝ) := by positivity
  have htranslate := (IsometryEquiv.addRight a).isometry.hausdorffMeasure_image
    (Or.inl hd) (closedBall (0 : Ambient n) r)
  rw [(IsometryEquiv.addRight a).image_closedBall] at htranslate
  change (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall (0 + a) r) = _ at htranslate
  rw [zero_add] at htranslate
  rw [htranslate]
  have hscale := Measure.hausdorffMeasure_smul₀ (𝕜 := ℝ) hd hr.ne'
    (closedBall (0 : Ambient n) 1)
  have hnorm : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
    rw [← Real.toNNReal_eq_nnnorm_of_nonneg hr.le]
    rfl
  simpa only [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le,
    mul_one, NNReal.rpow_natCast, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_pow, hnorm, planeUnitHausdorffMeasure] using! hscale

theorem native_hausdorff_global_upper_growth (n : ℕ) :
    GlobalUpperGrowth n (planeUnitHausdorffMeasure n).toReal
      (μH[(n : ℝ)] : Measure (Ambient n)) := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  intro x r hr
  have hbound := measure_mono (ball_subset_closedBall (x := x) (ε := r))
    (μ := (μH[(n : ℝ)] : Measure (Ambient n)))
  rw [ambient_closedBall_hausdorffMeasure n x r hr] at hbound
  convert! hbound using 1
  all_goals try with_reducible_and_instances rfl
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (planeUnitHausdorffMeasure_lt_top n).ne,
    ENNReal.ofReal_pow hr.le]
  exact mul_comm _ _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_ContractedAffineHausdorffPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem contracted_affine_patch_hausdorff_image_bound {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ)
    (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' A) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        ((δ + κ * R) / R) * R ^ n) := by
  let ν := (μH[(n : ℝ)] : Measure (Ambient n))
  let C := (planeUnitHausdorffMeasure n).toReal
  have hg := native_hausdorff_global_upper_growth n
  have hreal := contracted_affine_patch_translated_real_measure_bound S hS T hT u hu
    κ hκ hTu ν C hg b c hb A r a R δ hA hcenter hrad hheight hR hδ hwidth
  have htranslate : ν ((fun x => T (x - b)) '' A) = ν (T '' A) := by
    have h := (IsometryEquiv.addRight (-T b)).isometry.hausdorffMeasure_image
      (Or.inl (show 0 ≤ (n : ℝ) by positivity)) (T '' A)
    rw [Set.image_image] at h
    change ν ((fun x => T x + -T b) '' A) = ν (T '' A) at h
    simpa only [map_sub, sub_eq_add_neg, map_add, map_neg] using! h
  have hball : (fun x => T (x - b)) '' A ⊆ ball 0 (2 * R) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxb : ‖x - b‖ ≤ R := by
      rw [← dist_eq_norm]
      exact (dist_triangle x c b).trans ((add_le_add (hA hx) hcenter).trans hrad)
    rw [mem_ball, dist_zero_right]
    exact (hT _).trans_lt (by linarith)
  have hfinite : ν ((fun x => T (x - b)) '' A) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hball).trans (hg.2 0 (2 * R) (by positivity)))
  change (ν ((fun x => T (x - b)) '' A)).toReal ≤ _ at hreal
  rw [htranslate] at hreal hfinite
  rw [← ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hreal

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CappedStopPairScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_good_pair_cell_for_stop_center {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z Good) (hpositive : 0 < i.depth)
    (y : Ambient d) (hy : y ∈ cleanSupportCell μ R hR k z)
    (hsep : i.radius ≤ 8 * dist i.center y) :
    ∃ q : SupportCellDescendant μ R hR k z, Good q ∧ i.center ∈ q.cell ∧
      q.radius ≤ 512 * dist i.center y ∧ dist i.center y ≤ 512 * q.radius ∧
      i.center ∈ ball q.center (1024 * q.radius) ∧ y ∈ ball q.center (1024 * q.radius) := by
  have hD : 0 < dist i.center y := by have h := i.radius_pos; linarith
  let t := annularLatticeDepth R k (dist i.center y) hD
  let m := min t (i.depth - 1)
  obtain ⟨q, hq, hsub, hcenter⟩ := i.exists_ancestor_at_depth m (by dsimp [m]; omega)
  have hgood : Good q := hi.2 q (by dsimp [m] at hq; omega) hsub
  have hlower : dist i.center y ≤ 512 * q.radius := by
    have htop : dist i.center y ≤ 8 * latticeRadius R k := by
      have h := cleanSupportCell_pair_distance_le μ R hR k z i.center y
        (i.cell_subset_top i.center_mem_cell) hy
      have hr := latticeRadius_pos R hR k
      linarith
    have hscale := annularLatticeDepth_radius_lower R hR k (dist i.center y) hD htop
    have hle : latticeRadius R (k + t) ≤ q.radius := by
      apply latticeRadius_antitone R hR.le
      dsimp [m] at hq
      omega
    change dist i.center y ≤ 512 * latticeRadius R (k + t) at hscale
    linarith
  have hupper : q.radius ≤ 512 * dist i.center y := by
    by_cases ht : t ≤ i.depth - 1
    · have hqt : q.depth = t := by simpa only [m, min_eq_left ht] using! hq
      have h := annularLatticeDepth_radius_upper R k (dist i.center y) hD
      change latticeRadius R (k + t) ≤ dist i.center y / 8 at h
      change latticeRadius R (k + q.depth) ≤ _
      rw [hqt]
      linarith
    · have hqi : q.depth = i.depth - 1 := by
        simpa only [m, min_eq_right (le_of_not_ge ht)] using! hq
      have hscale := i.radius_parent_eq_64 q (by omega)
      linarith
  have hxc := q.dist_center_of_mem i.center hcenter
  have htri := dist_triangle y i.center q.center
  rw [dist_comm y i.center] at htri
  have hr := q.radius_pos
  refine ⟨q, hgood, hcenter, hupper, hlower, ?_, ?_⟩
  · rw [mem_ball]
    linarith
  · rw [mem_ball]
    linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_RegionRepresentativeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cellRegionRepresentatives_subset_top {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    cellRegionRepresentatives μ R hR k z Good ⊆ cleanSupportCell μ R hR k z := by
  rintro x (hx | ⟨i, rfl⟩)
  · exact hx.1
  · exact i.val.cell_subset_top i.val.center_mem_cell

theorem stop_radius_le_representative_distance {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ cellRegionStops μ R hR k z Good)
    (y : Ambient d) (hy : y ∈ cellRegionRepresentatives μ R hR k z Good) (hne : i.center ≠ y) :
    i.radius ≤ 8 * dist i.center y := by
  rcases hy with hy | ⟨j, rfl⟩
  · simpa only [dist_comm y i.center] using! cellRegionLimit_stop_center_separated μ R hR k z Good i hi y hy
  · have hij : i ≠ j.val := fun h => hne (congrArg SupportCellDescendant.center h)
    exact (le_max_left i.radius j.val.radius).trans
      (cellRegionStops_centers_separated μ R hR k z Good i j.val hi j.property hij)

theorem exists_good_pair_cell_for_representatives {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (x y : Ambient d) (hx : x ∈ cellRegionRepresentatives μ R hR k z Good)
    (hy : y ∈ cellRegionRepresentatives μ R hR k z Good) (hne : x ≠ y) :
    ∃ q : SupportCellDescendant μ R hR k z, Good q ∧ x ∈ q.cell ∧
      q.radius ≤ 512 * dist x y ∧ dist x y ≤ 512 * q.radius ∧
      x ∈ ball q.center (1024 * q.radius) ∧ y ∈ ball q.center (1024 * q.radius) := by
  have hytop := cellRegionRepresentatives_subset_top μ R hR k z Good hy
  rcases hx with hx | ⟨i, rfl⟩
  · obtain ⟨q, hxq, hupper, hlower, hxball, hyball⟩ :=
      exists_pair_scale_support_descendant μ R hR k z x y hx.1 hytop hne
    exact ⟨q, hx.2 q hxq, hxq, by linarith [dist_nonneg (x := x) (y := y)], hlower, hxball, hyball⟩
  · have hpositive : 0 < i.val.depth := Nat.pos_of_ne_zero (fun h => i.property.1 (hroot i.val h))
    exact exists_good_pair_cell_for_stop_center μ R hR k z Good i.val i.property hpositive y hytop
      (stop_radius_le_representative_distance μ R hR k z Good i.val i.property y hy hne)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteMassSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem retained_mass_ge_of_double_fraction {m a : ℝ≥0∞} (hm : m ≠ ⊤) (ha : a ≤ m)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (h : ENNReal.ofReal (2 * θ) * m ≤ a + ENNReal.ofReal θ * m) :
    ENNReal.ofReal θ * m ≤ a := by
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hm ha
  have hright : a + ENNReal.ofReal θ * m ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hright h
  rw [ENNReal.toReal_add hat (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * θ), ENNReal.toReal_ofReal hθ] at hr
  apply (ENNReal.toReal_le_toReal (by finiteness) hat).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ]
  nlinarith

theorem cellRegion_stopping_mass_contraction {d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (hfinite : ν (cleanSupportCell ν R hR k z) ≠ ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hretain : ENNReal.ofReal θ * ν (cleanSupportCell ν R hR k z) ≤
      ν (cellRegionLimit ν R hR k z Good)) :
    (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
      ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z) := by
  have hpart := cellRegion_mass_identity ν R hR k z Good
  have hstop := cellRegion_stopping_mass_le_top ν R hR k z Good
  have harea : ν (cellRegionLimit ν R hR k z Good) ≤ ν (cleanSupportCell ν R hR k z) :=
    measure_mono (fun _ hx => hx.1)
  have ha : ν (cellRegionLimit ν R hR k z Good) ≠ ⊤ := ne_top_of_le_ne_top hfinite harea
  have hs : (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hstop
  have hreal := congrArg ENNReal.toReal hpart
  rw [ENNReal.toReal_add ha hs] at hreal
  have hret := ENNReal.toReal_mono ha hretain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ] at hret
  apply (ENNReal.toReal_le_toReal hs (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1)]
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_NoncollapsingPlaneProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Noncollapsing projections of pairwise plane approximations

A contraction bounded below on an approximating plane separates nearby points
up to the plane-fitting error. Under a quantitative smallness condition, this
separation yields a Lipschitz ball map covering a set with pairwise plane fits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped NNReal

theorem projection_lower_bound_of_pairwise_plane {d e : ℕ}
    (T : Ambient d →L[ℝ] Ambient e) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hlower : ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖T v‖) :
    (κ - 2 * ε * (κ + 1)) * dist x y ≤ dist (T x) (T y) := by
  let sx : Ambient d := orthogonalProjection S x
  let sy : Ambient d := orthogonalProjection S y
  let w := sx - sy
  let a := (x - y) - w
  have hw : w ∈ S.direction :=
    AffineSubspace.vsub_mem_direction (orthogonalProjection_mem x) (orthogonalProjection_mem y)
  have ha : ‖a‖ ≤ 2 * ε * dist x y := by
    have hid : a = (x - sx) - (y - sy) := by dsimp [a, w]; abel
    calc
      _ = ‖(x - sx) - (y - sy)‖ := by rw [hid]
      _ ≤ ‖x - sx‖ + ‖y - sy‖ := norm_sub_le _ _
      _ = infDist x (S : Set (Ambient d)) + infDist y (S : Set (Ambient d)) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact congrArg₂ (· + ·) (dist_orthogonalProjection_eq_infDist S x)
          (dist_orthogonalProjection_eq_infDist S y)
      _ ≤ _ := by linarith
  have hsplit : x - y = w + a := by dsimp [a]; abel
  have hdist : dist x y ≤ ‖w‖ + ‖a‖ := by
    rw [dist_eq_norm, hsplit]
    exact norm_add_le _ _
  have hTw : ‖T w‖ ≤ dist (T x) (T y) + ‖a‖ := by
    have hw' : w = (x - y) - a := by dsimp [a]; abel
    calc
      _ = ‖T (x - y) - T a‖ := by rw [hw', map_sub]
      _ ≤ ‖T (x - y)‖ + ‖T a‖ := norm_sub_le _ _
      _ ≤ dist (T x) (T y) + ‖a‖ := by
        rw [map_sub, ← dist_eq_norm]
        exact add_le_add le_rfl (hT a)
  have hscaled := mul_le_mul_of_nonneg_left hdist hκ
  have herr := mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ κ + 1)
  nlinarith [hlower w hw]

theorem projection_separates_of_lower_bound {d e : ℕ}
    (T : Ambient d →L[ℝ] Ambient e) (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (x y : Ambient d) (ε κ : ℝ) (hκ : 0 < κ)
    (hsmall : 4 * ε * (κ + 1) ≤ κ)
    (hT : ∀ v, ‖T v‖ ≤ ‖v‖)
    (hx : infDist x (S : Set (Ambient d)) ≤ ε * dist x y)
    (hy : infDist y (S : Set (Ambient d)) ≤ ε * dist x y)
    (hlower : ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖T v‖) :
    dist x y ≤ (2 / κ) * dist (T x) (T y) := by
  have h := projection_lower_bound_of_pairwise_plane T S x y ε κ hκ.le hT hx hy hlower
  have hs := mul_le_mul_of_nonneg_right hsmall (dist_nonneg (x := x) (y := y))
  have hhalf : κ * dist x y ≤ 2 * dist (T x) (T y) := by nlinarith
  have hdiv := (le_div_iff₀ hκ).mpr (by nlinarith : dist x y * κ ≤ 2 * dist (T x) (T y))
  convert! hdiv using 1; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NoncollapsingRegionRepresentatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection separation of region representatives

A good cell containing two region representatives supplies a common fitted
plane. Its noncollapsing projection estimate and the tube error bound give
quantitative separation of the representatives after projection.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem projection_separates_noncollapsing_region_representatives {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (hroot : ∀ i : SupportCellDescendant μ R hR k z, i.depth = 0 → Good i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ) (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hfit : ∀ i : SupportCellDescendant μ R hR k z, Good i →
      ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
        (∀ w ∈ ball i.center (1024 * i.radius), w ∈ μ.support →
          infDist w (S : Set (Ambient d)) ≤ σ * i.radius) ∧
        ∀ v ∈ S.direction, κ * ‖v‖ ≤ ‖P.starProjection v‖) :
    ∀ x ∈ cellRegionRepresentatives μ R hR k z Good,
    ∀ y ∈ cellRegionRepresentatives μ R hR k z Good,
      dist x y ≤ (2 / κ) * dist (P.starProjection x) (P.starProjection y) := by
  intro x hx y hy
  by_cases hxy : x = y
  · simp only [hxy, dist_self, mul_zero, le_refl]
  obtain ⟨q, hgood, _, hupper, _, hxball, hyball⟩ :=
    exists_good_pair_cell_for_representatives μ R hR k z Good hroot x y hx hy hxy
  obtain ⟨S, hS, htube, hlower⟩ := hfit q hgood
  let : Nonempty S := hS.1.to_subtype
  have hxμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hx).1
  have hyμ := supportLatticeCell_subset_support μ R hR k z
    (cellRegionRepresentatives_subset_top μ R hR k z Good hy).1
  have hb : σ * q.radius ≤ (512 * σ) * dist x y := by
    have h := mul_le_mul_of_nonneg_left hupper hσ
    nlinarith
  have hxS := (htube x hxball hxμ).trans hb
  have hyS := (htube y hyball hyμ).trans hb
  exact projection_separates_of_lower_bound P.starProjection S x y (512 * σ) κ hκ
    (by nlinarith) (fun v => P.norm_starProjection_apply_le v) hxS hyS hlower

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FiniteFamilyRetractionCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_bounded_ball_cover_of_finite_family {n d : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (N : ℕ) (hN : Fintype.card ι ≤ N)
    (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (f : ι → ball (0 : Ambient n) r → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (f i)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d N M) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      ∀ i, closedBall a (3 * r) ∩ Set.range (f i) ⊆ Set.range g := by
  obtain ⟨p, hp, hpRange, hpFix⟩ := exists_nonexpansive_retraction_of_complete_convex
    (closedBall a (3 * r)) ⟨a, mem_closedBall_self (by positivity)⟩
    isClosed_closedBall.isComplete (convex_closedBall a (3 * r))
  let f' (i : ι) := p ∘ f i
  have hLip' : ∀ i, LipschitzWith M (f' i) := by
    intro i
    simpa only [one_mul] using! hp.comp (hLip i)
  have hRange' : ∀ i, Set.range (f' i) ⊆ closedBall a (3 * r) := by
    intro i y hy
    obtain ⟨u, rfl⟩ := hy
    exact hpRange (f i u)
  obtain ⟨h, hh, hcover⟩ := exists_ball_lipschitz_cover_of_bounded_finite_family hn N hN r hr a f' M hLip' hRange'
  refine ⟨p ∘ h, ?_, ?_, ?_⟩
  · simpa only [one_mul] using! hp.comp hh
  · rintro y ⟨u, rfl⟩
    exact hpRange (h u)
  · intro i y hy
    obtain ⟨u, hu⟩ := hy.2
    have hy' : y ∈ Set.range (f' i) := by
      refine ⟨u, ?_⟩
      change p (f i u) = y
      rw [hu, hpFix y hy.1]
    obtain ⟨v, hv⟩ := hcover (mem_iUnion.mpr ⟨i, hy'⟩)
    refine ⟨v, ?_⟩
    change p (h v) = y
    rw [hv, hpFix y hy.1]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionConditionedRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem cellProjectionNoncollapse_root {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (κ : ℝ) (hκ : κ ≤ 1) (i : SupportCellDescendant μ R hR k z) (hi : i.depth = 0) :
    cellProjectionNoncollapse S (S (supportCellRoot μ R hR k z)).direction κ i := by
  rw [i.eq_root_of_zero_depth hi]
  intro v hv
  rw [(S (supportCellRoot μ R hR k z)).direction.starProjection_eq_self_iff.mpr hv]
  simpa only [one_mul] using! mul_le_mul_of_nonneg_right hκ (norm_nonneg v)

theorem projection_conditioned_stop_contracted_unit {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (P : Submodule ℝ (Ambient d)) (κ : ℝ)
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ cellRegionStops μ R hR k z (cellProjectionNoncollapse S P κ)) :
    ∃ u : (S i).direction, ‖u‖ = 1 ∧ ‖P.starProjection (u : Ambient d)‖ < κ := by
  apply exists_contracted_unit_direction_of_not_lower (S i).direction P.starProjection.toLinearMap κ
  intro h
  apply hi.1
  intro v hv
  exact h ⟨v, hv⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionDiskCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Euclidean coordinates for projection disks

An orthonormal basis identifies a finite-dimensional subspace with Euclidean
space. Composing this isometry with orthogonal projection preserves projection
norms and transfers coverage of closed disks into these coordinates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_projection_disk_coordinates {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n) :
    ∃ T : Ambient d →L[ℝ] Ambient n,
      (∀ x, ‖T x‖ = ‖P.starProjection x‖) ∧
      (∀ x, ‖T x‖ ≤ ‖x‖) ∧
      ∀ (A : Set (Ambient d)) (p : Ambient d) (r : ℝ),
        closedBall (P.orthogonalProjectionOnto p) r ⊆ P.orthogonalProjectionOnto '' A →
          closedBall (T p) r ⊆ T '' A := by
  let b : OrthonormalBasis (Fin n) ℝ P :=
    (stdOrthonormalBasis ℝ P).reindex (finCongr hdim)
  let E : P ≃ₗᵢ[ℝ] Ambient n := b.repr
  let T : Ambient d →L[ℝ] Ambient n :=
    E.toLinearIsometry.toContinuousLinearMap.comp P.orthogonalProjectionOnto
  have hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖ := by
    intro x
    change ‖E (P.orthogonalProjectionOnto x)‖ = _
    rw [E.norm_map]
    rfl
  refine ⟨T, hnorm, fun x => (hnorm x).trans_le (P.norm_starProjection_apply_le x), ?_⟩
  intro A p r hcover u hu
  have hu' : E.symm u ∈ closedBall (P.orthogonalProjectionOnto p) r := by
    change dist (E.symm u) (P.orthogonalProjectionOnto p) ≤ r
    rw [← E.dist_map, E.apply_symm_apply]
    exact hu
  obtain ⟨x, hx, heq⟩ := hcover hu'
  refine ⟨x, hx, ?_⟩
  change E (P.orthogonalProjectionOnto x) = u
  rw [heq, E.apply_symm_apply]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FittedCellShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An affine fit places a lattice cell in a thin neighborhood of a plane.
Contraction along one plane direction bounds the Hausdorff measure of the cell's image.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem fitted_cell_contracted_shadow_bound {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (i : SupportCellDescendant ν R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S) (hcenter : i.center ∈ S)
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (hTu : ‖T (u : Ambient d)‖ ≤ κ) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.cell) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        (σ + κ) * (2 * i.radius) ^ n) := by
  have hcell : i.cell ⊆ closedBall i.center (2 * i.radius) :=
    sdiff_subset.trans (supportLatticeCell_bounds ν R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2
  have hheight : ∀ x ∈ i.cell, infDist x (S : Set (Ambient d)) < 2 * σ * i.radius := by
    intro x hx
    have hxν := supportLatticeCell_subset_support ν R hR (k + i.depth)
      ⟨i.center, i.mem_net⟩ hx.1
    have hball : x ∈ closedBall i.center (1024 * i.radius) := by
      exact closedBall_subset_closedBall (by nlinarith [i.radius_pos]) (hcell hx)
    have h := hfit x ⟨hxν, hball⟩
    nlinarith [mul_pos hσ i.radius_pos]
  have h := contracted_affine_patch_hausdorff_image_bound S hS T.toLinearMap hT u hu κ hκ hTu
    i.center i.center hcenter i.cell (2 * i.radius) 0 (2 * i.radius) (2 * σ * i.radius)
    hcell (by simp) (by linarith) hheight (by nlinarith [i.radius_pos])
    (by nlinarith [mul_pos hσ i.radius_pos])
    (by nlinarith [mul_le_mul_of_nonneg_right hwidth i.radius_pos.le])
  have heq : (2 * σ * i.radius + κ * (2 * i.radius)) / (2 * i.radius) = σ + κ := by
    field_simp [ne_of_gt i.radius_pos]
  simpa only [heq] using! h

theorem projection_conditioned_cell_shadow_bound {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖)
    (i : cellRegionStops ν R hR k z (cellProjectionNoncollapse S P κ)) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) ≤
      ENNReal.ofReal (((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
        (σ + κ) * (2 * i.val.radius) ^ n) := by
  obtain ⟨u, hu, hPu⟩ := projection_conditioned_stop_contracted_unit ν R hR k z S P κ i.val i.property
  exact fitted_cell_contracted_shadow_bound ν R hR k z i.val (S i.val) (hS i.val) (hcenter i.val)
    σ κ hσ hκ hwidth (hfit i.val) T hT u hu (by rw [hnorm]; exact hPu.le)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectedAreaSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem projected_cover_le_retained_area_add_shadow
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (T : X → Y) (hT : LipschitzWith 1 T)
    (A E : Set X) (D V : Set Y)
    (hcover : D ⊆ T '' A) (hshadow : T '' (A \ E) ⊆ V) :
    (μH[(n : ℝ)] : Measure Y) D ≤
      (μH[(n : ℝ)] : Measure X) (A ∩ E) + (μH[(n : ℝ)] : Measure Y) V := by
  have hsub : D ⊆ T '' (A ∩ E) ∪ V := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcover hy
    by_cases he : x ∈ E
    · exact Or.inl ⟨x, ⟨hx, he⟩, rfl⟩
    · exact Or.inr (hshadow ⟨x, ⟨hx, he⟩, rfl⟩)
  have harea := hT.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) (A ∩ E)
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at harea
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add harea le_rfl))

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ProjectionStopShadowMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projected mass of stopping-cell shadows

The stopping-cell radius bound converts individual fitted-plane shadow estimates into
a Hausdorff measure bound for their projected union, controlled by the top cell's mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem cellRegion_stopping_radius_power_le_top {n d : ℕ}
    (ν : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop) :
    (∑' i : cellRegionStops ν R hR k z Good, (ENNReal.ofReal i.val.radius) ^ n) ≤
      ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν (cleanSupportCell ν R hR k z) := by
  calc
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν i.val.cell :=
      ENNReal.tsum_le_tsum (fun i =>
        SupportCellDescendant.radius_power_le_mass ν C G hC hG hg hlower R hR k hcore z i.val)
    _ = ENNReal.ofReal (C * (8 : ℝ) ^ n) * ∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (cellRegion_stopping_mass_le_top ν R hR k z Good)

theorem projection_conditioned_stopping_shadow_le_top {n d : ℕ}
    (ν : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖) :
    (μH[(n : ℝ)] : Measure (Ambient n))
      (T '' (⋃ i : cellRegionStops ν R hR k z (cellProjectionNoncollapse S P κ), i.val.cell)) ≤
        ENNReal.ofReal (projectionStopShadowConstant n C σ κ) * ν (cleanSupportCell ν R hR k z) := by
  let := supportCellDescendant_countable ν R hR k z
  let Good := cellProjectionNoncollapse S P κ
  let B : ℝ := ((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
    (σ + κ) * (2 : ℝ) ^ n
  have hB : 0 ≤ B := by dsimp only [B] <;> positivity
  have hcell : ∀ i : cellRegionStops ν R hR k z Good,
      (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) ≤
        ENNReal.ofReal B * (ENNReal.ofReal i.val.radius) ^ n := by
    intro i
    have h := projection_conditioned_cell_shadow_bound ν R hR k z S hS hcenter P σ κ
      hσ hκ hwidth hfit T hT hnorm i
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    rw [← ENNReal.ofReal_pow i.val.radius_pos.le, ← ENNReal.ofReal_mul hB]
    congr 1
    dsimp only [B]
    rw [mul_pow]
    ring
  have hrad := cellRegion_stopping_radius_power_le_top ν C G hC hG hg hlower R hR k hcore z Good
  calc
    _ = (μH[(n : ℝ)] : Measure (Ambient n))
        (⋃ i : cellRegionStops ν R hR k z Good, T '' i.val.cell) := by rw [Set.image_iUnion]
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) := measure_iUnion_le _
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        ENNReal.ofReal B * (ENNReal.ofReal i.val.radius) ^ n := ENNReal.tsum_le_tsum hcell
    _ = ENNReal.ofReal B * ∑' i : cellRegionStops ν R hR k z Good,
        (ENNReal.ofReal i.val.radius) ^ n := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν (cleanSupportCell ν R hR k z)) :=
      mul_le_mul' le_rfl hrad
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hB]
      rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_NativeSurfaceArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Intrinsic surface-area measures

The native surface-area measure is Hausdorff measure restricted to the surface.
Upper area growth gives local finiteness and regularity, while lower area bounds
identify the support when the surface is closed.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

theorem nativeSurfaceArea_apply {n d : ℕ} (A B : Set (Ambient d))
    (hB : MeasurableSet B) :
    nativeSurfaceArea n A B = (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ B) := by
  rw [nativeSurfaceArea, Measure.restrict_apply hB, inter_comm]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_NativeSurfaceStopCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem nativeSurfaceArea_eq_hausdorff_of_subset {n d : ℕ}
    (A B : Set (Ambient d)) (hB : MeasurableSet B) (hsub : B ⊆ A) :
    nativeSurfaceArea n A B = (μH[(n : ℝ)] : Measure (Ambient d)) B := by
  rw [nativeSurfaceArea_apply A B hB, inter_eq_right.mpr hsub]

theorem native_surface_lattice_exceptional_hausdorff_null {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (supportLatticeExceptional ν R hR) = 0 := by
  have hsub : supportLatticeExceptional ν R hR ⊆ A := by
    intro x hx
    obtain ⟨t, ht⟩ := mem_iUnion.mp hx
    exact hsupport ▸ supportLatticeOverlap_subset_support ν R hR t ht
  have heq := nativeSurfaceArea_eq_hausdorff_of_subset (n := n) A (supportLatticeExceptional ν R hR)
    (supportLatticeExceptional_measurable ν R hR) hsub
  rw [← heq, ← hν]
  exact supportLatticeExceptional_null ν C G hC hG hg hlower R hR

theorem native_surface_core_disk_le_survivor_add_shadow {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (T : Ambient d → Ambient n) (hT : LipschitzWith 1 T)
    (hcover : closedBall (T z) (latticeRadius R k / 32) ⊆
      T '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16))) :
    (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall (T z) (latticeRadius R k / 32)) ≤
      ν (cellRegionLimit ν R hR k z Good) +
        (μH[(n : ℝ)] : Measure (Ambient n))
          (T '' (⋃ i : cellRegionStops ν R hR k z Good, i.val.cell)) := by
  let E := cellRegionLimit ν R hR k z Good
  let B := supportLatticeExceptional ν R hR
  let W := ⋃ i : cellRegionStops ν R hR k z Good, i.val.cell
  have hB : (μH[(n : ℝ)] : Measure (Ambient d)) B = 0 :=
    native_surface_lattice_exceptional_hausdorff_null ν A hν hsupport C G hC hG hg hlower R hR
  have hTB : (μH[(n : ℝ)] : Measure (Ambient n)) (T '' B) = 0 := by
    have h := hT.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) B
    simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul, hB] at h
    exact le_antisymm h (zero_le)
  have hshadow : T '' ((ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) \ E) ⊆
      T '' W ∪ T '' B := by
    rintro _ ⟨x, ⟨hx, hxE⟩, rfl⟩
    by_cases hxB : x ∈ B
    · exact Or.inr ⟨x, hxB, rfl⟩
    have hxcell : x ∈ cleanSupportCell ν R hR k z := by
      refine ⟨(supportLatticeCell_bounds ν R hR k z).1 ⟨hx.1, ?_⟩, hxB⟩
      exact closedBall_subset_ball (by have hr := latticeRadius_pos R hR k; linarith) hx.2
    obtain ⟨i, hi, hxi⟩ := exists_first_failing_cell ν R hR k z Good x hxcell hxE
    exact Or.inl ⟨x, mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩, rfl⟩
  have hproj := projected_cover_le_retained_area_add_shadow n T hT
    (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) E
    (closedBall (T z) (latticeRadius R k / 32)) (T '' W ∪ T '' B) hcover hshadow
  have hEsub : E ⊆ A := by
    intro x hx
    exact hsupport ▸ supportLatticeCell_subset_support ν R hR k z hx.1.1
  have hEeq : (μH[(n : ℝ)] : Measure (Ambient d)) E = ν E := by
    rw [hν]
    exact (nativeSurfaceArea_eq_hausdorff_of_subset A E
      (cellRegionLimit_measurable ν R hR k z Good) hEsub).symm
  have hfirst : (μH[(n : ℝ)] : Measure (Ambient d))
      ((ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) ∩ E) ≤ ν E := by
    rw [← hEeq]
    exact measure_mono inter_subset_right
  have hsecond : (μH[(n : ℝ)] : Measure (Ambient n)) (T '' W ∪ T '' B) ≤
      (μH[(n : ℝ)] : Measure (Ambient n)) (T '' W) := by
    simpa only [hTB, add_zero] using! (measure_union_le (T '' W) (T '' B)
      (μ := (μH[(n : ℝ)] : Measure (Ambient n))))
  exact hproj.trans (add_le_add hfirst hsecond)

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_NativeCoreAreaFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform fraction for core area

The core-area fraction depends only on the dimension and upper growth
constant. Its coefficient bound compares lattice-cell mass with the
Hausdorff measure of a plane disk at the smaller core scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem nativeCoreAreaFraction_pos_le_half (n : ℕ) (G : ℝ) (hG : 0 < G) :
    0 < nativeCoreAreaFraction n G ∧ nativeCoreAreaFraction n G ≤ 1 / 2 := by
  have hu : 0 < (planeUnitHausdorffMeasure n).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨planeUnitHausdorffMeasure_pos n, planeUnitHausdorffMeasure_lt_top n⟩
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _⟩

theorem nativeCoreAreaFraction_coefficient_bound (n : ℕ) (G : ℝ) (hG : 0 < G) :
    2 * nativeCoreAreaFraction n G * (G * (3 : ℝ) ^ n) ≤
      (planeUnitHausdorffMeasure n).toReal / (32 : ℝ) ^ n := by
  have h := min_le_right (1 / 2 : ℝ)
    ((planeUnitHausdorffMeasure n).toReal / (2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n)))
  change nativeCoreAreaFraction n G ≤ _ at h
  have hb := (le_div_iff₀ (by positivity : 0 < 2 * (G * (3 : ℝ) ^ n * (32 : ℝ) ^ n))).mp h
  apply (le_div_iff₀ (by positivity : 0 < (32 : ℝ) ^ n)).mpr
  nlinarith

theorem native_core_disk_area_ge_double_fraction {n d : ℕ}
    (ν : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points)
    (a : Ambient n) :
    ENNReal.ofReal (2 * nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
      (μH[(n : ℝ)] : Measure (Ambient n)) (closedBall a (latticeRadius R k / 32)) := by
  have hr := latticeRadius_pos R hR k
  have hθ := (nativeCoreAreaFraction_pos_le_half n G hG).1
  have htop : ν (cleanSupportCell ν R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
    have hb := (supportLatticeCell_bounds ν R hR k z).2
    have hsub : cleanSupportCell ν R hR k z ⊆ ball (z : Ambient d) (3 * latticeRadius R k) :=
      sdiff_subset.trans (hb.trans (closedBall_subset_ball (by have hr := latticeRadius_pos R hR k; linarith)))
    exact (measure_mono hsub).trans (hg.2 z _ (by positivity))
  have hcoeff := nativeCoreAreaFraction_coefficient_bound n G hG
  have hreal : (2 * nativeCoreAreaFraction n G) * (G * (3 * latticeRadius R k) ^ n) ≤
      (latticeRadius R k / 32) ^ n * (planeUnitHausdorffMeasure n).toReal := by
    have h := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (latticeRadius_pos R hR k).le n)
    calc
      _ = (2 * nativeCoreAreaFraction n G * (G * (3 : ℝ) ^ n)) * (latticeRadius R k) ^ n := by
        rw [mul_pow]; ring
      _ ≤ ((planeUnitHausdorffMeasure n).toReal / (32 : ℝ) ^ n) * (latticeRadius R k) ^ n := h
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ENNReal.ofReal (2 * nativeCoreAreaFraction n G) *
        ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := mul_le_mul' le_rfl htop
    _ = ENNReal.ofReal ((2 * nativeCoreAreaFraction n G) * (G * (3 * latticeRadius R k) ^ n)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ((latticeRadius R k / 32) ^ n * (planeUnitHausdorffMeasure n).toReal) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ambient_closedBall_hausdorffMeasure n a _ (by positivity),
        ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal (planeUnitHausdorffMeasure_lt_top n).ne,
        ENNReal.ofReal_pow (by positivity)]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionRegionAreaContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem projection_region_original_area_contraction {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖)
    (hcover : closedBall (T z) (latticeRadius R k / 32) ⊆
      T '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)))
    (hsmall : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G) :
    let Good := cellProjectionNoncollapse S P κ
    ENNReal.ofReal (nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
      ν (cellRegionLimit ν R hR k z Good) ∧
      (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
        ENNReal.ofReal (1 - nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) := by
  let Good := cellProjectionNoncollapse S P κ
  have hTlip : LipschitzWith 1 T := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, dist_eq_norm]
    exact hT _
  have hproj := native_surface_core_disk_le_survivor_add_shadow ν A hν hsupport
    C G hC hG hg hlower R hR k z Good T hTlip hcover
  have hshadow := projection_conditioned_stopping_shadow_le_top ν C G hC hG hg hlower
    R hR k hcore z S hS hcenter P σ κ hσ hκ hwidth hfit T hT hnorm
  have hshadow' := hshadow.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hsmall) le_rfl)
  have hdisk := native_core_disk_area_ge_double_fraction ν G hG hg R hR k z (T z)
  have hbound := hdisk.trans (hproj.trans (add_le_add le_rfl hshadow'))
  have hfinite : ν (cleanSupportCell ν R hR k z) ≠ ⊤ :=
    (cleanSupportCell_measure_pos_finite ν C G hC hG hg hlower R hR k hcore z).2.ne
  have harea : ν (cellRegionLimit ν R hR k z Good) ≤ ν (cleanSupportCell ν R hR k z) :=
    measure_mono (fun _ hx => hx.1)
  have hθ := nativeCoreAreaFraction_pos_le_half n G hG
  have hretain := retained_mass_ge_of_double_fraction hfinite harea (nativeCoreAreaFraction n G) hθ.1.le hbound
  exact ⟨hretain, cellRegion_stopping_mass_contraction ν R hR k z Good hfinite
    (nativeCoreAreaFraction n G) hθ.1.le (by linarith [hθ.2]) hretain⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_MatchedSurfaceCellPlanes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched planes for support-cell descendants

Pointwise geometric fits select an affine plane through every descendant center.
The root plane retains the projected disk coverage supplied by the same choice.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_matched_surface_cell_planes {n d : ℕ}
    (ν : Measure (Ambient d)) (σ : ℝ)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points) :
    ∃ S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d),
      (∀ i, IsAffineNPlane n (S i)) ∧ (∀ i, i.center ∈ S i) ∧
      (∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
        infDist x (S i : Set (Ambient d)) ≤ σ * i.radius) ∧
      let P := (S (supportCellRoot ν R hR k z)).direction
      closedBall (P.orthogonalProjectionOnto z) (latticeRadius R k / 32) ⊆
        P.orthogonalProjectionOnto '' (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16)) := by
  classical
  have hall (i : SupportCellDescendant ν R hR k z) :=
    hgeometry i.center i.center_mem_support i.radius i.radius_pos
  choose Ps hdim hfit hcover using hall
  let S (i : SupportCellDescendant ν R hR k z) := AffineSubspace.mk' i.center (Ps i)
  have hS : ∀ i, IsAffineNPlane n (S i) := by
    intro i
    refine ⟨AffineSubspace.mk'_nonempty i.center (Ps i), ?_⟩
    rw [AffineSubspace.direction_mk']
    exact hdim i
  refine ⟨S, hS, ?_, hfit, ?_⟩
  · intro i
    apply AffineSubspace.mem_mk'.mpr
    simpa only [vsub_self] using! (Ps i).zero_mem
  · change closedBall ((S (supportCellRoot ν R hR k z)).direction.orthogonalProjectionOnto z) _ ⊆ _
    dsimp only [S]
    rw [AffineSubspace.direction_mk']
    exact hcover (supportCellRoot ν R hR k z)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ContractingProjectionRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Contracting projection regions

Local surface flatness and projection coverage select a stopping region whose
representatives are quantitatively separated by projection. The core-area and
stop-shadow estimates control the mass of its stopping cells.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem exists_contracting_projection_region {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points) :
    ∃ Good : SupportCellDescendant ν R hR k z → Prop,
      (∀ i : SupportCellDescendant ν R hR k z, i.depth = 0 → Good i) ∧
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
          ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
            dist x y ≤ (2 / κ) * dist (P.starProjection x) (P.starProjection y)) ∧
        ENNReal.ofReal (nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) ≤
          ν (cellRegionLimit ν R hR k z Good) ∧
        (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
          ENNReal.ofReal (1 - nativeCoreAreaFraction n G) * ν (cleanSupportCell ν R hR k z) := by
  obtain ⟨S, hS, hcenter, hfit, hcover⟩ := exists_matched_surface_cell_planes ν σ hgeometry R hR k z
  let P := (S (supportCellRoot ν R hR k z)).direction
  let Good := cellProjectionNoncollapse S P κ
  have hroot : ∀ i : SupportCellDescendant ν R hR k z, i.depth = 0 → Good i :=
    cellProjectionNoncollapse_root ν R hR k z S κ hκ1
  have hdim : Module.finrank ℝ P = n := (hS (supportCellRoot ν R hR k z)).2
  obtain ⟨T, hnorm, hT, hdisks⟩ := exists_projection_disk_coordinates P hdim
  have hTcover := hdisks (ν.support ∩ closedBall (z : Ambient d) (latticeRadius R k / 16))
    z (latticeRadius R k / 32) hcover
  obtain ⟨hretain, hcontract⟩ := projection_region_original_area_contraction ν A hν hsupport C G hC hG
    hg hlower R hR k hcore z S hS hcenter P σ κ hσ hκ.le hwidth hfit T hT hnorm hTcover hshadow
  refine ⟨Good, hroot, P, hdim, ?_, hretain, hcontract⟩
  apply projection_separates_noncollapsing_region_representatives ν R hR k z Good hroot P σ κ
    hσ.le hκ hsmall
  intro i hi
  exact ⟨S i, hS i, fun w hw hνw => hfit i w ⟨hνw, ball_subset_closedBall hw⟩, hi⟩

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionRegionChildAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection-region child assembly

Projection-disk coordinates and separated-patch gluing assemble child charts into a
bounded Lipschitz chart covering the region limit and each child's covered cell.
The uncovered parent-cell mass is bounded by the sum of the uncovered child-cell masses.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_projection_region_child_assembly {n d : ℕ}
    (ν : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop)
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (L : ℝ≥0) (hL : 1 ≤ L)
    (hsep : ∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
      ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
        dist x y ≤ (L : ℝ) * dist (P.starProjection x) (P.starProjection y))
    (child : ∀ i : cellRegionStops ν R hR k z Good,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius)) :
    ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
      LipschitzWith (projectionRegionAssemblyConstant d L M) g ∧
      Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
      (cellRegionLimit ν R hR k z Good ⊆ Set.range g) ∧
      (∀ i, i.val.cell ∩ Set.range (child i) ⊆ Set.range g) ∧
      ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
        ∑' i : cellRegionStops ν R hR k z Good, ν (i.val.cell \ Set.range (child i)) := by
  let := supportCellDescendant_countable ν R hR k z
  let E := cellRegionRepresentatives ν R hR k z Good
  let F := cellRegionStops ν R hR k z Good
  have hr := latticeRadius_pos R hR k
  obtain ⟨T, hnorm, hT, _⟩ := exists_projection_disk_coordinates P hdim
  let coord (x : Ambient d) := T (x - z)
  have hdist (x y : Ambient d) : dist (coord x) (coord y) =
      dist (P.starProjection x) (P.starProjection y) := by
    change dist (T (x - z)) (T (y - z)) = _
    rw [dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, hnorm, map_sub, ← dist_eq_norm]
  have hcoord : ∀ x ∈ E, ∀ y ∈ E,
      dist x y ≤ (L : ℝ) * dist (coord x) (coord y) := by
    intro x hx y hy
    rw [hdist]
    exact hsep x hx y hy
  have hcoordBall : ∀ x ∈ E, coord x ∈ closedBall (0 : Ambient n) (2 * latticeRadius R k) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    change ‖T (x - z)‖ ≤ 2 * latticeRadius R k
    have hb := (supportLatticeCell_bounds ν R hR k z).2
      (cellRegionRepresentatives_subset_top ν R hR k z Good hx).1
    exact (hT (x - z)).trans (by simpa only [mem_closedBall, dist_eq_norm] using! hb)
  have hx (i : F) : i.val.center ∈ closedBall i.val.center (i.val.radius / 32) :=
    mem_closedBall_self (by have hi := i.val.radius_pos; positivity)
  have hxE (i : F) : i.val.center ∈ E := Or.inr (Set.mem_range_self i)
  have hradius (i : F) : i.val.radius ≤ 2 * latticeRadius R k := by
    have hi : i.val.radius ≤ latticeRadius R k :=
      latticeRadius_antitone R hR.le (Nat.le_add_right k i.val.depth)
    linarith
  obtain ⟨f, hf, hcover⟩ := exists_ball_lipschitz_cover_of_stop_children_and_survivors
    ν R hR k z Good E coord L hL hcoord (2 * latticeRadius R k) (by positivity) hcoordBall
    F (fun _ hi => hi) (fun i => i.val.center) hx hxE hradius child M hLip himage
  obtain ⟨g₁, hg₁, _, hcover₁⟩ := exists_bounded_normalized_ball_chart (2 * latticeRadius R k)
    (z : Ambient d) (2 * latticeRadius R k) (by positivity) f _ hf
  obtain ⟨g, hg, hgrange, hcover₂⟩ := exists_bounded_normalized_ball_chart (latticeRadius R k)
    (z : Ambient d) (2 * latticeRadius R k) (by positivity) g₁ _ hg₁
  have hfix (y : Ambient d) (hy : y ∈ cleanSupportCell ν R hR k z) (hyf : y ∈ Set.range f) :
      y ∈ Set.range g := by
    have hb := (supportLatticeCell_bounds ν R hR k z).2 hy.1
    exact hcover₂ ⟨hb, hcover₁ ⟨hb, hyf⟩⟩
  have hparent : cellRegionLimit ν R hR k z Good ⊆ Set.range g := by
    intro y hy
    exact hfix y hy.1 (hcover (Or.inl ⟨hy, Or.inl hy⟩))
  have hchild (i : F) : i.val.cell ∩ Set.range (child i) ⊆ Set.range g := by
    intro y hy
    exact hfix y (i.val.cell_subset_top hy.1) (hcover (Or.inr (mem_iUnion.mpr ⟨i, hy.2⟩)))
  have hsub : cleanSupportCell ν R hR k z \ Set.range g ⊆
      ⋃ i : F, i.val.cell \ Set.range (child i) := by
    intro y hy
    have hnot : y ∉ cellRegionLimit ν R hR k z Good := fun h => hy.2 (hparent h)
    obtain ⟨i, hi, hyi⟩ := exists_first_failing_cell ν R hR k z Good y hy.1 hnot
    refine mem_iUnion.mpr ⟨⟨i, hi⟩, hyi, ?_⟩
    intro h
    exact hy.2 (hchild ⟨i, hi⟩ ⟨hyi, h⟩)
  exact ⟨g, hg, hgrange, hparent, hchild, (measure_mono hsub).trans (measure_iUnion_le _)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Projections_ProjectionRegionDepthCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-depth projection-region charts

Iterating child assembly yields a bounded chart with recursively controlled Lipschitz
constant. A fixed fractional stop-mass bound gives a geometric uncovered-mass bound
at each finite depth.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_projection_region_depth_chart {n d : ℕ}
    (ν : Measure (Ambient d)) (L : ℝ≥0) (hL : 1 ≤ L) (θ : ℝ)
    (hregions : ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ Good : SupportCellDescendant ν R hR k z → Prop,
        ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
          (∀ x ∈ cellRegionRepresentatives ν R hR k z Good,
            ∀ y ∈ cellRegionRepresentatives ν R hR k z Good,
              dist x y ≤ (L : ℝ) * dist (P.starProjection x) (P.starProjection y)) ∧
          (∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell) ≤
            ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z))
    (J : ℕ) :
    ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith (projectionRegionDepthConstant d L J) g ∧
        Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
        ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
          (ENNReal.ofReal (1 - θ)) ^ J * ν (cleanSupportCell ν R hR k z) := by
  induction J with
  | zero =>
    intro R hR k z
    refine ⟨fun _ => (z : Ambient d), ?_, ?_, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_self]
      positivity
    · rintro y ⟨u, rfl⟩
      exact mem_closedBall_self (by have hr := latticeRadius_pos R hR k; positivity)
    · simpa only [pow_zero, one_mul] using!
        (measure_mono sdiff_subset (μ := ν)
          (s := cleanSupportCell ν R hR k z \ Set.range (fun _ : ball (0 : Ambient n) (latticeRadius R k) => (z : Ambient d))))
  | succ J ih =>
    intro R hR k z
    obtain ⟨Good, P, hdim, hsep, hstop⟩ := hregions R hR k z
    let F := cellRegionStops ν R hR k z Good
    have hchildren (i : F) := ih R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
    choose child hLip himage hloss using hchildren
    obtain ⟨g, hg, hgrange, _, _, hdeficit⟩ := exists_projection_region_child_assembly
      ν R hR k z Good P hdim L hL hsep child (projectionRegionDepthConstant d L J) hLip himage
    refine ⟨g, hg, hgrange, hdeficit.trans ?_⟩
    calc
      _ ≤ ∑' i : F, (ENNReal.ofReal (1 - θ)) ^ J * ν i.val.cell :=
        ENNReal.tsum_le_tsum hloss
      _ = (ENNReal.ofReal (1 - θ)) ^ J * ∑' i : F, ν i.val.cell := ENNReal.tsum_mul_left
      _ ≤ (ENNReal.ofReal (1 - θ)) ^ J *
          (ENNReal.ofReal (1 - θ) * ν (cleanSupportCell ν R hR k z)) := mul_le_mul' le_rfl hstop
      _ = _ := by rw [pow_succ, mul_assoc]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_MatchedSurfaceDepthCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matched surface charts with controlled loss

For surfaces of infinite support diameter, contracting projection regions provide
finite-depth charts with geometric mass loss. Choosing the depth from a positive
loss tolerance gives one Lipschitz bound valid at every lattice scale and cell.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

variable {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (hdiam : ediam ν.support = ⊤)

include hν hsupport hC hG hg hlower hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam

theorem exists_matched_surface_depth_chart (J : ℕ) :
    ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets ν R hR k).points),
      ∃ g : ball (0 : Ambient n) (latticeRadius R k) → Ambient d,
        LipschitzWith (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J) g ∧
        Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
        ν (cleanSupportCell ν R hR k z \ Set.range g) ≤
          (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ν (cleanSupportCell ν R hR k z) := by
  have hL : 1 ≤ Real.toNNReal (2 / κ) := by
    have h : (1 : ℝ) ≤ (Real.toNNReal (2 / κ) : ℝ) := by
      rw [Real.coe_toNNReal _ (by positivity)]
      apply (le_div_iff₀ hκ).mpr
      linarith
    exact_mod_cast h
  apply exists_projection_region_depth_chart ν (Real.toNNReal (2 / κ)) hL (nativeCoreAreaFraction n G) ?_ J
  intro R hR k z
  have hcore : AdmissibleRadius ν (latticeRadius R k / 8) := by
    refine ⟨by have hr := latticeRadius_pos R hR k; positivity, ?_⟩
    rw [hdiam]
    exact le_top
  obtain ⟨Good, _, P, hdim, hsep, _, hstop⟩ := exists_contracting_projection_region
    ν A hν hsupport C G hC hG hg hlower σ κ hσ hκ hκ1 hwidth hsmall hshadow hgeometry R hR k hcore z
  refine ⟨Good, P, hdim, ?_, hstop⟩
  simpa only [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 / κ)] using! hsep

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_SurfaceBallCellCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cell centers near a surface ball

Compactness makes the separated lattice centers near a ball finite. A Euclidean packing
estimate bounds their number uniformly in the ball center and radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem mem_surfaceBallCellCenters {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) (z : (supportLatticeNets ν r hr 0).points) :
    z ∈ surfaceBallCellCenters ν r hr a ↔ dist (z : Ambient d) a ≤ 5 * r := by
  simp only [surfaceBallCellCenters, Set.Finite.mem_toFinset, mem_ofPred_eq]

theorem surfaceBallCellCenters_card_le {d : ℕ} (ν : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    (surfaceBallCellCenters ν r hr a).card ≤ 11 ^ d := by
  classical
  let F := surfaceBallCellCenters ν r hr a
  let f : (supportLatticeNets ν r hr 0).points → Ambient d := fun z => z.val - a
  have hinj : Set.InjOn f F := by
    intro z hz w hw heq
    apply Subtype.ext
    have h := congrArg (fun v : Ambient d => v + a) heq
    simpa only [f, sub_add_cancel] using! h
  have hbound : ∀ x ∈ F.image f, ‖x‖ ≤ 5 * r := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    simpa only [f, ← dist_eq_norm] using! (mem_surfaceBallCellCenters ν r hr a z).mp hz
  have hsep : ∀ x ∈ F.image f, ∀ y ∈ F.image f, x ≠ y → 2 * (r / 2) ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hzw : (z : Ambient d) ≠ (w : Ambient d) := fun h => hxy (congrArg (fun v => v - a) h)
    have h := (supportLatticeNets ν r hr 0).separated z.property w.property hzw
    simpa only [f, dist_sub_right, latticeRadius_zero,
      mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using! h
  have hcard := euclidean_separated_card_le (F.image f) (5 * r) (r / 2)
    (by positivity) (by positivity) hbound hsep
  have heq : (5 * r + r / 2) / (r / 2) = 11 := by
    apply (div_eq_iff (show r / 2 ≠ 0 by positivity)).mpr
    ring
  rw [Finset.card_image_iff.mpr hinj, heq] at hcard
  exact_mod_cast hcard

theorem surface_ball_covered_by_selected_cells_off_exceptional {d : ℕ}
    (ν : Measure (Ambient d)) (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (x : Ambient d) (hx : x ∈ ν.support ∩ closedBall a (3 * r))
    (hnot : x ∉ supportLatticeExceptional ν r hr) :
    ∃ z ∈ surfaceBallCellCenters ν r hr a, x ∈ cleanSupportCell ν r hr 0 z := by
  obtain ⟨z, hz⟩ := cleanSupportCell_cover ν r hr 0 x hx.1 hnot
  refine ⟨z, (mem_surfaceBallCellCenters ν r hr a z).mpr ?_, hz⟩
  have hnear := (supportLatticeCell_bounds ν r hr 0 z).2 hz.1
  simp only [latticeRadius_zero] at hnear
  have hnear' : dist (z : Ambient d) x ≤ 2 * r := by simpa only [mem_closedBall, dist_comm] using! hnear
  have ha : dist x a ≤ 3 * r := hx.2
  exact (dist_triangle _ x a).trans (by linarith)

theorem selected_surface_ball_cell_subset_seven_ball {d : ℕ}
    (ν : Measure (Ambient d)) (r : ℝ) (hr : 0 < r) (a : Ambient d)
    (z : (supportLatticeNets ν r hr 0).points) (hz : z ∈ surfaceBallCellCenters ν r hr a) :
    cleanSupportCell ν r hr 0 z ⊆ closedBall a (7 * r) := by
  intro x hx
  have hnear := (supportLatticeCell_bounds ν r hr 0 z).2 hx.1
  simp only [latticeRadius_zero] at hnear
  have hxz : dist x (z : Ambient d) ≤ 2 * r := hnear
  have hza := (mem_surfaceBallCellCenters ν r hr a z).mp hz
  change dist x a ≤ 7 * r
  exact (dist_triangle x (z : Ambient d) a).trans (by linarith)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_SurfaceBallCellMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem surface_ball_cell_mass_sum_le {n d : ℕ}
    (ν : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G ν)
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    (∑ z : surfaceBallCellCenters ν r hr a, ν (cleanSupportCell ν r hr 0 z.val)) ≤
      ENNReal.ofReal (G * (8 * r) ^ n) := by
  let F := surfaceBallCellCenters ν r hr a
  have hd : Pairwise (fun z w : F => Disjoint (cleanSupportCell ν r hr 0 z.val)
      (cleanSupportCell ν r hr 0 w.val)) := by
    intro z w hzw
    exact cleanSupportCell_disjoint ν r hr 0 z.val w.val (fun h => hzw (Subtype.ext h))
  have hm : ∀ z : F, MeasurableSet (cleanSupportCell ν r hr 0 z.val) :=
    fun z => cleanSupportCell_measurable ν r hr 0 z.val
  have hsum : (∑ z : F, ν (cleanSupportCell ν r hr 0 z.val)) =
      ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val) := by
    simpa only [tsum_fintype] using! (measure_iUnion hd hm).symm
  have hsub : (⋃ z : F, cleanSupportCell ν r hr 0 z.val) ⊆ ball a (8 * r) := by
    apply iUnion_subset
    intro z
    exact (selected_surface_ball_cell_subset_seven_ball ν r hr a z.val z.property).trans
      (closedBall_subset_ball (by linarith : 7 * r < 8 * r))
  rw [hsum]
  exact (measure_mono hsub).trans (hg.2 a _ (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_SurfaceBallChartAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Assembling surface ball charts

Finite cell charts combine into a ball chart whose uncovered surface mass is
controlled by the sum of the cell deficits. Restriction to the surface identifies
this deficit with the corresponding Hausdorff measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_surface_ball_chart_of_cell_deficits {n d : ℕ} (hn : 0 < n)
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ s : ℝ, AdmissibleRadius ν s →
      ENNReal.ofReal (s ^ n / C) ≤ ν (ball x s))
    (r : ℝ) (hr : 0 < r) (a : Ambient d) (M : ℝ≥0) (loss : ℝ≥0∞)
    (hcharts : ∀ z : surfaceBallCellCenters ν r hr a,
      ∃ g : ball (0 : Ambient n) r → Ambient d, LipschitzWith M g ∧
        ν (cleanSupportCell ν r hr 0 z.val \ Set.range g) ≤ loss * ν (cleanSupportCell ν r hr 0 z.val)) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d (11 ^ d) M) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
        loss * ENNReal.ofReal (G * (8 * r) ^ n) := by
  classical
  let F := surfaceBallCellCenters ν r hr a
  choose child hLip hLoss using hcharts
  have hN : Fintype.card F ≤ 11 ^ d := by
    simpa only [Fintype.card_coe] using! surfaceBallCellCenters_card_le ν r hr a
  obtain ⟨g, hglip, hgrange, hcover⟩ := exists_bounded_ball_cover_of_finite_family hn
    (11 ^ d) hN r hr a child M hLip
  let B := supportLatticeExceptional ν r hr
  have hB : ν B = 0 := supportLatticeExceptional_null ν C G hC hG hg hlower r hr
  have hsub : ((A ∩ closedBall a (3 * r)) \ Set.range g) ⊆
      B ∪ ⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z) := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    have hxν : x ∈ ν.support := hsupport.symm ▸ hx.1.1
    obtain ⟨z, hz, hcell⟩ := surface_ball_covered_by_selected_cells_off_exceptional
      ν r hr a x ⟨hxν, hx.1.2⟩ hxB
    refine Or.inr (mem_iUnion.mpr ⟨⟨z, hz⟩, hcell, ?_⟩)
    intro h
    exact hx.2 (hcover ⟨z, hz⟩ ⟨hx.1.2, h⟩)
  have hEq : (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) =
      ν ((A ∩ closedBall a (3 * r)) \ Set.range g) := by
    rw [hν]
    exact ((μH[(n : ℝ)] : Measure (Ambient d)).restrict_eq_self
      (sdiff_subset.trans inter_subset_left)).symm
  refine ⟨g, hglip, hgrange, ?_⟩
  rw [hEq]
  calc
    _ ≤ ν (B ∪ ⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := measure_mono hsub
    _ ≤ ν B + ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := measure_union_le _ _
    _ = ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := by rw [hB, zero_add]
    _ ≤ ∑ z : F, ν (cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) := by
      simpa only [tsum_fintype] using! (measure_iUnion_le
        (fun z : F => cleanSupportCell ν r hr 0 z.val \ Set.range (child z)) (μ := ν))
    _ ≤ ∑ z : F, loss * ν (cleanSupportCell ν r hr 0 z.val) := Finset.sum_le_sum (fun z _ => hLoss z)
    _ = loss * ∑ z : F, ν (cleanSupportCell ν r hr 0 z.val) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul' le_rfl (surface_ball_cell_mass_sum_le ν G hg r hr a)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Surfaces_MatchedSurfaceBallDepthCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-depth charts on surface balls

Finite unions of matched-surface cell charts produce maps from Euclidean balls.
The construction retains the finite-depth mass-deficit estimate and an explicit
Lipschitz bound determined by the cell-chart bound and the covering multiplicity.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

variable {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (hdiam : ediam ν.support = ⊤)

include hν hsupport hC hG hg hlower hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam

theorem exists_matched_surface_ball_depth_chart_oai (hn : 0 < n) (J : ℕ)
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d (11 ^ d)
        (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
        (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ENNReal.ofReal (G * (8 * r) ^ n) := by
  apply exists_surface_ball_chart_of_cell_deficits hn ν A hν hsupport C G hC hG hg hlower
    r hr a (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)
    ((ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J)
  intro z
  have hlocal := exists_matched_surface_depth_chart ν A hν hsupport C G hC hG hg hlower
    σ κ hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam J r hr 0 z.val
  obtain ⟨g₀, hg₀, _, hdef⟩ := hlocal
  let cast : ball (0 : Ambient n) r → ball (0 : Ambient n) (latticeRadius r 0) :=
    fun u => ⟨u.val, by simpa only [latticeRadius_zero] using! u.property⟩
  have hcast : Isometry cast := fun _ _ => rfl
  have hsurj : Function.Surjective cast := by
    intro u
    exact ⟨⟨u.val, by simpa only [latticeRadius_zero] using! u.property⟩, Subtype.ext rfl⟩
  let g := g₀ ∘ cast
  have hrange : Set.range g = Set.range g₀ := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      exact Set.mem_range_self (cast u)
    · rintro y ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hsurj u
      exact ⟨v, congrArg g₀ hv⟩
  refine ⟨g, ?_, ?_⟩
  · simpa only [mul_one] using! hg₀.comp hcast.lipschitz
  · rw [hrange]
    exact hdef

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart_oai := @OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart_oai
