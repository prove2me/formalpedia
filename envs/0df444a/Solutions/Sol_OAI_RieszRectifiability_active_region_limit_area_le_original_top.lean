-- Prove2me | solution 1 for OAI.RieszRectifiability.active_region_limit_area_le_original_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:38.542948+00:00
-- url     : https://prove2.me/submissions/caa73d25-a676-4cdb-bced-621a64322b4b

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

theorem plane_disk_lipschitz_range_hausdorffMeasure_le {n d e : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n)
    (a : P) (r : ℝ) (hr : 0 < r) (K : ℝ≥0)
    (g : closedBall a r → Ambient e) (hg : LipschitzWith K g) :
    (μH[(n : ℝ)] : Measure (Ambient e)) (Set.range g) ≤
      (K : ℝ≥0∞) ^ n * ((ENNReal.ofReal r) ^ n * planeUnitHausdorffMeasure n) := by
  have h := hg.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) Set.univ
  simpa only [Set.image_univ, ENNReal.rpow_natCast,
    plane_closedBall_subtype_hausdorffMeasure P hdim a r hr] using! h

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_VitaliLocalMassCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A disjoint Vitali selection converts local charges on fivefold enlarged balls into
a comparison between the total mass of a set and the mass of its containing region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem measure_le_of_local_fivefold_charges {d : ℕ}
    (ν μ : Measure (Ambient d)) (A Ω : Set (Ambient d)) (r : Ambient d → ℝ)
    (R : ℝ) (hpos : ∀ x ∈ A, 0 < r x) (hbound : ∀ x ∈ A, r x ≤ R)
    (hcontained : ∀ x ∈ A, closedBall x (r x) ⊆ Ω) (C : ℝ≥0∞)
    (hcharge : ∀ x ∈ A, ν (A ∩ closedBall x (5 * r x)) ≤ C * μ (closedBall x (r x))) :
    ν A ≤ C * μ Ω := by
  obtain ⟨u, hu, hdisjoint, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A id r R hbound 5 (by norm_num)
  have hcount : u.Countable := hdisjoint.countable_of_nonempty_interior (by
    intro x hx
    exact ⟨x, ball_subset_interior_closedBall (mem_ball_self (hpos x (hu hx)))⟩)
  let := hcount.to_subtype
  have hcover' : A ⊆ ⋃ x : u, A ∩ closedBall (x : Ambient d) (5 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hx, hxy (mem_closedBall_self (hpos x hx).le)⟩
  have hd : Pairwise (fun x y : u =>
      Disjoint (closedBall (x : Ambient d) (r x)) (closedBall (y : Ambient d) (r y))) := by
    intro x y hxy
    exact hdisjoint x.property y.property (fun h => hxy (Subtype.ext h))
  have hsub : (⋃ x : u, closedBall (x : Ambient d) (r x)) ⊆ Ω :=
    iUnion_subset (fun x => hcontained x (hu x.property))
  calc
    ν A ≤ ν (⋃ x : u, A ∩ closedBall (x : Ambient d) (5 * r x)) := measure_mono hcover'
    _ ≤ ∑' x : u, ν (A ∩ closedBall (x : Ambient d) (5 * r x)) := measure_iUnion_le _
    _ ≤ ∑' x : u, C * μ (closedBall (x : Ambient d) (r x)) :=
      ENNReal.tsum_le_tsum (fun x => hcharge x (hu x.property))
    _ = C * ∑' x : u, μ (closedBall (x : Ambient d) (r x)) :=
      ENNReal.tsum_mul_left
    _ = C * μ (⋃ x : u, closedBall (x : Ambient d) (r x)) := by
      rw [measure_iUnion hd (fun _ => measurableSet_closedBall)]
    _ ≤ C * μ Ω := mul_le_mul_right (measure_mono hsub) C

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearSupportMassCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem near_support_radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (hμ : μ.support.Nonempty) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ a ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball a r))
    (x : Ambient d) (δ : ℝ) (hδ : 0 < δ) (hadm : AdmissibleRadius μ (δ / 256))
    (hnear : infDist x μ.support ≤ δ / 512) :
    (ENNReal.ofReal δ) ^ n ≤
      ENNReal.ofReal (C * 256 ^ n) * μ (closedBall x (δ / 128)) := by
  obtain ⟨a, ha, hdist⟩ := μ.isClosed_support.exists_infDist_eq_dist hμ x
  have hxa : dist x a ≤ δ / 512 := by rw [← hdist]; exact hnear
  have hsub : ball a (δ / 256) ⊆ closedBall x (δ / 128) := by
    intro y hy
    have hya : dist y a < δ / 256 := hy
    have ht := dist_triangle y a x
    rw [dist_comm a x] at ht
    change dist y x ≤ δ / 128
    linarith
  have hl := (hlower a ha (δ / 256) hadm).trans (measure_mono hsub)
  have heq : (ENNReal.ofReal δ) ^ n =
      ENNReal.ofReal (C * 256 ^ n) * ENNReal.ofReal ((δ / 256) ^ n / C) := by
    rw [← ENNReal.ofReal_pow hδ.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * 256 ^ n)]
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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_HausdorffFiniteCoverBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem hausdorff_measure_le_of_shrinking_finite_covers {d : ℕ}
    (n : ℕ) (A : Set (Ambient d)) (ι : ℕ → Type*) [∀ t, Fintype (ι t)]
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (B : ∀ t : ℕ, ι t → Set (Ambient d))
    (hdiam : ∀ t i, ediam (B t i) ≤ r t)
    (hcover : ∀ t, A ⊆ ⋃ i, B t i) (K : ℝ≥0∞)
    (hcost : ∀ t, (∑ i, ediam (B t i) ^ n) ≤ K) :
    (μH[(n : ℝ)] : Measure (Ambient d)) A ≤ K := by
  have h := Measure.hausdorffMeasure_le_liminf_sum (n : ℝ) A r hr B
    (Filter.Eventually.of_forall hdiam) (Filter.Eventually.of_forall hcover)
  simp only [ENNReal.rpow_natCast] at h
  have hc : (fun t => ∑ i, ediam (B t i) ^ n) ≤ᶠ[atTop] (fun _ => K) :=
    Filter.Eventually.of_forall hcost
  have hlim : (liminf (fun t => ∑ i, ediam (B t i) ^ n) atTop) ≤ K := by
    simpa only [liminf_const] using! Filter.liminf_le_liminf hc
  exact h.trans hlim

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

theorem finiteProjectionAverage_dist_le_of_weight_sum_le_one {ι : Type*} {d : ℕ}
    (F : Finset ι) (θ : ι → Ambient d → ℝ) (π : ι → Ambient d → Ambient d)
    (x y : Ambient d) (K B : ℝ) (hK : 0 ≤ K)
    (hθ : ∀ i ∈ F, 0 ≤ θ i x) (hsum : (∑ i ∈ F, θ i x) ≤ 1)
    (hlinear : ∀ i ∈ F, θ i x ≠ 0 →
      ‖(π i x - x) - (π i y - y)‖ ≤ K * dist x y)
    (hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ B) :
    dist (finiteProjectionAverage F θ π x) (finiteProjectionAverage F θ π y) ≤
      (1 + K) * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := by
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
  have hresidual : ‖(finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (x - y)‖ ≤
      K * dist x y + B * (∑ i ∈ F, |θ i x - θ i y|) := by
    rw [finiteProjectionAverage_residual_increment]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have ht := norm_add_le
    ((finiteProjectionAverage F θ π x - finiteProjectionAverage F θ π y) - (x - y)) (x - y)
  rw [sub_add_cancel,
    ← dist_eq_norm (finiteProjectionAverage F θ π x) (finiteProjectionAverage F θ π y),
    ← dist_eq_norm x y] at ht
  linarith

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

theorem cappedStoppingDistance_nonneg {ι X : Type*} [PseudoMetricSpace X]
    (R : ℝ) (c : ι → X) (r : ι → ℝ)
    (hR : 0 ≤ R) (hr : ∀ i : ι, 0 ≤ r i) (x : X) :
    0 ≤ cappedStoppingDistance R c r x := by
  apply le_ciInf
  intro i
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

theorem cellRegionStoppingScale_nonneg (x : Ambient d) :
    0 ≤ cellRegionStoppingScale μ R hR k z Good x :=
  cappedStoppingDistance_nonneg _ _ _ (latticeRadius_pos R hR k).le
    (fun i => i.val.radius_pos.le) x

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

theorem active_cell_surface_point_near_support (hεsmall : ε ≤ 1 / 524288)
    (x : Ambient d) (hx : x ∈ A)
    (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    infDist x μ.support ≤ (263168 * ε) * q.radius := by
  let : Nonempty S := hS.1.to_subtype
  let p := nonemptyAffineProjection S hS.1 x
  have hr := q.radius_pos
  have hheight := HasActiveCellSurfaceChart.height_on_inner_ball q S ε A hchart x hx hnear
  have hdist : dist p x ≤ (262144 * ε) * q.radius := by
    rw [nonemptyAffineProjection_dist_self]
    exact hheight
  have hδ := mul_le_mul_of_nonneg_right hεsmall hr.le
  have hpnear : p ∈ ball q.center (1024 * q.radius) := by
    have ht := dist_triangle p x q.center
    have hx' : dist x q.center ≤ (9 / 4 : ℝ) * q.radius := hnear
    change dist p q.center < 1024 * q.radius
    nlinarith
  have hpS : p ∈ S := orthogonalProjection_mem x
  have hpheight := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) S hS hfit).2 p hpnear hpS
  have ht : infDist x μ.support ≤ infDist p μ.support + dist x p := infDist_le_infDist_add_dist
  rw [dist_comm x p] at ht
  nlinarith

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

theorem active_level_cell_mass_sum_le_top {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ) :
    (∑ i : activeLevelIndex μ R hR k z Good t, μ i.val.cell) ≤
      μ (cleanSupportCell μ R hR k z) := by
  classical
  let F := activeLevelIndex μ R hR k z Good t
  have hd : Pairwise (fun i j : F => Disjoint i.val.cell j.val.cell) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (mem_activeLevelIndex μ R hR k z Good t i).mp i.property
    have hj := (mem_activeLevelIndex μ R hR k z Good t j).mp j.property
    exact hij (Subtype.ext (i.val.eq_of_common_point_same_depth j.val
      (hi.1.trans hj.1.symm) x hxi hxj))
  have hm (i : F) : MeasurableSet i.val.cell :=
    cleanSupportCell_measurable μ R hR (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩
  have hsum : (∑ i : F, μ i.val.cell) = μ (⋃ i : F, i.val.cell) := by
    simpa only [tsum_fintype] using! (measure_iUnion hd hm).symm
  change (∑ i : F, μ i.val.cell) ≤ _
  rw [hsum]
  exact measure_mono (iUnion_subset (fun i => i.val.cell_subset_top))

theorem active_level_radius_power_sum_le_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ) :
    (∑ i : activeLevelIndex μ R hR k z Good t, (ENNReal.ofReal i.val.radius) ^ n) ≤
      ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z) := by
  classical
  calc
    _ ≤ ∑ i : activeLevelIndex μ R hR k z Good t, ENNReal.ofReal (C * 8 ^ n) * μ i.val.cell :=
      Finset.sum_le_sum (fun i _ =>
        SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z i.val)
    _ = ENNReal.ofReal (C * 8 ^ n) *
        ∑ i : activeLevelIndex μ R hR k z Good t, μ i.val.cell := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_right (active_level_cell_mass_sum_le_top μ R hR k z Good t) _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionAmbientBounds
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
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hS hεsmall hfit

theorem active_level_plane_center_height_le
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ activeLevelIndex μ R hR k z Good t) :
    infDist i.center (S i : Set (Ambient d)) ≤ latticeRadius R (k + t) := by
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hrad : i.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hiA.1]
  have hr := i.radius_pos
  have hc := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) (S i) (hS i) (hfit i hi)).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hm := mul_le_mul_of_nonneg_right hεsmall hr.le
  rw [← hrad]
  nlinarith

theorem active_level_plane_displacement_le
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ activeLevelIndex μ R hR k z Good t)
    (x : Ambient d) (A : ℝ) (hx : dist x i.center ≤ A * latticeRadius R (k + t)) :
    dist (nonemptyAffineProjection (S i) (hS i).1 x) x ≤ (A + 1) * latticeRadius R (k + t) := by
  have hc := active_level_plane_center_height_le μ R hR k z Good t S hS ε hεsmall hfit i hi
  have ht : infDist x (S i : Set (Ambient d)) ≤ infDist i.center (S i : Set (Ambient d)) +
      dist x i.center := infDist_le_infDist_add_dist
  rw [nonemptyAffineProjection_dist_self]
  nlinarith

theorem activeLevelProjectionMap_global_displacement (x : Ambient d) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤ 5 * latticeRadius R (k + t) := by
  have hr := latticeRadius_pos R hR (k + t)
  apply finiteProjectionAverage_dist_self_le _ _ _ x (5 * latticeRadius R (k + t)) (by positivity)
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  simpa only [show (4 : ℝ) + 1 = 5 by norm_num] using!
    active_level_plane_displacement_le μ R hR k z Good t S hS ε hεsmall hfit i hi x 4 hnear.le

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveProjectionGlobalLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators NNReal

theorem activeLevelProjectionMap_global_lipschitz {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    LipschitzWith (activeProjectionGlobalLipschitzConstant d)
      (activeLevelProjectionMap μ R hR k z Good t S hS) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  let r := latticeRadius R (k + t)
  let F := activeLevelIndex μ R hR k z Good t
  let θ := activeLevelWeight μ R hR k z Good t
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  by_cases hnear : dist x y ≤ r
  · have hlinear : ∀ i ∈ F, θ i x ≠ 0 →
        ‖(π i x - x) - (π i y - y)‖ ≤ (2 : ℝ) * dist x y := by
      intro i _ _
      have hπ := (nonemptyAffineProjection_lipschitz (S i) (hS i).1).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul] at hπ
      have hid : (π i x - x) - (π i y - y) = (π i x - π i y) - (x - y) := by abel
      rw [hid]
      have h := norm_sub_le (π i x - π i y) (x - y)
      rw [← dist_eq_norm (π i x) (π i y), ← dist_eq_norm x y] at h
      change dist (π i x) (π i y) ≤ dist x y at hπ
      linarith
    have hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ 6 * r := by
      intro i hi hchange
      have hyi : dist y i.center ≤ 5 * r := by
        by_cases hny : θ i y = 0
        · have hnx : θ i x ≠ 0 := fun hx0 => hchange (hx0.trans hny.symm)
          have hx := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hnx
          have ht := dist_triangle y x i.center
          rw [dist_comm y x] at ht
          change dist x i.center < 4 * r at hx
          linarith
        · have hy := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i y).mp hny
          change dist y i.center < 4 * r at hy
          linarith
      simpa only [show (5 : ℝ) + 1 = 6 by norm_num] using!
        active_level_plane_displacement_le μ R hR k z Good t S hS ε hεsmall hfit i hi y 5 hyi
    have h := finiteProjectionAverage_dist_le_of_weight_sum_le_one F θ π x y 2 (6 * r)
      (by norm_num) (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
      (activeLevelWeight_sum_le_one μ R hR k z Good t x) hlinear hoffset
    have hvar : (∑ i ∈ F, |θ i x - θ i y|) ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
      activeLevelWeight_sum_abs_sub_le μ R hR k z Good t x y
    calc
      dist (σ x) (σ y) ≤ (1 + 2) * dist x y + (6 * r) * (∑ i ∈ F, |θ i x - θ i y|) := h
      _ ≤ (1 + 2) * dist x y + (6 * r) * ((4 * (9 : ℝ) ^ d) * (dist x y / r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar (by positivity))
      _ = (3 + 24 * (9 : ℝ) ^ d) * dist x y := by
        field_simp [ne_of_gt hr]
        ring
  · have hx := activeLevelProjectionMap_global_displacement μ R hR k z Good t S hS ε hεsmall hfit x
    have hy := activeLevelProjectionMap_global_displacement μ R hR k z Good t S hS ε hεsmall hfit y
    have h1 := dist_triangle (σ x) x (σ y)
    have h2 := dist_triangle x y (σ y)
    rw [dist_comm y (σ y)] at h2
    change dist (σ x) x ≤ 5 * r at hx
    change dist (σ y) y ≤ 5 * r at hy
    have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    calc
      dist (σ x) (σ y) ≤ 11 * dist x y := by linarith
      _ ≤ (3 + 24 * (9 : ℝ) ^ d) * dist x y :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionSurfaceApproximation
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
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hε hεtiny hsmall hfit

theorem activeRegionSurface_near_support_in_active_ball (t : ℕ)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (x : Ambient d) (hx : x ∈ activeRegionSurface μ R hR k z Good S hS t)
    (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t))) :
    infDist x μ.support ≤ (263168 * ε) * latticeRadius R (k + t) := by
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hrad : q.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hqA.1]
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
  have h := active_cell_surface_point_near_support μ R hR k z q (S q) (hS q) ε
    (hfit q hqA.2) (activeRegionSurface μ R hR k z Good S hS t) (hcharts q hq)
    (by linarith : ε ≤ 1 / 524288) x hx (by simpa only [hrad] using! hnear)
  simpa only [hrad] using! h

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

theorem activeRegionTransitionMap_global_lipschitz (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) (j : ℕ) :
    LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ j)
      (activeRegionTransitionMap μ R hR k z Good S hS s j) := by
  induction j with
  | zero =>
    rw [pow_zero]
    apply LipschitzWith.mk_one
    intro x y
    rfl
  | succ j ih =>
    have hstep := activeLevelProjectionMap_global_lipschitz μ R hR k z Good (s + j + 1)
      S hS ε hεsmall
      (fun i hi => hfit i ((mem_activeLevelIndex μ R hR k z Good (s + j + 1) i).mp hi).2)
    simpa only [activeRegionTransitionMap, pow_succ'] using! hstep.comp ih

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionLargeScaleCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Large-scale charts for active-region limits

The portion of an active-region limit model with large stopping scale is covered by
a root-plane disk chart transported through two active projection steps. The resulting
chart has Lipschitz bound equal to the square of the global projection bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_large_scale_chart {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtiny : ε ≤ 1 / 268435456)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d)) (hA : A ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ g : closedBall ((S (supportCellRoot μ R hR k z)).direction.orthogonalProjectionOnto (z : Ambient d))
        (3 * latticeRadius R k) → Ambient d,
      LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ 2) g ∧
        Set.range f ∩ A ⊆ Set.range g := by
  let P := (S (supportCellRoot μ R hR k z)).direction
  obtain ⟨g, hgLip, _, _, hgRange⟩ := exists_affine_plane_disk_chart
    (S (supportCellRoot μ R hR k z)) (hS _).1 (P.orthogonalProjectionOnto (z : Ambient d))
    (3 * latticeRadius R k)
  let T := activeRegionTransitionMap μ R hR k z Good S hS 0 2
  have hTLip := activeRegionTransitionMap_global_lipschitz μ R hR k z Good S hS 0
    ε (by linarith) hfit 2
  have hr0 := latticeRadius_pos R hR k
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr0.le
  have hr2 : latticeRadius R (k + 2) = latticeRadius R k / 4096 := by
    rw [latticeRadius_add]
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) ((17039360 * ε) / 63) (by positivity)
    hmodel.2.2.2.1 A (latticeRadius R (k + 1)) hD 2 (by
      rw [hr2, latticeRadius_succ]
      nlinarith)
  refine ⟨T ∘ g, by simpa only [mul_one] using! hTLip.comp hgLip, ?_⟩
  intro x hx
  have hx2 : x ∈ activeRegionSurface μ R hR k z Good S hS (0 + 2) := (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hx2
  obtain ⟨y, hy, hTy⟩ := hx2
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε f hmodel 0 2 y hy
  change dist (T y) y ≤ (2 * ((17039360 * ε) / 63)) * latticeRadius R k at hmove
  rw [hTy] at hmove
  have hyz : dist y (z : Ambient d) ≤ 3 * latticeRadius R k := by
    have ht := dist_triangle y x (z : Ambient d)
    rw [dist_comm y x] at ht
    have hxz : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := hA hx.2
    nlinarith
  have hproject := P.norm_starProjection_apply_le (y - (z : Ambient d))
  rw [map_sub, ← dist_eq_norm (P.starProjection y) (P.starProjection (z : Ambient d)),
    ← dist_eq_norm y (z : Ambient d)] at hproject
  have hyg : y ∈ Set.range g := by
    rw [hgRange]
    exact ⟨hy, hproject.trans hyz⟩
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

theorem active_region_large_scale_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 ≤ ε)
    (hεtiny : ε ≤ 1 / 268435456)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d)) (hA : A ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      activeRegionLargeAreaConstant n d * (ENNReal.ofReal (latticeRadius R k)) ^ n := by
  obtain ⟨g, hgLip, hgCover⟩ := exists_active_region_large_scale_chart μ R hR k z Good S hS ε hε
    hεtiny hfit f hmodel A hA hD
  have harea := plane_disk_lipschitz_range_hausdorffMeasure_le
    (S (supportCellRoot μ R hR k z)).direction (hS _).2 _ (3 * latticeRadius R k)
    (by have hr := latticeRadius_pos R hR k; positivity) _ g hgLip
  apply (measure_mono hgCover).trans
  convert! harea using 1
  all_goals try with_reducible_and_instances rfl
  unfold activeRegionLargeAreaConstant
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat, mul_pow]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionPositiveScaleCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A lower stopping-scale bound lets finite-stage charts capture a nearby part of the limit surface.
The resulting chart retains the quantitative Lipschitz bound from the transition maps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_scale_chart {n d : ℕ}
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
    ∃ g : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      LipschitzWith ((activeProjectionGlobalLipschitzConstant d) ^ 3 * 2) g ∧
      Set.range f ∩ A ⊆ Set.range g := by
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨g, hgLip, _, _, hgCapture⟩ := hcharts q hqF
  let T := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3
  have hTLip := activeRegionTransitionMap_global_lipschitz μ R hR k z Good S hS q.depth
    ε (by linarith) hfit 3
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
  refine ⟨T ∘ g, hTLip.comp hgLip, ?_⟩
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

theorem active_region_positive_scale_area_le {n d : ℕ}
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
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      activeRegionLocalAreaConstant n d * (ENNReal.ofReal q.radius) ^ n := by
  obtain ⟨g, hgLip, hgCover⟩ := exists_active_region_positive_scale_chart μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq A hnear hscale
  have harea := plane_disk_lipschitz_range_hausdorffMeasure_le (S q).direction (hS q).2
    ((S q).direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius)
    (by have hr := q.radius_pos; positivity) _ g hgLip
  apply (measure_mono hgCover).trans
  convert! harea using 1
  all_goals try with_reducible_and_instances rfl
  unfold activeRegionLocalAreaConstant
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5 / 2), mul_pow]
  ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_ActiveRegionStoppingBallArea
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
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem active_region_stopping_ball_area_le (x : Ambient d)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hDs : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    (μH[(n : ℝ)] : Measure (Ambient d))
      (Set.range f ∩ closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16)) ≤
      (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
        (ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x)) ^ n := by
  obtain ⟨q, hq, hrhi, hrlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good x hpos hDs
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good x q hrhi hrlo hnear
  have harea := active_region_positive_scale_area_le μ R hR k z Good S hS ε hε hεtiny hsmall
    hfit f hmodel q hq _ hball hscale
  apply harea.trans
  have hrad : ENNReal.ofReal q.radius ≤
      (4096 : ℝ≥0∞) * ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096), ENNReal.ofReal_ofNat]
      using! ENNReal.ofReal_le_ofReal hrhi
  calc
    _ ≤ activeRegionLocalAreaConstant n d *
        ((4096 : ℝ≥0∞) * ENNReal.ofReal (cellRegionStoppingScale μ R hR k z Good x)) ^ n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

theorem active_region_limit_support_distance_at_scale (x : Ambient d)
    (hx : x ∈ Set.range f)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hDs : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    infDist x μ.support ≤ (2187264000 * ε) * cellRegionStoppingScale μ R hR k z Good x := by
  obtain ⟨q, hq, hrhi, _, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good x hpos hDs
  obtain ⟨u, rfl⟩ := hx
  let y := activeRegionParameterMap μ R hR k z Good S hS q.depth u
  have hy : y ∈ activeRegionSurface μ R hR k z Good S hS q.depth := by
    rw [activeRegionSurface_eq_image]
    exact ⟨u, u.property, rfl⟩
  have hmove : dist y (f u) ≤ ((17039360 * ε) / 63) * q.radius :=
    hmodel.2.2.2.1 q.depth u
  have hr := q.radius_pos
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hBm := mul_le_mul_of_nonneg_right hB hr.le
  have hylocal : y ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + q.depth)) := by
    have htri := dist_triangle y (f u) q.center
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hyμ := activeRegionSurface_near_support_in_active_ball μ R hR k z Good S hS ε hε
    hεtiny hsmall hfit q.depth q hqF y hy hylocal
  change infDist y μ.support ≤ (263168 * ε) * q.radius at hyμ
  have hinf : infDist (f u) μ.support ≤ infDist y μ.support + dist (f u) y :=
    infDist_le_infDist_add_dist
  rw [dist_comm (f u) y] at hinf
  have hlocal : infDist (f u) μ.support ≤ (534000 * ε) * q.radius := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ 534000 * ε by positivity)
  nlinarith

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

theorem active_region_small_positive_scale_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ a ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball a r))
    (R : ℝ) (hR : 0 < R) (k : ℕ)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (A : Set (Ambient d))
    (hA : A ⊆ Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k))
    (hD : ∀ x ∈ A, 0 < cellRegionStoppingScale μ R hR k z Good x ∧
      cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    (μH[(n : ℝ)] : Measure (Ambient d)) A ≤
      activeRegionSmallScaleAreaConstant n d C *
        μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) := by
  let D := cellRegionStoppingScale μ R hR k z Good
  have hεtiny : ε ≤ 1 / 268435456 := by linarith
  have hr0 := latticeRadius_pos R hR k
  have hμ : μ.support.Nonempty := ⟨z, (supportLatticeNets μ R hR k).subset z.property⟩
  apply measure_le_of_local_fivefold_charges (μH[(n : ℝ)] : Measure (Ambient d)) μ A
    (closedBall (z : Ambient d) (3 * latticeRadius R k)) (fun x => D x / 128)
    (latticeRadius R k / 128)
  · intro x hx
    exact div_pos (hD x hx).1 (by norm_num)
  · intro x _
    exact div_le_div_of_nonneg_right (cellRegionStoppingScale_le_top μ R hR k z Good x)
      (by norm_num)
  · intro x hx y hy
    have hxy : dist y x ≤ D x / 128 := hy
    have hxz : dist x (z : Ambient d) ≤ 2 * latticeRadius R k := (hA hx).2
    have hcap := cellRegionStoppingScale_le_top μ R hR k z Good x
    have ht := dist_triangle y x (z : Ambient d)
    change dist y (z : Ambient d) ≤ 3 * latticeRadius R k
    change D x ≤ latticeRadius R k at hcap
    linarith
  · intro x hx
    have hDx : 0 < D x := (hD x hx).1
    have hcap : D x ≤ latticeRadius R k := cellRegionStoppingScale_le_top μ R hR k z Good x
    have hadm : AdmissibleRadius μ (D x / 256) := by
      refine ⟨by positivity, ?_⟩
      exact (ENNReal.ofReal_le_ofReal (show D x / 256 ≤ latticeRadius R k / 8 by linarith)).trans hcore.2
    have hclose := active_region_limit_support_distance_at_scale μ R hR k z Good S hS ε hε
      hεtiny hsmall hfit f hmodel x (hA hx).1 (hD x hx).1 (hD x hx).2
    have hnear : infDist x μ.support ≤ D x / 512 := by
      change infDist x μ.support ≤ (2187264000 * ε) * D x at hclose
      have hm := mul_le_mul_of_nonneg_right hεfine hDx.le
      nlinarith
    have hmass := near_support_radius_power_le_mass μ hμ C hC hlower x (D x) hDx hadm hnear
    have harea := active_region_stopping_ball_area_le μ R hR k z Good S hS ε hε hεtiny hsmall
      hfit f hmodel x (hD x hx).1 (hD x hx).2
    have hsub : A ∩ closedBall x (5 * (D x / 128)) ⊆
        Set.range f ∩ closedBall x (D x / 16) := by
      intro y hy
      exact ⟨(hA hy.1).1, closedBall_subset_closedBall (by linarith) hy.2⟩
    calc
      _ ≤ (μH[(n : ℝ)] : Measure (Ambient d))
          (Set.range f ∩ closedBall x (D x / 16)) := measure_mono hsub
      _ ≤ (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) * (ENNReal.ofReal (D x)) ^ n := harea
      _ ≤ (activeRegionLocalAreaConstant n d * (4096 : ℝ≥0∞) ^ n) *
          (ENNReal.ofReal (C * 256 ^ n) * μ (closedBall x (D x / 128))) := mul_le_mul_right hmass _
      _ = _ := by unfold activeRegionSmallScaleAreaConstant; simp only [mul_assoc]

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

theorem active_region_zero_set_area_le_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (cellRegionZeroSet μ R hR k z Good) ≤
      activeRegionZeroAreaConstant n C * μ (cleanSupportCell μ R hR k z) := by
  classical
  let ι (t : ℕ) := ↥(activeLevelIndex μ R hR k z Good t)
  let B (t : ℕ) (i : ι t) := closedBall i.val.center (3 * latticeRadius R (k + t))
  have hrad (t : ℕ) (i : ι t) : i.val.radius = latticeRadius R (k + t) := by
    have hi := (mem_activeLevelIndex μ R hR k z Good t i).mp i.property
    simp only [SupportCellDescendant.radius, hi.1]
  have hdiam (t : ℕ) (i : ι t) : ediam (B t i) ≤ ENNReal.ofReal (6 * latticeRadius R (k + t)) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x i.val.center ≤ 3 * latticeRadius R (k + t) := hx
    have hy' : dist y i.val.center ≤ 3 * latticeRadius R (k + t) := hy
    have ht := dist_triangle_right x y i.val.center
    linarith
  have hcover (t : ℕ) : cellRegionZeroSet μ R hR k z Good ⊆ ⋃ i : ι t, B t i := by
    intro x hx
    have hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t) := by
      rw [show cellRegionStoppingScale μ R hR k z Good x = 0 from hx]
      exact latticeRadius_pos R hR (k + t)
    obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x hsmall
    exact mem_iUnion.mpr ⟨⟨i, (mem_activeLevelIndex μ R hR k z Good t i).mpr hi⟩, hxi.le⟩
  have hdecay : Tendsto (fun t : ℕ => 6 * latticeRadius R (k + t)) atTop (𝓝 0) := by
    simp_rw [latticeRadius_add]
    simpa only [mul_zero] using! (latticeRadius_tendsto_zero (latticeRadius R k)).const_mul 6
  have hdecay' : Tendsto (fun t : ℕ => ENNReal.ofReal (6 * latticeRadius R (k + t))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using! (ENNReal.continuous_ofReal.tendsto 0).comp hdecay
  apply hausdorff_measure_le_of_shrinking_finite_covers n _ ι _ hdecay' B hdiam hcover
  intro t
  have hmass := active_level_radius_power_sum_le_top μ C G hC hG hg hlower R hR k hcore z Good t
  calc
    _ ≤ ∑ i : ι t, (ENNReal.ofReal (6 * latticeRadius R (k + t))) ^ n :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left' (hdiam t i) n)
    _ = (6 : ℝ≥0∞) ^ n * ∑ i : ι t, (ENNReal.ofReal i.val.radius) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrad t i, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat, mul_pow]
    _ ≤ (6 : ℝ≥0∞) ^ n * (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) :=
      mul_le_mul_right hmass _
    _ = _ := by unfold activeRegionZeroAreaConstant; rw [mul_assoc]

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

theorem clean_top_radius_power_le_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (ENNReal.ofReal (latticeRadius R k)) ^ n ≤
      ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z) := by
  simpa only [SupportCellDescendant.radius, SupportCellDescendant.cell, supportCellRoot, Nat.add_zero]
    using! SupportCellDescendant.radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
      (supportCellRoot μ R hR k z)

theorem enlarged_top_ball_mass_le_clean_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) ≤
      enlargedTopMassConstant n C G * μ (cleanSupportCell μ R hR k z) := by
  have hr := latticeRadius_pos R hR k
  have hupper : μ (closedBall (z : Ambient d) (3 * latticeRadius R k)) ≤
      ENNReal.ofReal (G * 4 ^ n) * (ENNReal.ofReal (latticeRadius R k)) ^ n := by
    calc
      _ ≤ μ (ball (z : Ambient d) (4 * latticeRadius R k)) :=
        measure_mono (closedBall_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal (G * (4 * latticeRadius R k) ^ n) :=
        hg.2 (z : Ambient d) (4 * latticeRadius R k) (by positivity)
      _ = _ := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ G * 4 ^ n),
          ENNReal.ofReal_pow hr.le]
  have hlowerTop := clean_top_radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
  calc
    _ ≤ ENNReal.ofReal (G * 4 ^ n) * (ENNReal.ofReal (latticeRadius R k)) ^ n := hupper
    _ ≤ ENNReal.ofReal (G * 4 ^ n) *
        (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) := mul_le_mul_right hlowerTop _
    _ = _ := by unfold enlargedTopMassConstant; rw [mul_assoc]

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

theorem active_region_limit_area_le_original_top_oai {n d : ℕ}
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
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f) :
    (μH[(n : ℝ)] : Measure (Ambient d))
      (Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)) ≤
      activeRegionUniformAreaConstant n d C G * μ (cleanSupportCell μ R hR k z) := by
  let D := cellRegionStoppingScale μ R hR k z Good
  let Z := cellRegionZeroSet μ R hR k z Good
  let T := Set.range f ∩ closedBall (z : Ambient d) (2 * latticeRadius R k)
  let A := T ∩ {x | 0 < D x ∧ D x < latticeRadius R (k + 1)}
  let B := closedBall (z : Ambient d) (2 * latticeRadius R k) ∩
    {x | latticeRadius R (k + 1) ≤ D x}
  have hz := active_region_zero_set_area_le_top μ C G hC hG hg hlower R hR k hcore z Good
  have hs := active_region_small_positive_scale_area_le μ C hC hlower R hR k hcore z Good S hS
    ε hε hεfine hsmall hfit f hmodel A (fun _ hx => hx.1) (fun _ hx => hx.2)
  have ht := enlarged_top_ball_mass_le_clean_top μ C G hC hG hg hlower R hR k hcore z
  have hs' := hs.trans (mul_le_mul_right ht (activeRegionSmallScaleAreaConstant n d C))
  have hl := active_region_large_scale_area_le μ R hR k z Good S hS ε hε.le (by linarith)
    hfit f hmodel B inter_subset_left (fun _ hx => hx.2)
  have hr := clean_top_radius_power_le_mass μ C G hC hG hg hlower R hR k hcore z
  have hl' := hl.trans (mul_le_mul_right hr (activeRegionLargeAreaConstant n d))
  have hcover : T ⊆ (Z ∪ A) ∪ (Set.range f ∩ B) := by
    intro x hx
    by_cases hzero : D x = 0
    · exact Or.inl (Or.inl hzero)
    · have hnonneg : 0 ≤ D x := cellRegionStoppingScale_nonneg μ R hR k z Good x
      have hpos : 0 < D x := by exact lt_of_le_of_ne hnonneg (Ne.symm hzero)
      by_cases hsmallx : D x < latticeRadius R (k + 1)
      · exact Or.inl (Or.inr ⟨hx, hpos, hsmallx⟩)
      · exact Or.inr ⟨hx.1, hx.2, le_of_not_gt hsmallx⟩
  calc
    _ ≤ (μH[(n : ℝ)] : Measure (Ambient d)) ((Z ∪ A) ∪ (Set.range f ∩ B)) := measure_mono hcover
    _ ≤ ((μH[(n : ℝ)] : Measure (Ambient d)) Z + (μH[(n : ℝ)] : Measure (Ambient d)) A) +
        (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ B) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (activeRegionZeroAreaConstant n C * μ (cleanSupportCell μ R hR k z) +
        activeRegionSmallScaleAreaConstant n d C *
          (enlargedTopMassConstant n C G * μ (cleanSupportCell μ R hR k z))) +
        activeRegionLargeAreaConstant n d *
          (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) :=
      add_le_add (add_le_add hz hs') hl'
    _ = _ := by unfold activeRegionUniformAreaConstant; ring

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.active_region_limit_area_le_original_top_oai := @OAI.RieszRectifiability.active_region_limit_area_le_original_top_oai
