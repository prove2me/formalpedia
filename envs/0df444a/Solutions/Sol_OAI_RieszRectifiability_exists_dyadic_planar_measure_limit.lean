-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_dyadic_planar_measure_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:48.433219+00:00
-- url     : https://prove2.me/submissions/01de0e33-0233-4c5b-b490-86aed83146d6

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BallLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization to balls

Restricting a measure preserves its global upper growth bound and gives finite mass on
positive-radius balls. The diameter estimate controls pairs of points in a ball, while
the Lipschitz height estimate supplies the boundedness needed for local `MemLp` control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem finiteMeasure_restrict_ball_of_globalGrowth {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (μ.restrict (ball a R)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using! (hg.2 a R hR).trans_lt ENNReal.ofReal_lt_top

theorem lipschitz_height_bound_on_ball {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a x : Ambient d) (R : ℝ) (hx : x ∈ ball a R) :
    |w x| ≤ |w a| + (K : ℝ) * R := by
  have hdiff : |w x - w a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hw.dist_le_mul x a
  have habs : |w x| ≤ |w x - w a| + |w a| := by
    simpa only [sub_zero] using! abs_sub_le (w x) (w a) 0
  have hprod := mul_le_mul_of_nonneg_left hx.le K.coe_nonneg
  linarith

theorem lipschitz_height_memLp_on_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    MemLp w 2 (μ.restrict (ball a R)) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable (|w a| + (K : ℝ) * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa only [Real.norm_eq_abs] using! lipschitz_height_bound_on_ball w K hw a x R hx

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalCoordinateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

theorem normalDirection_norm {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    ‖normalDirection N i‖ = 1 := by
  rw [normalDirection, N.norm_map]
  exact (EuclideanSpace.basisFun (Fin q) ℝ).norm_eq_one i

theorem normalCoordinate_eq_inner {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x : Ambient d) :
    normalCoordinate a N i x = inner ℝ (normalDirection N i) (x - a) := by
  calc
    _ = inner ℝ (EuclideanSpace.basisFun (Fin q) ℝ i)
        (N.toContinuousLinearMap.adjoint (x - a)) :=
      (EuclideanSpace.basisFun_inner (Fin q) ℝ (N.toContinuousLinearMap.adjoint (x - a)) i).symm
    _ = _ := N.toContinuousLinearMap.adjoint_inner_right _ _

theorem normalCoordinate_difference {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x y : Ambient d) :
    normalCoordinate a N i x - normalCoordinate a N i y = inner ℝ (normalDirection N i) (x - y) := by
  rw [normalCoordinate_eq_inner, normalCoordinate_eq_inner, ← inner_sub_right,
    sub_sub_sub_cancel_right]

theorem normalCoordinate_lipschitz {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : LipschitzWith 1 (normalCoordinate a N i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, normalCoordinate_difference, dist_eq_norm]
  have h := abs_real_inner_le_norm (normalDirection N i) (x - y)
  simpa only [normalDirection_norm, one_mul] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_NormalHeightFromPlaneMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem normalCoordinate_abs_le_plane_distance {q d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (x : Ambient d) :
    |normalCoordinate a N i x| ≤ infDist x (S : Set (Ambient d)) := by
  rw [hdist x]
  exact PiLp.norm_apply_le (N.toContinuousLinearMap.adjoint (x - a)) i

theorem normalCoordinate_memLp_on_ball {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q)
    (R : ℝ) (hR : 0 < R) : MemLp (normalCoordinate a N i) 2 (μ.restrict (ball 0 R)) :=
  lipschitz_height_memLp_on_ball m C μ hg (normalCoordinate a N i) 1
    (normalCoordinate_lipschitz a N i) 0 R hR

theorem normalized_normalCoordinate_memLp_on_ball {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q)
    (R : ℝ) (hR : 0 < R) (δ : ℝ) :
    MemLp (fun x => normalCoordinate a N i x / δ) 2 (μ.restrict (ball 0 R)) := by
  simpa only [div_eq_mul_inv] using! (normalCoordinate_memLp_on_ball m μ C hg a N i R hR).mul_const δ⁻¹

theorem normalCoordinate_second_moment_le_plane {q d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth m C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (i : Fin q) (R : ℝ) (hR : 0 < R) :
    (∫ x in ball (0 : Ambient d) R, normalCoordinate a N i x ^ 2 ∂μ) ≤
      ∫ x in ball (0 : Ambient d) R, infDist x (S : Set (Ambient d)) ^ 2 ∂μ := by
  apply integral_mono (normalCoordinate_memLp_on_ball m μ C hg a N i R hR).integrable_sq
    (squared_infDist_integrableOn_ball μ 0 R S hS)
  intro x
  have h := (sq_le_sq₀ (abs_nonneg (normalCoordinate a N i x)) infDist_nonneg).mpr
    (normalCoordinate_abs_le_plane_distance S a N hdist i x)
  simpa only [sq_abs] using! h

theorem normalCoordinate_dyadic_source_bound {n q d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d)
    (hdist : ∀ x, infDist x (S : Set (Ambient d)) = ‖N.toContinuousLinearMap.adjoint (x - a)‖)
    (M δ b : ℝ) (l : ℕ)
    (hbound : (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ) ≤
      M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (i : Fin q) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate a N i x ^ 2 ∂μ) ≤
      δ ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  calc
    _ ≤ ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S : Set (Ambient d)) ^ 2 ∂μ :=
      normalCoordinate_second_moment_le_plane n μ C hg S hS a N hdist i ((2 : ℝ) ^ l) (by positivity)
    _ ≤ M * (δ * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2) := hbound
    _ = _ := by rw [pow_add ((2 : ℝ) ^ l) n 2]; ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_PlaneSupportFromMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem lipschitz_square_energy_lower_bound {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : Ambient d → ℝ) (hf : LipschitzWith 1 f)
    (s : Set (Ambient d)) (hi : IntegrableOn (fun y => f y ^ 2) s μ)
    (x : Ambient d) (ε r c : ℝ) (hε : 0 ≤ ε) (hr : r ≤ ε / 2)
    (hsub : ball x r ⊆ s) (hmass : c ≤ μ.real (ball x r)) (hlarge : ε ≤ f x) :
    (ε / 2) ^ 2 * c ≤ ∫ y in s, f y ^ 2 ∂μ := by
  have hpoint : ∀ y ∈ ball x r, (ε / 2) ^ 2 ≤ f y ^ 2 := by
    intro y hy
    have hd : dist x y ≤ r := by
      simpa only [dist_comm] using! (show dist y x < r from hy).le
    have hdiff : f x - f y ≤ dist x y := by
      have h := hf.dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      exact (le_abs_self _).trans h
    have hfy : ε / 2 ≤ f y := by linarith
    nlinarith [sq_nonneg (f y - ε / 2)]
  have hfinite : μ (ball x r) ≠ ∞ := ne_of_lt
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top)
  calc
    _ ≤ (ε / 2) ^ 2 * μ.real (ball x r) :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ ≤ ∫ y in ball x r, f y ^ 2 ∂μ :=
      setIntegral_ge_of_const_le_real measurableSet_ball hfinite hpoint
        (IntegrableOn.mono_set hi hsub)
    _ ≤ _ := setIntegral_mono_set hi (Eventually.of_forall fun y => sq_nonneg (f y))
      (Eventually.of_forall fun y hy => hsub hy)

theorem small_square_integrals_force_support_tube {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (f : ℕ → Ambient d → ℝ) (hf : ∀ j, LipschitzWith 1 (f j))
    (a : Ambient d) (R : ℝ)
    (hi : ∀ j, IntegrableOn (fun x => f j x ^ 2) (ball a (R + 1)) (μ j))
    (hlim : Tendsto (fun j => ∫ x in ball a (R + 1), f j x ^ 2 ∂μ j) atTop (𝓝 0))
    (hball : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → c ≤ (μ j).real (ball x r))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → f j x < ε := by
  let r := min 1 (ε / 2)
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  obtain ⟨c, hc, hbc⟩ := hball r hr
  have ht : 0 < (ε / 2) ^ 2 * c := mul_pos (sq_pos_of_pos (by positivity)) hc
  filter_upwards [hbc, hlim.eventually (gt_mem_nhds ht)] with j hj hsmall
  intro x hx hxsupport
  by_contra hlarge
  have hsub : ball x r ⊆ ball a (R + 1) := by
    intro y hy
    have htri := dist_triangle y x a
    have hy' : dist y x < r := hy
    have hx' : dist x a < R := hx
    have hr1 : r ≤ 1 := min_le_left _ _
    exact mem_ball.mpr (by linarith)
  have h := lipschitz_square_energy_lower_bound (μ j) (f j) (hf j)
    (ball a (R + 1)) (hi j) x ε r c hε.le (min_le_right _ _) hsub
    (hj x hx hxsupport) (le_of_not_gt hlarge)
  exact (not_lt_of_ge h) hsmall

theorem moving_plane_support_tube_of_moments {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : Ambient d) (R : ℝ)
    (hlim : Tendsto (fun j => ∫ x in ball a (R + 1),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support →
      infDist x (S j : Set (Ambient d)) < ε := by
  apply small_square_integrals_force_support_tube μ
    (fun j x => infDist x (S j : Set (Ambient d))) (fun j => lipschitz_infDist_pt _)
    a R (fun j => squared_infDist_integrableOn_ball (μ j) a (R + 1) _ (hS j)) hlim _ ε hε
  intro r hr
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ClosedBallMeasureComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem measure_le_of_closedBall_le {d : ℕ} (ρ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ρ] [IsFiniteMeasureOnCompacts ν]
    (hball : ∀ x : Ambient d, ∀ r : ℝ, 0 < r → ρ (closedBall x r) ≤ ν (closedBall x r)) :
    ρ ≤ ν := by
  apply Measure.le_iff'.mpr
  intro s
  let v := Besicovitch.vitaliFamily ρ
  apply v.measure_le_of_frequently_le ν Measure.AbsolutelyContinuous.rfl s
  intro x _hx
  apply Filter.Eventually.frequently
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with a ha
  obtain ⟨r, hr, rfl⟩ := ha
  exact hball x r hr

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

theorem planarPullbackMeasure_recover {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d))) :
    (planarPullbackMeasure L ν).map L = ν := by
  rw [planarPullbackMeasure, Measure.map_map L.continuous.measurable
    L.toContinuousLinearMap.adjoint.continuous.measurable]
  have heq : (fun x => L (L.toContinuousLinearMap.adjoint x)) =ᵐ[ν] id := by
    filter_upwards [ν.support_mem_ae] with x hx
    obtain ⟨y, hy⟩ := hs hx
    change L y = x at hy
    rw [← hy]
    have hleft : L.toContinuousLinearMap.adjoint (L y) = y := DFunLike.congr_fun L.adjoint_comp_self y
    simp only [id_eq, hleft]
  exact (Measure.map_congr heq).trans Measure.map_id

theorem planarPullbackMeasure_ball {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (x : Ambient n) (r : ℝ) : planarPullbackMeasure L ν (ball x r) = ν (ball (L x) r) := by
  rw [planarPullbackMeasure, Measure.map_apply L.toContinuousLinearMap.adjoint.continuous.measurable
    measurableSet_ball]
  apply measure_congr
  filter_upwards [ν.support_mem_ae] with y hy
  obtain ⟨z, hz⟩ := hs hy
  change L z = y at hz
  rw [← hz]
  have hleft : L.toContinuousLinearMap.adjoint (L z) = z := DFunLike.congr_fun L.adjoint_comp_self z
  apply propext
  change dist (L.toContinuousLinearMap.adjoint (L z)) x < r ↔ dist (L z) (L x) < r
  rw [hleft, L.dist_map]

theorem planarPullbackMeasure_growth {n d : ℕ} (L : Ambient n →ₗᵢ[ℝ] Ambient d)
    (ν : Measure (Ambient d)) (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hg : GlobalUpperGrowth n C ν) : GlobalUpperGrowth n C (planarPullbackMeasure L ν) := by
  refine ⟨hg.1, ?_⟩
  intro x r hr
  rw [planarPullbackMeasure_ball L ν hs]
  exact hg.2 (L x) r hr

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GrowthVolumeDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Volume domination from intrinsic upper growth

An upper growth bound in the intrinsic Euclidean dimension implies domination
by Lebesgue measure. The density bound is normalized by the unit-ball volume
and includes the dimensional factor needed for closed-ball comparison.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem intrinsic_growth_le_volume (n : ℕ) (C : ℝ) (μ : Measure (Ambient n))
    (hg : GlobalUpperGrowth n C μ) :
    μ ≤ intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts C μ hg
  let V : ℝ := (volume : Measure (Ambient n)).real (ball 0 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (measure_ball_pos volume (0 : Ambient n) zero_lt_one)) measure_ball_lt_top.ne
  have hD : (intrinsicGrowthDensityBound n C : ℝ) = C * 2 ^ n / V := by
    exact Real.coe_toNNReal _ (div_nonneg (mul_nonneg hg.1 (by positivity)) hV.le)
  have hDV : (intrinsicGrowthDensityBound n C : ℝ) * V = C * 2 ^ n := by
    rw [hD]
    exact div_mul_cancel₀ _ hV.ne'
  apply measure_le_of_closedBall_le
  intro x r hr
  have hvol : (volume : Measure (Ambient n)).real (closedBall x r) = r ^ n * V := by
    simpa only [Ambient, finrank_euclideanSpace, Fintype.card_fin] using!
      (Measure.addHaar_real_closedBall (volume : Measure (Ambient n)) x hr.le)
  have hid : (intrinsicGrowthDensityBound n C : ℝ) *
      (volume : Measure (Ambient n)).real (closedBall x r) = C * (2 * r) ^ n := by
    rw [hvol]
    calc
      _ = ((intrinsicGrowthDensityBound n C : ℝ) * V) * r ^ n := by ring
      _ = _ := by rw [hDV, mul_pow, mul_assoc]
  calc
    μ (closedBall x r) ≤ μ (ball x (2 * r)) :=
      measure_mono (closedBall_subset_ball (by linarith))
    _ ≤ ENNReal.ofReal (C * (2 * r) ^ n) := hg.2 x (2 * r) (by positivity)
    _ = ENNReal.ofReal ((intrinsicGrowthDensityBound n C : ℝ) *
        (volume : Measure (Ambient n)).real (closedBall x r)) := congrArg ENNReal.ofReal hid.symm
    _ = (intrinsicGrowthDensityBound n C • (volume : Measure (Ambient n)))
        (closedBall x r) := by
      rw [ENNReal.ofReal_mul (intrinsicGrowthDensityBound n C).coe_nonneg,
        ENNReal.ofReal_coe_nnreal, Measure.real,
        ENNReal.ofReal_toReal (measure_closedBall_lt_top.ne), Measure.coe_nnreal_smul_apply]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_BoundedPlanarDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded densities for measures supported on planes

Domination by a scalar multiple of a reference measure bounds the
Radon–Nikodym derivative and gives a measurable, everywhere bounded density.
Intrinsic upper growth applies this construction to Euclidean volume and to
measures supported on the range of a linear isometry.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rnDeriv_le_of_nnreal_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite ν] (c : ℝ≥0) (hdom : μ ≤ c • ν) :
    ∀ᵐ x ∂ν, μ.rnDeriv ν x ≤ (c : ℝ≥0∞) := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν)
  intro s _hs _hfin
  simpa only [lintegral_const, Measure.restrict_apply_univ, Measure.coe_nnreal_smul_apply] using!
    (Measure.setLIntegral_rnDeriv_le (μ := μ) (ν := ν) s).trans (hdom s)

theorem exists_bounded_density_of_domination {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (c : ℝ≥0) (hdom : μ ≤ c • ν) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ c) ∧
      ν.withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let f : α → ℝ := fun x => min (c : ℝ) (μ.rnDeriv ν x).toReal
  have hm : Measurable f := measurable_const.min (μ.measurable_rnDeriv ν).ennreal_toReal
  have heq : (fun x => ENNReal.ofReal (f x)) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [rnDeriv_le_of_nnreal_domination μ ν c hdom] with x hx
    have hne : μ.rnDeriv ν x ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hx
    have hreal : (μ.rnDeriv ν x).toReal ≤ (c : ℝ) := by
      simpa only [ENNReal.coe_toReal] using! (ENNReal.toReal_le_toReal hne ENNReal.coe_ne_top).mpr hx
    change ENNReal.ofReal (min (c : ℝ) (μ.rnDeriv ν x).toReal) = μ.rnDeriv ν x
    rw [min_eq_right hreal, ENNReal.ofReal_toReal hne]
  refine ⟨f, hm, fun x => ⟨le_min c.coe_nonneg ENNReal.toReal_nonneg, min_le_left _ _⟩, ?_⟩
  rw [withDensity_congr_ae heq]
  exact Measure.withDensity_rnDeriv_eq μ ν
    (hdom.absolutelyContinuous.trans Measure.smul_absolutelyContinuous)

theorem exists_bounded_intrinsic_density (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient n)) (hg : GlobalUpperGrowth n C μ) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n C) ∧
      (volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts C μ hg
  exact exists_bounded_density_of_domination μ volume (intrinsicGrowthDensityBound n C)
    (intrinsic_growth_le_volume n C μ hg)

theorem exists_bounded_planar_density {n d : ℕ}
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d))
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C : ℝ) (hg : GlobalUpperGrowth n C ν) :
    ∃ f : Ambient n → ℝ, Measurable f ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n C) ∧
      ((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).map L = ν := by
  obtain ⟨f, hm, hb, heq⟩ := exists_bounded_intrinsic_density n C
    (planarPullbackMeasure L ν) (planarPullbackMeasure_growth L ν hs C hg)
  refine ⟨f, hm, hb, ?_⟩
  rw [heq]
  exact planarPullbackMeasure_recover L ν hs

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_IsometricFrameCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set Function Filter Topology

theorem exists_isometric_frame_subsequence {n d : ℕ}
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
      Tendsto (fun j => (L (ρ j)).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) := by
  let A : ℕ → Ambient n →L[ℝ] Ambient d := fun j => (L j).toContinuousLinearMap
  have hbound : ∀ j, A j ∈ closedBall 0 1 := by
    intro j
    rw [mem_closedBall, dist_zero_right]
    apply ContinuousLinearMap.opNorm_le_bound (A j) zero_le_one
    intro x
    simpa only [A, LinearIsometry.coe_toContinuousLinearMap, (L j).norm_map, one_mul]
      using! (le_rfl : ‖x‖ ≤ ‖x‖)
  obtain ⟨T, _hT, ρ, hρ, hlim⟩ := (isCompact_closedBall (0 : Ambient n →L[ℝ] Ambient d) 1).tendsto_subseq hbound
  have hnorm : ∀ x, ‖T x‖ = ‖x‖ := by
    intro x
    have heval : Continuous (fun B : Ambient n →L[ℝ] Ambient d => B x) := by fun_prop
    have ht : Tendsto (fun j => ‖A (ρ j) x‖) atTop (𝓝 ‖T x‖) :=
      ((heval.tendsto T).comp hlim).norm
    have ht' : Tendsto (fun j => ‖A (ρ j) x‖) atTop (𝓝 ‖x‖) := by
      simpa only [A, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map] using!
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))
    exact tendsto_nhds_unique ht ht'
  let Llim : Ambient n →ₗᵢ[ℝ] Ambient d := { toLinearMap := T.toLinearMap, norm_map' := hnorm }
  refine ⟨ρ, hρ, Llim, ?_⟩
  convert! hlim using 1
  all_goals try with_reducible_and_instances rfl

theorem tangentPlaneProjection_tendsto {n d : ℕ}
    (a : ℕ → Ambient d) (alim : Ambient d) (ha : Tendsto a atTop (𝓝 alim))
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hL : Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap))
    (x : Ambient d) :
    Tendsto (fun j => tangentPlaneProjection (a j) (L j) x) atTop
      (𝓝 (tangentPlaneProjection alim Llim x)) := by
  let P : (Ambient d × (Ambient n →L[ℝ] Ambient d)) → Ambient d :=
    fun p => p.1 + p.2 (p.2.adjoint (x - p.1))
  have hc : Continuous P := by
    apply continuous_fst.add
    apply continuous_snd.clm_apply
    exact (ContinuousLinearMap.adjoint.continuous.comp continuous_snd).clm_apply
      (continuous_const.sub continuous_fst)
  exact (hc.tendsto (alim, Llim.toContinuousLinearMap)).comp (ha.prodMk_nhds hL)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FittingPlaneFrameSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem closest_plane_base_tendsto_zero {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : ℕ → Ambient d) (ha : ∀ j, ‖a j‖ = infDist (0 : Ambient d) (S j : Set (Ambient d)))
    (hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall fun j => hr.trans_le (norm_nonneg (a j))
  · intro ε hε
    have hlim' : Tendsto (fun j => ∫ x in ball (0 : Ambient d) (1 + 1),
        infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
      simpa only [one_add_one_eq_two] using! hlim
    filter_upwards [moving_plane_support_tube_of_moments n μ C hC hlower hdiam
      S hS 0 1 hlim' ε hε] with j hj
    rw [ha j]
    exact hj 0 (mem_ball_self zero_lt_one) (hzero j)

theorem exists_fitting_plane_frame_subsequence {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ a : ℕ → Ambient d,
      ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧
        (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        ∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖ := by
  choose a ha hnorm L hL N horth hsplit hdist using fun j =>
    exists_affine_plane_normal_frame (S j) (hS j)
  have ha0 := closest_plane_base_tendsto_zero μ C hC hlower hdiam hzero S
    (fun j => (hS j).1) a hnorm hlim
  obtain ⟨ρ, hρ, Llim, hLlim⟩ := exists_isometric_frame_subsequence L
  exact ⟨ρ, hρ, (fun j => a (ρ j)), (fun j => L (ρ j)), (fun j => N (ρ j)),
    Llim, ha0.comp hρ.tendsto_atTop, hLlim,
    (fun j => ha (ρ j)), (fun j => hL (ρ j)), (fun j => horth (ρ j)),
    (fun j => hsplit (ρ j)), (fun j => hdist (ρ j))⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_DyadicFittingFrameLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem fixed_plane_dyadic_moment_tendsto_zero {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (S : ℕ → AffineSubspace ℝ (Ambient d))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (l : ℕ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun j => M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) atTop (𝓝 0) := by
    simpa using! (((hδ.mul_const (b ^ l)).pow 2).const_mul M).mul_const (((2 : ℝ) ^ l) ^ (n + 2))
  apply squeeze_zero' (Eventually.of_forall (fun j =>
    integral_nonneg (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))) _ hlim
  filter_upwards [hT.eventually (eventually_ge_atTop l)] with j hj
  exact hmoment j l hj

theorem exists_dyadically_controlled_frame_subsequence {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ a : ℕ → Ambient d,
      ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - n), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        ∀ i : Fin (d - n), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  have hlim : Tendsto (fun j => ∫ x in ball (0 : Ambient d) 2,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
    simpa only [pow_one] using! fixed_plane_dyadic_moment_tendsto_zero μ S δ T hδ hT M b hmoment 1
  obtain ⟨ρ, hρ, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist⟩ :=
    exists_fitting_plane_frame_subsequence μ C hC hlower hdiam hzero S hS hlim
  refine ⟨ρ, hρ, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist, ?_, ?_⟩
  · intro i j R hR
    exact normalized_normalCoordinate_memLp_on_ball n (μ (ρ j)) G (hg (ρ j))
      (a j) (N j) i R hR (δ (ρ j))
  · intro i j l hl
    exact normalCoordinate_dyadic_source_bound (μ (ρ j)) G (hg (ρ j))
      (S (ρ j)) (hS (ρ j)).1 (a j) (N j) (hdist j) M (δ (ρ j)) b l (hmoment (ρ j) l hl) i

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicMomentAllRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem plane_moment_tendsto_zero_from_dyadic {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (hdyadic : ∀ l : ℕ, Tendsto (fun j => ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
  obtain ⟨l, _hl, hlarge⟩ := exists_nat_pow_near (le_max_left (1 : ℝ) R) (by norm_num : (1 : ℝ) < 2)
  have hsub : ball (0 : Ambient d) R ⊆ ball 0 ((2 : ℝ) ^ (l + 1)) :=
    ball_subset_ball ((le_max_right 1 R).trans hlarge.le)
  apply squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))
    _ (hdyadic (l + 1))
  intro j
  exact setIntegral_mono_set
    (squared_infDist_integrableOn_ball (μ j) 0 ((2 : ℝ) ^ (l + 1)) _ (hS j))
    (Eventually.of_forall (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))
    (Eventually.of_forall (fun _ hx => hsub hx))

theorem fixed_plane_moment_tendsto_zero_on_ball {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (R : ℝ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) :=
  plane_moment_tendsto_zero_from_dyadic μ S hS
    (fixed_plane_dyadic_moment_tendsto_zero μ S δ T hδ hT M b hmoment) R

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

theorem compactTestConvergence_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have hquarter : 0 < r / 4 := by positivity
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by
    rw [div_pow]
    ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    filter_upwards [hdiam (r / 4) hquarter] with j hj
    intro y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hlower j y hy (r / 4) ⟨hquarter, hj⟩)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C)] at h
    simpa only [heq, Measure.real] using! h
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

theorem compactTestConvergence_origin_mem_support {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) : (0 : Ambient d) ∈ ν.support := by
  apply compactTestConvergence_mem_support_of_ball_masses μ ν hlocal 0
  intro r hr
  obtain ⟨c, hc, hmass⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmass] with j hj
  exact hj 0 (hzero j)

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_MovingTubeSupportLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Support containment from moving tubes

Nonnegative, uniformly Lipschitz functions that vanish along the approximating
supports also vanish on the support of a compact-test limit measure. Applied to
distances from affine planes with convergent frames, this identifies the plane
containing the limiting support.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology EuclideanGeometry
open scoped NNReal ENNReal

theorem moving_lipschitz_tubes_vanish_on_limit_support {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (f : ℕ → Ambient d → ℝ)
    (hf : ∀ j, LipschitzWith 1 (f j)) (hnn : ∀ j x, 0 ≤ f j x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → f j x < ε) :
    ∀ x ∈ ν.support, Tendsto (fun j => f j x) atTop (𝓝 0) := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro r hr
    exact Eventually.of_forall (fun j => hr.trans_le (hnn j x))
  · intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hR : 0 < ‖x‖ + ε / 2 := by linarith [norm_nonneg x]
    filter_upwards [compactTestConvergence_nearby_support μ ν hlocal x hx (ε / 2) hhalf,
      htube (‖x‖ + ε / 2) (ε / 2) hR hhalf] with j hnear hjtube
    obtain ⟨y, hysupp, hyball⟩ := hnear
    have hyx : dist y x < ε / 2 := hyball
    have hy0 : y ∈ ball (0 : Ambient d) (‖x‖ + ε / 2) := by
      have htri := dist_triangle y x (0 : Ambient d)
      simp only [mem_ball, dist_zero_right] at htri ⊢
      linarith
    have hsmall := hjtube y hy0 hysupp
    have hdiff : f j x - f j y ≤ dist x y := by
      have h := (hf j).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      exact (le_abs_self _).trans h
    rw [dist_comm x y] at hdiff
    linarith

theorem moving_plane_limit_support {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (a : ℕ → Ambient d) (ha : ∀ j, a j ∈ S j) (ha0 : Tendsto a atTop (𝓝 0))
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (hL : ∀ j, (L j).toLinearMap.range = (S j).direction)
    (Llim : Ambient n →ₗᵢ[ℝ] Ambient d)
    (hLlim : Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap))
    (hmoment : ∀ R : ℝ, 0 < R →
      Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
        infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) :
    ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) := by
  have htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support →
        infDist x (S j : Set (Ambient d)) < ε := by
    intro R ε hR hε
    exact moving_plane_support_tube_of_moments n μ C hC hlower hdiam S hS 0 R
      (hmoment (R + 1) (by linarith)) ε hε
  have hzero := moving_lipschitz_tubes_vanish_on_limit_support μ ν hlocal
    (fun j x => infDist x (S j : Set (Ambient d)))
    (fun j => lipschitz_infDist_pt _) (fun _ _ => infDist_nonneg) htube
  intro x hx
  have heq : ∀ j, infDist x (S j : Set (Ambient d)) = dist x (tangentPlaneProjection (a j) (L j) x) := by
    intro j
    let : Nonempty (S j) := (hS j).to_subtype
    rw [← dist_orthogonalProjection_eq_infDist (S j) x,
      affine_plane_projection_of_frame (S j) (a j) (ha j) (L j) (hL j)]
  have hdist0 : Tendsto (fun j => dist x (tangentPlaneProjection (a j) (L j) x)) atTop (𝓝 0) := by
    simpa only [heq] using! hzero x hx
  have hdistlim : Tendsto (fun j => dist x (tangentPlaneProjection (a j) (L j) x)) atTop
      (𝓝 (dist x (tangentPlaneProjection 0 Llim x))) :=
    tendsto_const_nhds.dist (tangentPlaneProjection_tendsto a 0 ha0 L Llim hLlim x)
  have he := dist_eq_zero.mp (tendsto_nhds_unique hdistlim hdist0)
  simp only [tangentPlaneProjection, zero_add, sub_zero] at he
  exact ⟨Llim.toContinuousLinearMap.adjoint x, he.symm⟩

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OriginalADLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Compact-test limits retain the original upper growth and lower AD mass bounds along a
subsequence whose support diameters eventually admit every fixed positive radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_original_AD_growth_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  obtain ⟨c, hc, hmass⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam 1 zero_lt_one
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hmass
  have hshift : StrictMono (fun j : ℕ => j + J) := fun _ _ h => Nat.add_lt_add_right h J
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlimit, hgν⟩ := exists_original_growth_limit n
    (fun j => μ (j + J)) G c hc (fun j => hg (j + J))
      (fun j => hJ (j + J) (Nat.le_add_left J j) 0 (hzero (j + J)))
  let := hfinite
  have hρ' : StrictMono (fun j => ρ j + J) := hshift.comp hρ
  refine ⟨(fun j => ρ j + J), hρ', ν, hfinite, hne, hlimit, hgν, ?_⟩
  exact compactTestConvergence_AD_lower n (fun j => μ (ρ j + J)) ν hlimit C hC
    (fun j => hlower (ρ j + J)) (fun r hr => hρ'.tendsto_atTop.eventually (hdiam r hr))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_DyadicPlanarMeasureLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic planar measure limits

Vanishing dyadic plane moments yield a subsequential AD growth limit supported on a
linear plane through the origin. The limit has a bounded intrinsic density, while
the convergent frames retain the normal-coordinate moment and local `MemLp` bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_planar_measure_limit_oai {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane n (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - n) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient n →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r)) ∧
        ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient n → ℝ, Measurable f ∧
          (∀ x, 0 ≤ f x ∧ f x ≤ intrinsicGrowthDensityBound n (G * 2 ^ n)) ∧
          ((volume : Measure (Ambient n)).withDensity (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - n), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        ∀ i : Fin (d - n), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2 := by
  obtain ⟨α, hα, a, L, N, Llim, ha0, hLlim, ha, hL, horth, hsplit, hdist, hmem, hsource⟩ :=
    exists_dyadically_controlled_frame_subsequence μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment
  obtain ⟨β, hβ, ν, hfinite, hne, hlocal, hgν, hlowerν⟩ := exists_original_AD_growth_limit n
    (fun j => μ (α j)) C G hC (fun j => hg (α j)) (fun j => hlower (α j))
      (fun r hr => hα.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (α j))
  let := hfinite
  have hρ : StrictMono (fun j => α (β j)) := hα.comp hβ
  have hsupport : ν.support ⊆ (Llim.toLinearMap.range : Set (Ambient d)) := by
    apply moving_plane_limit_support (fun j => μ (α (β j))) ν hlocal C hC
      (fun j => hlower (α (β j))) (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr))
      (fun j => S (α (β j))) (fun j => (hS (α (β j))).1)
      (fun j => a (β j)) (fun j => ha (β j)) (ha0.comp hβ.tendsto_atTop)
      (fun j => L (β j)) (fun j => hL (β j)) Llim (hLlim.comp hβ.tendsto_atTop)
    intro R _hR
    exact (fixed_plane_moment_tendsto_zero_on_ball μ S (fun j => (hS j).1)
      δ T hδ hT M b hmoment R).comp hρ.tendsto_atTop
  have horigin : (0 : Ambient d) ∈ ν.support := compactTestConvergence_origin_mem_support n
    (fun j => μ (α (β j))) ν hlocal C hC (fun j => hlower (α (β j)))
      (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr)) (fun j => hzero (α (β j)))
  have hdensity := exists_bounded_planar_density Llim ν hsupport (G * 2 ^ n) hgν
  refine ⟨(fun j => α (β j)), hρ, ν, (fun j => a (β j)), (fun j => L (β j)),
    (fun j => N (β j)), Llim, hfinite, hne, hlocal, hgν, hlowerν, hsupport, horigin, hdensity,
    ha0.comp hβ.tendsto_atTop, hLlim.comp hβ.tendsto_atTop,
    (fun j => ha (β j)), (fun j => hL (β j)), (fun j => horth (β j)),
    (fun j => hsplit (β j)), (fun j => hdist (β j)), ?_, ?_⟩
  · exact fun i j R hR => hmem i (β j) R hR
  · exact fun i j l hl => hsource i (β j) l hl

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_dyadic_planar_measure_limit_oai := @OAI.RieszRectifiability.exists_dyadic_planar_measure_limit_oai
