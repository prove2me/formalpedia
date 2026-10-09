-- Prove2me | solution 1 for OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:22:46.062991+00:00
-- url     : https://prove2.me/submissions/6e4ef60f-e83c-4f12-bb06-b38c3754de5e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B100
import Theorems.Thm_OAI_Erdos3_cutoff_box_image_comparison_sqrt

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteInversePerturbation
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_twice_mul_of_inverse_perturbation
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) (v : E) :
    ‖v‖ ≤ 2 * (K : ℝ) * ‖B v‖ := by
  have hid : v = A.inverse (B v) - A.inverse ((B - A) v) := by
    rw [← map_sub]
    simp only [sub_apply, sub_sub_cancel, hA.inverse_apply_self]
  have hmain : ‖A.inverse (B v)‖ ≤ (K : ℝ) * ‖B v‖ :=
    (A.inverse.le_opNorm _).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have herr : ‖A.inverse ((B - A) v)‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    calc
      _ ≤ ‖A.inverse‖ * ‖(B - A) v‖ := A.inverse.le_opNorm _
      _ ≤ (K : ℝ) * (‖B - A‖ * ‖v‖) :=
        mul_le_mul hK ((B - A).le_opNorm _) (norm_nonneg _) K.coe_nonneg
      _ = ((K : ℝ) * ‖B - A‖) * ‖v‖ := by ring
      _ ≤ (1 / 2 : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hnorm : ‖v‖ ≤ (K : ℝ) * ‖B v‖ + (1 / 2 : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖A.inverse (B v) - A.inverse ((B - A) v)‖ := congrArg norm hid
      _ ≤ ‖A.inverse (B v)‖ + ‖A.inverse ((B - A) v)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hmain herr
  linarith

theorem inverse_perturbation_bound [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.IsInvertible) (K : ℝ≥0)
    (hK : ‖A.inverse‖ ≤ K) (hsmall : (K : ℝ) * ‖B - A‖ ≤ 1 / 2) :
    B.IsInvertible ∧ ‖B.inverse‖ ≤ 2 * (K : ℝ) := by
  have hlower := norm_le_twice_mul_of_inverse_perturbation A B hA K hK hsmall
  have hinj : Function.Injective B := by
    intro x y hxy
    have h := hlower (x - y)
    rw [map_sub, hxy, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  have hbij : Function.Bijective B :=
    ⟨hinj, LinearMap.surjective_of_injective (f := B.toLinearMap) hinj⟩
  have hB : B.IsInvertible :=
    ⟨(LinearEquiv.ofBijective B.toLinearMap hbij).toContinuousLinearEquiv, rfl⟩
  refine ⟨hB, B.inverse.opNorm_le_bound (by positivity) ?_⟩
  intro v
  simpa only [hB.self_apply_inverse] using hlower (B.inverse v)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem ae_realDensityMeasure_of_forall_nonzero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (P : X → Prop)
    (hP : ∀ x, f x ≠ 0 → P x) : ∀ᵐ x ∂realDensityMeasure μ f, P x := by
  apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
  filter_upwards [] with x hx
  apply hP x
  intro hzero
  simp only [hzero, ENNReal.ofReal_zero, ne_eq, not_true_eq_false] at hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X]

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CutoffImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : Integrable w μ := by
  apply (integrable_const (1 : ℝ)).mono' hw.aestronglyMeasurable
  filter_upwards [] with a
  rw [Real.norm_of_nonneg (hbound a).1]
  exact (hbound a).2

theorem cutoffMeasure_mass_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : Measurable w)
    (hbound : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1) : (realDensityMeasure μ w).real Set.univ ≤ 1 := by
  have hi := cutoff_integrable μ w hw hbound
  rw [realDensityMeasure_real_univ μ w hi (fun a => (hbound a).1)]
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun a => (hbound a).2)
  simpa using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DivergenceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuousLinearMap_coordinate_sum (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    L v = L (∑ i, v i • Pi.single i (1 : ℝ)) := congrArg L hv.symm
    _ = ∑ i, v i * L (Pi.single i 1) := by simp only [map_sum, map_smul, smul_eq_mul]

theorem coordinateDivergence_continuous (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, ContDiff ℝ 1 (Q i)) : Continuous (coordinateDivergence Q) := by
  apply continuous_finsetSum
  intro i _
  exact ((hQ i).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem coordinateDivergence_hasCompactSupport (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, HasCompactSupport (Q i)) : HasCompactSupport (coordinateDivergence Q) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun i _ => (hQ i).fderiv_apply ℝ (Pi.single i 1))
  have heq : (∑ i, fun x => fderiv ℝ (Q i) x (Pi.single i 1)) = coordinateDivergence Q := by
    ext x
    simp [coordinateDivergence]
  rw [heq] at h
  exact h

theorem coordinate_vectorField_integration_by_parts (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, ContDiff ℝ 1 (Q i)) (hs : ∀ i, HasCompactSupport (Q i))
    (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, fderiv ℝ ψ x (fun i => Q i x)) = - ∫ x, coordinateDivergence Q x * ψ x := by
  have hDQ (i : ι) : Continuous (fun x => fderiv ℝ (Q i) x (Pi.single i 1)) :=
    ((hQ i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDψ (i : ι) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hleft (i : ι) : Integrable (fun x => Q i x * fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hQ i).continuous.mul (hDψ i)).integrable_of_hasCompactSupport ((hs i).mul_right)
  have hright (i : ι) : Integrable (fun x => fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) :=
    ((hDQ i).mul hψ.continuous).integrable_of_hasCompactSupport
      (((hs i).fderiv_apply ℝ (Pi.single i 1)).mul_right)
  have hprod (i : ι) : Integrable (fun x => Q i x * ψ x) :=
    ((hQ i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport ((hs i).mul_right)
  have hibp (i : ι) : (∫ x, Q i x * fderiv ℝ ψ x (Pi.single i 1)) =
      -∫ x, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hright i) (hleft i) (hprod i)
      (fun x _ => (hQ i).differentiable (by norm_num) x)
      (fun x _ => hψ.differentiable (by norm_num) x)
  calc
    (∫ x, fderiv ℝ ψ x (fun i => Q i x)) =
        ∫ x, ∑ i, Q i x * fderiv ℝ ψ x (Pi.single i 1) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact continuousLinearMap_coordinate_sum _ _
    _ = ∑ i, ∫ x, Q i x * fderiv ℝ ψ x (Pi.single i 1) :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = -(∑ i, ∫ x, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) := by
      simp only [hibp, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) := by
      rw [integral_finsetSum _ (fun i _ => hright i)]
    _ = -∫ x, coordinateDivergence Q x * ψ x := by
      simp only [coordinateDivergence, Finset.sum_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coordinateDivergence_tsupport_subset
    (Q : ι → (ι → ℝ) → ℝ) {K : Set (ι → ℝ)} (hK : IsClosed K)
    (hQ : ∀ i, tsupport (Q i) ⊆ K) : tsupport (coordinateDivergence Q) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  have hzero : coordinateDivergence Q x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hnot : x ∉ tsupport (fun y => fderiv ℝ (Q i) y (Pi.single i 1)) :=
      fun h => hxK (hQ i ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)) h))
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ (Q i) y (Pi.single i 1)) (x := x) hnot
  exact hx hzero

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CompactSmoothApproximation
namespace OAI

section

namespace Erdos3

open scoped ContDiff
open MeasureTheory

theorem exists_compact_smooth_uniform_approx {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℝ)
    (hf : Continuous f) (hs : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x, ‖g x - f x‖ ≤ ε := by
  obtain ⟨u, hu, huf⟩ := (hs.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  obtain ⟨R, hR, hbound⟩ := hs.isCompact.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  have hfix (x : E) : χ x * f x = f x := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero]
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hbound x (subset_tsupport f hx))
      rw [hχ, one_mul]
  refine ⟨fun x => χ x * u x, χ.contDiff.mul hu, χ.hasCompactSupport.mul_right, ?_⟩
  intro x
  calc
    ‖χ x * u x - f x‖ = ‖χ x * (u x - f x)‖ := by rw [mul_sub, hfix]
    _ = χ x * ‖u x - f x‖ := by rw [norm_mul, Real.norm_of_nonneg χ.nonneg]
    _ ≤ χ x * ε := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using (huf x).le) χ.nonneg
    _ ≤ ε := mul_le_of_le_one_left hε.le χ.le_one

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitTestClipping
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem unitTestClip_continuous : Continuous unitTestClip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem unitTestClip_zero : unitTestClip 0 = 0 := by norm_num [unitTestClip]

theorem unitTestClip_error {x : ℝ} (hx : |x| ≤ 1) (y : ℝ) :
    |x - unitTestClip y| ≤ |x - y| := by
  have hx' := abs_le.mp hx
  by_cases hy : y ≤ -1
  · have hmin : min 1 y = y := min_eq_right (by linarith)
    rw [unitTestClip, hmin, max_eq_left hy,
      abs_of_nonneg (by linarith : 0 ≤ x - -1), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · by_cases hy' : 1 ≤ y
    · rw [unitTestClip, min_eq_left hy', max_eq_right (by norm_num : (-1 : ℝ) ≤ 1),
        abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
      linarith
    · rw [unitTestClip, min_eq_right (le_of_not_ge hy'), max_eq_right (le_of_not_ge hy)]

theorem exists_continuous_unit_test_l1 {X : Type*} [TopologicalSpace X] [NormalSpace X]
    [MeasurableSpace X] [BorelSpace X] [R1Space X] [WeaklyLocallyCompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  obtain ⟨u, hus, herr, huc, hui⟩ := hfi.exists_hasCompactSupport_integral_sub_le hε
  let g := fun x => unitTestClip (u x)
  have hgc : Continuous g := unitTestClip_continuous.comp huc
  have hgb : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact unitTestClip_mem (u x)
  have hgi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hgc.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  refine ⟨g, hgc, hus.comp_left unitTestClip_zero, hgb, hgi, ?_⟩
  apply (integral_mono (hfi.sub hgi).norm (hfi.sub hui).norm ?_).trans herr
  intro x
  exact unitTestClip_error (by simpa only [Real.norm_eq_abs] using hbound x) (u x)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BoundedSmoothTestDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_unit_uniform_approx (f : E → ℝ) (hf : Continuous f)
    (hs : HasCompactSupport f) (hbound : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      ∀ x, ‖g x - f x‖ ≤ 2 * δ := by
  obtain ⟨u, hu, hus, herr⟩ := exists_compact_smooth_uniform_approx f hf hs hδ
  have hd : 0 < 1 + δ := by linarith
  have hub (x : E) : ‖u x‖ ≤ 1 + δ := by
    calc
      ‖u x‖ = ‖(u x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖u x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ 1 + δ := by linarith [herr x, hbound x]
  have hgb (x : E) : ‖u x / (1 + δ)‖ ≤ 1 := by
    rw [norm_div, Real.norm_of_nonneg hd.le]
    exact (div_le_one hd).mpr (hub x)
  refine ⟨fun x => u x / (1 + δ), hu.div_const _,
    hus.comp_left (g := fun y : ℝ => y / (1 + δ)) (zero_div _), hgb, ?_⟩
  intro x
  have hid : u x / (1 + δ) - u x = -δ * (u x / (1 + δ)) := by
    field_simp
    ring
  calc
    ‖u x / (1 + δ) - f x‖ ≤ ‖u x / (1 + δ) - u x‖ + ‖u x - f x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (u x / (1 + δ)) (u x) (f x)
    _ = δ * ‖u x / (1 + δ)‖ + ‖u x - f x‖ := by
      rw [hid, norm_mul, norm_neg, Real.norm_of_nonneg hδ.le]
    _ ≤ 2 * δ := by nlinarith [hgb x, herr x]

theorem exists_smooth_unit_test_l1 [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] [μ.Regular] (f : E → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      Integrable g μ ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε := by
  obtain ⟨v, hvc, hvs, hvb, hvi, herr⟩ := exists_continuous_unit_test_l1 μ f hf hbound (half_pos hε)
  let m := μ.real Set.univ
  have hm : 0 ≤ m := measureReal_nonneg
  let δ := ε / (4 * (m + 1))
  have hd : 0 < δ := div_pos hε (by positivity)
  obtain ⟨g, hgc, hgs, hgb, hgv⟩ := exists_smooth_unit_uniform_approx v hvc hvs hvb hd
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hgi : Integrable g μ := (integrable_const (1 : ℝ)).mono' hgc.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)
  refine ⟨g, hgc, hgs, hgb, hgi, ?_⟩
  have hpoint (x : E) : ‖f x - g x‖ ≤ ‖f x - v x‖ + 2 * δ := by
    have h : ‖f x - g x‖ ≤ ‖f x - v x‖ + ‖v x - g x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f x) (v x) (g x)
    rw [norm_sub_rev (v x) (g x)] at h
    linarith [hgv x]
  have hi : Integrable (fun x => ‖f x - v x‖ + 2 * δ) μ :=
    (hfi.sub hvi).norm.add (integrable_const _)
  have hfv : Integrable (fun x => ‖f x - v x‖) μ := (hfi.sub hvi).norm
  have h := integral_mono (hfi.sub hgi).norm hi hpoint
  rw [integral_add hfv (integrable_const _), integral_const, smul_eq_mul] at h
  have hδeq : 4 * (m + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  have hcost : m * (2 * δ) ≤ ε / 2 := by nlinarith
  change (∫ x, ‖f x - g x‖ ∂μ) ≤ (∫ x, ‖f x - v x‖ ∂μ) + m * (2 * δ) at h
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedImageDerivative
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

theorem integral_unit_test_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem integral_test_difference_le_l1 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  exact norm_integral_le_integral_norm _

theorem bounded_test_comparison_of_smooth {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ}
    (h : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → (∀ x, ‖g x‖ ≤ 1) →
      |(∫ x, g x ∂μ) - ∫ x, g x ∂ν| ≤ C)
    (f : E → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g, hgc, hgs, hgb, _, herr⟩ := exists_smooth_unit_test_l1 (μ + ν) f hf hbound hε
  have hfμ := integral_unit_test_integrable μ f hf hbound
  have hfν := integral_unit_test_integrable ν f hf hbound
  have hgμ := integral_unit_test_integrable μ g hgc.continuous.measurable hgb
  have hgν := integral_unit_test_integrable ν g hgc.continuous.measurable hgb
  have hμ := integral_test_difference_le_l1 μ f g hfμ hgμ
  have hν := integral_test_difference_le_l1 ν f g hfν hgν
  have hdiffμ : Integrable (fun x => ‖f x - g x‖) μ := (hfμ.sub hgμ).norm
  have hdiffν : Integrable (fun x => ‖f x - g x‖) ν := (hfν.sub hgν).norm
  rw [integral_add_measure hdiffμ hdiffν] at herr
  have hg := h g hgc hgs hgb
  have htri := abs_sub_le (∫ x, f x ∂μ) (∫ x, g x ∂μ) (∫ x, f x ∂ν)
  have htri' := abs_sub_le (∫ x, g x ∂μ) (∫ x, g x ∂ν) (∫ x, f x ∂ν)
  rw [abs_sub_comm (∫ x, g x ∂ν) (∫ x, f x ∂ν)] at htri'
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem smooth_translated_integral_hasDerivAt (μ : Measure E) [IsFiniteMeasure μ]
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1) (z : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, φ (x + t • z) ∂μ)
      (∫ x, fderiv ℝ φ (x + t • z) z ∂μ) t := by
  have hdc := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hdc
  have hline (x : E) (s : ℝ) : HasDerivAt (fun t : ℝ => φ (x + t • z))
      (fderiv ℝ φ (x + s • z) z) s := by
    have hz : HasDerivAt (fun t : ℝ => x + t • z) z s := by
      have h := ((hasDerivAt_id s).smul_const z).const_add x
      simp only [one_smul, id_eq] at h
      exact h
    exact ((hφ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s hz
  have hmeas (s : ℝ) : Measurable (fun x : E => φ (x + s • z)) :=
    hφ.continuous.measurable.comp (measurable_id.add_const _)
  have hderivMeas : AEStronglyMeasurable (fun x : E => fderiv ℝ φ (x + t • z) z) μ :=
    ((hdc.comp (continuous_id.add continuous_const)).clm_apply continuous_const).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (bound := fun _ : E => K * ‖z‖) Filter.univ_mem
    (Filter.Eventually.of_forall (fun s => (hmeas s).aestronglyMeasurable))
    (integral_unit_test_integrable μ _ (hmeas t) (fun x => hbound _)) hderivMeas
    (Filter.Eventually.of_forall (fun x s _ =>
      ((fderiv ℝ φ (x + s • z)).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg z))))
    (integrable_const _) (Filter.Eventually.of_forall (fun x s _ => hline x s))).2

theorem smooth_translation_bound_of_weak_derivative (μ : Measure E) [IsFiniteMeasure μ]
    (z : E) (D : ℝ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      |∫ x, fderiv ℝ ψ x z ∂μ| ≤ D)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, φ (x + z) ∂μ) - ∫ x, φ x ∂μ| ≤ D := by
  have hd (t : ℝ) := smooth_translated_integral_hasDerivAt μ φ hφ hs hbound z t
  have hb (t : ℝ) : ‖∫ x, fderiv ℝ φ (x + t • z) z ∂μ‖ ≤ D := by
    have hc : ContDiff ℝ ∞ (fun x : E => φ (x + t • z)) :=
      hφ.comp (contDiff_id.add contDiff_const)
    have hsupport : HasCompactSupport (fun x : E => φ (x + t • z)) :=
      hs.comp_homeomorph (Homeomorph.addRight (t • z))
    have h := hweak _ hc hsupport (fun x => hbound _)
    simp only [fderiv_comp_add_right] at h
    exact h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := fun t : ℝ => ∫ x, φ (x + t • z) ∂μ)
    (f' := fun t : ℝ => ∫ x, fderiv ℝ φ (x + t • z) z ∂μ)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t) convex_univ
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
  simpa only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one, Real.norm_eq_abs] using h

theorem translation_bound_of_weak_derivative [FiniteDimensional ℝ E] (μ : Measure E) [IsFiniteMeasure μ]
    (z : E) (D : ℝ)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      |∫ x, fderiv ℝ ψ x z ∂μ| ≤ D)
    (φ : E → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, φ (x + z) ∂μ) - ∫ x, φ x ∂μ| ≤ D := by
  have hm : Measurable (fun x : E => x + z) := measurable_id.add_const z
  have h := bounded_test_comparison_of_smooth (Measure.map (fun x => x + z) μ) μ (C := D)
    (fun ψ hc hs hb => by
      rw [integral_map hm.aemeasurable hc.continuous.aestronglyMeasurable]
      exact smooth_translation_bound_of_weak_derivative μ z D hweak ψ hc hs hb) φ hφ hbound
  rw [integral_map hm.aemeasurable hφ.aestronglyMeasurable] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal

theorem imageTranslationBound_of_smooth_derivative {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (H : ℝ≥0)
    (hweak : ∀ (ψ : (ι → ℝ) → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ x, ‖ψ x‖ ≤ 1) → ∀ z,
      |∫ a, fderiv ℝ ψ (U a) z ∂μ| ≤ H * dist z 0) : ImageTranslationBound μ U H := by
  intro φ hφ hbound z
  have h := translation_bound_of_weak_derivative (Measure.map U μ) z ((H : ℝ) * dist z 0)
    (fun ψ hc hs hb => by
      have hm : Measurable (fun x => fderiv ℝ ψ x z) :=
        ((hc.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
      rw [integral_map hU.aemeasurable hm.aestronglyMeasurable]
      exact hweak ψ hc hs hb z) φ hφ hbound
  have hm : Measurable (fun x : ι → ℝ => φ (x + z)) :=
    hφ.comp (measurable_id.add_const z)
  rw [integral_map hU.aemeasurable hm.aestronglyMeasurable,
    integral_map hU.aemeasurable hφ.aestronglyMeasurable] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

theorem weighted_image_derivative_identity
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U) (w : (κ → ℝ) → ℝ)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (z : ι → ℝ)
    (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ x, w x * fderiv ℝ φ (U x) z) = -∫ x, coordinateDivergence Q x * φ (U x) := by
  have hpoint (x : κ → ℝ) : fderiv ℝ (fun x => φ (U x)) x (fun j => Q j x) =
      w x * fderiv ℝ φ (U x) z := by
    change fderiv ℝ (φ ∘ U) x (fun j => Q j x) = _
    rw [fderiv_comp x (hφ.differentiable (by norm_num) _) (hU.differentiable (by norm_num) _),
      ContinuousLinearMap.comp_apply, hcolumn, map_smul, smul_eq_mul]
  have h := coordinate_vectorField_integration_by_parts Q hQ hs (fun x => φ (U x)) (hφ.comp hU)
  simpa only [hpoint] using h

theorem weighted_image_derivative_bound
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U)
    (w : (κ → ℝ) → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (z : ι → ℝ)
    (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    {B : ℝ} (hdiv : (∫ x, |coordinateDivergence Q x|) ≤ B)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |∫ x, fderiv ℝ φ (U x) z ∂realDensityMeasure volume w| ≤ B := by
  rw [realDensityMeasure_integral volume w hw hw0,
    weighted_image_derivative_identity U hU w Q hQ hs z hcolumn φ hφ, abs_neg]
  have hi : Integrable (fun x => |coordinateDivergence Q x|) := by
    have hint : Integrable (coordinateDivergence Q) volume :=
      (coordinateDivergence_continuous Q hQ).integrable_of_hasCompactSupport
        (coordinateDivergence_hasCompactSupport Q hs)
    have h := hint.norm
    simp only [Real.norm_eq_abs] at h
    exact h
  have hp (x : κ → ℝ) : ‖coordinateDivergence Q x * φ (U x)‖ ≤ |coordinateDivergence Q x| := by
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h.trans hdiv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ImageCoordinateDerivative
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

theorem smooth_image_derivative_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (z : ι → ℝ) :
    Integrable (fun a => fderiv ℝ φ (U a) z) μ := by
  have hc := hφ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := (hs.fderiv ℝ).exists_bound_of_continuous hc
  apply (integrable_const (K * ‖z‖)).mono'
    (((hc.clm_apply continuous_const).measurable.comp hU).aestronglyMeasurable)
  filter_upwards [] with a
  exact ((fderiv ℝ φ (U a)).le_opNorm z).trans
    (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _))

theorem imageTranslationBound_of_coordinate_derivatives [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → (ι → ℝ)) (hU : Measurable U) (B : ι → ℝ≥0)
    (hweak : ∀ (φ : (ι → ℝ) → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, ‖φ x‖ ≤ 1) → ∀ i,
      |∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ| ≤ B i) :
    ImageTranslationBound μ U (∑ i, B i) := by
  apply imageTranslationBound_of_smooth_derivative μ U hU
  intro φ hc hs hb z
  have hi (i : ι) := smooth_image_derivative_integrable μ U hU φ hc hs (Pi.single i 1)
  have heq : (∫ a, fderiv ℝ φ (U a) z ∂μ) =
      ∑ i, z i * ∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
    calc
      (∫ a, fderiv ℝ φ (U a) z ∂μ) =
          ∫ a, ∑ i, z i * fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with a
        exact continuousLinearMap_coordinate_sum _ _
      _ = ∑ i, z i * ∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ := by
        rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (z i))]
        simp only [integral_const_mul]
  rw [heq, ← Real.norm_eq_abs]
  apply (norm_sum_le _ _).trans
  rw [NNReal.coe_sum, Finset.sum_mul, dist_eq_norm, sub_zero]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul]
  have hbi : ‖∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ‖ ≤ (B i : ℝ) := hweak φ hc hs hb i
  calc
    ‖z i‖ * ‖∫ a, fderiv ℝ φ (U a) (Pi.single i 1) ∂μ‖ ≤ ‖z i‖ * (B i : ℝ) :=
      mul_le_mul_of_nonneg_left hbi (norm_nonneg _)
    _ ≤ (B i : ℝ) * ‖z‖ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (B i).coe_nonneg

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem imageTranslationBound_of_weighted_fields
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U)
    (w : (κ → ℝ) → ℝ) (hw : Measurable w) (hwi : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : ι → κ → (κ → ℝ) → ℝ) (hQ : ∀ i j, ContDiff ℝ 1 (Q i j))
    (hs : ∀ i j, HasCompactSupport (Q i j))
    (hcolumn : ∀ i x, fderiv ℝ U x (fun j => Q i j x) = w x • Pi.single i 1)
    (B : ι → ℝ≥0) (hdiv : ∀ i, (∫ x, |coordinateDivergence (Q i) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  let : IsFiniteMeasure (realDensityMeasure volume w) := realDensityMeasure_finite volume w hwi hw0
  apply imageTranslationBound_of_coordinate_derivatives _ U hU.continuous.measurable B
  intro φ hc _ hb i
  exact weighted_image_derivative_bound U hU w hw hw0 (Q i) (hQ i) (hs i)
    (Pi.single i 1) (hcolumn i) (hdiv i) φ (hc.of_le (by simp)) hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology NNReal BigOperators

theorem contDiff_mul_of_local_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x) : ContDiff ℝ 1 (fun x => f x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt.mul (hg x hx)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem selectedInverseField_contDiffAt (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hx : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) :
    ContDiffAt ℝ 1 (selectedInverseField U J i j) x := by
  have hA : ContDiff ℝ 1 (selectedDerivative U J) :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hi : ContDiffAt ℝ 1 (fun y => (selectedDerivative U J y).inverse) x :=
    hx.contDiffAt_map_inverse.comp x hA.contDiffAt
  have hv : ContDiffAt ℝ 1 (fun y => J ((selectedDerivative U J y).inverse (Pi.single i 1))) x :=
    J.contDiff.contDiffAt.comp x (hi.clm_apply contDiffAt_const)
  exact (contDiffAt_apply ℝ ℝ j _).comp x hv

omit [Fintype κ] [Fintype ι] in
theorem selectedInverseField_column (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hx : (selectedDerivative U J x).IsInvertible) (i : ι) :
    fderiv ℝ U x (fun j => selectedInverseField U J i j x) = Pi.single i 1 := by
  change selectedDerivative U J x ((selectedDerivative U J x).inverse (Pi.single i 1)) = _
  exact hx.self_apply_inverse _

theorem selectedWeightedField_spec (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) :
    (∀ i j, ContDiff ℝ 1 (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i j, HasCompactSupport (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i x, fderiv ℝ U x (fun j => w x * selectedInverseField U J i j x) = w x • Pi.single i 1) := by
  refine ⟨fun i j => contDiff_mul_of_local_right hw (fun x hx =>
      selectedInverseField_contDiffAt U hU J (hinv x hx) i j),
    fun _ _ => hws.mul_right, ?_⟩
  intro i x
  change fderiv ℝ U x (w x • (fun j => selectedInverseField U J i j x)) = _
  rw [map_smul]
  by_cases hx : w x = 0
  · simp only [hx, zero_smul]
  · rw [selectedInverseField_column U J (hinv x (subset_tsupport w hx))]

theorem imageTranslationBound_of_selected_inverse [DecidableEq κ]
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) (B : ι → ℝ≥0)
    (hdiv : ∀ i, (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  obtain ⟨hc, hs, hcolumn⟩ := selectedWeightedField_spec U hU J w hw hws hinv
  exact imageTranslationBound_of_weighted_fields U (hU.of_le (by norm_num)) w
    hw.continuous.measurable (hw.continuous.integrable_of_hasCompactSupport hws) hw0
    (fun i j x => w x * selectedInverseField U J i j x) hc hs hcolumn B hdiv

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem selectedInverseField_contDiffAt_of_local
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hU : ContDiffAt ℝ 2 U x) (hx : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) :
    ContDiffAt ℝ 1 (selectedInverseField U J i j) x := by
  have hA : ContDiffAt ℝ 1 (selectedDerivative U J) x :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  have hi : ContDiffAt ℝ 1 (fun y => (selectedDerivative U J y).inverse) x :=
    hx.contDiffAt_map_inverse.comp x hA
  have hv : ContDiffAt ℝ 1 (fun y => J ((selectedDerivative U J y).inverse (Pi.single i 1))) x :=
    J.contDiff.contDiffAt.comp x (hi.clm_apply contDiffAt_const)
  exact (contDiffAt_apply ℝ ℝ j _).comp x hv

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem selectedDerivative_sub_norm_le
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖selectedDerivative V J x - selectedDerivative U J x‖ ≤
      ‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖ := by
  unfold selectedDerivative
  rw [← ContinuousLinearMap.sub_comp]
  exact (fderiv ℝ V x - fderiv ℝ U x).opNorm_comp_le J

theorem selected_inverse_perturbation
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ)
    (hinv : (selectedDerivative U J x).IsInvertible) (K : ℝ≥0)
    (hK : ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : (K : ℝ) * (‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖) ≤ 1 / 2) :
    (selectedDerivative V J x).IsInvertible ∧
      ‖(selectedDerivative V J x).inverse‖ ≤ 2 * (K : ℝ) := by
  apply inverse_perturbation_bound (selectedDerivative U J x) (selectedDerivative V J x) hinv K hK
  exact (mul_le_mul_of_nonneg_left (selectedDerivative_sub_norm_le U V J x) K.coe_nonneg).trans hsmall

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InverseDerivativeBound
namespace OAI

section

namespace Erdos3

open ContinuousLinearMap

theorem ringInverse_fderiv_norm_le
    {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]
    (A : E → R) {x : E} (hA : DifferentiableAt ℝ A x) (hu : IsUnit (A x)) (v : E) :
    ‖fderiv ℝ (fun y => Ring.inverse (A y)) x v‖ ≤
      ‖Ring.inverse (A x)‖ ^ 2 * ‖fderiv ℝ A x v‖ := by
  have hnorm : ‖fderiv ℝ (Ring.inverse : R → R) (A x)‖ ≤ ‖Ring.inverse (A x)‖ ^ 2 := by
    rcases hu with ⟨u, heq⟩
    rw [← heq, fderiv_inverse, norm_neg, Ring.inverse_unit]
    exact (opNorm_mulLeftRight_apply_apply_le ℝ R _ _).trans_eq (by ring)
  change ‖fderiv ℝ (Ring.inverse ∘ A) x v‖ ≤ _
  rw [fderiv_comp x (differentiableAt_inverse hu) hA, ContinuousLinearMap.comp_apply]
  exact ((fderiv ℝ Ring.inverse (A x)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

theorem continuousLinearMap_isUnit_of_isInvertible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : F →L[ℝ] F} (hA : A.IsInvertible) : IsUnit A := by
  rcases hA with ⟨e, he⟩
  exact ⟨(ContinuousLinearEquiv.unitsEquiv ℝ F).symm e, he⟩

theorem inverseMap_fderiv_norm_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E → F →L[ℝ] F) {x : E} (hA : DifferentiableAt ℝ A x)
    (hu : (A x).IsInvertible) (v : E) :
    ‖fderiv ℝ (fun y => (A y).inverse) x v‖ ≤
      ‖(A x).inverse‖ ^ 2 * ‖fderiv ℝ A x v‖ := by
  have h := ringInverse_fderiv_norm_le A hA (continuousLinearMap_isUnit_of_isInvertible hu) v
  simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.BudgetedOpenImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_divergence_pointwise
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (V : ι → (ι → ℝ) → ℝ)
    (hV : ∀ i x, x ∈ tsupport w → ContDiffAt ℝ 1 (V i) x)
    (K L : ℝ≥0) (hK : ∀ i x, x ∈ tsupport w → |V i x| ≤ K)
    (hL : ∀ i x, x ∈ tsupport w → |fderiv ℝ (V i) x (Pi.single i 1)| ≤ L)
    (x : ι → ℝ) :
    |coordinateDivergence (fun i x => w x * V i x) x| ≤
      (K : ℝ) * (∑ i, |fderiv ℝ w x (Pi.single i 1)|) +
        (Fintype.card ι : ℝ) * L * |w x| := by
  by_cases hx : x ∈ tsupport w
  · have hp (i : ι) : |fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1)| ≤
        (K : ℝ) * |fderiv ℝ w x (Pi.single i 1)| + L * |w x| := by
      rw [fderiv_fun_mul (hw.differentiable (by norm_num) x)
        ((hV i x hx).differentiableAt (by norm_num))]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have h := abs_add_le (w x * fderiv ℝ (V i) x (Pi.single i 1))
        (V i x * fderiv ℝ w x (Pi.single i 1))
      simp only [abs_mul] at h
      have ha := mul_le_mul_of_nonneg_left (hL i x hx) (abs_nonneg (w x))
      have hb := mul_le_mul_of_nonneg_right (hK i x hx) (abs_nonneg (fderiv ℝ w x (Pi.single i 1)))
      linarith
    calc
      |coordinateDivergence (fun i x => w x * V i x) x| ≤
          ∑ i, |fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1)| := by
        have h := norm_sum_le Finset.univ
          (fun i : ι => fderiv ℝ (fun x => w x * V i x) x (Pi.single i 1))
        simp only [Real.norm_eq_abs] at h
        exact h
      _ ≤ ∑ i, ((K : ℝ) * |fderiv ℝ w x (Pi.single i 1)| + L * |w x|) :=
        Finset.sum_le_sum (fun i _ => hp i)
      _ = (K : ℝ) * (∑ i, |fderiv ℝ w x (Pi.single i 1)|) +
          (Fintype.card ι : ℝ) * L * |w x| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  · have hs : tsupport (coordinateDivergence (fun i x => w x * V i x)) ⊆ tsupport w :=
      coordinateDivergence_tsupport_subset _ (isClosed_tsupport w)
        (fun i => tsupport_smul_subset_left w (V i))
    rw [image_eq_zero_of_notMem_tsupport (f := coordinateDivergence (fun i x => w x * V i x))
      (fun h => hx (hs h)), abs_zero]
    positivity

theorem coordinate_derivative_integrable
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (i : ι) :
    Integrable (fun x => |fderiv ℝ w x (Pi.single i 1)|) := by
  have hi : Integrable (fun x => fderiv ℝ w x (Pi.single i 1)) volume :=
    ((hw.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (Pi.single i 1))
  simpa only [Real.norm_eq_abs] using hi.norm

theorem weighted_divergence_integral_bound
    (w : (ι → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (V : ι → (ι → ℝ) → ℝ) (hV : ∀ i x, x ∈ tsupport w → ContDiffAt ℝ 1 (V i) x)
    (K L : ℝ≥0) (hK : ∀ i x, x ∈ tsupport w → |V i x| ≤ K)
    (hL : ∀ i x, x ∈ tsupport w → |fderiv ℝ (V i) x (Pi.single i 1)| ≤ L) :
    (∫ x, |coordinateDivergence (fun i x => w x * V i x) x|) ≤
      (K : ℝ) * (∑ i, ∫ x, |fderiv ℝ w x (Pi.single i 1)|) +
        (Fintype.card ι : ℝ) * L * ∫ x, |w x| := by
  have hQi (i : ι) : ContDiff ℝ 1 (fun x => w x * V i x) :=
    contDiff_mul_of_local_right hw (hV i)
  have hdi : Integrable (coordinateDivergence (fun i x => w x * V i x)) volume :=
    (coordinateDivergence_continuous _ hQi).integrable_of_hasCompactSupport
      (coordinateDivergence_hasCompactSupport _ (fun _ => hs.mul_right))
  have hleft : Integrable (fun x => |coordinateDivergence (fun i x => w x * V i x) x|) := by
    simpa only [Real.norm_eq_abs] using hdi.norm
  have hgrad : Integrable (fun x => ∑ i, |fderiv ℝ w x (Pi.single i 1)|) :=
    integrable_finsetSum _ (fun i _ => coordinate_derivative_integrable w hw hs i)
  have hwi : Integrable (fun x => |w x|) volume := by
    have hi : Integrable w volume := hw.continuous.integrable_of_hasCompactSupport hs
    simpa only [Real.norm_eq_abs] using hi.norm
  have h := integral_mono hleft ((hgrad.const_mul (K : ℝ)).add
    (hwi.const_mul ((Fintype.card ι : ℝ) * L))) (weighted_divergence_pointwise w hw V hV K L hK hL)
  simp only [Pi.add_apply] at h
  rw [integral_add (hgrad.const_mul (K : ℝ)) (hwi.const_mul ((Fintype.card ι : ℝ) * L)),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => coordinate_derivative_integrable w hw hs i)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem selectedInverseField_norm_le (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) (x : κ → ℝ) :
    |selectedInverseField U J i j x| ≤ ‖J‖ * ‖(selectedDerivative U J x).inverse‖ := by
  calc
    |selectedInverseField U J i j x| ≤ ‖J ((selectedDerivative U J x).inverse (Pi.single i 1))‖ :=
      by
        have h := norm_le_pi_norm (J ((selectedDerivative U J x).inverse (Pi.single i 1))) j
        simp only [Real.norm_eq_abs] at h
        exact h
    _ ≤ ‖J‖ * ‖(selectedDerivative U J x).inverse (Pi.single i 1)‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖(selectedDerivative U J x).inverse‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) :=
      mul_le_mul_of_nonneg_left ((selectedDerivative U J x).inverse.le_opNorm _) (norm_nonneg _)
    _ = ‖J‖ * ‖(selectedDerivative U J x).inverse‖ := by simp only [Pi.norm_single, norm_one, mul_one]

theorem selectedInverseField_derivative_norm_le (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ} (hU : ContDiffAt ℝ 2 U x)
    (hinv : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) (v : κ → ℝ) :
    |fderiv ℝ (selectedInverseField U J i j) x v| ≤
      ‖J‖ * ‖(selectedDerivative U J x).inverse‖ ^ 2 * ‖fderiv ℝ (selectedDerivative U J) x v‖ := by
  let A := selectedDerivative U J
  let W := fun y => J ((A y).inverse (Pi.single i 1))
  have hA : ContDiffAt ℝ 1 A x := (hU.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  have hi : DifferentiableAt ℝ (fun y => (A y).inverse) x :=
    (hinv.contDiffAt_map_inverse.comp x hA).differentiableAt (by norm_num)
  have hinner : DifferentiableAt ℝ (fun y => (A y).inverse (Pi.single i 1)) x :=
    hi.clm_apply (differentiableAt_const _)
  have hW : DifferentiableAt ℝ W x := J.differentiableAt.comp x hinner
  have hcoord : fderiv ℝ (selectedInverseField U J i j) x v = (fderiv ℝ W x v) j := by
    change fderiv ℝ (fun y => W y j) x v = _
    rw [fderiv_apply hW j]
    rfl
  have hvec : fderiv ℝ W x v = J ((fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1)) := by
    change fderiv ℝ (J ∘ (fun y => (A y).inverse (Pi.single i 1))) x v = _
    rw [fderiv_comp x J.differentiableAt hinner, J.fderiv, ContinuousLinearMap.comp_apply,
      fderiv_clm_apply hi (differentiableAt_const _)]
    simp
  rw [hcoord]
  calc
    |(fderiv ℝ W x v) j| ≤ ‖fderiv ℝ W x v‖ := by
      have h := norm_le_pi_norm (fderiv ℝ W x v) j
      simp only [Real.norm_eq_abs] at h
      exact h
    _ = ‖J ((fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1))‖ := by rw [hvec]
    _ ≤ ‖J‖ * ‖(fderiv ℝ (fun y => (A y).inverse) x v) (Pi.single i 1)‖ := J.le_opNorm _
    _ ≤ ‖J‖ * (‖fderiv ℝ (fun y => (A y).inverse) x v‖ * ‖(Pi.single i (1 : ℝ) : ι → ℝ)‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ (fun y => (A y).inverse) x v).le_opNorm _) (norm_nonneg _)
    _ = ‖J‖ * ‖fderiv ℝ (fun y => (A y).inverse) x v‖ := by
      simp only [Pi.norm_single, norm_one, mul_one]
    _ ≤ ‖J‖ * (‖(A x).inverse‖ ^ 2 * ‖fderiv ℝ A x v‖) :=
      mul_le_mul_of_nonneg_left (inverseMap_fderiv_norm_le A (hA.differentiableAt (by norm_num)) hinv v)
        (norm_nonneg _)
    _ = _ := by ring

theorem selected_inverse_divergence_bound [DecidableEq κ]
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 2 U x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (K H : ℝ≥0) (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hH : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H) (i : ι) :
    (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤
      (‖J‖ * K) * (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) +
        (Fintype.card κ : ℝ) * (‖J‖ * K ^ 2 * H) * ∫ x, |w x| := by
  have hval (j : κ) (x : κ → ℝ) (hx : x ∈ tsupport w) :
      |selectedInverseField U J i j x| ≤ (‖J‖₊ * K : ℝ≥0) := by
    exact (selectedInverseField_norm_le U J i j x).trans
      (mul_le_mul_of_nonneg_left (hK x hx) (norm_nonneg _))
  have hder (j : κ) (x : κ → ℝ) (hx : x ∈ tsupport w) :
      |fderiv ℝ (selectedInverseField U J i j) x (Pi.single j 1)| ≤ (‖J‖₊ * K ^ 2 * H : ℝ≥0) := by
    have hA : ‖fderiv ℝ (selectedDerivative U J) x (Pi.single j 1)‖ ≤ (H : ℝ) := by
      have h := (fderiv ℝ (selectedDerivative U J) x).le_opNorm (Pi.single j 1)
      simp only [Pi.norm_single, norm_one, mul_one] at h
      exact h.trans (hH x hx)
    have hpow : ‖(selectedDerivative U J x).inverse‖ ^ 2 ≤ (K : ℝ) ^ 2 := by
      gcongr
      exact hK x hx
    apply (selectedInverseField_derivative_norm_le U J (hU x hx) (hinv x hx) i j (Pi.single j 1)).trans
    change _ ≤ ‖J‖ * (K : ℝ) ^ 2 * (H : ℝ)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (norm_nonneg J)) hA (norm_nonneg _)
      (mul_nonneg (norm_nonneg J) (sq_nonneg (K : ℝ)))
  exact weighted_divergence_integral_bound w hw hs (selectedInverseField U J i)
    (fun j x hx => selectedInverseField_contDiffAt_of_local U J (hU x hx) (hinv x hx) i j)
    (‖J‖₊ * K) (‖J‖₊ * K ^ 2 * H) hval hder

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem imageTranslationBound_of_inverse_budget
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1)
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∫ x, |w x|) ≤ 1)
    (K H S B : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hH : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    (hB : (K : ℝ) * S + (Fintype.card κ : ℝ) * ((K : ℝ) ^ 2 * H) ≤ B) :
    ImageTranslationBound (realDensityMeasure volume w) U ((Fintype.card ι : ℝ≥0) * B) := by
  have hsum : (∑ _ : ι, B) = (Fintype.card ι : ℝ≥0) * B := by simp
  rw [← hsum]
  apply imageTranslationBound_of_selected_inverse U hU J w hw hs hw0 hinv (fun _ => B)
  intro i
  apply (selected_inverse_divergence_bound U J w hw hs (fun _ _ => hU.contDiffAt)
    hinv K H hK hH i).trans
  apply le_trans _ hB
  have hJK : ‖J‖ * (K : ℝ) ≤ K := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ K.coe_nonneg
  have hJH : ‖J‖ * (K : ℝ) ^ 2 * H ≤ (K : ℝ) ^ 2 * H := by
    have ht := mul_le_mul_of_nonneg_right hJ (sq_nonneg (K : ℝ))
    rw [one_mul] at ht
    exact mul_le_mul_of_nonneg_right ht H.coe_nonneg
  have hsum0 : 0 ≤ ∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)| :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  refine add_le_add (mul_le_mul hJK hS hsum0 K.coe_nonneg) ?_
  calc
    _ ≤ (Fintype.card κ : ℝ) * ((K : ℝ) ^ 2 * H) * ∫ x, |w x| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJH (Nat.cast_nonneg _))
        (integral_nonneg (fun _ => abs_nonneg _))
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hmass

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointBooleanCutoffLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_loss_of_density_mass {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] (χ w : X → ℝ)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hwi : Integrable w ν) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure ν w = realDensityMeasure μ χ)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, w x ∂ν) : (∫ x, 1 - χ x ∂μ) ≤ η := by
  have hi := cutoff_integrable μ χ hχ hχ01
  have hm : (∫ x, χ x ∂μ) = ∫ x, w x ∂ν := by
    rw [← realDensityMeasure_real_univ μ χ hi (fun x => (hχ01 x).1),
      ← hlaw, realDensityMeasure_real_univ ν w hwi hw0]
  rw [integral_sub (integrable_const (1 : ℝ)) hi, hm]
  simpa only [integral_const, probReal_univ, one_smul] using sub_le_iff_le_add.mpr
    (show (1 : ℝ) ≤ η + ∫ x, w x ∂ν by linarith)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [Fintype O]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem selected_cutoff_comparison_of_close_derivatives
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (μ : Measure (κ → ℝ)) [IsProbabilityMeasure μ]
    (χ w : (κ → ℝ) → ℝ) (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure volume w = realDensityMeasure μ χ)
    (U V : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (hJ : ‖J‖ ≤ 1) (K H S : ℝ≥0)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible)
    (hK : ∀ x ∈ tsupport w, ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : ∀ x ∈ tsupport w, (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ U x‖ ≤ 1 / 2)
    (hHU : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H)
    (hHV : ∀ x ∈ tsupport w, ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ H)
    (hS : (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) ≤ S)
    {ε η : ℝ} (hε : 0 < ε) (hmass : 1 - η ≤ ∫ x, w x)
    (hclose : ∀ x, w x ≠ 0 → dist (U x) (V x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    let B := 1 + 2 * (K : ℝ) * S + (Fintype.card κ : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |mappedTest μ U φ - mappedTest μ V φ| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt (B * ε) := by
  have hwi : Integrable w := hw.continuous.integrable_of_hasCompactSupport hs
  have hmass1 : (∫ x, |w x|) ≤ 1 := by
    have ht := cutoffMeasure_mass_le_one μ χ hχ hχ01
    rw [← hlaw, realDensityMeasure_real_univ volume w hwi hw0] at ht
    have he (x) : |w x| = w x := abs_of_nonneg (hw0 x)
    simpa only [he] using ht
  have hv (x) (hx : x ∈ tsupport w) :
      (selectedDerivative V J x).IsInvertible ∧ ‖(selectedDerivative V J x).inverse‖ ≤ 2 * K := by
    apply selected_inverse_perturbation U V J x (hinv x hx) K (hK x hx)
    apply le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) K.coe_nonneg)
    simpa only [mul_one] using hsmall x hx
  let B : ℝ≥0 := 1 + (2 * K) * S + (Fintype.card κ : ℝ≥0) * ((2 * K) ^ 2 * H)
  have hB : 0 < (B : ℝ) := by dsimp only [B]; positivity
  have hbudget : ((2 * K : ℝ≥0) : ℝ) * S +
      (Fintype.card κ : ℝ) * (((2 * K : ℝ≥0) : ℝ) ^ 2 * H) ≤ B := by
    simp only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
      NNReal.coe_ofNat, NNReal.coe_one]
    linarith
  have hTU := imageTranslationBound_of_inverse_budget U hU J hJ w hw hs hw0 hmass1
    (2 * K) H S B hinv (fun x hx => (hK x hx).trans (by
      change (K : ℝ) ≤ 2 * K
      linarith [K.coe_nonneg])) hHU hS hbudget
  have hTV := imageTranslationBound_of_inverse_budget V hV J hJ w hw hs hw0 hmass1
    (2 * K) H S B (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2) hHV hS hbudget
  rw [hlaw] at hTU hTV
  have hc : ∀ᵐ x ∂realDensityMeasure μ χ, dist (U x) (V x) ≤ ε := by
    rw [← hlaw]
    exact ae_realDensityMeasure_of_forall_nonzero volume w hw.continuous.measurable _ hclose
  have ht := cutoff_box_image_comparison_sqrt μ χ hχ hχ01 U V hU.continuous.measurable
    hV.continuous.measurable B hB hTU hTV hε
    (cutoff_loss_of_density_mass μ volume χ w hχ hχ01 hwi hw0 hlaw hmass) hc φ hφ hbound
  simpa only [B, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_ofNat, NNReal.coe_one] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives.{u_1, u_2} := @OAI.Erdos3.selected_cutoff_comparison_of_close_derivatives.{u_1, u_2}
