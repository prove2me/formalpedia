-- Prove2me | solution 1 for GlobalTheory.CompactAvgSchwartz.integral_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:40.295903+00:00
-- url     : https://prove2.me/submissions/b2046763-67b0-4b25-87fb-2f578eade9bb

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_exists_schwartz_integral
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_comp_mem_SB
import Theorems.Thm_GlobalTheory_CompactAvgSchwartz_isLocallyConstant_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
namespace GlobalTheory.CompactAvgSchwartz
section Real
variable {S V : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
private theorem integrable_of_continuous_isFiniteMeasure {E : Type} [NormedAddCommGroup E] [MeasurableSpace S] [OpensMeasurableSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] {φ : S → E} (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.mono' (integrable_const C) hφ.aestronglyMeasurable_of_compactSpace
    (ae_of_all _ fun s => hC s (Set.mem_univ _))
end Real
section Fin
variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y] {a b : S → Y → Y} {g : Y → ℂ}
end Fin
end GlobalTheory.CompactAvgSchwartz
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz
namespace GlobalTheory.CompactAvgSchwartz
theorem _root_.solution {S V Y : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace S] [OpensMeasurableSpace S] [TopologicalSpace Y] (ν : Measure S)
    [IsFiniteMeasure ν] (L Li : S → V →L[ℝ] V) (hL : Continuous L) (hLi : Continuous Li) (h : ∀ s x, Li s (L s x) = x)
    (a b : S → Y → Y) (ha : Continuous fun p : S × Y => a p.1 p.2) (hb : Continuous fun p : S × Y => b p.1 p.2)
    (hab : ∀ s y, b s (a s y) = y) (f : SchwartzMap V ℂ) {g : Y → ℂ} (hg : g ∈ WeilM.SB Y) :
    (∀ x y, Integrable (fun s => f (L s x) * g (a s y)) ν) ∧
    ∃ (t : Finset (Y → ℂ)) (F : (Y → ℂ) → SchwartzMap V ℂ), (∀ g' ∈ t, g' ∈ WeilM.SB Y) ∧
      ∀ x y, ∫ s, f (L s x) * g (a s y) ∂ν = ∑ g' ∈ t, F g' x * g' y := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hLx : ∀ x, Continuous fun s => f (L s x) := fun x => f.continuous.comp (hL.clm_apply continuous_const)
  have hay : ∀ y, Continuous fun s => a s y := fun y => ha.comp (continuous_id.prodMk continuous_const)
  refine ⟨fun x y => integrable_of_continuous_isFiniteMeasure ν ((hLx x).mul (hg'.1.continuous.comp (hay y))), ?_⟩
  have hφ : IsLocallyConstant fun s y => g (a s y) := isLocallyConstant_comp ha hb hab hg
  have hfin := hφ.range_finite
  have hmeas : ∀ g₁ : Y → ℂ, MeasurableSet ((fun s y => g (a s y)) ⁻¹' {g₁}) :=
    fun g₁ => (hφ.isOpen_fiber g₁).measurableSet
  choose F hF using fun g₁ : Y → ℂ =>
    exists_schwartz_integral (ν.restrict ((fun s y => g (a s y)) ⁻¹' {g₁})) L Li hL hLi h f
  refine ⟨hfin.toFinset, F, ?_, ?_⟩
  · intro g₁ hg₁
    rw [Set.Finite.mem_toFinset] at hg₁
    obtain ⟨s, rfl⟩ := hg₁
    exact comp_mem_SB (a := a s) (b := b s) (ha.comp (continuous_const.prodMk continuous_id))
      (hb.comp (continuous_const.prodMk continuous_id)) (hab s) hg
  · intro x y
    have hsplit : ∀ s, f (L s x) * g (a s y) = ∑ g₁ ∈ hfin.toFinset,
        Set.indicator ((fun s y => g (a s y)) ⁻¹' {g₁}) (fun s => f (L s x) * g₁ y) s := by
      intro s
      rw [Finset.sum_eq_single (fun y => g (a s y))]
      · rw [Set.indicator_of_mem (show s ∈ (fun s y => g (a s y)) ⁻¹' {fun y => g (a s y)} from rfl)]
      · intro g₁ _ hne
        exact Set.indicator_of_notMem (fun hs => hne hs.symm) _
      · intro hn
        exact absurd (hfin.mem_toFinset.2 ⟨s, rfl⟩) hn
    calc ∫ s, f (L s x) * g (a s y) ∂ν
        = ∫ s, ∑ g₁ ∈ hfin.toFinset,
            Set.indicator ((fun s y => g (a s y)) ⁻¹' {g₁}) (fun s => f (L s x) * g₁ y) s ∂ν :=
          integral_congr_ae (ae_of_all _ hsplit)
      _ = ∑ g₁ ∈ hfin.toFinset,
            ∫ s, Set.indicator ((fun s y => g (a s y)) ⁻¹' {g₁}) (fun s => f (L s x) * g₁ y) s ∂ν :=
          integral_finsetSum _ fun g₁ _ =>
            (integrable_of_continuous_isFiniteMeasure ν ((hLx x).mul continuous_const)).indicator (hmeas g₁)
      _ = ∑ g₁ ∈ hfin.toFinset, F g₁ x * g₁ y := by
          refine Finset.sum_congr rfl fun g₁ _ => ?_
          rw [integral_indicator (hmeas g₁), integral_mul_const, hF g₁ x]
end GlobalTheory.CompactAvgSchwartz
