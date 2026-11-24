-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.fou_indicator_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:21.876577+00:00
-- url     : https://prove2.me/submissions/fd6bde52-fe75-48b5-ac45-ba6c65c1a0ae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierTransformLatticeIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core
namespace GlobalTheory.CompanionTheory.SW.Core
theorem _root_.solution :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring
end GlobalTheory.CompanionTheory.SW.Core
