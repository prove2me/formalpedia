-- Prove2me | solution 1 for GlobalTheory.LogResInt.isAnalyticSubset_boundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:36.542277+00:00
-- url     : https://prove2.me/submissions/6d883328-6152-4650-b4df-5759b6e66ee6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Theorems.Thm_GlobalTheory_LogResInt_HasHoloImm_mono
import Theorems.Thm_GlobalTheory_LogResInt_isSection_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.LogResInt
theorem _root_.solution {A : FinHolAtlas d X} {m : ℕ} {Λ : Fin m → LocPot X}
    {σ : Fin m → X → X → ℂ} (hσ : ∀ i, IsSection A (Λ i) (σ i)) :
    A.IsAnalyticSubset (boundary σ) := by
  intro x
  refine ⟨⋂ i, (Λ i).U x, isOpen_iInter_of_finite fun i => (Λ i).isOpen_U x,
    Set.mem_iInter.2 fun i => (Λ i).mem_U x, 1, fun _ y => ∏ i, σ i x y, fun _ j => ?_, ?_⟩
  · have h : ∀ i, AnalyticOnNhd ℂ (σ i x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Λ i).U x) :=
      fun i => ((hσ i).1 x j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2 i⟩
    exact Finset.univ.analyticOnNhd_fun_prod (fun i _ => h i)
  · ext y
    simp only [boundary, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hU⟩
      exact ⟨hU, fun _ => ⟨i, (isSection_zero_iff (hσ i) (hU i)).2 hi⟩⟩
    · rintro ⟨hU, h⟩
      obtain ⟨i, hi⟩ := h 0
      exact ⟨⟨i, (isSection_zero_iff (hσ i) (hU i)).1 hi⟩, hU⟩
end GlobalTheory.LogResInt
