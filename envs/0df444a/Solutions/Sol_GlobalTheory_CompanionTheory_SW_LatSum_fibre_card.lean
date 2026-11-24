-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.fibre_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:23.683363+00:00
-- url     : https://prove2.me/submissions/3062fc47-a18f-4bb7-8b0f-09e33cf88218

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
open Classical
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (S : Finset (𝓞 F)) (hS : ∀ α : 𝓞 F, (∀ w, |ρ w (α : F)| < 1) → α ∈ S)
    (x : InfinitePlace F → ℝ) (T : Finset (𝓞 F)) (n : InfinitePlace F → ℤ) :
    (T.filter fun r : 𝓞 F => (fun w => ⌊x w + ρ w (r : F)⌋) = n).card ≤ S.card := by
  rcases (T.filter fun r : 𝓞 F => (fun w => ⌊x w + ρ w (r : F)⌋) = n).eq_empty_or_nonempty with h | ⟨r₀, h₀⟩
  · rw [h]
    simp
  · refine Finset.card_le_card_of_injOn (fun r => r - r₀) ?_ ?_
    · intro r hr
      apply hS
      intro w
      have e1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hr)).2
      have e0 := (Finset.mem_filter.1 h₀).2
      have e : ⌊x w + ρ w (r : F)⌋ = ⌊x w + ρ w (r₀ : F)⌋ := by
        rw [congrFun e1 w, congrFun e0 w]
      have := Int.abs_sub_lt_one_of_floor_eq_floor e
      have e2 : ρ w ((r - r₀ : 𝓞 F) : F) = (x w + ρ w (r : F)) - (x w + ρ w (r₀ : F)) := by
        push_cast
        rw [map_sub]
        ring
      rw [e2]
      exact this
    · intro a _ b _ hab
      exact sub_left_injective hab
end GlobalTheory.CompanionTheory.SW.LatSum
