-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.finrank_killed_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:07.618985+00:00
-- url     : https://prove2.me/submissions/356c2574-39af-4d48-9ddd-37727a2fbecf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_map_mem_killed
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_hom_congr_left
import Theorems.Thm_GlobalTheory_SemisimpleCount_injective_of_ne_zero
import Theorems.Thm_GlobalTheory_SemisimpleCount_rank_killed_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution : ∀ (Rg : Type) [Ring Rg] [Algebra ℂ Rg] (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M] [IsScalarTower ℂ Rg M] [SMulCommClass Rg ℂ M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N] [SMulCommClass Rg ℂ N] (I : Set Rg) (FM : Submodule ℂ M) (FN : Submodule ℂ N), IsSemisimpleModule Rg M → IsSemisimpleModule Rg N → (∀ m, m ∈ FM ↔ ∀ x ∈ I, x • m = 0) → (∀ n, n ∈ FN ↔ ∀ x ∈ I, x • n = 0) → FiniteDimensional ℂ FM → FiniteDimensional ℂ FN → (∀ U : Submodule Rg M, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FM) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → (∀ U : Submodule Rg N, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FN) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → Module.finrank ℂ FM = Module.finrank ℂ FN := by
  intro Rg _ _ M N _ _ _ _ _ _ _ _ _ _ I FM FN hM hN hFM hFN fM fN HM HN
  obtain rfl : FM = killed I M := Submodule.ext hFM
  obtain rfl : FN = killed I N := Submodule.ext hFN
  have key := rank_killed_eq I (Module.finrank ℂ (killed I M)) M N
    (Module.finrank_eq_rank ℂ _).symm (by
      intro S _ _ _ s hs hI
      by_cases h1 : ∃ f : S →ₗ[Rg] M, f ≠ 0
      · obtain ⟨f, hf⟩ := h1
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HM _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      by_cases h2 : ∃ f : S →ₗ[Rg] N, f ≠ 0
      · obtain ⟨f, hf⟩ := h2
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HN _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      push_neg at h1 h2
      rw [rank_zero_iff_forall_zero.2 h1, rank_zero_iff_forall_zero.2 h2])
  exact (Module.finrank_eq_of_rank_eq key).symm
end GlobalTheory.SemisimpleCount
