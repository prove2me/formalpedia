-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.exists_isFirstMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:39.832944+00:00
-- url     : https://prove2.me/submissions/68aae371-7471-46f9-805a-9ff42eb74a05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k),
    (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  intro k _ _ _ _ a d Y ⟨J0, hJ0⟩
  classical
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ (fun J => valuation k (minor Y J))
    ⟨J0, Finset.mem_univ _⟩
  set S := Finset.univ.filter (fun J => valuation k (minor Y J) = valuation k (minor Y M)) with hS
  obtain ⟨J, hJS, hJmin⟩ := S.exists_min_image (fun J => idx J) ⟨M, by simp [S]⟩
  have hJ : valuation k (minor Y J) = valuation k (minor Y M) := (Finset.mem_filter.1 hJS).2
  refine ⟨J, ?_, fun J' => ⟨?_, fun hlt => ?_⟩⟩
  · intro h0
    apply hJ0
    have hM0 : valuation k (minor Y M) = 0 := by rw [← hJ, h0, map_zero]
    have h1 := hM J0 (Finset.mem_univ _)
    rw [hM0] at h1
    exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · rw [hJ]; exact hM J' (Finset.mem_univ _)
  · rw [hJ]
    refine lt_of_le_of_ne (hM J' (Finset.mem_univ _)) fun heq => ?_
    have := hJmin J' (by simp [S, heq])
    exact absurd hlt (not_lt.2 this)
end GlobalTheory.RankFibreKer
