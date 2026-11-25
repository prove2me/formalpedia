-- Prove2me | solution 1 for GlobalTheory.MatchTerm.limit_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:49.44085+00:00
-- url     : https://prove2.me/submissions/fe47ec37-8729-450b-8056-81325363301a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_tendsto_tsum_pow_classes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']
namespace GlobalTheory.MatchTerm
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (x : X) (α' : ℕ → X')
    (hα : ∀ j, ∃ μ, α' (j + 1) = α' j + n ^ j • μ)
    (hs : ∀ j, ∑' μ, σ' (α' j + n ^ j • μ) = c * ∑' μ, σ (x + n ^ j • μ)) :
    (∀ x', (∀ j, ∃ μ, x' = α' j + n ^ j • μ) → σ' x' = c * σ x) ∧
      (c * σ x ≠ 0 → ∃ x', ∀ j, ∃ μ, x' = α' j + n ^ j • μ) := by
  have h1 := ((tendsto_tsum_pow_classes K X n hn σ hσ (fun _ => x) fun j => ⟨0, by simp⟩).1 x
    fun j => ⟨0, by simp⟩).const_mul c
  have h2 := tendsto_tsum_pow_classes K X' n hn σ' hσ' α' hα
  simp only [hs] at h2
  refine ⟨fun x' hx => tendsto_nhds_unique (h2.1 x' hx) h1, fun hc => ?_⟩
  by_contra h
  exact hc (tendsto_nhds_unique h1 (h2.2 h))
end GlobalTheory.MatchTerm
