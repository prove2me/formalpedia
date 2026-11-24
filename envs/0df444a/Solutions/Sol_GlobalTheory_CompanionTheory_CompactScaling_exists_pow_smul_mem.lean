-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CompactScaling.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:24:36.148694+00:00
-- url     : https://prove2.me/submissions/9a92fea6-2bd9-47ea-9c37-e7795d5830bb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompactScaledIntoNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CompactScaling
namespace GlobalTheory.CompanionTheory.CompactScaling
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  intro k _ _ _ _ n K hK U hU ϖ hϖ
  have hpow : Tendsto (fun l : ℕ => ϖ ^ l) atTop (𝓝 (0 : k)) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hϖ γ
    rw [eventually_atTop]
    refine ⟨m, fun l hl => ?_⟩
    simp only [Set.mem_ofPred_eq, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hl) hm
  have hnear : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ K, c • x ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun x _ => ?_)
    have hcont : Continuous (fun p : k × (Fin n → k) => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    have hlim : Tendsto (fun p : k × (Fin n → k) => p.1 • p.2) (𝓝 (0, x)) (𝓝 0) := by
      simpa using hcont.tendsto (0, x)
    exact hlim hU
  exact (hpow.eventually hnear).exists
end GlobalTheory.CompanionTheory.CompactScaling
