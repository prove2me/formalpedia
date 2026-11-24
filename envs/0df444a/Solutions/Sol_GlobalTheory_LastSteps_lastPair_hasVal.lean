-- Prove2me | solution 1 for GlobalTheory.LastSteps.lastPair_hasVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:36:22.975456+00:00
-- url     : https://prove2.me/submissions/f93ea629-f414-4153-b90f-eb06080ba688

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n']
omit [Fintype n']
namespace GlobalTheory.LastSteps
theorem _root_.solution (q : Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (v : n'' ⊕ Fin 1 → k)
    (a : 𝓀[k]) : (lastPair q L).HasVal v a ↔
      v ∘ Sum.inl ∈ L ∧ ∃ s : 𝒪[k], (s : k) = q.1 • v (Sum.inr 0) ∧ residue 𝒪[k] s = a := by
  have hq : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  have h1 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) ∘ Sum.inl = v ∘ Sum.inl := fun s => by
    ext i
    simp [avec]
  have h2 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) (Sum.inr 0) = v (Sum.inr 0) - s * q.inv := fun s => by
    simp [avec, Subring.smul_def]
  rw [lastPair, Pair.hasVal_iff (glue_hasVal _), glue_ker]
  simp only [mem_lastKer, h1, h2]
  constructor
  · rintro ⟨s, rfl, hL, ht⟩
    refine ⟨hL, s + q.1 * ⟨_, ht⟩, ?_, ?_⟩
    · change (s : k) + q.1 * (v (Sum.inr 0) - s * q.inv) = q.1 * v (Sum.inr 0)
      linear_combination (-(s : k)) * hq
    · rw [map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero]
  · rintro ⟨hL, s, hs, rfl⟩
    refine ⟨s, rfl, hL, ?_⟩
    have : v (Sum.inr 0) - s * q.inv = 0 := by
      rw [hs]
      change _ - (q.1 : k) * v (Sum.inr 0) * q.inv = 0
      linear_combination (-(v (Sum.inr 0))) * hq
    rw [this]
    exact zero_mem _
end GlobalTheory.LastSteps
