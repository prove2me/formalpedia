-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.value_lt_one_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:26.961855+00:00
-- url     : https://prove2.me/submissions/9c2375f5-d90e-4101-b0eb-ab2d0825f22c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_tendsto_pow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution (τ : E ≃ₐ[k] E) (hτ : Continuous τ) {x : E}
    (hx : valuation E x < 1) : valuation E (τ x) < 1 := by
  have ht : Tendsto (fun n : ℕ => τ (x ^ n)) atTop (𝓝 0) := by
    have h := (hτ.tendsto 0).comp (tendsto_pow_zero hx)
    rw [map_zero] at h
    exact h
  have hmem : {y : E | valuation E y < 1} ∈ 𝓝 (0 : E) :=
    (IsValuativeTopology.hasBasis_nhds_zero' E).mem_of_mem one_ne_zero
  obtain ⟨n, hn, hn0⟩ := ((ht.eventually hmem).and (eventually_gt_atTop 0)).exists
  by_contra hc
  have h1 : 1 ≤ valuation E (τ x) ^ n := one_le_pow₀ (not_lt.1 hc)
  have h2 : valuation E (τ (x ^ n)) < 1 := hn
  rw [map_pow, map_pow] at h2
  exact absurd h2 (not_lt.2 h1)
end GlobalTheory.CompanionTheory.UnramDict
