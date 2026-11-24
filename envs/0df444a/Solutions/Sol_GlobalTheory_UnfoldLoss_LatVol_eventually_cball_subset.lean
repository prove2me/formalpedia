-- Prove2me | solution 1 for GlobalTheory.UnfoldLoss.LatVol.eventually_cball_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:04.683216+00:00
-- url     : https://prove2.me/submissions/460bf381-8298-4e04-b71b-0ea3c88f8d75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemVarLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VariablesUniformizerPowerLatticeBasisOpenVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.UnfoldLoss
open GlobalTheory GlobalTheory.UnfoldLoss GlobalTheory.UnfoldLoss.LatVol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.UnfoldLoss.LatVol
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∀ᶠ n : ℕ in Filter.atTop, cball (ϖ ^ n) ⊆ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  haveI : MulArchimedean (ValueGroupWithZero k) := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 γ
  refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => hγ ?_⟩
  have hz' : valuation k z ≤ valuation k ((ϖ ^ n : kˣ) : k) := hz
  rw [Units.val_pow_eq_pow_val, map_pow] at hz'
  exact (hz'.trans (pow_le_pow_of_le_one zero_le h1.le hn)).trans_lt hN
end GlobalTheory.UnfoldLoss.LatVol
