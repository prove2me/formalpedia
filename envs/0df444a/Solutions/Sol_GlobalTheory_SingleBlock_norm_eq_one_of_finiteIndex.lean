-- Prove2me | solution 1 for GlobalTheory.SingleBlock.norm_eq_one_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:52.108076+00:00
-- url     : https://prove2.me/submissions/b36f8ac2-8b8f-4b2c-87c8-d135ecba5f9b

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F]
namespace GlobalTheory.SingleBlock
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G) (hK : K.index ≠ 0)
    (ρ : G →* ℂˣ) (hρ : ∀ k ∈ K, ρ k = 1) (g : G) : ‖((ρ g : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : ρ.ker.index ≠ 0 := fun h => hK (Nat.eq_zero_of_zero_dvd
    (h ▸ Subgroup.index_dvd_of_le (fun k hk => hρ k hk : K ≤ ρ.ker)))
  have h2 : ρ (g ^ ρ.ker.index) = 1 := ρ.ker.pow_index_mem g
  have h3 : ‖((ρ g : ℂˣ) : ℂ)‖ ^ ρ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h2]; simp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h1).1 h3
end GlobalTheory.SingleBlock
