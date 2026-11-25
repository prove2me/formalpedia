-- Prove2me | solution 1 for GlobalTheory.SingleBlock.isLocalAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:17.846302+00:00
-- url     : https://prove2.me/submissions/cac73e03-2079-4580-824a-8b08b8b68908

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Theorems.Thm_GlobalTheory_SingleBlock_unif_ne_zero
import Theorems.Thm_GlobalTheory_SingleBlock_residue_eq_iff
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) : IsLocalAt 𝒪[F] (ϖ : F) := by
  constructor
  · intro h
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩
      (Subtype.ext (mul_inv_cancel₀ (unif_ne_zero hϖ))))
  · intro x hx h
    have h1 : IsUnit (⟨x, hx⟩ : 𝒪[F]) := by
      by_contra hn
      have h2 : IsLocalRing.residue 𝒪[F] ⟨x, hx⟩ = IsLocalRing.residue 𝒪[F] 0 := by
        rw [map_zero, IsLocalRing.residue_eq_zero_iff]; exact hn
      obtain ⟨o, ho, e⟩ := (residue_eq_iff hϖ _ _).1 h2
      exact h o ho (by simpa using e)
    obtain ⟨y, hy⟩ := h1.exists_right_inv
    have h3 : x * (y : F) = 1 := congrArg Subtype.val hy
    rw [← eq_inv_of_mul_eq_one_right h3]; exact y.2
end GlobalTheory.SingleBlock
