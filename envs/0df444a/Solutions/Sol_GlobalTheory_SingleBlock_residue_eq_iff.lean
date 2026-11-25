-- Prove2me | solution 1 for GlobalTheory.SingleBlock.residue_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:54.422404+00:00
-- url     : https://prove2.me/submissions/a0999156-faab-4af2-8626-b7a661dc4c89

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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
namespace GlobalTheory.SingleBlock
theorem _root_.solution (hϖ : Irreducible ϖ) (x y : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = IsLocalRing.residue 𝒪[F] y ↔
      ∃ o ∈ (𝒪[F] : Subring F), (x : F) - y = ϖ * o := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    have := congrArg Subtype.val hc
    simpa [mul_comm] using this.symm
  · rintro ⟨o, ho, e⟩
    exact ⟨⟨o, ho⟩, Subtype.ext (by simpa [mul_comm] using e.symm)⟩
end GlobalTheory.SingleBlock
