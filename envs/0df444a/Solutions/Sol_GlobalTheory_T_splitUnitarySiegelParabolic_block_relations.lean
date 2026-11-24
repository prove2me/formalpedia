-- Prove2me | solution 1 for GlobalTheory.T.splitUnitarySiegelParabolic_block_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:40:12.953871+00:00
-- url     : https://prove2.me/submissions/addc86ab-c4c5-44d5-acc9-1496f458387a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitUnitarySiegelParabolicBlockRelations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitUnitarySiegelParabolicBlockRelationsStatement
import Theorems.Thm_GlobalTheory_KSp_sieg_blocks
import Theorems.Thm_GlobalTheory_WeilM_IsQuad_invol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : UG c (stdJ ν E)), p ∈ sieg c ν → (mat c p).toBlocks₁₁ * (((mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧ (mat c p).toBlocks₁₁ * (((mat c p).toBlocks₁₂).map c)ᵀ = (mat c p).toBlocks₁₂ * (((mat c p).toBlocks₁₁).map c)ᵀ ∧ ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = levi c hE.invol a * unip c b hb := by
  first | exact @GlobalTheory.KSp.sieg_blocks | exact GlobalTheory.KSp.sieg_blocks | (intros; apply GlobalTheory.KSp.sieg_blocks <;> assumption)
end _root_.GlobalTheory.T
