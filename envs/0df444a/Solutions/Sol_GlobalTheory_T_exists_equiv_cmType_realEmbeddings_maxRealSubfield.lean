-- Prove2me | solution 1 for GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:51.854302+00:00
-- url     : https://prove2.me/submissions/82804628-aa3f-401f-946d-32b299a2c773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
import Theorems.Thm_GlobalTheory_CMTypeRealEmb_exists_equiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeRealEmb.exists_equiv | exact GlobalTheory.CMTypeRealEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeRealEmb.exists_equiv <;> assumption)
end _root_.GlobalTheory.T
