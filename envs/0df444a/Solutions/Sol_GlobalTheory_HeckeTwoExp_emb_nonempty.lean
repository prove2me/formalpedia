-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.emb_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:52.179857+00:00
-- url     : https://prove2.me/submissions/5d272059-587a-4315-801e-4077ac39958f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution [IsTotallyReal F] : Nonempty (Emb F) := by
  have : Nonempty (F →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := this
  exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
end GlobalTheory.HeckeTwoExp
