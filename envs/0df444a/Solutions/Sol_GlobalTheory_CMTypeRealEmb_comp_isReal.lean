-- Prove2me | solution 1 for GlobalTheory.CMTypeRealEmb.comp_isReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:58.084698+00:00
-- url     : https://prove2.me/submissions/b213ffb7-ec68-4882-9cee-8da8c08b0360

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.CMTypeRealEmb
namespace GlobalTheory.CMTypeRealEmb
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a
end GlobalTheory.CMTypeRealEmb
