-- Prove2me | solution 1 for GlobalTheory.CMFormBound.ord_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:03:59.791101+00:00
-- url     : https://prove2.me/submissions/1a61ad45-f910-4734-a8d5-e0793d213744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]
namespace GlobalTheory.CMFormBound
theorem _root_.solution (x : O) (hx : x ∉ IsLocalRing.maximalIdeal O) : ord_vw O (algebraMap O K x) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) = 1 :=
    le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one x)
      (not_lt.1 fun h => hx (((IsDiscreteValuationRing.maximalIdeal O).valuation_lt_one_iff_mem x).1 h))
  unfold ord_vw
  rw [h1, WithZero.log_one, neg_zero]
end GlobalTheory.CMFormBound
