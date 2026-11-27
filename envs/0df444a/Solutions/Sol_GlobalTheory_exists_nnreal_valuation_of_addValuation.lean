-- Prove2me | solution 1 for GlobalTheory.exists_nnreal_valuation_of_addValuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:30.015168+00:00
-- url     : https://prove2.me/submissions/0510bbb2-1282-4ad7-8013-abe7f326f9fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Theorems.Thm_GlobalTheory_expNegValuation_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩
end GlobalTheory
