-- Prove2me | solution 1 for GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:26.985275+00:00
-- url     : https://prove2.me/submissions/f9712df5-c010-4592-994a-31608346ea04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonneg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonnegStatement
import Theorems.Thm_GlobalTheory_UnitLemma_exists_surjective_valuation_isIntegral_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  first | exact @GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | exact GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff | (intros; apply GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff <;> assumption)
end _root_.GlobalTheory.T
