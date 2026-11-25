-- Prove2me | solution 1 for GlobalTheory.OrderBasis.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:53.865812+00:00
-- url     : https://prove2.me/submissions/a5793b2a-d1d9-4f92-be42-ec479ea3fc85

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrderBasis
namespace GlobalTheory.OrderBasis
theorem _root_.solution {E : Type} [CommRing E] (R : Subring E) {ι : Type} [Fintype ι]
    (P : ι → E → Prop) (hP : ∀ i d c, c ∈ R → P i d → P i (c * d))
    (h : ∀ i, ∃ d ∈ R, IsUnit d ∧ P i d) : ∃ d ∈ R, IsUnit d ∧ ∀ i, P i d := by
  choose d hdR hdu hd using h
  refine ⟨∏ i, d i, R.prod_mem fun i _ => hdR i, IsUnit.prod_iff.mpr fun i _ => hdu i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP _ _ _ (R.prod_mem fun i _ => hdR i) (hd i)
end GlobalTheory.OrderBasis
