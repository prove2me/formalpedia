-- Prove2me | solution 1 for GlobalTheory.HL.FixFrames.psiOf_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:27.929611+00:00
-- url     : https://prove2.me/submissions/58b6e6e3-c833-472a-9bb2-92603fc8248e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFrameUnipotentExchangingDualIsotropicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesComplementUnitaryNormalisesStabil
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FixFrames
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FixFrames
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (m : S.GLV) (mfix : ∀ a, m (g a) = g a) : S.psiOf g gs m = 1 := by
  have ne : ∀ j : Fin r, j.succ ≠ j.castSucc := fun j e => by
    have := congrArg Fin.val e
    simp at this
  unfold Frames.psiOf Frames.coef
  simp only [mfix, Frames.h, hd, ne, if_false, Finset.sum_const_zero, mul_zero, AddChar.map_zero_eq_one]
end GlobalTheory.HL.FixFrames
