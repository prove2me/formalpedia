-- Prove2me | solution 1 for GlobalTheory.HL.MoveChar.uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:25:12.837246+00:00
-- url     : https://prove2.me/submissions/bf1e864c-b320-4121-bd20-9c2cd4c6b389

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOne
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveChar
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveChar
theorem _root_.solution {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    {a a' b b' : Fin (r + 1) → E}
    (h : ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, b i • g i + ∑ i, b' i • g' i) :
    a = b ∧ a' = b' := by
  have := Fintype.linearIndependent_iffₛ.1 hl (Sum.elim a a') (Sum.elim b b')
    (by simpa [Fintype.sum_sum_type] using h)
  exact ⟨funext fun i => this (.inl i), funext fun i => this (.inr i)⟩
end GlobalTheory.HL.MoveChar
