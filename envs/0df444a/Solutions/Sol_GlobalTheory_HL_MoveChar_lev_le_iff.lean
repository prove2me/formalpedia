-- Prove2me | solution 1 for GlobalTheory.HL.MoveChar.lev_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:09.880062+00:00
-- url     : https://prove2.me/submissions/fd9f2406-a9dc-449b-b70e-3675d1fa827d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOne
import Theorems.Thm_GlobalTheory_HL_MoveChar_uniq

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveChar
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveChar
theorem _root_.solution {g g' : Fin (r + 1) → S.V} (hl : LinearIndependent E (Sum.elim g g'))
    (a a' : Fin (r + 1) → E) (j : ℕ) :
    S.lev g g' (∑ i, a i • g i + ∑ i, a' i • g' i) ≤ j ↔
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (a i) (a' i) := by
  refine ⟨fun h i hi => ?_, fun h => Nat.sInf_le ⟨a, a', rfl, h⟩⟩
  have hne : {j : ℕ | ∃ al al' : Fin (r + 1) → E,
      ∑ i, a i • g i + ∑ i, a' i • g' i = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
      ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)}.Nonempty :=
    ⟨r + 1, a, a', rfl, fun i hi => absurd i.2 (not_lt.2 hi)⟩
  obtain ⟨b, b', e, hb⟩ := Nat.sInf_mem hne
  obtain ⟨rfl, rfl⟩ := uniq S hl e
  exact hb i (le_trans h hi)
end GlobalTheory.HL.MoveChar
