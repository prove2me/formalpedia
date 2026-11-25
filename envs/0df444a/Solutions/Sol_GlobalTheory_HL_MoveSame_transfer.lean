-- Prove2me | solution 1 for GlobalTheory.HL.MoveSame.transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:16.343526+00:00
-- url     : https://prove2.me/submissions/680338c0-c203-422e-9c35-e0a04e95bcd5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevels
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveSame
theorem _root_.solution {V : Type} [AddCommGroup V] [Module E V] {m : ℕ} {g g' h h' : Fin m → V}
    (hli : LinearIndependent E (Sum.elim g g')) {y : V} {al al' : Fin m → E}
    (e1 : y = ∑ i, al i • g i + ∑ i, al' i • g' i) (e2 : y = ∑ i, al i • h i + ∑ i, al' i • h' i)
    (P : (Fin m → E) → (Fin m → E) → Prop)
    (H : ∃ be be' : Fin m → E, y = ∑ i, be i • g i + ∑ i, be' i • g' i ∧ P be be') :
    ∃ be be' : Fin m → E, y = ∑ i, be i • h i + ∑ i, be' i • h' i ∧ P be be' := by
  obtain ⟨be, be', e3, hP⟩ := H
  have h0 := Fintype.linearIndependent_iff.1 hli (Sum.elim (al - be) (al' - be')) (by
    have := e1.symm.trans e3
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul,
      Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, this, sub_self])
  have a1 : al = be := funext fun i => sub_eq_zero.1 (h0 (Sum.inl i))
  have a2 : al' = be' := funext fun i => sub_eq_zero.1 (h0 (Sum.inr i))
  subst a1 a2
  exact ⟨_, _, e2, hP⟩
end GlobalTheory.HL.MoveSame
