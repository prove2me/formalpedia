-- Prove2me | solution 1 for GlobalTheory.HL.mass_eq_sumCls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:58.308818+00:00
-- url     : https://prove2.me/submissions/b1cd7337-9eb9-434f-a534-c9c2b4603d78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
import Theorems.Thm_GlobalTheory_HL_mass_orbits_eq_tsum_fiber
import Theorems.Thm_GlobalTheory_T_commonStabilizer_stabilizers_commensurable_volume
import Theorems.Thm_GlobalTheory_T_hermitianFrames_stabilizer_acts_on_terms
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP
  have hK : S.K0 ≤ S.St := inf_le_left.trans inf_le_left
  have key := mass_orbits_eq_tsum_fiber S.St S.K0 (fun Λ => S.IsTerm d Λ ∧ P Λ) (S.Fr d) hK
    (by
      rintro h hh Λ ⟨ht, hp⟩
      obtain ⟨ht', -, -, -, hFr, -⟩ := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ ht h hh
      have hlat := (TermBasic.term_basic L r k S d Λ ht).1.1
      exact ⟨⟨ht', hP h hh Λ ht hp⟩, hFr, ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hlat).2.2 h hh⟩)
    (by
      rintro Λ ⟨ht, -⟩
      have tb := TermBasic.term_basic L r k S d Λ ht
      have hA := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ tb.1.1
      have hC := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).2 (S.Fr d Λ) tb.2.2.2.2.2.2.1.1
      exact ⟨hA.1, hA.2.1, hC.1, hC.2.1⟩)
  beta_reduce at key
  unfold Frames.mass Frames.mu
  refine Eq.trans ?_ (key.trans ?_)
  · exact tsum_congr fun o => by split_ifs <;> rfl
  unfold Frames.sumCls Frames.nT Frames.wC
  refine tsum_congr fun c => ?_
  by_cases hc : S.IsIntCls c.out
  · rw [if_pos hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out}
        = {Λ | S.IsTerm d Λ ∧ P Λ ∧ S.Fr d Λ = c.out} := by
      ext Λ
      simp only [Set.mem_ofPred_eq, and_assoc]
    rw [hs]
  · rw [if_neg hc]
    have hs : {x | (S.IsTerm d x ∧ P x) ∧ S.Fr d x = c.out} = (∅ : Set (Submodule L.O S.V)) := by
      ext Λ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, -⟩, hF⟩
      exact hc (hF ▸ (TermBasic.term_basic L r k S d Λ ht).2.2.2.2.2.2.1)
    rw [hs, Set.encard_empty]
    simp
end GlobalTheory.HL
