-- Prove2me | solution 1 for GlobalTheory.HL.FibU.cint_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:46.510643+00:00
-- url     : https://prove2.me/submissions/42b510b0-224f-4ee8-a18c-ba7c9a288a80

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_eq_mean_over_representatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
namespace GlobalTheory.HL.FibU
theorem _root_.solution {W : Type} [AddCommGroup W] (A P : AddSubgroup W) (R : Finset W) (Q : W → Prop)
    (g : W → ℂ) (hR : ∀ w ∈ R, w ∈ A) (hR' : ∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ P)
    (hQ : ∀ w ∈ A, ∀ b ∈ P, Q w → Q (w + b)) (hg : ∀ w, ∀ b ∈ P, g (w + b) = g w) :
    cint A (fun u => ind (fun u => u ∈ A ∧ Q u) u * g u) = (∑ u ∈ R.filter Q, g u) / (R.card : ℂ) := by
  have := (GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives A (P ⊓ A) (fun u => ind (fun u => u ∈ A ∧ Q u) u * g u) R inf_le_right ?_ ?_ hR ?_).2.2
  · rw [this, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    simp [ind, hR u hu]
  · rintro w b ⟨hb, hb'⟩
    have : (w + b ∈ A ∧ Q (w + b)) ↔ (w ∈ A ∧ Q w) := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by simpa using A.sub_mem h1 hb', ?_⟩
        simpa using hQ _ h1 _ (P.neg_mem hb) h2
      · rintro ⟨h1, h2⟩
        exact ⟨A.add_mem h1 hb', hQ _ h1 _ hb h2⟩
    have h' : ind (fun u => u ∈ A ∧ Q u) (w + b) = ind (fun u => u ∈ A ∧ Q u) w := by
      unfold ind
      exact congrArg (fun p : Prop => @ite ℂ p (Classical.propDecidable p) 1 0) (propext this)
    simp only [h', hg w b hb]
  · intro w hw
    simp [ind, hw]
  · intro w hw
    obtain ⟨x, ⟨hx, hx'⟩, hu⟩ := hR' w hw
    exact ⟨x, ⟨hx, hx', A.sub_mem hw (hR x hx)⟩, fun y hy => hu y ⟨hy.1, hy.2.1⟩⟩
end GlobalTheory.HL.FibU
