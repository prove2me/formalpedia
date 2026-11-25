-- Prove2me | solution 1 for GlobalTheory.HL.LocPattern.zh_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:20:47.013229+00:00
-- url     : https://prove2.me/submissions/81712303-f98b-4af9-bef1-bdee23ffb74e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrame
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_entry_zero
import Theorems.Thm_GlobalTheory_FrameBasic_sig_sig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.LocPattern
theorem _root_.solution (l : Fin (r + 2)) (hl : S.D l ≠ 0) (x y : Fin (r + 1))
    (hxy : ((x : ℕ) < l ∧ (l : ℕ) ≤ y) ∨ ((y : ℕ) < l ∧ (l : ℕ) ≤ x)) : S.Zh x y = 0 := by
  have hZ : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
    fun a b => S.relevant a b
  have hA : ∀ a : Fin (r + 1), (a : ℕ) < l → GlobalTheory.FrameBasic.sig S.w.blocks a < l := by
    intro a ha
    by_contra hc
    push_neg at hc
    apply hl
    unfold Frames.D lead
    apply Matrix.det_eq_zero_of_row_eq_zero (⟨a, ha⟩ : Fin l)
    intro j
    simp only [Matrix.submatrix_apply]
    rw [hZ]
    have hj := j.2
    have : ((Fin.castLE (Nat.lt_succ_iff.mp l.2) j : Fin (r + 1)) : ℕ) ≠
        GlobalTheory.FrameBasic.sig S.w.blocks (Fin.castLE (Nat.lt_succ_iff.mp l.2) (⟨a, ha⟩ : Fin l) : Fin (r + 1)) := by
      simp only [Fin.coe_castLE]; omega
    rw [GlobalTheory.FrameBasic.entry_zero _ _ _ this, zero_mul]
  rw [hZ]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ (by have := hA x h1; omega), zero_mul]
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ ?_, zero_mul]
    intro he
    have h3 := hA y h1
    rw [he, GlobalTheory.FrameBasic.sig_sig] at h3
    omega
end GlobalTheory.HL.LocPattern
