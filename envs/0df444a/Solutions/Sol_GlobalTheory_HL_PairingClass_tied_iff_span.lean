-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.tied_iff_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:31.903895+00:00
-- url     : https://prove2.me/submissions/0f7fdfb1-5ef6-4361-bd02-86b296fd7335

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.PairingClass
theorem _root_.solution (O : Subring E) (θ : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ O) ∧
      ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ O) ∧
      (∀ a b, A a b - A' a b ∈ Submodule.span O {θ})) ↔ Tied O θ A A' := by
  constructor
  · rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, h⟩
    choose c hc using fun a b => Submodule.mem_span_singleton.1 (h a b)
    refine ⟨⟨a1, a2⟩, ⟨b1, b2⟩, a3, b3, Matrix.of fun a b => -(c a b : E), fun a b => O.neg_mem (c a b).2, ?_⟩
    ext a b
    have := hc a b
    rw [Subring.smul_def, smul_eq_mul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination this
  · rintro ⟨a, b, a3, b3, C, hC, e⟩
    refine ⟨⟨a.1, a.2, a3⟩, ⟨b.1, b.2, b3⟩, fun i j => Submodule.mem_span_singleton.2
      ⟨⟨-C i j, O.neg_mem (hC i j)⟩, ?_⟩⟩
    rw [Subring.smul_def, smul_eq_mul, e]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.HL.PairingClass
