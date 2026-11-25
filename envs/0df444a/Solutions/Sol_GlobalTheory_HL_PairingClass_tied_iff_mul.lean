-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.tied_iff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:20.747195+00:00
-- url     : https://prove2.me/submissions/bd34280c-6efb-400f-ad78-835ab1e4ca46

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
    ((∀ i j, A i j ∈ O ∧ A' i j ∈ O ∧ ∃ c ∈ O, A' i j - A i j = θ * c) ∧
      (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1)) ↔ Tied O θ A A' := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    choose c hc hc' using fun a b => (h1 a b).2.2
    refine ⟨⟨fun i j h => (h2 i j h).1, fun i => (h3 i).1⟩, ⟨fun i j h => (h2 i j h).2, fun i => (h3 i).2⟩,
      fun i j => (h1 i j).1, fun i j => (h1 i j).2.1, Matrix.of c, hc, ?_⟩
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination hc' a b
  · rintro ⟨a, b, a3, b3, C, hC, e⟩
    refine ⟨fun i j => ⟨a3 i j, b3 i j, C i j, hC i j, ?_⟩, fun i j h => ⟨a.1 i j h, b.1 i j h⟩,
      fun i => ⟨a.2 i, b.2 i⟩⟩
    rw [e]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
end GlobalTheory.HL.PairingClass
