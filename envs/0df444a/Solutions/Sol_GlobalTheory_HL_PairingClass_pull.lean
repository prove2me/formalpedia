-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:17.464609+00:00
-- url     : https://prove2.me/submissions/2703813d-7a41-4327-aff6-55b3514f1a9b

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
import Theorems.Thm_GlobalTheory_HL_CoordUnip_grp_apply
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
namespace GlobalTheory.HL.PairingClass
theorem _root_.solution {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V)
    (f : Fin (r + 1) → V) (f₁ : Fin (r + 1) → S.V) (hf : ∀ a, f₁ a = c.e (f a))
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (h : ∀ j, c.grp g (f₁ j) = ∑ i, s i j • f₁ i) :
    (fun j => g (f j)) = act f s := by
  funext j
  apply c.e.injective
  have := h j
  simp only [hf, CoordUnip.grp_apply] at this
  rw [this]
  simp [act]
end GlobalTheory.HL.PairingClass
