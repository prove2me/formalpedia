-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.unitary_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:51.366297+00:00
-- url     : https://prove2.me/submissions/e5be3610-ff63-4502-b9b9-11ed491d579b

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
import Theorems.Thm_GlobalTheory_HL_PairingClass_UT_mul
import Theorems.Thm_GlobalTheory_HL_PairingClass_IntM_mul
import Theorems.Thm_GlobalTheory_HL_PairingClass_UT_inv
import Theorems.Thm_GlobalTheory_HL_PairingClass_Tied_mul
import Theorems.Thm_GlobalTheory_HL_PairingClass_Tied_inv
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
namespace GlobalTheory.HL.PairingClass
theorem _root_.solution {Fr : LocNG.FrameD H r} {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : LocNG.IsUnitary H g := by
  unfold LocNG.FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => intro x y; rfl
  | mul a b _ _ ha hb => intro x y; exact (ha _ _).trans (hb x y)
  | inv a _ ha =>
    intro x y
    have := ha (a⁻¹ x) (a⁻¹ y)
    rw [← this]
    simp [LinearEquiv.coe_inv]
end GlobalTheory.HL.PairingClass
