-- Prove2me | solution 1 for GlobalTheory.HL.MoveWit.graph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:59:11.062936+00:00
-- url     : https://prove2.me/submissions/0a49593b-46a2-4ea1-adb0-c2336af75143

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnesses
import Theorems.Thm_GlobalTheory_HL_MoveWit_inTh_mem
import Theorems.Thm_GlobalTheory_HL_MoveWit_inTh_add
import Theorems.Thm_GlobalTheory_HL_MoveWit_app_inv
import Theorems.Thm_GlobalTheory_HL_MoveWit_inTh_tr

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveWit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveWit
theorem _root_.solution {Λ Λ₁ : Submodule L.O S.V} {a a' : S.GLV} (ha : ∀ v, v ∈ Λ₁ ↔ a v ∈ Λ)
    (hN : a ∈ S.N) (hN' : a' ∈ S.N')
    (H : ∀ v ∈ Λ, v ∈ perp L S.Hm S.X' → S.InTh Λ (a (a' v) - v)) : S.graphOf Λ ⊆ S.graphOf Λ₁ := by
  rintro p ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
  have hi := (S.N.inv_mem hN).2
  have hi' := hN'.2
  refine ⟨a' y', (ha _).2 ?_, a⁻¹ y, (ha _).2 (by rwa [app_inv]), (hi'.1 _).2 h1, (hi.1 _).2 h2, ?_, ?_, ?_⟩
  · have := Λ.add_mem (inTh_mem S (H _ hy' h1)) hy'
    rwa [sub_add_cancel] at this
  · have := S.X'.add_mem (hi'.2 _ h1) h3
    rwa [sub_add_sub_cancel] at this
  · have := S.X.add_mem (hi.2 _ h2) h4
    rwa [sub_add_sub_cancel] at this
  · apply inTh_tr S ha
    have := inTh_add S (H _ hy' h1) h5
    rwa [sub_add_sub_cancel, ← app_inv S a y, ← map_sub] at this
end GlobalTheory.HL.MoveWit
