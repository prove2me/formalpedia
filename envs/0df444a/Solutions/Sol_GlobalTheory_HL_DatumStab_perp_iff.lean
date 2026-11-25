-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.perp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:47.732314+00:00
-- url     : https://prove2.me/submissions/8618803c-860f-4f63-b93b-81066890f0cf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hg : g ∈ isomG L Hm) {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) :
    g x ∈ perp L Hm Y ↔ x ∈ perp L Hm Y := by
  have h : ∀ y ∈ Y, hf L Hm (g x) y = hf L Hm x y := fun y hy => by
    conv_lhs => rw [← hY y hy]
    exact hg x y
  exact ⟨fun H y hy => (h y hy).symm.trans (H y hy), fun H y hy => (h y hy).trans (H y hy)⟩
end GlobalTheory.HL.DatumStab
