-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.mem_innerOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:00.050429+00:00
-- url     : https://prove2.me/submissions/2ee9f660-8aea-490d-be52-2bf3f64b6816

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_Inhab_spanTo_eq
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ innerOf S g gs Λ ↔ (∀ j : Fin r, hf L S.Hm x (g j.castSucc) = 0) ∧ proj S g gs x ∈ Λ := by
  simp only [innerOf, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, spanTo_eq, mem_perp_span, Set.forall_mem_range]
end GlobalTheory.HL.Inhab
