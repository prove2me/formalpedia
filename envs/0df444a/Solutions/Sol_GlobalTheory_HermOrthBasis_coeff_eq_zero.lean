-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:32.850056+00:00
-- url     : https://prove2.me/submissions/250e93fa-795a-4022-a007-00315bc22874

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_gram_mulVec
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HermOrthBasis
theorem _root_.solution {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    (c : Fin m → E) (h : ∀ a, hf L Hm (∑ b, c b • x b) (x a) = 0) : c = 0 := by
  have h1 : gramT L Hm x *ᵥ c = 0 := funext fun a => (gram_mulVec L Hm x c a).trans (h a)
  have h2 := congrArg (fun v => (gramT L Hm x)⁻¹ *ᵥ v) h1
  simpa only [mulVec_mulVec, nonsing_inv_mul _ hx, one_mulVec, mulVec_zero] using h2
end GlobalTheory.HermOrthBasis
