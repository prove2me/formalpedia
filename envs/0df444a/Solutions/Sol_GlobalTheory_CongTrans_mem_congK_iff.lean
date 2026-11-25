-- Prove2me | solution 1 for GlobalTheory.CongTrans.mem_congK_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:24.993456+00:00
-- url     : https://prove2.me/submissions/87a058b8-76db-405f-b435-ec355400fb1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
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
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {m : ℕ}
namespace GlobalTheory.CongTrans
theorem _root_.solution (ϖ : 𝒪[F]) (i : ℕ) (A : Matrix (Fin m) (Fin m) E) :
    A ∈ congK L ϖ m i ↔ ∃ N, IsIntM L N ∧ A = 1 + algebraMap F E ϖ ^ i • N := by
  constructor
  · intro h
    choose c hc hc' using h
    refine ⟨Matrix.of c, hc, ?_⟩
    ext a b
    have := hc' a b
    rw [map_pow] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination this
  · rintro ⟨N, hN, rfl⟩ a b
    exact ⟨N a b, hN a b, by simp⟩
end GlobalTheory.CongTrans
