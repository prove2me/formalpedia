-- Prove2me | solution 1 for GlobalTheory.CongTrans.eq_zero_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:26.512032+00:00
-- url     : https://prove2.me/submissions/ab67c2fa-a8d7-4ef3-9796-8753824d10a1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitian
import Theorems.Thm_GlobalTheory_CongTrans_isAdicComplete_int

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
open GlobalTheory GlobalTheory.CongTrans
open GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.CongTrans
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : 𝒪[F]) (h : ∀ n, ϖ ^ n ∣ x) : x = 0 := by
  have hc := isAdicComplete_int (F := F)
  rw [hϖ.maximalIdeal_eq] at hc
  refine hc.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
  exact h n
end GlobalTheory.CongTrans
