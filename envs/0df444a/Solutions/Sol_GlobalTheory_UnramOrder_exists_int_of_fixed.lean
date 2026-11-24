-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_int_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:37:41.046538+00:00
-- url     : https://prove2.me/submissions/c3258843-12a6-4a53-847d-92f727a81a55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff

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
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.UnramOrder
theorem _root_.solution (L : LocE F E) {x : E} (hx : x ∈ L.O) (h : L.cj x = x) :
    ∃ c : 𝒪[F], x = algebraMap F E c := by
  obtain ⟨a, rfl⟩ := (L.cj_fix x).1 h
  exact ⟨⟨a, (algebraMap_mem_iff L a).1 hx⟩, rfl⟩
end GlobalTheory.UnramOrder
