-- Prove2me | solution 1 for GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:50:54.153733+00:00
-- url     : https://prove2.me/submissions/c850e09f-3487-44bd-b8a9-b9de553ddb97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBase
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Theorems.Thm_GlobalTheory_UnramOrder_card_coker_of_det_eq


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = resQ ϖ ^ (2 * j) := by
  first | exact @GlobalTheory.UnramOrder.card_coker_of_det_eq | exact GlobalTheory.UnramOrder.card_coker_of_det_eq | (intros; apply GlobalTheory.UnramOrder.card_coker_of_det_eq <;> assumption)
end _root_.GlobalTheory.T
