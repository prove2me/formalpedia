-- Prove2me | solution 1 for GlobalTheory.T.relIndex_span_lattice_matrix_det_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:19.859905+00:00
-- url     : https://prove2.me/submissions/287e1324-fda5-4d97-8e72-77206a591db6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Theorems.Thm_GlobalTheory_HL_FrameIndex_relIndex_span_matrix


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ {n m : ℕ} (b : Fin m → Fin n → E), LinearIndependent E b → ∀ (A : Matrix (Fin m) (Fin m) E) (c : F), c ≠ 0 → A.det * L.cj A.det = algebraMap F E c → ∀ Q Q' : Submodule L.O (Fin n → E), Q = Submodule.span L.O (Set.range b) → Q' = Submodule.span L.O (Set.range fun j => ∑ i, A i j • b i) → Q'.toAddSubgroup.relIndex Q.toAddSubgroup ≠ 0 ∧ Q.toAddSubgroup.relIndex Q'.toAddSubgroup ≠ 0 ∧ (Q'.toAddSubgroup.relIndex Q.toAddSubgroup : ℝ) = (resQ ϖ : ℝ) ^ (vE L ϖ (algebraMap F E c)) * (Q.toAddSubgroup.relIndex Q'.toAddSubgroup : ℝ) := by
  first | exact @GlobalTheory.HL.FrameIndex.relIndex_span_matrix | exact GlobalTheory.HL.FrameIndex.relIndex_span_matrix | (intros; apply GlobalTheory.HL.FrameIndex.relIndex_span_matrix <;> assumption)
end _root_.GlobalTheory.T
