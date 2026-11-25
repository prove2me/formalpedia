-- Prove2me | solution 1 for GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:40.424102+00:00
-- url     : https://prove2.me/submissions/7ed9d5f6-fa92-4122-812c-9f288f60c2fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Theorems.Thm_GlobalTheory_KSp_map_twoSided_haar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_twoSided_haar | exact GlobalTheory.KSp.map_twoSided_haar | (intros; apply GlobalTheory.KSp.map_twoSided_haar <;> assumption)
end _root_.GlobalTheory.T
