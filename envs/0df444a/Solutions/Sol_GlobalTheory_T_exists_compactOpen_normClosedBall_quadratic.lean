-- Prove2me | solution 1 for GlobalTheory.T.exists_compactOpen_normClosedBall_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:38:54.443149+00:00
-- url     : https://prove2.me/submissions/78be4009-70f7-42d1-97d9-aae8e8dc9888

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenNormClosedBallQuadraticStatement
import Theorems.Thm_GlobalTheory_NormBall_exists_normBall


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s : Fˣ), ∃ L : AddSubgroup E, (L : Set E) = {z | Algebra.norm F z ∈ GlobalTheory.SplitWeil.cball s} ∧ IsCompact (L : Set E) ∧ IsOpen (L : Set E) := by
  first | exact @GlobalTheory.NormBall.exists_normBall | exact GlobalTheory.NormBall.exists_normBall | (intros; apply GlobalTheory.NormBall.exists_normBall <;> assumption)
end _root_.GlobalTheory.T
