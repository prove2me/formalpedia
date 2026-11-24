-- Prove2me | solution 1 for GlobalTheory.T.map_mul_left_eq_inv_norm_haarChar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:10.684342+00:00
-- url     : https://prove2.me/submissions/77d3d922-8b06-47c3-b210-44df9a312ecf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMulLeftEqNormSmulStatement
import Theorems.Thm_GlobalTheory_KSp_map_mul_left_eq_norm_smul


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (z : Eˣ), μ.map (fun x => (z : E) * x) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) z))⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_mul_left_eq_norm_smul | exact GlobalTheory.KSp.map_mul_left_eq_norm_smul | (intros; apply GlobalTheory.KSp.map_mul_left_eq_norm_smul <;> assumption)
end _root_.GlobalTheory.T
