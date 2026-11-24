-- Prove2me | solution 1 for GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:37.139372+00:00
-- url     : https://prove2.me/submissions/9b10eb8f-05e2-4d80-8f33-72b635144032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalFieldStatement
import Theorems.Thm_GlobalTheory_KSp_Homog_eq_smul_haar_of_homog


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
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by
  first | exact @GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | exact GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | (intros; apply GlobalTheory.KSp.Homog.eq_smul_haar_of_homog <;> assumption)
end _root_.GlobalTheory.T
