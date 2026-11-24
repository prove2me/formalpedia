-- Prove2me | solution 1 for GlobalTheory.WeilSmooth.nl_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:55:27.013+00:00
-- url     : https://prove2.me/submissions/638c8bf1-77ee-402f-8a37-f1ce9d8b59b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
import Theorems.Thm_GlobalTheory_T_continuous_etaleHermitianPair_norm_and_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.WeilSmooth
open GlobalTheory.JR
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.WeilSmooth
theorem _root_.solution [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero F E A
end GlobalTheory.WeilSmooth
