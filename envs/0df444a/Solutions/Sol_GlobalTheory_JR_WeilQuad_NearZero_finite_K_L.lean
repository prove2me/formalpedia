-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NearZero.finite_K_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:13.674089+00:00
-- url     : https://prove2.me/submissions/3d1934a9-77cf-4bd5-b64b-756bd52128dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_F_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.NearZero
theorem _root_.solution [Unram F E] (A : Et F E) : Module.Finite A.K A.L := by
  have := finite_F_L A
  exact Module.Finite.of_restrictScalars_finite F A.K A.L
end GlobalTheory.JR.WeilQuad.NearZero
