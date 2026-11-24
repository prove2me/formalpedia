-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.NearZero.finite_F_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:12.439414+00:00
-- url     : https://prove2.me/submissions/726dc62c-9f6b-44b5-b95c-8c020186556b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
import Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_E_L

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
theorem _root_.solution [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have := finite_E_L A
  exact Module.Finite.trans E A.L
end GlobalTheory.JR.WeilQuad.NearZero
