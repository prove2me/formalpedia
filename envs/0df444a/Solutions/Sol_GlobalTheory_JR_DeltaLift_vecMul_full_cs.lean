-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.vecMul_full_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:40.165807+00:00
-- url     : https://prove2.me/submissions/6f51ec29-2437-4c78-a741-1ba199cca1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_full_cc
import Theorems.Thm_GlobalTheory_JR_DeltaLift_full_lc

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.DeltaLift
theorem _root_.solution (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]
end GlobalTheory.JR.DeltaLift
