-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.full_mulVec_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:12:38.108068+00:00
-- url     : https://prove2.me/submissions/176a4bff-a950-40ba-b3da-9bd848f0dc9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift
import Theorems.Thm_GlobalTheory_JR_DeltaLift_full_cc
import Theorems.Thm_GlobalTheory_JR_DeltaLift_full_cl

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
theorem _root_.solution (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]
  ring
end GlobalTheory.JR.DeltaLift
