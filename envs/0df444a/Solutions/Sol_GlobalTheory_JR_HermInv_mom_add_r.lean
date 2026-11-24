-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.mom_add_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:19:50.114667+00:00
-- url     : https://prove2.me/submissions/c78161a7-d3f1-4a0e-8cc3-df16e7a81c64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_mulBm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (Y : Gl r K) (q : Fin r → K) (hq : Y.1 ^ r *ᵥ Y.2.1 = -(Bm Y *ᵥ q)) (k : ℕ) :
    mom Y (k + r) = -((fun j : Fin r => mom Y (k + j)) ⬝ᵥ q) := by
  rw [← mulBm_eq, ← dotProduct_mulVec, ← mulVec_mulVec, ← dotProduct_neg, ← mulVec_neg, ← hq, mulVec_mulVec, ← pow_add]
  rfl
end GlobalTheory.JR.HermInv
