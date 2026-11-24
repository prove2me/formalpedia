-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.comp_pow_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:59.649588+00:00
-- url     : https://prove2.me/submissions/a3d67f32-1e8a-4eb6-96fc-0f42b44663c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_mulVec_ev

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
theorem _root_.solution (p : Fin r → K) (j : ℕ) (hj : j < r) : companion p ^ j *ᵥ ev r K 0 = ev r K j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', ← mulVec_mulVec, ih (by omega), comp_mulVec_ev p j hj]
end GlobalTheory.JR.HermInv
