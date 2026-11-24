-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.sec_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:11.457391+00:00
-- url     : https://prove2.me/submissions/57305b30-be8d-40ad-b18a-1f55b1726f03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_add_r
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_pow_r
import Theorems.Thm_GlobalTheory_JR_HermInv_Bm_sec

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
theorem _root_.solution (a : Inv r K) (k : ℕ) :
    mom (sec a) (k + r) = -((fun j : Fin r => mom (sec a) (k + j)) ⬝ᵥ a.1) :=
  mom_add_r (sec a) a.1 (by rw [Bm_sec, one_mulVec]; exact comp_pow_r a.1) k
end GlobalTheory.JR.HermInv
