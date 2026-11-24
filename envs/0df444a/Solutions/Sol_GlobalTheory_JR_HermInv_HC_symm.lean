-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.HC_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:26:00.780418+00:00
-- url     : https://prove2.me/submissions/b2bc7273-1110-4719-ab4d-9248b6f0b588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_hankel_symm
import Theorems.Thm_GlobalTheory_JR_HermInv_HC_apply

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
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution {K : Type} [CommRing K] (a : Inv r K) :
    (companion a.1)ᵀ * hankel a = hankel a * companion a.1 := by
  have : (hankel a * companion a.1)ᵀ = hankel a * companion a.1 := by
    ext i j
    rw [transpose_apply, HC_apply, HC_apply, add_comm (j : ℕ)]
  rw [← this, transpose_mul, hankel_symm]
end GlobalTheory.JR.HermInv
