-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.comp_pow_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:39.537255+00:00
-- url     : https://prove2.me/submissions/cee8a45e-8536-40ed-8dd4-76ad20634503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_comp_pow_ev

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
theorem _root_.solution (p : Fin r → K) : companion p ^ r *ᵥ ev r K 0 = -p := by
  cases r with
  | zero => funext i; exact i.elim0
  | succ s =>
    rw [pow_succ', ← mulVec_mulVec, comp_pow_ev p s (by omega)]
    funext i
    simp only [mulVec, dotProduct, ev, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single ⟨s, by omega⟩]
    · simp [companion]
    · intro l _ hl
      rw [if_neg]
      exact fun h => hl (Fin.ext h)
    · simp
end GlobalTheory.JR.HermInv
