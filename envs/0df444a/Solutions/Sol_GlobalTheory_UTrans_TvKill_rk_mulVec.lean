-- Prove2me | solution 1 for GlobalTheory.UTrans.TvKill.rk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:35.235255+00:00
-- url     : https://prove2.me/submissions/746f4b81-78bc-417d-9acf-143887a7e429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.TvKill
open GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.TvKill
theorem _root_.solution (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by
  funext a
  simp only [rk, Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring
end GlobalTheory.UTrans.TvKill
