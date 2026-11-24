-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.unit_conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:19:50.445338+00:00
-- url     : https://prove2.me/submissions/49209a5c-ddef-4da7-aa4c-d94a1c4f83ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_starU_mul
import Theorems.Thm_GlobalTheory_JR_HermInv_mul_starU

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
theorem _root_.solution (g : Matrix.unitaryGroup (Fin r) E) (A : Matrix (Fin r) (Fin r) E) (k : ℕ) :
    (g.1 * A * star g.1) ^ k = g.1 * A ^ k * star g.1 := by
  induction k with
  | zero => simp [mul_starU g]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (star g.1) g.1, starU_mul g, one_mul]
end GlobalTheory.JR.HermInv
