-- Prove2me | solution 1 for GlobalTheory.RedBound.prod_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:07.272971+00:00
-- url     : https://prove2.me/submissions/58ceac0b-544a-40e7-a3ec-18c44d39465d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
import Theorems.Thm_GlobalTheory_RedBound_le_of_le_idx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound
namespace GlobalTheory.RedBound
theorem _root_.solution {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {p q r s : Fin N} (hr : p ≤ r) (hs : q ≤ s) : a p * a q ≤ Cm ^ 2 * (a r * a s) := by
  have har := le_of_le_idx hS h1 hC hr
  have has := le_of_le_idx hS h1 hC hs
  have h0 : 0 ≤ Cm * a r := mul_nonneg (by linarith) (hS.pos r).le
  calc a p * a q ≤ (Cm * a r) * (Cm * a s) := mul_le_mul har has (hS.pos q).le h0
    _ = Cm ^ 2 * (a r * a s) := by ring
end GlobalTheory.RedBound
