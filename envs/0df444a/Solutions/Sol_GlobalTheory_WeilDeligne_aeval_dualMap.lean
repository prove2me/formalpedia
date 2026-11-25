-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.aeval_dualMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:57:37.328938+00:00
-- url     : https://prove2.me/submissions/ac967b80-20b6-49be-bd7d-19abcb4bd2ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (f : End ℂ V) (p : ℂ[X]) :
    aeval (f.dualMap : End ℂ (Dual ℂ V)) p = (aeval f p : End ℂ V).dualMap := by
  have hp : ∀ n : ℕ, (f.dualMap : End ℂ (Dual ℂ V)) ^ n = (f ^ n : End ℂ V).dualMap := by
    intro n
    induction n with
    | zero => ext; simp
    | succ n ih => rw [pow_succ, ih, pow_succ']; ext; simp
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]; ext; simp
  | monomial n a => rw [aeval_monomial, aeval_monomial, hp]; ext; simp
end GlobalTheory.WeilDeligne
