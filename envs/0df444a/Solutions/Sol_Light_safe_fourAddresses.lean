-- Prove2me | solution 1 for Light.safe_fourAddresses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:59.878566+00:00
-- url     : https://prove2.me/submissions/60613fed-ac32-458f-b976-066195569104

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_WordRam_Bounded_abs_le
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {c : ℕ} (hc : c ≤ 4) {n : ℕ} {lim : Limits} {σ : State}
    (h3 : σ.loc 3 = ((n * n : ℕ) : ℤ)) (hw : ((8 * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k c *' v 3], e.Safe lim σ := by
  have hnn : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have hcn : (c : ℤ) * ((n : ℤ) * n) ≤ 4 * ((n : ℤ) * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hnn
  have hcn0 : (0 : ℤ) ≤ (c : ℤ) * ((n : ℤ) * n) := by positivity
  have hc' : (c : ℤ) ≤ 4 := by exact_mod_cast hc
  push_cast at hw h3
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  simp only [Expr.Safe, Expr.val, Op.eval, h3, true_and, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩,
    ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩,
    by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩
end Light
