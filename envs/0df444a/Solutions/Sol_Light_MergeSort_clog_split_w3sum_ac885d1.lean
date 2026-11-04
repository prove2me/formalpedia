-- Prove2me | solution 1 for Light.MergeSort.clog_split_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:29.368448+00:00
-- url     : https://prove2.me/submissions/1a8b9fed-dbd8-4db9-af14-045a41f4f5bb

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program}
open Light.MergeSort
namespace Light.MergeSort
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
  have h2 : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hh : (n + 1) / 2 ≤ n := by omega
  rw [h1]
  generalize (n + 1) / 2 = h at *
  generalize Nat.clog 2 h = c at *
  have a1 : (n - h) * Nat.clog 2 (n - h) ≤ (n - h) * c := Nat.mul_le_mul_left _ h2
  have a2 : h * c + (n - h) * c = n * c := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have a3 : n * (c + 1) = n * c + n := by ring
  omega
end Light.MergeSort
