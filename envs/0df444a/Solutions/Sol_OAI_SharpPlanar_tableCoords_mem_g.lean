-- Prove2me | solution 1 for OAI.SharpPlanar.tableCoords_mem_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:13:34.114511+00:00
-- url     : https://prove2.me/submissions/609ad8e6-8e65-4f6b-a38d-ed34f3d4e0c4

import Mathlib
import Definitions.Def_OAIQ098G007
import Definitions.Def_OAIQ098G015
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_range_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar
open Numerical
lemma tableRaw_large {n : ℕ} (hn : 100<n) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> first | omega | rfl
lemma tableC_large (a : Bool) {n : ℕ} (hn : 100<n) : tableC a n=0 := by
  simp [tableC,tableRaw_large hn,show n≠0 by omega]
lemma tableD_large (a : Bool) {n : ℕ} (hn : 100<n) : tableD a n=0 := by
  simp [tableD,tableRaw_large hn,show n≠0 by omega]
lemma tableCoords_mem_g_oai (a : Bool) : Memℓp (tableCoords a) 1 := by
  classical
  apply memℓp_gen
  have hs : (Function.support (fun ni => |tableCoords a ni|)).Finite := by
    apply (Set.finite_range finiteIndex).subset
    intro ni hni
    change (∃ i, finiteIndex i=ni)
    have hindex : (∃ i, finiteIndex i=ni) ↔ ni.1.val≤100 := by
      rcases ni with ⟨n,d⟩
      exact finiteIndex_range_g n d
    rw [hindex]
    by_contra hn
    have hn' : 100<ni.1.val := by omega
    have hz : tableCoords a ni=0 := by
      simp [tableCoords,tableD_large a hn',tableC_large a hn']
    exact hni (by simp [hz])
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using summable_of_hasFiniteSupport hs
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableCoords_mem_g_oai := @OAI.SharpPlanar.tableCoords_mem_g_oai
