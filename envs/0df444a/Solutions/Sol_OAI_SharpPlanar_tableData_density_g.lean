-- Prove2me | solution 1 for OAI.SharpPlanar.tableData_density_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:43:23.049921+00:00
-- url     : https://prove2.me/submissions/52c5ae94-aafe-4e34-b53d-d4f2645de0a8

import Mathlib
import Definitions.Def_OAIQ098G1681
import Definitions.Def_OAIQ098G1691
import Theorems.Thm_OAI_SharpPlanar_tableC_offnode_g
import Theorems.Thm_OAI_SharpPlanar_tableD_offnode_g

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cardinal densities and finite coefficient families

The finite coefficient densities agree with the cardinal densities of the corresponding data.
-/

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma tableData_density_g_oai (a : Bool) (j : ℕ) (t : ℝ) :
    density (tableData a) j t = tableDensity a j t := by
  classical
  let term (n : ℕ) : ℂ := ((tableC a n:ℝ):ℂ)*u n j t+((tableD a n:ℝ):ℂ)*v n j t
  have hz : ∀ n ∉ Finset.range 101, term n=0 := by
    intro n hn
    have hn' : 100<n := by have hh := Finset.mem_range.not.mp hn; omega
    simp [term,tableC_large a hn',tableD_large a hn']
  have ht : (∑' n : Node, term n.val)=∑' n : ℕ, if n=0 then 0 else term n := by
    have he : (∑' n : Node, term n.val) =
        ∑' n : Node, (if n.val=0 then 0 else term n.val) := by
      apply tsum_congr
      intro n
      rw [ite_eq_right (Nat.ne_of_gt n.property.1)]
    rw [he]
    apply tsum_subtype_eq_of_support_subset (s := {n : ℕ | 0<n ∧ n%12∈residues}) (f := fun n => if n=0 then 0 else term n)
    intro n hn
    by_cases hn0 : n=0
    · subst n; simp at hn
    have hnp : 0<n := Nat.pos_of_ne_zero hn0
    refine ⟨hnp,?_⟩
    by_contra hh
    exact hn (by simp [hn0,term,tableC_offnode_g a hh,tableD_offnode_g a hh])
  have he : ∑' n : ℕ, (if n=0 then 0 else term n) =
      ∑ n ∈ (Finset.range 101).erase 0,term n := by
    rw [tsum_eq_sum (s := (Finset.range 101).erase 0) (by
      intro n hn
      by_cases hn0 : n=0
      · simp [hn0]
      · rw [ite_eq_right hn0]
        apply hz
        simpa only [Finset.mem_erase,hn0,ne_eq,not_false_eq_true,true_and] using hn)]
    apply Finset.sum_congr rfl
    intro n hn
    exact ite_eq_right (Finset.ne_of_mem_erase hn)
  change term 0+(∑' n : Node,term n.val)=_
  rw [ht,he,add_comm,Finset.sum_erase_add _ _ (by simp)]
  rfl
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableData_density_g_oai := @OAI.SharpPlanar.tableData_density_g_oai
