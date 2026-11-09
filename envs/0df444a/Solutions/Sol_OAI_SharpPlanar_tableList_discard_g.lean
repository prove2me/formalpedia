-- Prove2me | solution 1 for OAI.SharpPlanar.tableList_discard_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:19.492239+00:00
-- url     : https://prove2.me/submissions/d058ad21-dea5-4d6a-b161-c3afc7fe5e37

import Mathlib
import Definitions.Def_OAIQ098G010
import Definitions.Def_OAIQ098G1673
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_injective_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_finiteIndex_range_g
import Theorems.Thm_OAI_SharpPlanar_finiteEmbedding_apply_g

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
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteProjection_apply (x : X) (k : Node × Bool) :
    finiteEmbedding e (finiteRestriction e he x) k = if ∃ i, e i=k then x k else 0 := by
  classical
  rw [finiteEmbedding_apply_g]
  split_ifs with h
  · obtain ⟨i,rfl⟩ := h
    simp only [he.eq_iff, finiteRestriction_apply]
    simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun hh => h ⟨i,hh⟩)]
end
end SharpPlanar

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
lemma tableList_apply (a : Bool) (ni : Node×Bool) :
    tableList a ni = if ni.2 then (tableD a ni.1.val:ℝ) else (tableC a ni.1.val:ℝ) := rfl
lemma tableList_discard_g_oai (a : Bool) : tableList a-IF (RF (tableList a))=0 := by
  apply lp.ext; funext ni
  have hh := finiteProjection_apply finiteIndex finiteIndex_injective_g (tableList a) ni
  change IF (RF (tableList a)) ni = _ at hh
  rw [lp.coeFn_sub,Pi.sub_apply,hh]
  rcases ni with ⟨n,d⟩
  simp only [finiteIndex_range_g]
  split
  · simp
  · have hn : 100<n.val := by omega
    simp [tableList_apply,tableD_large a hn,tableC_large a hn]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableList_discard_g_oai := @OAI.SharpPlanar.tableList_discard_g_oai
