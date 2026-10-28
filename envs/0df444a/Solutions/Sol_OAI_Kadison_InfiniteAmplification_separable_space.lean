-- Prove2me | solution 1 for OAI.Kadison.InfiniteAmplification.separable_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:16:34.087986+00:00
-- url     : https://prove2.me/submissions/c9f515ac-c9e5-4ea7-827c-12c7a6db7134

import Mathlib
import Definitions.Def_OAIQ039C006

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison.InfiniteAmplification

variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem separable_space_oai : TopologicalSpace.SeparableSpace (Space ι H) := by
  classical
  obtain ⟨x,hx⟩ := TopologicalSpace.exists_dense_seq H
  let v : ι × ℕ → Space ι H := fun p => lp.single 2 p.1 (x p.2)
  let K : Submodule ℂ (Space ι H) := Submodule.span ℂ (Set.range v)
  have hK : K.topologicalClosure=⊤ := by
    apply Submodule.topologicalClosure_eq_top_iff.mpr
    apply le_antisymm ?_ bot_le
    intro f hf
    have hv (i : ι) (n : ℕ) : inner ℂ (x n) (f i)=0 := by
      have hh := (K.mem_orthogonal f).mp hf _ (Submodule.subset_span (Set.mem_range_self (i,n)))
      exact (lp.inner_single_left (𝕜:=ℂ) i (x n) f).symm.trans hh
    have hf0 : f=0 := by
      ext i
      exact hx.eq_of_inner_right ℂ (fun n => by simpa only [lp.coeFn_zero,Pi.zero_apply,inner_zero_right] using hv i n)
    simpa only [Submodule.mem_bot] using hf0
  have hs : TopologicalSpace.IsSeparable (K.topologicalClosure : Set (Space ι H)) :=
    ((Set.countable_range v).isSeparable.span (R:=ℂ)).closure
  rw [hK] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.InfiniteAmplification.separable_space_oai.{u_1, u_2} := @OAI.Kadison.InfiniteAmplification.separable_space_oai.{u_1, u_2}
