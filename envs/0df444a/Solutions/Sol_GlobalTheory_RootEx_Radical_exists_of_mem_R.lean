-- Prove2me | solution 1 for GlobalTheory.RootEx.Radical.exists_of_mem_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:34.16801+00:00
-- url     : https://prove2.me/submissions/5abf7fcd-43b9-4634-82e5-d534d4754800

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Theorems.Thm_GlobalTheory_RootEx_Radical_conj_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.Radical
theorem _root_.solution {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {r | ∃ x : GL n k, ∃ g ∈ N k n c p, r = embX c x * g}
      one_mem' := ⟨1, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, g, hg, rfl⟩ ⟨y, h, hh, rfl⟩
        refine ⟨x * y, _, mul_mem (conj_mem y⁻¹ hg) hh, ?_⟩
        rw [map_mul, map_inv]
        group
      inv_mem' := by
        rintro _ ⟨x, g, hg, rfl⟩
        refine ⟨x⁻¹, _, conj_mem x (inv_mem hg), ?_⟩
        rw [map_inv]
        group }
  have : R k n c p ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, 1, one_mem _, (mul_one _).symm⟩
    · intro g hg
      exact ⟨1, g, hg, by simp⟩
  exact this hr
end GlobalTheory.RootEx.Radical
