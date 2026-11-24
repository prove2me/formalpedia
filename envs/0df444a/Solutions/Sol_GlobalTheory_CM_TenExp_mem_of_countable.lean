-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.mem_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.859824+00:00
-- url     : https://prove2.me/submissions/a69ab2b6-34e3-4aea-946a-016d8e5ccfd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {Λ : Set V} (hΛ : Λ.Countable)
    (W : Submodule ℂ V) {v : V} (h : ∀ z : ℂ, ∃ l ∈ Λ, z • v - l ∈ W) : v ∈ W := by
  choose l hl hW using h
  have := hΛ.to_subtype
  obtain ⟨z, z', hne, e⟩ : ∃ z z' : ℂ, z ≠ z' ∧ l z = l z' := by
    by_contra hc
    push Not at hc
    have hi : Function.Injective fun z => (⟨l z, hl z⟩ : Λ) := fun z z' e => by
      by_contra h0
      exact hc z z' h0 (congrArg Subtype.val e)
    exact not_countable (α := ℝ) (hi.comp Complex.ofReal_injective).countable
  have h1 := W.sub_mem (hW z) (hW z')
  rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
  exact (W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1
end GlobalTheory.CM.TenExp
