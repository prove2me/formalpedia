-- Prove2me | solution 1 for GlobalTheory.exists_common_eigenvector_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:04.31151+00:00
-- url     : https://prove2.me/submissions/030354d4-306d-4821-9cf2-a406078709be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V ι : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : ι → V →ₗ[K] V)
    (hT : ∀ i j v, T i (T j v) = T j (T i v)) (W : Submodule K V) (hW : W ≠ ⊥)
    (hs : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ l : K, T i v = l • v := by
  obtain ⟨U, ⟨hUW, hU0, hUs⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule K V)).has_min
      {U | U ≤ W ∧ U ≠ ⊥ ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, le_rfl, hW, hs⟩
  obtain ⟨v, hvU, hv0⟩ := (Submodule.ne_bot_iff U).1 hU0
  refine ⟨v, hUW hvU, hv0, fun i => ?_⟩
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((T i).restrict (hUs i))
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw1 : T i w = l • (w : V) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  let U' : Submodule K V := U ⊓ LinearMap.ker (T i - l • LinearMap.id)
  have hmem : ∀ x, x ∈ U' ↔ x ∈ U ∧ T i x = l • x := by
    intro x
    simp [U', sub_eq_zero]
  have hU' : U' = U := by
    by_contra hne
    refine hmin U' ⟨le_trans inf_le_left hUW, ?_, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
    · exact (Submodule.ne_bot_iff _).2 ⟨w, (hmem _).2 ⟨w.2, hw1⟩, hw0⟩
    · intro j x hx
      obtain ⟨h1, h2⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨hUs j x h1, by rw [hT, h2, map_smul]⟩
  exact ⟨l, ((hmem v).1 (hU'.symm ▸ hvU)).2⟩
end GlobalTheory
