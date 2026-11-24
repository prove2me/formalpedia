-- Prove2me | solution 1 for GlobalTheory.AbsDec.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:00.61344+00:00
-- url     : https://prove2.me/submissions/cdcba920-123c-4041-aca8-c79036ee5df0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedVectorsIrreducibleSubrepDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.AbsDec
namespace GlobalTheory.AbsDec
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (ht : iSupIndep t) :
    ∃ T : ι → V →ₗ[ℂ] V, (∀ i v, T i v ∈ t i) ∧
      (∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (⨆ i, t i)
  have hcompl : ∀ i, IsCompl (t i) ((⨆ (j) (_ : j ≠ i), t j) ⊔ C) := by
    intro i
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨q, hq, c, hc, rfl⟩ := Submodule.mem_sup.1 hx'
      have hcQ : c ∈ ⨆ i, t i := by
        have h1 : q + c ∈ ⨆ i, t i := Submodule.mem_iSup_of_mem i hx
        have h2 : q ∈ ⨆ i, t i :=
          (iSup₂_le fun j _ => le_iSup t j : (⨆ (j) (_ : j ≠ i), t j) ≤ ⨆ i, t i) hq
        simpa using Submodule.sub_mem _ h1 h2
      have hc0 : c = 0 := (Submodule.disjoint_def.1 hC.disjoint) c hcQ hc
      subst hc0
      rw [add_zero] at hx ⊢
      exact (Submodule.disjoint_def.1 ((iSupIndep_def.1 ht) i)) q hx hq
    · rw [codisjoint_iff, eq_top_iff, ← hC.sup_eq_top]
      refine sup_le (iSup_le fun j => ?_) (le_sup_of_le_right le_sup_right)
      by_cases h : j = i
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le j h le_rfl))
  refine ⟨fun i => (t i).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ (hcompl i),
    fun i v => ?_, fun i j v hv => ?_⟩
  · simp
  · split_ifs with h
    · subst h
      exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hcompl i) ⟨v, hv⟩)
    · have hv' : v ∈ (⨆ (k) (_ : k ≠ i), t k) ⊔ C :=
        Submodule.mem_sup_left (Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem (Ne.symm h) hv))
      have := Submodule.linearProjOfIsCompl_apply_right (hcompl i) ⟨v, hv'⟩
      exact congrArg Subtype.val this
end GlobalTheory.AbsDec
