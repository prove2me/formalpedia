-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.RedInv.finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:28:09.289987+00:00
-- url     : https://prove2.me/submissions/843db730-676c-42c7-9f5c-7393daa811a3

module
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorModel
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_MinorClosed
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_preserves
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_fix
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_RIn_symm
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_dartSymm_apply
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_removeFromCycle_apply_self
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_restrict_adj
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_sameCycle_removeFromCycle
attribute [local simp] LeanPool.K5MinorFreeChoosability.dartSymm_apply
attribute [local simp] LeanPool.K5MinorFreeChoosability.restrict_adj



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable (M : MinorModel G H) (inK : G.Dart → Prop)
variable {M inK}
variable [DecidableEq V]
namespace LeanPool.K5MinorFreeChoosability
namespace RedInv
theorem _root_.solution {A : Finset G.Dart} {σ α σ₁ : Perm G.Dart} {r r' : V → V}
    (I : RedInv M inK A σ α r) {z : G.Dart} (hzA : z ∈ A) (hzK : ¬ inK z)
    (hKsymm : ∀ z, inK z → inK z.symm)
    (P1 : ∀ u, u ∉ A → σ₁ u = u) (P2 : ∀ u, r' (σ₁ u).fst = r' u.fst)
    (P3 : ∀ u ∈ A, ∀ v ∈ A, u ≠ z → u ≠ z.symm → v ≠ z → v ≠ z.symm →
      r' u.fst = r' v.fst → SameCycle σ₁ u v)
    (P4 : ∀ u v, r' u = r' v → M.SameBranch u v)
    (P5 : ∀ u, (u ∉ A ∨ u = z ∨ u = z.symm) → M.Internal u → r' u.fst = r' u.snd) :
    RedInv M inK ((A.erase z).erase z.symm)
      (removeFromCycle (removeFromCycle σ₁ z) z.symm) (α * swap z z.symm) r' := by
  have hzz : z ≠ z.symm := (SimpleGraph.Dart.symm_ne z).symm
  have hz'A : z.symm ∈ A := I.symm_mem z hzA
  have hmem : ∀ u, u ∈ (A.erase z).erase z.symm ↔ u ≠ z.symm ∧ u ≠ z ∧ u ∈ A := by
    intro u; simp [Finset.mem_erase]
  have hz'K : ¬ inK z.symm := fun h => hzK (by simpa using hKsymm _ h)
  refine ⟨?_, ?_, ?_, ?_, ?_, P4, ?_, ?_⟩
  · intro u hu
    rw [hmem] at hu
    constructor
    · by_cases h1 : u = z.symm
      · rw [h1, removeFromCycle_apply_self]
      by_cases h2 : u = z
      · rw [h2]
        exact removeFromCycle_fix (removeFromCycle_apply_self _ _) hzz
      have h3 : u ∉ A := by tauto
      have h4 : σ₁ u = u := P1 u h3
      exact removeFromCycle_fix (removeFromCycle_fix h4 h2) h1
    · simp only [Perm.mul_apply]
      by_cases h1 : u = z.symm
      · rw [h1, swap_apply_right, I.α_eq z hzA]
      by_cases h2 : u = z
      · rw [h2, swap_apply_left, I.α_eq _ hz'A, SimpleGraph.Dart.symm_symm]
      have h3 : u ∉ A := by tauto
      rw [swap_apply_of_ne_of_ne h2 h1]
      exact (I.fix_out u h3).2
  · intro u hu
    rw [hmem] at hu ⊢
    refine ⟨fun h => hu.2.1 ?_, fun h => hu.1 ?_, I.symm_mem u hu.2.2⟩
    · simpa using congrArg SimpleGraph.Dart.symm h
    · simpa using congrArg SimpleGraph.Dart.symm h
  · intro u hu
    rw [hmem] at hu
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hu.2.1 hu.1, I.α_eq u hu.2.2]
  · intro u
    exact removeFromCycle_preserves (fun d : G.Dart => r' d.fst)
      (removeFromCycle_preserves (fun d : G.Dart => r' d.fst) P2 z) z.symm u
  · intro u hu v hv huv
    rw [hmem] at hu hv
    exact sameCycle_removeFromCycle hu.1 hv.1
      (sameCycle_removeFromCycle hu.2.1 hv.2.1
        (P3 u hu.2.2 v hv.2.2 hu.2.1 hu.1 hv.2.1 hv.1 huv))
  · intro u hu hint
    rw [hmem] at hu
    exact P5 u (by tauto) hint
  · intro u hu
    rw [hmem]
    refine ⟨fun h => hz'K (h ▸ hu), fun h => hzK (h ▸ hu), I.K_sub u hu⟩
end RedInv
end LeanPool.K5MinorFreeChoosability
