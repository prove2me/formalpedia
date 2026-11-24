-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.hasFiniteLength_jacU_relabel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:10.438136+00:00
-- url     : https://prove2.me/submissions/d3703a44-3c8b-4c67-9b72-d45232876b32

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_JacquetBlocks_mem_unipRad_iff_blk
import Theorems.Thm_GlobalTheory_JacquetBlocks_leviEmb_apply_of_blk_ne
import Theorems.Thm_GlobalTheory_JacquetBlocks_leviEmb_leviProj_of_blk
import Theorems.Thm_GlobalTheory_JacquetBlocks_leviProj_eq_of_coe_eq
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_jacU_of_transport
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacquetBlocks
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.JacquetBlocks
theorem _root_.solution (e : (Σ a, m a) ≃ n) (s : (Σ b, m' b) ≃ (Σ a, m a))
    (f : β → α) (hf : StrictMono f) (hs : ∀ x, (s x).1 = f x.1) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU (s.trans e) π)) : HasFiniteLength (jacU e π) := by
  set e₁ := s.trans e
  have hblk : ∀ i, blk e i = f (blk e₁ i) := fun i => by
    have := hs (s.symm (e.symm i))
    rw [Equiv.apply_symm_apply] at this
    exact this
  have hlt : ∀ i j, blk e i < blk e j ↔ blk e₁ i < blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.lt_iff_lt]
  have heq : ∀ i j, blk e i = blk e j ↔ blk e₁ i = blk e₁ j := fun i j => by
    rw [hblk, hblk, hf.injective.eq_iff]
  have hpar : ∀ g : GL n k, g ∈ parab k e ↔ g ∈ parab k e₁ := fun g => by
    rw [mem_parab, mem_parab]
    exact forall_congr' fun i => forall_congr' fun j => by rw [hlt]
  let Ψ : Levi k m' →* Levi k m := (leviProj k e).comp ((leviEmb k e₁).codRestrict (parab k e)
    fun g => (hpar _).2 (leviEmb_mem_parab k e₁ g))
  have hL : ∀ g, leviEmb k e₁ g = leviEmb k e (Ψ g) := fun g => by
    refine (leviEmb_leviProj_of_blk (R := k) e ⟨leviEmb k e₁ g, (hpar _).2 (leviEmb_mem_parab k e₁ g)⟩
      fun i j hij => ?_).symm
    exact leviEmb_apply_of_blk_ne e₁ g fun h' => hij ((heq i j).2 h')
  have hΨ : Function.Surjective Ψ := by
    intro g
    refine ⟨leviProj k e₁ ⟨leviEmb k e g, (hpar _).1 (leviEmb_mem_parab k e g)⟩, ?_⟩
    refine leviProj_eq_of_coe_eq (R := k) e _ g ?_
    exact leviEmb_leviProj_of_blk (R := k) e₁ _ fun i j hij =>
      leviEmb_apply_of_blk_ne e g fun h' => hij ((heq i j).1 h')
  refine hasFiniteLength_jacU_of_transport e e₁ (MonoidHom.id _) Ψ hΨ (fun u hu => ?_)
    (fun g => hL g) π h
  rw [mem_unipRad_iff_blk] at hu ⊢
  exact ⟨(hpar _).2 hu.1, fun i j hij => hu.2 i j ((heq i j).1 hij)⟩
end GlobalTheory.JacquetBlocks
