-- Prove2me | solution 1 for GlobalTheory.JacquetBlocks.hasFiniteLength_jacU_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:06.92789+00:00
-- url     : https://prove2.me/submissions/77d33f51-bb11-43ee-ae3b-db58a3a644e3

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InductionFiniteLength
import Theorems.Thm_GlobalTheory_JacquetBlocks_hasFiniteLength_jacU_of_transport
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad


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
theorem _root_.solution (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    obtain ⟨⟨a, x⟩, rfl⟩ := (e.trans ψ).surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := (e.trans ψ).surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, MonoidHom.id_apply]
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨a, y⟩) = (e.trans ψ) ⟨a, y⟩ from rfl, leviEmb_apply_same]
    · rw [leviEmb_apply_ne k e _ hab, show ψ (e ⟨a, x⟩) = (e.trans ψ) ⟨a, x⟩ from rfl,
        show ψ (e ⟨b, y⟩) = (e.trans ψ) ⟨b, y⟩ from rfl, leviEmb_apply_ne k _ _ hab]
end GlobalTheory.JacquetBlocks
