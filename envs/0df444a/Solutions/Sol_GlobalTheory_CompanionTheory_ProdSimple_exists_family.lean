-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdSimple.exists_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:53.69828+00:00
-- url     : https://prove2.me/submissions/07bc0086-e156-499d-ae0f-1ac7b2f4b2b9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_exists_irr
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_psi_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple
variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.ProdSimple
theorem _root_.solution (ρ : Representation ℂ (∀ c, L c) W) (v : W) (hv : v ≠ 0) :
    ∃ x : ∀ c, MonoidAlgebra ℂ (L c),
      (∀ c, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
  have key : ∀ S : Finset (Fin s), ∃ x : ∀ c, MonoidAlgebra ℂ (L c), (∀ c, c ∉ S → x c = 1) ∧
      (∀ c ∈ S, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => 1, fun _ _ => rfl, by simp, by rwa [psi_one]⟩
    | insert c S hc ih =>
      obtain ⟨x, h1, h2, h3⟩ := ih
      have hT : (psi ρ v).toLinearMap x c 1 ≠ 0 := by
        rw [MultilinearMap.toLinearMap_apply, ← h1 c hc, Function.update_eq_self]
        exact h3
      obtain ⟨N, h, hirr, n, hn, hTn⟩ := exists_irr _ hT
      refine ⟨Function.update x c n, fun c' hc' => ?_, fun c' hc' => ?_, ?_⟩
      · rw [Finset.mem_insert, not_or] at hc'
        rw [Function.update_of_ne hc'.1]
        exact h1 c' hc'.2
      · by_cases hcc : c' = c
        · subst hcc
          exact ⟨N, h, hirr, by rwa [Function.update_self]⟩
        · obtain ⟨N', h', hirr', hm⟩ := h2 c' ((Finset.mem_insert.mp hc').resolve_left hcc)
          exact ⟨N', h', hirr', by rwa [Function.update_of_ne hcc]⟩
      · simpa [MultilinearMap.toLinearMap_apply] using hTn
  obtain ⟨x, -, h2, h3⟩ := key Finset.univ
  exact ⟨x, fun c => h2 c (Finset.mem_univ c), h3⟩
end GlobalTheory.CompanionTheory.ProdSimple
