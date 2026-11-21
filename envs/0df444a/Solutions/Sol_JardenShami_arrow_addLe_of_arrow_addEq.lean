-- Prove2me | solution 1 for JardenShami.arrow_addLe_of_arrow_addEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:32.477921+00:00
-- url     : https://prove2.me/submissions/0c8adb19-6268-4118-9c34-f1b02f7765cf

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]
namespace JardenShami
theorem _root_.solution (κ : Cardinal.{v}) (F₁ F₂ : Set (Set X))
    (h : Arrow F₁ F₂ (addEq κ)) : Arrow F₁ F₂ (fun _ D C => IsAdditive C ∧ #D ≤ κ) := by
  classical
  rintro S hS D C ⟨⟨s₀, hs₀⟩, hD⟩
  obtain ⟨e⟩ : Nonempty (D ↪ κ.out) := by
    rw [← Cardinal.le_def, Cardinal.mk_out]
    exact hD
  let C' : Coloring S κ.out := fun p => e (C p)
  have hC'add : IsAdditive C' := by
    by_cases hne : Nonempty D
    · refine ⟨fun xy => e (s₀ (Function.invFun e xy.1, Function.invFun e xy.2)), ?_⟩
      intro a b c hab hbc
      change e (C.color a c (hab.trans hbc)) = e (s₀ (Function.invFun e (e (C.color a b hab)),
        Function.invFun e (e (C.color b c hbc))))
      rw [Function.leftInverse_invFun e.injective, Function.leftInverse_invFun e.injective,
        hs₀ a b c hab hbc]
    · exact ⟨Prod.fst, fun a b _ hab _ => absurd ⟨C.color a b hab⟩ hne⟩
  obtain ⟨E, hEF, hEhom⟩ := h S hS κ.out C' ⟨hC'add, Cardinal.mk_out κ⟩
  exact ⟨E, hEF, fun p q hp hq => e.injective (hEhom p q hp hq)⟩
end JardenShami
