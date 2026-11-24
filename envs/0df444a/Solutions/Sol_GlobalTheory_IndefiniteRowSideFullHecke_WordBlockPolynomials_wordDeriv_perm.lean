-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials.wordDeriv_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:15.17748+00:00
-- url     : https://prove2.me/submissions/ad8942bc-f499-4dc0-955e-243779954556

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_WordBlockPolynomials_iteratedFDeriv_directions_comp_perm_of_analyticAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
theorem _root_.solution (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {l l' : List Λ} (h : l.Perm l') : wordDeriv dir l F p = wordDeriv dir l' F p := by
  have key : ∀ {l l' : List Λ}, l.Perm l' →
      ∃ e : Fin l.length ≃ Fin l'.length, ∀ j, l.get j = l'.get (e j) := by
    intro l l' h
    induction h with
    | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
    | cons x _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm), ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simpa using he j
    | swap x y l =>
      refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
      · simp
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
        simp
    | trans _ _ ih₁ ih₂ =>
      obtain ⟨e₁, h₁⟩ := ih₁
      obtain ⟨e₂, h₂⟩ := ih₂
      exact ⟨e₁.trans e₂, fun j => by rw [h₁, h₂]; rfl⟩
  obtain ⟨e, he⟩ := key h
  have hl := h.length_eq
  unfold wordDeriv
  have gen : ∀ (a b : ℕ) (_ : a = b) (u : Fin a → Λ) (v : Fin b → Λ) (e : Fin a ≃ Fin b),
      (∀ j, u j = v (e j)) → iteratedFDeriv ℂ a F p (fun j => dir (u j)) =
        iteratedFDeriv ℂ b F p (fun j => dir (v j)) := by
    intro a b hab u v e he
    subst hab
    exact iteratedFDeriv_directions_comp_perm_of_analyticAt dir hF u v e (funext he)
  exact gen _ _ hl _ _ e he
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
