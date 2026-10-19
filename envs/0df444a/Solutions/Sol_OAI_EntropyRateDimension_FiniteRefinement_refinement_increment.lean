-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteRefinement.refinement_increment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:10:39.763116+00:00
-- url     : https://prove2.me/submissions/48b108dc-4685-4ac9-8975-cb1d31ee8550

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]
theorem h41n_oe_inj {α' : Type*} {β' : Type*} {γ' : Type*} [DecidableEq β'] [DecidableEq γ']
    (s : Finset α') (p : α' → ℝ) (f : α' → β') (φ : β' → γ') (hφ : Function.Injective φ) :
    FiniteEntropy.observableEntropy s p (φ ∘ f) = FiniteEntropy.observableEntropy s p f := by
  rw [FiniteEntropy.observableEntropy_comp]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  rw [Finset.sum_image (fun x _ y _ h => hφ h)]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  unfold FiniteEntropy.mass
  rw [Finset.sum_eq_single_of_mem (s := (s.image f).filter (fun b' => φ b' = φ b)) b
    (Finset.mem_filter.mpr ⟨hb, rfl⟩)]
  intro b' hb' hne
  exact absurd (hφ (Finset.mem_filter.mp hb').2) hne

theorem solution (p : α → ℝ) (v : α → ℝ) (g : α → List ℤ)
    (hp : ∀ a, 0 ≤ p a) (k : ℕ) (δ : ℝ) (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)) :: g (x i)) (fun x => ∑ i, v (x i)) =
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) (fun x => ∑ i, v (x i)) +
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) := by
  unfold conditionalEntropy
  have hinj : Function.Injective
      (fun q : (Fin k → ℤ) × (ℝ × (Fin k → List ℤ)) => ((fun i => q.1 i :: q.2.2 i), q.2.1)) := by
    rintro ⟨c, r, l⟩ ⟨c', r', l'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hc : ∀ i, c i = c' i ∧ l i = l' i := fun i => List.cons.inj (congrFun h1 i)
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => (hc i).1, h2, funext fun i => (hc i).2⟩
  have e1 := h41n_oe_inj Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
    (fun x => ((fun i => RandomGrid.cell δ u (v (x i))), (∑ i, v (x i), fun i => g (x i)))) _ hinj
  have e2 := h41n_oe_inj Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
    (fun x => (∑ i, v (x i), fun i => g (x i))) Prod.swap Prod.swap_injective
  simp only [Function.comp_def, Prod.swap_prod_mk] at e1 e2
  rw [e1, e2]
  ring

