-- Prove2me | solution 1 for NashVecOpt.SharedConstraint.order_characterization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:21:49.034336+00:00
-- url     : https://prove2.me/submissions/56cbfa3f-d0b5-4187-8cef-dce357617660

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace Aux_NVO_order
open NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

lemma memI (i : ι) (z : (∀ j, E j) × (ι → ℝ)) :
    z ∈ coneI (E := E) i ↔ (∀ j, j ≠ i → z.1 j = 0) ∧ 0 ≤ z.2 i := by
  unfold coneI
  rw [Set.mem_prod, Set.mem_univ_pi, Set.mem_univ_pi]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · simpa [hj] using h1 j
    · simpa using h2 i
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · by_cases hj : j = i
      · simp [hj]
      · simpa [hj] using h1 j hj
    · by_cases hj : j = i
      · subst hj; simpa using h2
      · simp [hj]

end Aux_NVO_order

open NashVecOpt.SharedConstraint in
theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] (hN : 2 ≤ Fintype.card ι)
    (f : ι → (∀ j, E j) → ℝ) (x xbar : ∀ j, E j) :
    (∀ i, coneLE (coneI (E := E) i) (obj f xbar) (obj f x) ↔
      (∀ j, j ≠ i → x j = xbar j) ∧ f i xbar ≤ f i x) ∧
    (coneLE (orderCone (E := E)) (obj f xbar) (obj f x) ↔
      ∃ i, coneLE (coneI (E := E) i) (obj f xbar) (obj f x)) := by
  constructor
  · intro i
    unfold coneLE
    rw [Aux_NVO_order.memI]
    simp only [obj, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_eq_zero, sub_nonneg]
  · unfold coneLE
    exact exists_congr (fun i => (Aux_NVO_order.memI i _).symm)
