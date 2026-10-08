-- Prove2me | solution 1 for MechanismDesign.VCG.ex_post_ir_iff_lowest_type
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:18:12.044601+00:00
-- url     : https://prove2.me/submissions/a31daf00-454e-487e-864e-2b37148d8e57

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

theorem ex_post_ir_iff_lowest_type_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : DSIC u M) (i : ι)
    (R : A → A → Prop)
    (θlow : Θ i) (hθlow : ∀ x : Θ i, x ≠ θlow → HigherType R (u i) x θlow)
    (alow : A) (halow : ∀ b : A, b ≠ alow → R b alow) :
    ExPostIRAgent u M i alow ↔
      ∀ θ : ∀ j, Θ j, u i (M.q (Function.update θ i θlow)) θlow
        - M.t i (Function.update θ i θlow) ≥ u i alow θlow := by
  constructor
  · intro h θ
    have := h (Function.update θ i θlow)
    simpa using this
  · intro h θ
    have hlow := h θ
    have hic := hM θ i θlow
    by_cases hx : θ i = θlow
    · have : Function.update θ i θlow = θ := by rw [← hx]; simp
      rw [this] at hlow
      show u i (M.q θ) (θ i) - M.t i θ ≥ u i alow (θ i)
      rw [hx]; exact hlow
    · have hH := hθlow (θ i) hx
      set b := M.q (Function.update θ i θlow)
      have key : u i b (θ i) - u i alow (θ i) ≥ u i b θlow - u i alow θlow := by
        by_cases hb : b = alow
        · rw [hb]; simp
        · have hR := halow b hb
          by_cases hs : R alow b
          · have := hH.2 b alow ⟨hR, hs⟩
            linarith [this.1, this.2]
          · have := hH.1 b alow ⟨hR, hs⟩
            linarith
      linarith

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism Θ A) (hM : DSIC u M) (i : ι)
    (R : A → A → Prop) (hR : IsCompleteOrder R) (h1d : OneDimensional R (u i))
    (θlow : Θ i) (hθlow : ∀ x : Θ i, x ≠ θlow → HigherType R (u i) x θlow)
    (alow : A) (halow : ∀ b : A, b ≠ alow → R b alow) :
    ExPostIRAgent u M i alow ↔
      ∀ θ : ∀ j, Θ j, u i (M.q (Function.update θ i θlow)) θlow
        - M.t i (Function.update θ i θlow) ≥ u i alow θlow := by
  exact ex_post_ir_iff_lowest_type_core u M hM i R θlow hθlow alow halow
