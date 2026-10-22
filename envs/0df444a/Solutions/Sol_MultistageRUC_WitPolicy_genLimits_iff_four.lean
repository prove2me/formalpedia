-- Prove2me | solution 1 for MultistageRUC.WitPolicy.genLimits_iff_four
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:59:22.902955+00:00
-- url     : https://prove2.me/submissions/2e201487-502c-4c39-b753-17bb9925c401

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

set_option autoImplicit false
open MultistageRUC.WitPolicy

theorem solution {Ng Nd T : ℕ}
    (pmin pmax : Fin Ng → ℝ) (x w W : Fin Ng → Fin T → ℝ)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin) (i : Fin Ng) (t : Fin T) :
    GenLimits pmin pmax x w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
      (pmin i * x i t ≤ w i t + W i t * totalLoad dmax t ∧
          w i t + W i t * totalLoad dmax t ≤ pmax i * x i t) ∧
        (pmin i * x i t ≤ w i t + W i t * totalLoad dmin t ∧
          w i t + W i t * totalLoad dmin t ≤ pmax i * x i t) := by
  simp only [GenLimits, witDispatch]
  constructor
  · intro h
    exact ⟨h dmax hmax.1, h dmin hmin.1⟩
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ d hd
    have h1 := hmax.2 d hd t
    have h2 := hmin.2 d hd t
    rcases le_total 0 (W i t) with hW | hW
    · have e1 := mul_le_mul_of_nonneg_left h1 hW
      have e2 := mul_le_mul_of_nonneg_left h2 hW
      constructor <;> linarith
    · have e1 := mul_le_mul_of_nonpos_left h1 hW
      have e2 := mul_le_mul_of_nonpos_left h2 hW
      constructor <;> linarith
