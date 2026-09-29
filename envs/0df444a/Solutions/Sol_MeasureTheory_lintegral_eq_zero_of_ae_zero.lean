-- Prove2me | solution 1 for MeasureTheory.lintegral_eq_zero_of_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T19:31:40.63134+00:00
-- url     : https://prove2.me/submissions/6c0c5d03-7250-471b-9e0c-de958bf84947

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Entropy.Mathlib.LebesgueBasic =====
section
/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`,
at commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.MeasureTheory.Integral.Lebesgue.Basic`, `public section`) to a plain
  `import Mathlib`.
- Both lemmas are genuinely absent from mathlib v4.32.0-rc1; statements and
  proofs are ported verbatim.  This residue is in the W1-3 lane's closure:
  upstream `PFR/Mathlib/Probability/Kernel/Disintegration.lean` imports it.
-/

/-!
# TODO

Rename `setLIntegral_congr` to `setLIntegral_congr_set`
-/

open ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

lemma lintegral_eq_zero_of_ae_zero {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0)
    (hmes : MeasurableSet s) : ∫⁻ x, f x ∂μ = 0 := by
  rw [← lintegral_add_compl f hmes, setLIntegral_measure_zero sᶜ f hs,
    setLIntegral_congr_fun (f := f) (g := fun _ ↦ 0) hmes hf]
  simp

lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

end MeasureTheory

end




section
open MeasureTheory
open scoped ENNReal

theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ≥0∞} (hs : μ sᶜ = 0) (hf : ∀ x ∈ s, f x = 0) (hmes : MeasurableSet s) :
    ∫⁻ x, f x ∂μ = 0 := by
  apply MeasureTheory.lintegral_eq_zero_of_ae_zero <;> assumption

end
