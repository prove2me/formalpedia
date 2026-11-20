-- Prove2me | solution 1 for LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:08:24.587457+00:00
-- url     : https://prove2.me/submissions/cbe8f828-2d9a-40a6-b874-4753e3bca9ca

import Definitions.Def_LevyStochCalc_Martingale_SquareCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated square of a square-integrable martingale

For a square-integrable martingale `M` and an adapted integrable process `A`, the process
`M² − A` is a martingale as soon as the increments satisfy the set-level identity
`∫_B (M_t − M_s)² = ∫_B (A_t − A_s)` for every `s ≤ t` and every `B ∈ ℱ_s`: the cross term
`∫_B M_s M_t` equals `∫_B M_s²` by the martingale property, so the identity says exactly that
`∫_B (M_t² − A_t) = ∫_B (M_s² − A_s)`.
-/

open MeasureTheory Filter

namespace LevyStochCalc.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} [IsFiniteMeasure μ] {M A : ι → Ω → ℝ}



theorem _root_.solution (hM : Martingale M ℱ μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hA : StronglyAdapted ℱ A) (hAint : ∀ t, Integrable (A t) μ)
    (h : ∀ s t, s ≤ t → ∀ B, MeasurableSet[ℱ s] B →
      ∫ ω in B, (M t ω - M s ω) ^ 2 ∂μ = ∫ ω in B, (A t ω - A s ω) ∂μ) :
    Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ := by
  have hadapt : StronglyAdapted ℱ (fun t ω => (M t ω) ^ 2 - A t ω) := fun t =>
    ((hM.stronglyAdapted t).pow 2).sub (hA t)
  refine ⟨hadapt, fun s t hst => ?_⟩
  have hint : ∀ u, Integrable (fun ω => (M u ω) ^ 2 - A u ω) μ := fun u =>
    (hM2 u).integrable_sq.sub (hAint u)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun B _ _ => (hint s).integrableOn) (fun B hB _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  have e1 := h s t hst B hB
  have e2 := setIntegral_increment_sq hM hM2 hst hB
  have hBm : MeasurableSet B := ℱ.le s B hB
  rw [integral_sub (hM2 s).integrable_sq.integrableOn (hAint s).integrableOn,
    integral_sub (hM2 t).integrable_sq.integrableOn (hAint t).integrableOn]
  rw [integral_sub (hAint t).integrableOn (hAint s).integrableOn] at e1
  linarith
