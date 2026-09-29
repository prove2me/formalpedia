-- Prove2me | solution 1 for MeasureTheory.prod_real_apply_singleton
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:45:47.934569+00:00
-- url     : https://prove2.me/submissions/a4760202-a4c5-494b-aece-f57b315e17de

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Entropy.Mathlib.MeasureProd =====
section
/-
Copyright (c) 2023 The Polynomial Freiman–Ruzsa (PFR) project contributors.
Released under the Apache License, Version 2.0; see the full license text in
`Salt/Entropy/LICENSE-PFR-Apache-2.0`.

Derivative work notice. This file is adapted from the Polynomial Freiman–Ruzsa
(PFR) project, upstream file `PFR/Mathlib/MeasureTheory/Measure/Prod.lean`, at
commit a177b2e4abe4b31c8024b9afebe646bf6bb8f91b (upstream toolchain
`leanprover/lean4:v4.33.0-rc1`).

Original authors: Terence Tao and the PFR project contributors.

Modifications for Salt (ported to mathlib v4.32.0-rc1, toolchain
`leanprover/lean4:v4.32.0-rc1`):
- Converted the PFR module-system header (`module`, `public import
  Mathlib.MeasureTheory.Measure.Prod`, `public section`) to a plain
  `import Mathlib`.
- All declarations, names, and proof bodies are otherwise verbatim from upstream.
-/

open Function
open scoped ENNReal NNReal

namespace MeasureTheory.Measure
variable {Ω α β γ : Type*} [MeasurableSpace Ω]
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}

/-- The law of $(X, Z)$ is the image of the law of $(Z,X)$. -/
lemma map_prod_comap_swap (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  ext s hs
  rw [Measure.map_apply (hZ.prodMk hX) hs, Measure.comap_apply _ Prod.swap_injective _ _ hs]
  · rw [Measure.map_apply (hX.prodMk hZ)]
    · congr!
      ext ω
      simp only [Set.image_swap_eq_preimage_swap, Set.mem_preimage, Prod.swap_prod_mk]
    · exact MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' hs
  · exact fun t ht ↦ MeasurableEquiv.prodComm.measurableEmbedding.measurableSet_image' ht

lemma prod_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν) {x} = μ {x.1} * ν {x.2} := by
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Measure.prod_prod]

lemma prod_real_apply_singleton {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  simp [Measure.real, prod_apply_singleton]

lemma prod_of_full_measure_finset {μ : Measure α} {ν : Measure β} [SigmaFinite ν]
    {A : Finset α} {B : Finset β} (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) :
    (μ.prod ν) (A ×ˢ B : Finset (α × β))ᶜ = 0 := by
  have : (↑(A ×ˢ B) : Set (α × β))ᶜ = ((A : Set α)ᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ (B : Set β)ᶜ) := by
    ext ⟨s, t⟩; simp; tauto
  rw [this]
  simp [hA, hB]

end MeasureTheory.Measure

open MeasureTheory

set_option linter.flexible false in
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [IsZeroOrProbabilityMeasure μ] {ν : Measure β} [IsZeroOrProbabilityMeasure ν] :
    IsZeroOrProbabilityMeasure (μ.prod ν) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp; infer_instance
  rcases eq_zero_or_isProbabilityMeasure ν with rfl | hν
  · simp; infer_instance
  infer_instance

end




section
open MeasureTheory MeasureTheory.Measure
open Function
open scoped ENNReal NNReal
variable {Ω α β γ : Type*} [MeasurableSpace Ω]

theorem solution {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [SigmaFinite ν] (x : α × β) :
    (μ.prod ν).real {x} = μ.real {x.1} * ν.real {x.2} := by
  apply MeasureTheory.Measure.prod_real_apply_singleton <;> assumption

end

