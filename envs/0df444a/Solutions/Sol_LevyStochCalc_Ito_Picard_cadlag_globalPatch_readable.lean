-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.cadlag_globalPatch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:25.932009+00:00
-- url     : https://prove2.me/submissions/06a2f0b9-c0ab-4504-bb40-c3733dee0f26

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
section Glue
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map is almost surely càdlàg on the SDE time domain. -/
theorem solution {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      LevyStochCalc.Ito.Picard.globalPatch Y t ω = Y k t ω)
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => Y k s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => LevyStochCalc.Ito.Picard.globalPatch Y s ω) (nhdsWithin t (Set.Ioi t))
          (nhds (LevyStochCalc.Ito.Picard.globalPatch Y t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => LevyStochCalc.Ito.Picard.globalPatch Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ) := by
  filter_upwards [hagree, MeasureTheory.ae_all_iff.mpr hYcad] with ω hω hcad
  intro t ht
  set k := ⌈t⌉₊ + 1 with hk
  have htk : t < (k : ℝ) := by
    have := Nat.le_ceil t
    push_cast [hk]
    linarith
  have hpatch : ∀ s : ℝ, 0 ≤ s → s ≤ (k : ℝ) + 1 → LevyStochCalc.Ito.Picard.globalPatch Y s ω = Y k s ω :=
    fun s hs0 hs1 => hω k s ⟨hs0, hs1⟩
  constructor
  · have hev : ∀ᶠ s in nhdsWithin t (Set.Ioi t), LevyStochCalc.Ito.Picard.globalPatch Y s ω = Y k s ω := by
      have hmem : Set.Iio ((k : ℝ) + 1) ∈ nhdsWithin t (Set.Ioi t) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [hmem, self_mem_nhdsWithin] with s hs hs'
      exact hpatch s (ht.trans (le_of_lt hs')) (le_of_lt hs)
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
    rw [hpatch t ht (by linarith)]
    exact (hcad k t).1
  · intro i
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · obtain ⟨ℓ, hℓ⟩ := (hcad 0 t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Iio t ∈ nhdsWithin t (Set.Iio t) := self_mem_nhdsWithin
      filter_upwards [hmem] with s hs
      have : ⌈s⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by simp only [Set.mem_Iio] at hs; linarith [ht0])
      simp [LevyStochCalc.Ito.Picard.globalPatch, this]
    · obtain ⟨ℓ, hℓ⟩ := (hcad k t).2 i
      refine ⟨ℓ, Filter.Tendsto.congr' ?_ hℓ⟩
      have hmem : Set.Ioo (0 : ℝ) t ∈ nhdsWithin t (Set.Iio t) := by
        refine Filter.inter_mem ?_ self_mem_nhdsWithin
        exact nhdsWithin_le_nhds (Ioi_mem_nhds ht0)
      filter_upwards [hmem] with s hs
      rw [hpatch s hs.1.le (by linarith [hs.2])]
