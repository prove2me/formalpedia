-- Prove2me | solution 1 for LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:19:52.600438+00:00
-- url     : https://prove2.me/submissions/1efd6c9e-1ed9-4634-9e6a-c730013033ce

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A.e. measurability for the infimum of a decreasing sequence of σ-algebras

A real function a.e.-measurable for every member of an antitone sequence of sub-σ-algebras is
a.e.-measurable for their infimum. The witness is the `limsup` of the approximants: dropping the
first `N` terms does not change a `limsup`, and after that every approximant is `m N`-measurable,
while on the a.e. set where all the approximants agree with `f` the `limsup` is `f` itself.

This is the step that identifies `⨅ n, lpMeas (m n)` with `lpMeas (⨅ n, m n)`, which is what turns
the convergence of orthogonal projections (`LevyStochCalc/Probability/ProjectionLimit.lean`) into
convergence of conditional expectations along a decreasing filtration.
-/

open MeasureTheory Filter
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}



theorem _root_.solution {m : ℕ → MeasurableSpace Ω} (hanti : Antitone m)
    {f : Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable[m n] f μ) :
    AEStronglyMeasurable[⨅ n, m n] f μ := by
  let g : ℕ → Ω → ℝ := fun n => (hf n).mk f
  have hg : ∀ n, Measurable[m n] (g n) := fun n => (hf n).stronglyMeasurable_mk.measurable
  have hfg : ∀ n, f =ᵐ[μ] g n := fun n => (hf n).ae_eq_mk
  let G : Ω → ℝ := fun x => limsup (fun i => g i x) atTop
  have hGk : ∀ k, Measurable[m k] G := by
    intro k
    have heq : G = fun x => limsup (fun i => g (i + k) x) atTop := by
      funext x
      exact (limsup_nat_add (fun i => g i x) k).symm
    rw [heq]
    have hgi : ∀ i, Measurable[m k] (g (i + k)) := fun i =>
      (hg (i + k)).mono (hanti (by omega : k ≤ i + k)) le_rfl
    letI : MeasurableSpace Ω := m k
    exact Measurable.limsup hgi
  have hG : Measurable[⨅ n, m n] G := by
    rw [measurable_iff_comap_le, le_iInf_iff]
    intro k
    exact (hGk k).comap_le
  refine ⟨G, hG.stronglyMeasurable, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, f x = g n x := ae_all_iff.2 hfg
  filter_upwards [hall] with x hx
  show f x = limsup (fun i => g i x) atTop
  simp only [← hx, limsup_const]

