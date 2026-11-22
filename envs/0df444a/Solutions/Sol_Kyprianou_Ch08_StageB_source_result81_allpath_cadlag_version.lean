-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_allpath_cadlag_version
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:16:53.285182+00:00
-- url     : https://prove2.me/submissions/03d36308-253c-40fa-957e-99d3ea7ae079

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Nat
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t, AEMeasurable (X t) P)
    (hzero : X 0 = fun _ => 0)
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (hjump : ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds l) → X t ω ≤ l) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω) ∧
      (∀ t, Measurable (Y t)) ∧ (Y 0 = fun _ => 0) ∧
      (∀ ω, IsCadlag (fun t => Y t ω)) ∧
      (∀ (ω : Ω) (t : ℝ≥0) (l : ℝ), 0 < t →
        Tendsto (fun s => Y s ω) (nhdsWithin t (Iio t)) (nhds l) → Y t ω ≤ l) := by
  classical
  let d (p : ℕ × ℕ) : ℝ≥0 := (p.2 : ℝ≥0) / ((p.1 + 1 : ℕ) : ℝ≥0)
  let j (t : ℝ≥0) (n : ℕ) : ℕ × ℕ := (n, ⌈(t : ℝ) * ↑(n + 1)⌉₊)
  let g (p : ℕ × ℕ) := (hmeas (d p)).mk (X (d p))
  let good (ω : Ω) := (∀ p, g p ω = X (d p) ω) ∧ IsCadlag (fun t => X t ω) ∧
    ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => X s ω) (nhdsWithin t (Iio t)) (nhds l) → X t ω ≤ l
  have hg : ∀ᵐ ω ∂P, ∀ p, g p ω = X (d p) ω :=
    ae_all_iff.mpr fun p => (hmeas (d p)).ae_eq_mk.symm
  have hgood : ∀ᵐ ω ∂P, good ω := hg.and (hcad.and hjump)
  obtain ⟨N, hN, hmN, hnN⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hmem : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.mpr (by simpa using hnN)
  obtain ⟨ω₀, hω₀⟩ := hmem.exists
  have hG (ω : Ω) (hω : ω ∉ N) : good ω :=
    Classical.byContradiction fun h => hω (hN h)
  let F (ω : Ω) : {w // w ∉ N} := if h : ω ∈ N then ⟨ω₀, hω₀⟩ else ⟨ω, h⟩
  let Y (t : ℝ≥0) (ω : Ω) := X t (F ω).1
  refine ⟨Y, hmem.mono (fun ω hω t => by simp [Y, F, hω]), ?_,
    funext (fun ω => congrFun hzero (F ω).1),
    fun ω => (hG _ (F ω).2).2.1, fun ω => (hG _ (F ω).2).2.2⟩
  intro t
  apply measurable_of_tendsto_metrizable
    (f := fun n => N.piecewise (fun _ => X t ω₀) (g (j t n)))
    (fun n => measurable_const.piecewise hmN (hmeas (d (j t n))).measurable_mk)
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ N
  · simpa [Y, F, hω] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => X t ω₀) atTop (𝓝 (X t ω₀)))
  · have hs : Tendsto (fun n => d (j t n)) atTop (𝓝[≥] t) :=
      levy_foundations_tendsto_ceilApprox_nhdsWithin_Ici t
    simpa [Y, F, hω, (hG ω hω).1, Function.comp_def] using
      (((hG ω hω).2.1 t).1.tendsto.comp hs)
