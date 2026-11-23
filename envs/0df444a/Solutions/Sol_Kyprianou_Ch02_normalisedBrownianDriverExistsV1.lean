-- Prove2me | solution 1 for Kyprianou.Ch02.normalisedBrownianDriverExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:34:28.420822+00:00
-- url     : https://prove2.me/submissions/979d9f6c-9101-4399-9791-6e0e3a500cbc

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence

section
/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/BrownianMotion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω}
section
section IsPreBrownianReal
variable (X : ℝ≥0 → Ω → ℝ)
variable {X} {P : MeasureTheory.Measure Ω}
lemma ProbabilityTheory.IsPreBrownianReal.memHolder_mk (h : IsPreBrownianReal X P) (ω : Ω) (t : ℝ≥0) (β : ℝ≥0)
    (hβ_pos : 0 < β) (hβ_lt : β < 2⁻¹) :
    ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (h.mk X · ω) U := by
  convert h.exists_continuous_modification.choose_spec.2.2 ω t β hβ_pos ?_
  · rfl
  suffices ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ)) = 2⁻¹ by rw [this]; norm_cast
  refine iSup_eq_of_forall_le_of_tendsto (F := Filter.atTop) (fun n ↦ ?_) ?_
  · calc
    ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2)) = 2⁻¹ * (n + 1) / (n + 2) := by
      simp only [Nat.cast_add, Nat.cast_ofNat]; field_simp; ring
    _ ≤ 2⁻¹ * 1 := by grw [mul_div_assoc, (div_le_one₀ (by positivity)).2]; linarith
    _ = 2⁻¹ := mul_one _
  · have : (fun n : ℕ ↦ ((↑(n + 2) : ℝ) - 1) / (2 * ↑(n + 2))) =
        (fun n : ℕ ↦ 2⁻¹ * ((n : ℝ) / (n + 1))) ∘ (fun n ↦ n + 1) := by
      ext n
      simp only [Nat.cast_add, Nat.cast_ofNat, Function.comp_apply, Nat.cast_one]
      field_simp
      ring
    rw [this]
    refine Filter.Tendsto.comp ?_ (Filter.tendsto_add_atTop_nat 1)
    nth_rw 2 [← mul_one 2⁻¹]
    exact (tendsto_natCast_div_add_atTop (1 : ℝ)).const_mul _
@[fun_prop]
lemma ProbabilityTheory.IsPreBrownianReal.measurable_mk (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (h.mk X t) :=
  h.exists_continuous_modification.choose_spec.1 t
lemma ProbabilityTheory.IsPreBrownianReal.mk_ae_eq (h : IsPreBrownianReal X P) (t : ℝ≥0) :
    h.mk X t =ᵐ[P] X t :=
  h.exists_continuous_modification.choose_spec.2.1 t
lemma ProbabilityTheory.IsPreBrownianReal.continuous_mk (h : IsPreBrownianReal X P) (ω : Ω) :
    Continuous (h.mk X · ω) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  obtain ⟨U, hu_mem, ⟨C, h⟩⟩ := h.memHolder_mk ω t 4⁻¹ (by norm_num)
    (NNReal.inv_lt_inv (by norm_num) (by norm_num))
  exact (h.continuousOn (by norm_num)).continuousAt hu_mem
end IsPreBrownianReal
section IsBrownianReal
variable (X : ℝ≥0 → Ω → ℝ)
variable {X}
lemma ProbabilityTheory.IsPreBrownianReal.isBrownianReal_mk (h : IsPreBrownianReal X P) :
    IsBrownianReal (h.mk X) P where
  toIsPreBrownianReal := h.congr fun _ ↦ (h.mk_ae_eq _).symm
  cont := ae_of_all _ h.continuous_mk
end IsBrownianReal
@[fun_prop]
lemma ProbabilityTheory.measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  isPreBrownianReal_preBrownian.measurable_mk t
@[fun_prop]
lemma ProbabilityTheory.continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) :=
  isPreBrownianReal_preBrownian.continuous_mk ω
theorem ProbabilityTheory.isBrownianReal_brownian : IsBrownianReal brownian gaussianLimit :=
  isPreBrownianReal_preBrownian.isBrownianReal_mk
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Existence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- Existence of a probability space carrying a Brownian motion: the canonical Brownian motion
`brownian` on the projective-limit space `gaussianLimit`, transported along `ULift`. -/
theorem solution :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := mΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ (B : LevyStochCalc.Brownian.BrownianMotion P),
          ∀ ω : Ω, B.W 0 ω = 0 := by
  let e : ULift.{0} (ℝ≥0 → ℝ) ≃ᵐ (ℝ≥0 → ℝ) := MeasurableEquiv.ulift
  let P : Measure (ULift.{0} (ℝ≥0 → ℝ)) :=
    ProbabilityTheory.gaussianLimit.map e.symm
  have hP : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map e.symm.measurable.aemeasurable
  have hdown : HasLaw e ProbabilityTheory.gaussianLimit P :=
    ⟨e.measurable.aemeasurable, by
      simp [P, Measure.map_map e.measurable e.symm.measurable]⟩
  refine ⟨ULift.{0} (ℝ≥0 → ℝ), inferInstance, P, hP, ?_⟩
  let B : LevyStochCalc.Brownian.BrownianMotion P :=
    LevyStochCalc.Brownian.BrownianMotion.ofIsPreBrownianReal
      (X := fun t ω => ProbabilityTheory.brownian t (e ω))
      (by exact ⟨fun I =>
        (ProbabilityTheory.isBrownianReal_brownian.hasLaw I).comp hdown⟩)
      (fun t => (ProbabilityTheory.measurable_brownian t).comp e.measurable)
      (fun ω => ProbabilityTheory.continuous_brownian (e ω))
  refine ⟨B, ?_⟩
  intro ω
  change LevyStochCalc.Brownian.realTime
    (fun t ω => ProbabilityTheory.brownian t (e ω)) 0 ω = 0
  simp [LevyStochCalc.Brownian.realTime]
