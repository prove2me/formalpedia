-- Prove2me | solution 1 for Kyprianou.Ch01.probabilityAbsDifferenceLeExceptionOfAEAgreement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:12:31.835882+00:00
-- url     : https://prove2.me/submissions/74baaf3e-0f20-4c81-b326-96c0c957ef4c

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A B E : Set Ω)
    (hAgree : ∀ᵐ ω ∂Q,
      ω ∉ E → (ω ∈ A ↔ ω ∈ B)) :
    |(Q A).toReal - (Q B).toReal| ≤ (Q E).toReal := by
  have hf (S : Set Ω) : Q S ≠ ⊤ :=
    measure_ne_top Q S
  have hAB : ∀ᵐ ω ∂Q, ω ∈ A → ω ∈ B ∪ E := by
    filter_upwards [hAgree] with ω hω hA
    by_cases he : ω ∈ E
    · exact Or.inr he
    · exact Or.inl ((hω he).mp hA)
  have hBA : ∀ᵐ ω ∂Q, ω ∈ B → ω ∈ A ∪ E := by
    filter_upwards [hAgree] with ω hω hB
    by_cases he : ω ∈ E
    · exact Or.inr he
    · exact Or.inl ((hω he).mpr hB)
  have hOne :
      (Q A).toReal ≤ (Q B).toReal + (Q E).toReal := by
    calc
      (Q A).toReal ≤ (Q (B ∪ E)).toReal :=
        ENNReal.toReal_mono (hf _) (measure_mono_ae hAB)
      _ ≤ (Q B + Q E).toReal :=
        ENNReal.toReal_mono
          ((ENNReal.add_ne_top).2 ⟨hf B, hf E⟩)
          (measure_union_le B E)
      _ = (Q B).toReal + (Q E).toReal :=
        ENNReal.toReal_add (hf B) (hf E)
  have hTwo :
      (Q B).toReal ≤ (Q A).toReal + (Q E).toReal := by
    calc
      (Q B).toReal ≤ (Q (A ∪ E)).toReal :=
        ENNReal.toReal_mono (hf _) (measure_mono_ae hBA)
      _ ≤ (Q A + Q E).toReal :=
        ENNReal.toReal_mono
          ((ENNReal.add_ne_top).2 ⟨hf A, hf E⟩)
          (measure_union_le A E)
      _ = (Q A).toReal + (Q E).toReal :=
        ENNReal.toReal_add (hf A) (hf E)
  exact abs_le.mpr ⟨by linarith, by linarith⟩
