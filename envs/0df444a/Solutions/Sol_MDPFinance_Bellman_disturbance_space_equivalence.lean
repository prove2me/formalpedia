-- Prove2me | solution 1 for MDPFinance.Bellman.disturbance_space_equivalence
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:03:27.19609+00:00
-- url     : https://prove2.me/submissions/cafa5173-7d1b-4634-8a8b-71ec6715b478

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution : ¬ (∀ {E : Type 1} {A : Type} [MeasurableSpace E] [MeasurableSpace A]
    (D : ℕ → Set (E × A)) (Q : ℕ → Kernel (E × A) E),
    (∃ (Z : Type) (_ : MeasurableSpace Z) (QZ : ℕ → Kernel (E × A) Z) (T : ℕ → E × A → Z → E),
        (∀ n, Measurable (Function.uncurry (T n))) ∧
        ∀ n (xa : E × A) (B : Set E), MeasurableSet B →
          Q n xa B = QZ n xa {z | T n xa z ∈ B})
    ∧
    (∀ (Z : Type) [MeasurableSpace Z] (QZ : ℕ → Kernel (E × A) Z) (T : ℕ → E × A → Z → E),
        (∀ n, Measurable (Function.uncurry (T n))) →
        ∃ Q' : ℕ → Kernel (E × A) E,
          ∀ n (xa : E × A) (B : Set E), MeasurableSet B →
            Q' n xa B = QZ n xa {z | T n xa z ∈ B})) := by
  intro h
  letI : MeasurableSpace (Type) := ⊤
  letI : MeasurableSpace Unit := ⊤
  obtain ⟨⟨Z, _, QZ, T, -, hQ⟩, -⟩ := h (E := Type) (A := Unit) (fun _ => ∅)
    (fun _ => Kernel.const _ Measure.count)
  have hsurj : Function.Surjective (T 0 (Unit, ())) := by
    intro e
    have h1 := hQ 0 (Unit, ()) {e} (MeasurableSpace.measurableSet_top)
    rw [Kernel.const_apply, Measure.count_singleton] at h1
    by_contra hne
    push_neg at hne
    have : {z | T 0 (Unit, ()) z ∈ ({e} : Set Type)} = ∅ := by
      ext z; simp [hne z]
    rw [this, measure_empty] at h1
    exact one_ne_zero h1
  haveI : Small.{0} Type := small_of_surjective hsurj
  exact not_small_type.{0, 0} this
