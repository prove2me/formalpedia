-- Prove2me | solution 1 for NatureSLT.Consistency.entropy_le_annealed_le_growth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:03:19.686707+00:00
-- url     : https://prove2.me/submissions/9b283f6b-6d9d-4c52-b113-49377670e099

import Mathlib
import Definitions.Def_NatureSLT_Consistency_indicatorEntropy

open MeasureTheory
open NatureSLT.Consistency

theorem g69w_div_finite {Z Λ : Type*} (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1)
    {ℓ : ℕ} (z : Fin ℓ → Z) :
    Finite (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)) ∧
      diversity Q z ≤ 2 ^ ℓ := by
  let g : (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)) → (Fin ℓ → Bool) :=
    fun f i => decide (f.1 i = 1)
  have hg : Function.Injective g := by
    rintro ⟨f1, α1, rfl⟩ ⟨f2, α2, rfl⟩ h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simp only [g, decide_eq_decide] at this
    rcases hQ α1 (z i) with h1 | h1 <;> rcases hQ α2 (z i) with h2 | h2 <;>
      simp_all
  refine ⟨Finite.of_injective g hg, ?_⟩
  unfold diversity
  have := Nat.card_le_card_of_injective g hg
  simpa [Nat.card_eq_fintype_card] using this

theorem solution {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1)
    (hN : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => (diversity Q z : ℝ))) (ℓ : ℕ) :
    entropy F Q ℓ ≤ annealedEntropy F Q ℓ ∧
      annealedEntropy F Q ℓ ≤ growthFunction Q ℓ := by
  rcases isEmpty_or_nonempty Λ with hΛ | hΛ
  · have h0 : ∀ z : Fin ℓ → Z, diversity Q z = 0 := by
      intro z; unfold diversity; rw [Set.range_eq_empty]; simp
    simp [entropy, annealedEntropy, growthFunction, h0]
  set μ := Measure.pi fun _ : Fin ℓ => F
  set D : (Fin ℓ → Z) → ℝ := fun z => (diversity Q z : ℝ) with hD
  have hDle : ∀ z, D z ≤ 2 ^ ℓ := fun z => by
    simp only [hD]; exact_mod_cast (g69w_div_finite Q hQ z).2
  have hD1 : ∀ z, 1 ≤ D z := fun z => by
    simp only [hD]
    have hfin := (g69w_div_finite Q hQ z).1
    have : (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)).Nonempty := Set.range_nonempty _
    have := Nat.card_pos (α := (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i)))
    exact_mod_cast this
  have hDm : Measurable D := hN ℓ
  have hDi : Integrable D μ := Integrable.of_bound hDm.aestronglyMeasurable (2 ^ ℓ)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hD1 z])]; exact hDle z)
  have hLm : Measurable fun z => Real.log (D z) := Real.measurable_log.comp hDm
  have hLi : Integrable (fun z => Real.log (D z)) μ := Integrable.of_bound
    hLm.aestronglyMeasurable (2 ^ ℓ) (Filter.Eventually.of_forall fun z => by
      have h1 := hD1 z
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < D z)
      linarith [hDle z])
  set E := ∫ z, D z ∂μ with hE
  have hE1 : 1 ≤ E := by
    have := integral_mono (integrable_const (1 : ℝ)) hDi (fun z => hD1 z)
    simpa using this
  have hE0 : 0 < E := by linarith
  refine ⟨?_, ?_⟩
  · show ∫ z, Real.log (D z) ∂μ ≤ Real.log E
    have hpt : ∀ z, Real.log (D z) ≤ Real.log E + (D z / E - 1) := fun z => by
      have h1 := hD1 z
      have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < D z) hE0)
      rw [Real.log_div (by linarith) hE0.ne'] at this
      linarith
    have hi3 : Integrable (fun z => D z / E - 1) μ := (hDi.div_const E).sub (integrable_const _)
    have hi2 : Integrable (fun z => Real.log E + (D z / E - 1)) μ :=
      (integrable_const _).add hi3
    have := integral_mono hLi hi2 hpt
    rw [integral_add (integrable_const _) hi3,
      integral_sub (hDi.div_const E) (integrable_const _), integral_div] at this
    simp only [integral_const, probReal_univ, one_smul] at this
    rw [div_self hE0.ne'] at this
    linarith
  · show Real.log E ≤ Real.log (⨆ z : Fin ℓ → Z, D z)
    have hbdd : BddAbove (Set.range D) := ⟨2 ^ ℓ, by rintro _ ⟨z, rfl⟩; exact hDle z⟩
    apply Real.log_le_log hE0
    have : E ≤ ∫ _z, (⨆ z : Fin ℓ → Z, D z) ∂μ :=
      integral_mono hDi (integrable_const _) (fun z => le_ciSup hbdd z)
    simpa using this
