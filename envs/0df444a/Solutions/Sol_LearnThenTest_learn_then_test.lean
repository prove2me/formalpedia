-- Prove2me | solution 1 for LearnThenTest.learn_then_test
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T06:42:29.429708+00:00
-- url     : https://prove2.me/submissions/c0f796db-6736-407c-b0ec-118305e85e01

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

open LearnThenTest

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (R : Fin N → ℝ) (α δ : ℝ) (p : Fin N → Ω → ℝ)
    (hp : ∀ j, Measurable (p j)) (hp01 : ∀ j ω, p j ω ∈ Set.Icc (0 : ℝ) 1)
    (hvalid : ∀ j, α < R j → IsValidPValue P (p j))
    (A : (Fin N → ℝ) → Finset (Fin N)) (hA : IsFWERControlling N δ A) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | (A (fun j => p j ω)).sup (fun j => (R j : WithBot ℝ)) ≤ (α : WithBot ℝ)} ∧
    ∀ lhat : Ω → Fin N,
      (∀ ω, (A (fun j => p j ω)).Nonempty → lhat ω ∈ A (fun j => p j ω)) →
      ENNReal.ofReal (1 - δ) ≤
        P {ω | (A (fun j => p j ω)).Nonempty → R (lhat ω) ≤ α} := by
  set f : Ω → (Fin N → ℝ) := fun ω j => p j ω with hf_def
  have hf : Measurable f := measurable_pi_lambda _ hp
  set μ : Measure (Fin N → ℝ) := P.map f with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hf.aemeasurable
  set J0 : Finset (Fin N) := Finset.univ.filter (fun j => α < R j) with hJ0
  have hrange : ∀ᵐ x ∂μ, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hμ, ae_map_iff hf.aemeasurable]
    · exact Filter.Eventually.of_forall (fun ω j => hp01 j ω)
    · have : {x : Fin N → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} = ⋂ j, (fun x => x j) ⁻¹' Set.Icc 0 1 := by
        ext x; simp
      rw [this]
      exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) measurableSet_Icc)
  have hval : ∀ j ∈ J0, IsValidPValue μ (fun x => x j) := by
    intro j hj u hu
    have hj' : α < R j := by simpa [hJ0] using hj
    rw [hμ, Measure.map_apply hf (measurableSet_le (measurable_pi_apply j) measurable_const)]
    exact hvalid j hj' u hu
  have key := hA.2 μ inferInstance J0 hrange hval
  have hmeas : MeasurableSet {x : Fin N → ℝ | A x ⊆ J0ᶜ} := by
    have : {x : Fin N → ℝ | A x ⊆ J0ᶜ} = ⋂ j ∈ J0, {x | j ∈ A x}ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h j hj hjA
        exact (Finset.mem_compl.mp (h hjA)) hj
      · intro h j hjA
        exact Finset.mem_compl.mpr (fun hj => h j hj hjA)
    rw [this]
    exact Finset.measurableSet_biInter _ (fun j _ => (hA.1 j).compl)
  have hle : ENNReal.ofReal (1 - δ) ≤ P {ω | A (f ω) ⊆ J0ᶜ} := by
    have := key
    rwa [hμ, Measure.map_apply hf hmeas] at this
  have hgood : ∀ ω, A (f ω) ⊆ J0ᶜ → ∀ j ∈ A (f ω), R j ≤ α := by
    intro ω h j hj
    have := h hj
    simp [hJ0] at this
    exact this
  refine ⟨hle.trans (measure_mono ?_), fun lhat hlhat => hle.trans (measure_mono ?_)⟩
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact Finset.sup_le (fun j hj => WithBot.coe_le_coe.mpr (hgood ω hω j hj))
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hne
    exact hgood ω hω _ (hlhat ω hne)

