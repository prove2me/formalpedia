-- Prove2me | solution 1 for ModelRiskOT.Duality.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:53:48.191747+00:00
-- url     : https://prove2.me/submissions/44f7982f-e5a4-4b38-ac41-06d9727f36af

import Mathlib

set_option autoImplicit false

open MeasureTheory BoundedContinuousFunction

namespace A074532d

lemma usc_bdd {S : Type*} [TopologicalSpace S] [CompactSpace S] (f : S → ℝ)
    (hf : UpperSemicontinuous f) : ∃ c : ℝ, ∀ y, f y ≤ c := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, fun y => (IsEmpty.false y).elim⟩
  · obtain ⟨a, -, ha⟩ := (hf.upperSemicontinuousOn (s := Set.univ)).exists_isMaxOn
      Set.univ_nonempty isCompact_univ
    exact ⟨f a, fun y => ha (Set.mem_univ y)⟩

end A074532d

open MeasureTheory BoundedContinuousFunction in
theorem solution {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [CompactSpace S]
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f)
    (π : SignedMeasure (S × S)) (A : Set (S × S)) (hA : MeasurableSet A)
    (hpos : π.toJordanDecomposition.posPart A = 0)
    (hneg : 0 < π.toJordanDecomposition.negPart A) :
    ∀ M : ℝ, ∃ g : S × S →ᵇ ℝ, (∀ x y, f y ≤ g (x, y)) ∧
      (∫ p, g p ∂π.toJordanDecomposition.posPart) - (∫ p, g p ∂π.toJordanDecomposition.negPart)
        < M := by
  intro M
  set μ := π.toJordanDecomposition.posPart with hμ
  set ν := π.toJordanDecomposition.negPart with hν
  let _ : PseudoMetricSpace (S × S) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric _
  have : ν.WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure ν
  have : μ.WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure μ
  obtain ⟨c0, hc0⟩ := A074532d.usc_bdd f hf_usc
  obtain ⟨K, hKA, hKc, hK⟩ := hA.exists_lt_isClosed_of_ne_top (measure_ne_top ν A) hneg
  have hμK : μ K < ν K := by
    rw [measure_mono_null hKA hpos]; exact hK
  obtain ⟨U, hKU, hUo, hU⟩ := K.exists_isOpen_lt_of_lt (μ := μ) (ν K) hμK
  obtain ⟨φ, hφ0, hφ1, hφI⟩ := exists_bounded_zero_one_of_closed hUo.isClosed_compl hKc
    ((disjoint_compl_left (a := U)).mono_right hKU)
  -- integral bounds
  have hUm : MeasurableSet U := hUo.measurableSet
  have hKm : MeasurableSet K := hKc.measurableSet
  have h1 : ∫ p, φ p ∂μ ≤ μ.real U := by
    rw [← integral_indicator_one hUm]
    refine integral_mono (φ.integrable μ) ?_ ?_
    · exact (integrable_const (1:ℝ)).indicator hUm
    · intro p
      by_cases hp : p ∈ U
      · simp [Set.indicator_of_mem hp, (hφI p).2]
      · simp [Set.indicator_of_notMem hp, hφ0 hp]
  have h2 : ν.real K ≤ ∫ p, φ p ∂ν := by
    rw [← integral_indicator_one hKm]
    refine integral_mono ((integrable_const (1:ℝ)).indicator hKm) (φ.integrable ν) ?_
    intro p
    by_cases hp : p ∈ K
    · simp [Set.indicator_of_mem hp, hφ1 hp]
    · simp [Set.indicator_of_notMem hp, (hφI p).1]
  have h3 : μ.real U < ν.real K := by
    rw [measureReal_def, measureReal_def]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr hU
  set δ := ∫ p, φ p ∂ν - ∫ p, φ p ∂μ with hδ
  have hδpos : 0 < δ := by linarith
  set D := c0 * μ.real Set.univ - c0 * ν.real Set.univ with hD
  set C : ℝ := (|D - M| + 1) / δ with hC
  have hCpos : 0 ≤ C := by positivity
  refine ⟨(BoundedContinuousFunction.const (S × S) c0 + C • φ : S × S →ᵇ ℝ), ?_, ?_⟩
  · intro x y
    have := hc0 y
    have h0 := (hφI (x, y)).1
    simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.coe_smul, smul_eq_mul]
    nlinarith
  · have e : ∀ m : Measure (S × S), IsFiniteMeasure m →
        ∫ p, ((BoundedContinuousFunction.const (S × S) c0 + C • φ : S × S →ᵇ ℝ)) p ∂m
          = c0 * m.real Set.univ + C * ∫ p, φ p ∂m := by
      intro m _
      simp only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply,
        BoundedContinuousFunction.coe_smul, smul_eq_mul]
      rw [integral_add (integrable_const _) ((φ.integrable m).const_mul C), integral_const,
        integral_const_mul, smul_eq_mul, mul_comm]
    rw [e μ inferInstance, e ν inferInstance]
    have hCδ : C * δ = |D - M| + 1 := by
      rw [hC]; field_simp
    have := le_abs_self (D - M)
    nlinarith
