-- Prove2me | solution 1 for Kyprianou.Ch02.emptyMarkPRMExistsV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:31:22.582801+00:00
-- url     : https://prove2.me/submissions/2d4845a5-36a5-45a8-b1b0-ee5c7c430440

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    (E : Type) [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    (hempty : ¬ Nonempty E) :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          (∀ (A : Set E), MeasurableSet A →
            Measurable (fun ω => N ω A)) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            P.map (fun ω => N ω A) =
              (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) ∧
          (∀ (A : Set E), MeasurableSet A → m A = ⊤ →
            ∀ᵐ ω ∂P, N ω A = ⊤) ∧
          (∀ {ι : Type} [Countable ι] (A : ι → Set E),
            (∀ i, MeasurableSet (A i)) →
            Pairwise (fun i j => Disjoint (A i) (A j)) →
            ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P) := by
  classical
  haveI : IsEmpty E := ⟨fun x => hempty ⟨x⟩⟩
  have hzero : m = 0 := Measure.eq_zero_of_isEmpty m
  have hPoissonZero : ProbabilityTheory.poissonMeasure 0 = Measure.dirac 0 := by
    refine Measure.ext_of_singleton fun n => ?_
    rw [ProbabilityTheory.poissonMeasure_singleton,
      Measure.dirac_apply' 0 (measurableSet_singleton n)]
    by_cases hn : n = 0
    · subst hn
      simp
    · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, NNReal.coe_zero]
      rw [if_neg (fun h => hn h.symm)]
      simp [zero_pow hn]
  let P : Measure Unit := Measure.dirac ()
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  refine ⟨Unit, inferInstance, P, inferInstance, fun _ => (0 : Measure E), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact measurable_const
  · intro A hA hfinite
    filter_upwards [] with ω
    exact ⟨0, by simp⟩
  · intro A hA hfinite
    have hm : m A = 0 := by simp [hzero]
    rw [hm]
    simp only [ENNReal.toNNReal_zero, hPoissonZero]
    rw [Measure.map_const]
    simp [P, Measure.map_dirac']
  · intro A hA htop
    have hm : m A = 0 := by simp [hzero]
    simp [hm] at htop
  · intro ι inst A hA hdis
    apply (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul).2
    intro S sets hsets
    have heq :
        (if ∀ i ∈ S, (0 : ENNReal) ∈ sets i then (1 : ENNReal) else 0) =
        ∏ i ∈ S, (if (0 : ENNReal) ∈ sets i then (1 : ENNReal) else 0) := by
      by_cases hall : ∀ i ∈ S, (0 : ENNReal) ∈ sets i
      · have hprod : (∏ i ∈ S, if (0 : ENNReal) ∈ sets i then (1 : ENNReal)
            else 0) = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          simp [hall i hi]
        simp only [if_pos hall, hprod]
      · have hn := hall
        push_neg at hall
        obtain ⟨i, hi, hni⟩ := hall
        have hprod : (∏ j ∈ S, if (0 : ENNReal) ∈ sets j then (1 : ENNReal)
              else 0) = 0 :=
          Finset.prod_eq_zero hi (by simp [hni])
        simp only [if_neg hn, hprod]
    simpa [P, Measure.dirac_apply, Set.preimage_const, Set.mem_iInter,
      Set.indicator_apply, Set.mem_ite_empty_right] using heq
