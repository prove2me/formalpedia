-- Prove2me | solution 1 for Kyprianou.Ch02.prmSimpleMarkFiniteCountRepresentationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:15:39.857211+00:00
-- url     : https://prove2.me/submissions/2192078b-9ce6-43ba-a0f2-a290af5bc6bf

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ) :
    ∀ t : ℝ≥0,
      ∃ (F : ℕ → Finset ℕ) (C : ℕ → ℕ → Set (ℝ × ℝ))
        (a : ℕ → ℕ → ℝ),
      (∀ n i, i ∈ F n → MeasurableSet (C n i)) ∧
      (∀ n i, i ∈ F n →
        LevyStochCalc.Poisson.referenceIntensity ν (C n i) ≠ ⊤) ∧
      (∀ n i, i ∈ F n →
        C n i ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) ∧
      (∀ᵐ ω ∂P, ∀ n,
        (∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) =
          ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
            (f n) z.2 ∂(N.N ω)) := by
  classical
  intro t
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B
  have hR : MeasurableSet R := measurableSet_Ioc.prod hB
  have hRF : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
      ν B hB hfinite 0 t
  let s (n : ℕ) : Finset ℝ := (f n).range
  let ix (n i : ℕ) : ℝ :=
    if hi : i < (s n).card then (((s n).equivFin).symm ⟨i, hi⟩).val else 0
  let F (n : ℕ) : Finset ℕ := Finset.range (s n).card
  let C (n i : ℕ) : Set (ℝ × ℝ) :=
    R ∩ {z : ℝ × ℝ | (f n) z.2 = ix n i}
  let a (n i : ℕ) : ℝ := ix n i
  refine ⟨F, C, a, ?_, ?_, ?_, ?_⟩
  · intro n i hi
    exact hR.inter (((f n).measurableSet_fiber (ix n i)).preimage measurable_snd)
  · intro n i hi
    exact ne_top_of_le_ne_top hRF (measure_mono Set.inter_subset_left)
  · intro n i hi
    exact Set.inter_subset_left
  · filter_upwards [N.integer_valued hR hRF] with ω ⟨k, hk⟩
    intro n
    have hfinR : N.N ω R < ⊤ := by rw [hk]; simp
    have hFibre :=
      (Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
        P ν N R hR (f n) ω hfinR).symm
    let g : ℝ → ℝ := fun x =>
      x * (N.N ω (R ∩ {z : ℝ × ℝ | (f n) z.2 = x})).toReal
    have hSum :
        (∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) =
          ∑ x ∈ s n, g x := by
      change (∑ i ∈ Finset.range (s n).card, g (ix n i)) =
        ∑ x ∈ s n, g x
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        (∑ i : Fin (s n).card, g (ix n i.val)) =
            ∑ x : {x // x ∈ s n}, g x.val := by
          refine Fintype.sum_equiv (((s n).equivFin).symm)
            (fun i => g (ix n i.val)) (fun x => g x.val) ?_
          intro i
          simp [ix, i.isLt]
        _ = ∑ x ∈ s n, g x :=
          (Finset.sum_subtype (s n) (fun x => Iff.rfl) g).symm
    calc
      (∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) =
          ∑ x ∈ s n, g x := hSum
      _ = ∑ x ∈ s n,
          (N.N ω (R ∩ {z : ℝ × ℝ | (f n) z.2 = x})).toReal * x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact mul_comm _ _
      _ = ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
            (f n) z.2 ∂(N.N ω) := by
        simpa only [s, R] using hFibre

