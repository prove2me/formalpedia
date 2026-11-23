-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpUniformLimitL2MartingaleV1
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-23T20:21:24.260684+00:00
-- url     : https://prove2.me/submissions/384b2d63-7449-4b7f-a0fe-5c991097afad

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

@[instance_reducible]
private def m3 : MeasurableSpace (Fin 3) :=
  MeasurableSpace.generateFrom {({0} : Set (Fin 3))}

private lemma m3_indist (s : Set (Fin 3)) (hs : @MeasurableSet (Fin 3) m3 s) :
    ((1 : Fin 3) ∈ s ↔ (2 : Fin 3) ∈ s) := by
  induction hs with
  | basic u hu =>
    rcases Set.mem_singleton_iff.mp hu with rfl
    decide
  | empty => simp
  | compl u _ ih => simp [ih]
  | iUnion f _ ih => simp [ih]

private lemma not_m3_singleton_one : ¬ @MeasurableSet (Fin 3) m3 ({1} : Set (Fin 3)) := by
  intro h
  have := m3_indist {1} h
  simp at this

theorem solution :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
      (_ : ProbabilityTheory.IsLevyMeasure levyMeasure)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
      (_ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
      (M : ℝ≥0 → Ω → ℝ)
      (_ : M 0 = fun _ => 0)
      (_ :
        ∀ T : ℝ≥0, 0 < T →
          ∃ ε : ℕ → ℝ,
            StrictAnti ε ∧
            (∀ n, 0 < ε n ∧ ε n < 1) ∧
            Tendsto ε Filter.atTop (nhds 0) ∧
            (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
              ∃ n₀ : ℕ, ∀ n ≥ n₀,
                ∀ t : ℝ≥0, t ≤ T →
                  |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                      M t ω| < δ)),
      MeasureTheory.Martingale M ℱ P ∧
      ∀ t : ℝ≥0, MemLp (M t) 2 P) := by
  classical
  intro hthm
  let : MeasurableSpace (Fin 3) := m3
  let P : Measure (Fin 3) := Measure.dirac 0
  have hPprob : IsProbabilityMeasure P := Measure.dirac.isProbabilityMeasure
  have hlevy : ProbabilityTheory.IsLevyMeasure (0 : Measure ℝ) := by
    refine ⟨by simp, by simp⟩
  have hpm0 : LevyStochCalc.Poisson.poissonMeasureENN 0 = Measure.dirac (0 : ℝ≥0∞) := by
    unfold LevyStochCalc.Poisson.poissonMeasureENN
    ext s hs
    rw [Measure.map_apply measurable_from_top hs, Measure.dirac_apply' _ hs]
    rw [ProbabilityTheory.poissonMeasure, Measure.sum_apply _ (measurable_from_top hs)]
    rw [tsum_eq_single 0]
    · simp [Measure.dirac_apply' _ (measurable_from_top hs), Set.indicator]
    · intro b hb
      cases b with
      | zero => exact absurd rfl hb
      | succ k => simp
  let N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P (0 : Measure ℝ) :=
    { N := fun _ => 0
      measurable_eval := fun _ => measurable_const
      integer_valued := fun _ _ => Filter.Eventually.of_forall (fun _ => ⟨0, by simp⟩)
      infinite_at_infinite_intensity := fun _ h => by
        simp [LevyStochCalc.Poisson.referenceIntensity] at h
      poisson_law := fun _ _ => by
        simp [LevyStochCalc.Poisson.referenceIntensity, hpm0, Measure.map_const]
      independent_disjoint := fun B _ _ => by
        rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
        intro S sets _
        simp only [Measure.coe_zero, Pi.zero_apply]
        have hconst : ∀ i, (fun _ : Fin 3 => (0 : ℝ≥0∞)) ⁻¹' sets i =
            if (0 : ℝ≥0∞) ∈ sets i then Set.univ else ∅ := fun i => by
          ext ω; by_cases h : (0 : ℝ≥0∞) ∈ sets i <;> simp [h]
        by_cases hall : ∀ i ∈ S, (0 : ℝ≥0∞) ∈ sets i
        · have hL : (⋂ i ∈ S, (fun _ : Fin 3 => (0 : ℝ≥0∞)) ⁻¹' sets i) = Set.univ := by
            ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_univ, iff_true]
            exact fun i hi => hall i hi
          rw [hL, measure_univ]
          symm
          apply Finset.prod_eq_one
          intro i hi
          rw [hconst i, if_pos (hall i hi), measure_univ]
        · push Not at hall
          rcases hall with ⟨i0, hi0, hnot⟩
          have hL : (⋂ i ∈ S, (fun _ : Fin 3 => (0 : ℝ≥0∞)) ⁻¹' sets i) = ∅ := by
            ext ω; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
            intro h; exact hnot (h i0 hi0)
          rw [hL, measure_empty]
          symm
          apply Finset.prod_eq_zero hi0
          rw [hconst i0, if_neg hnot, measure_empty]
      joint_past_future_independent := fun _ _ _ _ _ => by
        simp only [Measure.coe_zero, Pi.zero_apply, MeasurableSpace.comap_const, iSup_bot]
        exact ProbabilityTheory.indep_bot_left _ }
  let ℱ : Filtration ℝ≥0 m3 :=
    { seq := fun _ => m3
      mono' := fun _ _ _ => le_rfl
      le' := fun _ => le_rfl }
  have hm0 : @MeasurableSet (Fin 3) m3 ({0} : Set (Fin 3)) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  have hm12 : @MeasurableSet (Fin 3) m3 ({0}ᶜ : Set (Fin 3)) := hm0.compl
  have hP12 : P ({0}ᶜ : Set (Fin 3)) = 0 := by
    simp [P, Measure.dirac_apply' _ hm12]
  have hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P (0 : Measure ℝ) N ℱ := by
    refine ⟨fun _ _ _ _ _ => measurable_const, fun _ _ hS _ => hS, ?_, ?_⟩
    · refine ⟨fun t => ?_⟩
      exact ℱ.rightCont.le t
    · intro G _ hGcomp _ t
      change m3 ≤ G t
      refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      rcases Set.mem_singleton_iff.mp hs with rfl
      have hcompl : @MeasurableSet (Fin 3) (G t) ({0}ᶜ : Set (Fin 3)) := hGcomp t _ hm12 hP12
      simpa using hcompl.compl
  let M : ℝ≥0 → Fin 3 → ℝ := fun t ω => if t = 0 then 0 else if ω = 1 then 1 else 0
  have hzero : M 0 = fun _ => 0 := by funext ω; simp [M]
  have huniform : ∀ T : ℝ≥0, 0 < T →
      ∃ ε : ℕ → ℝ,
        StrictAnti ε ∧
        (∀ n, 0 < ε n ∧ ε n < 1) ∧
        Tendsto ε Filter.atTop (nhds 0) ∧
        (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
          ∃ n₀ : ℕ, ∀ n ≥ n₀,
            ∀ t : ℝ≥0, t ≤ T →
              |Kyprianou.compensatedSmallJumpBand P (0 : Measure ℝ) N (ε n) t ω - M t ω| < δ) := by
    intro T _
    refine ⟨fun n => 1 / ((n : ℝ) + 2), ?_, ?_, ?_, ?_⟩
    · intro a b hab
      apply one_div_lt_one_div_of_lt (by positivity)
      exact_mod_cast (show a + 2 < b + 2 by omega)
    · intro n
      constructor
      · positivity
      · rw [div_lt_one (by positivity)]; linarith
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) + 1)) atTop (nhds 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine h1.congr (fun n => ?_)
      push_cast
      ring
    · have hae : ∀ᵐ ω ∂P, ω = 0 := by
        rw [ae_iff]
        exact hP12
      filter_upwards [hae] with ω hω δ hδ
      refine ⟨0, fun n _ t _ => ?_⟩
      subst hω
      simp [Kyprianou.compensatedSmallJumpBand, N, M, hδ]
  have hres := @hthm (Fin 3) m3 P hPprob (0 : Measure ℝ) inferInstance hlevy N ℱ hℱ M hzero huniform
  have hsm : StronglyMeasurable[ℱ 1] (M 1) := hres.1.1 1
  have hm : @Measurable (Fin 3) ℝ m3 inferInstance (M 1) := hsm.measurable
  have hpre : @MeasurableSet (Fin 3) m3 ((M 1) ⁻¹' ({1} : Set ℝ)) := hm (measurableSet_singleton 1)
  have heq : (M 1) ⁻¹' ({1} : Set ℝ) = ({1} : Set (Fin 3)) := by
    ext ω
    fin_cases ω <;> simp [M]
  rw [heq] at hpre
  exact not_m3_singleton_one hpre
