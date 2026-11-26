-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_shiftedChunk_le_offLattice_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:36:00.601383+00:00
-- url     : https://prove2.me/submissions/795c5442-6407-4347-a03d-df845d4d9f5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_shiftedChunk_lattice_integral_eq_zero
import Theorems.Thm_Kyprianou_Ch05_killedPotential_inner_aemeasurable
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (∀ h : Real, 0 < h → ∀ a b : Real, 0 < a → a ≤ b →
      (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) →
      ∀ δ : Real,
        (∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume) ≤
        ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume) := by
  intro h hh a b ha hab hoff δ
  -- J2a: the lattice-restricted shifted-chunk charge integrates to zero.
  have hJ2a := Kyprianou.Ch05.killedPotential_shiftedChunk_lattice_integral_eq_zero
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
    h hh a b ha hab hoff δ
  -- AEMeasurable marginals (Round-5 derivation from stationary increments).
  have hAe : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have hstat := hKilled.1.1.stationary_increments 0 s
    have hm2 : AEMeasurable (ProbabilityTheory.increment Y 0 s) P := hstat.aemeasurable_snd
    have h0 : Y 0 = fun _ => (0 : Real) := hKilled.1.1.start_zero
    have heq : ProbabilityTheory.increment Y 0 s = Y s := by
      funext ω
      simp only [ProbabilityTheory.increment, h0]
      simp
    rwa [heq] at hm2
  have hdeath : Measurable death := hKilled.2.2.1
  have hA : ∀ t : Real, MeasurableSet
      {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega} :=
    fun t => measurableSet_lt measurable_const hdeath
  have hoff_meas : MeasurableSet {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := by
    have hcompl : {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
        = (⋃ n : Int, {(n : Real) * h})ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · intro hz hzn
        obtain ⟨n, hn⟩ := hzn
        exact hz n hn
      · intro hz n hn
        exact hz ⟨n, hn⟩
    rw [hcompl]
    exact (MeasurableSet.iUnion (fun n => measurableSet_singleton _)).compl
  have hfmeas : Measurable (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
      (1 : Real → ℝ≥0∞)) :=
    measurable_const.indicator hoff_meas
  -- L1b applied to the off-lattice indicator.
  have hL1b := Kyprianou.Ch05.killedPotential_inner_aemeasurable
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
    (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞)) hfmeas
  obtain ⟨G, hGmeas, hFG⟩ := hL1b
  -- Per-time identity: the L1b inner integral at the indicator equals the
  -- (outer) measure of the alive-and-off-lattice event. Proved via a measurable
  -- representative of Y (toNNReal t): both quantities equal P of the
  -- representative's event, since the two events differ inside a null set.
  have hId : ∀ t : Real,
      (∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
          (Y (Real.toNNReal t) omega) ∂P)
      = P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} := by
    intro t
    obtain ⟨u, hum, hueq⟩ := hAe (Real.toNNReal t)
    have hN : P {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega} = 0 :=
      ae_iff.mp hueq
    have hcongr : (∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
          (Y (Real.toNNReal t) omega) ∂P)
        = ∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
          (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
            (u omega) ∂P := by
      apply lintegral_congr_ae
      exact (ae_restrict_of_ae hueq).mono (fun ω hω => by simp only [hω])
    have hB : (∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
          (u omega) ∂P)
        = P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
            ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}) := by
      have step1 : (∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
          (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
            (u omega) ∂P)
          = ∫⁻ omega, ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}.indicator
              (fun ω => (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
                (1 : Real → ℝ≥0∞)) (u ω))) omega ∂P :=
        (lintegral_indicator (hA t) _).symm
      have step2 : (∫⁻ omega, ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}.indicator
            (fun ω => (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
              (1 : Real → ℝ≥0∞)) (u ω))) omega ∂P)
          = ∫⁻ omega, (({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}).indicator
              (1 : Omega → ℝ≥0∞)) omega ∂P := by
        apply lintegral_congr
        intro ω
        by_cases h1 : ω ∈ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega} <;>
          by_cases h2 : u ω ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
        · have hmem : ω ∈ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := ⟨h1, h2⟩
          simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_mem hmem, _root_.Pi.one_apply]
        · have hnmem : ω ∉ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := fun hm => h2 hm.2
          simp only [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
            Set.indicator_of_notMem hnmem]
        · have hnmem : ω ∉ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := fun hm => h1 hm.1
          simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem hnmem]
        · have hnmem : ω ∉ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := fun hm => h1 hm.1
          simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem hnmem]
      have step3 : (∫⁻ omega, (({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
            ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}).indicator
            (1 : Omega → ℝ≥0∞)) omega ∂P)
          = P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
            ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}) :=
        lintegral_indicator_one ((hA t).inter (hum hoff_meas))
      exact step1.trans (step2.trans step3)
    have hC1 : P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
        ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h})
      ≤ P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} := by
      have hsub : {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
          ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
        ⊆ {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
          ∪ {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega} := by
        intro ω hω
        obtain ⟨hωA, hωu⟩ := hω
        by_cases hωY : Y (Real.toNNReal t) ω = u ω
        · refine Or.inl ⟨hωA, ?_⟩
          rw [hωY]
          exact hωu
        · exact Or.inr hωY
      calc P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
            ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h})
          ≤ P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
            ∪ {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega}) := measure_mono hsub
      _ ≤ P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
            + P {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega} := measure_union_le _ _
      _ = P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} := by
          rw [hN, add_zero]
    have hC2 : P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
      ≤ P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
          ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}) := by
      have hsub : {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
        ⊆ ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
            ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h})
          ∪ {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega} := by
        intro ω hω
        obtain ⟨hωA, hωY⟩ := hω
        by_cases hωu : u ω = Y (Real.toNNReal t) ω
        · refine Or.inl ⟨hωA, ?_⟩
          show u ω ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}
          rw [hωu]
          exact hωY
        · refine Or.inr (fun hh => hωu hh.symm)
      calc P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
          ≤ P (({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h})
            ∪ {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega}) := measure_mono hsub
      _ ≤ P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h})
            + P {omega : Omega | Y (Real.toNNReal t) omega ≠ u omega} := measure_union_le _ _
      _ = P ({omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega}
              ∩ u ⁻¹' {z : Real | ∀ n : Int, z ≠ (n : Real) * h}) := by
          rw [hN, add_zero]
    exact hcongr.trans (hB.trans (le_antisymm hC1 hC2))
  -- AEMeasurability of the off-lattice charge as a function of t, on Ioc 0 δ.
  have hf : AEMeasurable (fun t : Real =>
      P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
        Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}})
      (volume.restrict (Set.Ioc (0 : Real) δ)) := by
    refine ⟨G, hGmeas, ?_⟩
    have h1 : (fun t : Real => ∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
        (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
          (Y (Real.toNNReal t) omega) ∂P)
        =ᵐ[volume.restrict (Set.Ioc (0 : Real) δ)] G :=
      ae_restrict_of_ae_restrict_of_subset (fun t ht => ht.1.le) hFG
    have h2 : (fun t : Real =>
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}})
        =ᵐ[volume.restrict (Set.Ioc (0 : Real) δ)]
        (fun t : Real => ∫⁻ omega in {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega},
          (Set.indicator {z : Real | ∀ n : Int, z ≠ (n : Real) * h} (1 : Real → ℝ≥0∞))
            (Y (Real.toNNReal t) omega) ∂P) :=
      Filter.Eventually.of_forall (fun t => (hId t).symm)
    exact h2.trans h1
  -- Pointwise bound: shifted ⊆ off ∪ (shifted ∧ lattice), as measures.
  have hpt : ∀ t : Real,
      P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}}
        ≤ P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
          + P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} := by
    intro t
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ω hω
    obtain ⟨hal, hsh⟩ := hω
    by_cases hlat : Y (Real.toNNReal t) ω ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}
    · exact Or.inr ⟨hal, hsh, hlat⟩
    · refine Or.inl ⟨hal, ?_⟩
      intro n hn
      exact hlat ⟨n, hn⟩
  -- Assembly.
  calc (∫⁻ t in Set.Ioc (0 : Real) δ,
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y}} ∂volume)
      ≤ ∫⁻ t in Set.Ioc (0 : Real) δ,
          (P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
              Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}}
            + P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
                Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
                Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}}) :=
        lintegral_mono hpt
  _ = (∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume)
        + ∫⁻ t in Set.Ioc (0 : Real) δ,
          P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ y ∈ Set.Icc a b, z = d * t + y} ∧
            Y (Real.toNNReal t) omega ∈ {z : Real | ∃ n : Int, z = (n : Real) * h}} ∂volume :=
        lintegral_add_left' hf _
  _ = ∫⁻ t in Set.Ioc (0 : Real) δ,
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} ∂volume := by
      rw [hJ2a, add_zero]
