-- Prove2me | solution 2 for Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:23:48.913239+00:00
-- url     : https://prove2.me/submissions/8f49e11f-3c83-4ce0-a463-0ff87e3d10e2

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNull : n (B ∩ C) = 0) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) ∧
      N omega t C = N omega t (C \ B) := by
  -- P is a probability measure (k = 0 rectangle law)
  have hP1 : P Set.univ = 1 := by
    have h := hPPP.2.2 0 Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    have hs : {omega : Omega | ∀ i : Fin 0,
        N omega (Fin.elim0 i) (Fin.elim0 i) - N omega (Fin.elim0 i) (Fin.elim0 i) = Fin.elim0 i}
        = Set.univ := by
      ext omega; simp
    rw [hs] at h
    simpa using h
  have hP : IsProbabilityMeasure P := ⟨hP1⟩
  set A := B ∩ C with hA
  have hAm : MeasurableSet A := hB.inter hC
  -- for each natural m, a.s. N m A - N 0 A = 0
  have hk : ∀ m : ℕ, ∀ᵐ omega ∂P, N omega (m : ℝ≥0) A - N omega 0 A = 0 := by
    intro m
    have h := hPPP.2.2 1 (fun _ => 0) (fun _ => (m : ℝ≥0)) (fun _ => A) (fun _ => 0)
      (fun _ => ⟨bot_le, hAm, by rw [hNull]; exact ENNReal.zero_lt_top⟩)
      (fun i j hij => absurd (Subsingleton.elim i j) hij)
    have hs : {omega : Omega | ∀ i : Fin 1,
        N omega ((fun _ => (m : ℝ≥0)) i) ((fun _ => A) i) -
          N omega ((fun _ => (0 : ℝ≥0)) i) ((fun _ => A) i) = (fun _ => 0) i}
        = {omega | N omega (m : ℝ≥0) A - N omega 0 A = 0} := by
      ext omega; simp
    rw [hs] at h
    have hval : P {omega | N omega (m : ℝ≥0) A - N omega 0 A = 0} = 1 := by
      rw [h]; simp [hNull, ProbabilityTheory.poissonMeasure_singleton]
    have hmeas : MeasurableSet {omega | N omega (m : ℝ≥0) A - N omega 0 A = 0} := by
      have h1 := hPPP.1 (m : ℝ≥0) A hAm
      have h2 := hPPP.1 0 A hAm
      exact (h1.sub h2) (measurableSet_singleton 0)
    rw [ae_iff_measure_eq hmeas.nullMeasurableSet, hval, hP1]
  have hall := ae_all_iff.2 hk
  filter_upwards [hall, hPPP.2.1] with omega hom hstr
  obtain ⟨h0, hadd, hmono⟩ := hstr
  have hzero : ∀ t : ℝ≥0, N omega t A = 0 := by
    intro t
    have h1 : N omega (⌈t⌉₊ : ℝ≥0) A = 0 := by
      have := hom ⌈t⌉₊
      rw [h0 A] at this
      simpa using this
    have h2 : N omega t A ≤ N omega (⌈t⌉₊ : ℝ≥0) A :=
      hmono A (Nat.le_ceil t)
    omega
  intro t
  constructor
  · have hd : Disjoint (B \ C) (B ∩ C) :=
      Set.disjoint_left.2 (fun x hx hx' => hx.2 hx'.2)
    have := hadd t (B \ C) (B ∩ C) hd
    rw [Set.sdiff_union_inter] at this
    rw [this, hzero t]; simp
  · have hd : Disjoint (C \ B) (C ∩ B) :=
      Set.disjoint_left.2 (fun x hx hx' => hx.2 hx'.2)
    have := hadd t (C \ B) (C ∩ B) hd
    rw [Set.sdiff_union_inter, Set.inter_comm] at this
    rw [this, hzero t]; simp

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNull : n (B ∩ C) = 0) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) ∧
      N omega t C = N omega t (C \ B) :=
  Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe P n N hPPP B C hB hC hNull
