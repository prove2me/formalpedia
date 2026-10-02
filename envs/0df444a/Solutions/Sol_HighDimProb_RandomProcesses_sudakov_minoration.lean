-- Prove2me | solution 1 for HighDimProb.RandomProcesses.sudakov_minoration
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T11:06:53.283227+00:00
-- url     : https://prove2.me/submissions/684de715-ed09-4f78-a037-667ba4b7a472
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_CoveringNumber
import Definitions.Def_HighDimProb_RandomProcesses_CanonicalMetric
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_minoration_finite_separated

-- Inlined module: SudakovPacking
section

open MeasureTheory ProbabilityTheory HighDimProb.RandomProcesses

namespace SudakovProof

/-- A greedy finite packing is enough; no compactness or maximal infinite set is needed. -/
lemma separated_finset_of_coveringNumber_le {T : Type}
    (d : T → T → ℝ) (hd0 : ∀ t, d t t = 0) (hds : ∀ t s, d t s = d s t)
    (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (hN : (N : ℕ∞) ≤ coveringNumber d ε) :
    ∃ s : Finset T, s.card = N ∧ (s : Set T).Pairwise (fun t u => ε < d t u) := by
  classical
  induction N with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ n ih =>
    have hn : (n : ℕ∞) ≤ coveringNumber d ε :=
      (show (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ n).trans hN
    obtain ⟨s, hs, hpair⟩ := ih hn
    have hnot : ¬ ∀ t : T, ∃ u ∈ s, d t u ≤ ε := by
      intro hnet
      have hc : coveringNumber d ε ≤ (s.card : ℕ∞) :=
        iInf_le_of_le ⟨s, hnet⟩ le_rfl
      have hbad : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by simpa [hs] using hN.trans hc
      have : n + 1 ≤ n := by exact_mod_cast hbad
      omega
    push_neg at hnot
    obtain ⟨t, ht⟩ := hnot
    have hts : t ∉ s := by
      intro hmem
      have h := ht t hmem
      rw [hd0] at h
      linarith
    refine ⟨insert t s, by rw [Finset.card_insert_of_notMem hts, hs], ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hae | has
    · rcases Finset.mem_insert.mp hb with hbe | hbs
      · exact (hab (hae.trans hbe.symm)).elim
      · rw [hae]
        exact ht b hbs
    · rcases Finset.mem_insert.mp hb with hbe | hbs
      · rw [hbe, hds]
        exact ht a has
      · exact hpair has hbs hab

lemma canonicalMetric_self {Ω T : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : T → Ω → ℝ) (t : T) : canonicalMetric P X t t = 0 := by
  simp [canonicalMetric]

lemma canonicalMetric_symm {Ω T : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : T → Ω → ℝ) (t s : T) : canonicalMetric P X t s = canonicalMetric P X s t := by
  unfold canonicalMetric
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by ring)

lemma separated_finset_of_canonical_coveringNumber {Ω T : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : T → Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ)
    (hN : coveringNumber (canonicalMetric P X) ε = (N : ℕ∞)) :
    ∃ s : Finset T, s.card = N ∧ (s : Set T).Pairwise
      (fun t u => ε < canonicalMetric P X t u) :=
  separated_finset_of_coveringNumber_le (canonicalMetric P X)
    (canonicalMetric_self P X) (canonicalMetric_symm P X) ε hε N (by rw [hN])

end SudakovProof
end

-- Inlined module: SudakovMinorationReduction
section

open MeasureTheory ProbabilityTheory HighDimProb.RandomProcesses

namespace SudakovProof

abbrev FiniteSeparatedGaussianMinoration : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0)
      (ε : ℝ), 0 ≤ ε →
      (∀ i j, i ≠ j → ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P) →
      c * ε * Real.sqrt (Real.log (Fintype.card ι)) ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P

lemma centered_processESup_nonneg {Ω T : Type} [MeasurableSpace Ω] [Nonempty T]
    (P : Measure Ω) (X : T → Ω → ℝ) (hmean : ∀ t, ∫ ω, X t ω ∂P = 0) :
    0 ≤ processESup P X := by
  classical
  obtain ⟨t⟩ := ‹Nonempty T›
  unfold processESup
  apply le_iSup_of_le ⟨{t}, Finset.singleton_nonempty t⟩
  simp [hmean]

theorem sudakov_minoration_of_finite_separated (hfinite : FiniteSeparatedGaussianMinoration) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [Nonempty T] (X : T → Ω → ℝ)
        (hXG : IsGaussianProcess X P) (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0)
        (ε : ℝ), 0 ≤ ε →
        ∀ (N : ℕ), coveringNumber (canonicalMetric P X) ε = (N : ℕ∞) →
        ((c * ε * Real.sqrt (Real.log N) : ℝ) : EReal) ≤ processESup P X := by
  classical
  obtain ⟨c, hc, hfinite⟩ := hfinite
  refine ⟨c, hc, ?_⟩
  intro Ω _ P _ T _ X hXG hXmean ε hε N hN
  by_cases hzero : N = 0
  · simpa [hzero] using centered_processESup_nonneg P X hXmean
  have hpos : 0 < N := Nat.pos_of_ne_zero hzero
  obtain ⟨s, hsN, hsep⟩ := separated_finset_of_canonical_coveringNumber P X ε hε N hN
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty s := by obtain ⟨t, ht⟩ := hs; exact ⟨⟨t, ht⟩⟩
  have hinc (i j : s) (hij : i ≠ j) : ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P := by
    have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have hd := hsep i.property j.property hij'
    unfold canonicalMetric at hd
    have hv : 0 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P := integral_nonneg (fun _ => sq_nonneg _)
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg (∫ ω, (X i ω - X j ω) ^ 2 ∂P)]
  have h := hfinite P (fun i : s => X i) (hXG.comp_right Subtype.val)
    (fun i => hXmean i) ε hε hinc
  have hmax (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun i : s => X i ω) =
        s.sup' hs (fun i => X i ω) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact Finset.le_sup' (f := fun t => X t ω) i.property
    · apply Finset.sup'_le
      intro i hi
      exact Finset.le_sup' (f := fun t : s => X t ω) (Finset.mem_univ ⟨i, hi⟩)
  have hcard : Fintype.card s = N := by simpa using hsN
  simp only [hcard, hmax] at h
  calc
    ((c * ε * Real.sqrt (Real.log N) : ℝ) : EReal) ≤
        ((∫ ω, s.sup' hs (fun i => X i ω) ∂P : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr h
    _ ≤ processESup P X := le_iSup_of_le ⟨s, hs⟩ le_rfl

end SudakovProof
end

open MeasureTheory ProbabilityTheory HighDimProb.RandomProcesses

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {T : Type} [Nonempty T] (X : T → Ω → ℝ)
        (hXG : IsGaussianProcess X P) (hXmean : ∀ t, ∫ ω, X t ω ∂P = 0)
        (ε : ℝ), 0 ≤ ε →
        ∀ (N : ℕ), coveringNumber (canonicalMetric P X) ε = (N : ℕ∞) →
        ((c * ε * Real.sqrt (Real.log N) : ℝ) : EReal) ≤ processESup P X := by
  exact SudakovProof.sudakov_minoration_of_finite_separated
    HighDimProb.RandomProcesses.sudakov_minoration_finite_separated
