-- Prove2me | solution 1 for IdentityTesting39.ExactRadius.eq_7_tv_branches
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:37:00.123323+00:00
-- url     : https://prove2.me/submissions/6f5758b1-82d9-454f-9aee-94d9e731b03b

import Definitions.Def_IdentityTesting39_ExactRadius_MomentPrograms

open scoped BigOperators

open IdentityTesting39.ExactRadius MeasureTheory

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (i₀ : ι) (hp : ProbabilityVector p) (hq : ProbabilityVector q) :
    FoundationsRL.GeneralDM.totalVariationDiscrete p q = max (∑ i ∈ Finset.univ.erase i₀, max (q i-p i) 0)
      (∑ i ∈ Finset.univ.erase i₀, max (p i-q i) 0) ∧
    (∀ ε : ℝ, ε ≤ FoundationsRL.GeneralDM.totalVariationDiscrete p q →
      deterministicTuple q p (.excess i₀) ∈ feasibleMoments q ε (.excess i₀) ∨
      deterministicTuple q p (.deficit i₀) ∈ feasibleMoments q ε (.deficit i₀)) ∧
    (∀ ε : ℝ, ε < FoundationsRL.GeneralDM.totalVariationDiscrete p q →
      (ε < ∑ i ∈ Finset.univ.erase i₀, max (p i-q i) 0) ∨
      (ε < ∑ i ∈ Finset.univ.erase i₀, max (q i-p i) 0)) := by
  have hp0 : ∀ i, 0 ≤ p i := hp.1
  have hp1 : ∑ i, p i = 1 := hp.2
  have hq1 : ∑ i, q i = 1 := hq.2
  have hple : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp1]; exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hfullA : max (q i₀ - p i₀) 0 + ∑ i ∈ Finset.univ.erase i₀, max (q i - p i) 0
      = ∑ i, max (q i - p i) 0 :=
    Finset.add_sum_erase Finset.univ (fun i => max (q i - p i) 0) (Finset.mem_univ i₀)
  have hfullB : max (p i₀ - q i₀) 0 + ∑ i ∈ Finset.univ.erase i₀, max (p i - q i) 0
      = ∑ i, max (p i - q i) 0 :=
    Finset.add_sum_erase Finset.univ (fun i => max (p i - q i) 0) (Finset.mem_univ i₀)
  have habs : ∑ i, |p i - q i| = ∑ i, max (q i - p i) 0 + ∑ i, max (p i - q i) 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (p i) (q i) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have hdiff : ∑ i, max (p i - q i) 0 - ∑ i, max (q i - p i) 0 = 0 := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ i, max (p i - q i) 0 - max (q i - p i) 0 = p i - q i := by
      intro i
      rcases le_total (p i) (q i) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    simp only [this, Finset.sum_sub_distrib, hp1, hq1, sub_self]
  have hTVA : FoundationsRL.GeneralDM.totalVariationDiscrete p q = ∑ i, max (q i - p i) 0 := by
    unfold FoundationsRL.GeneralDM.totalVariationDiscrete
    rw [habs]; linarith
  have hTVB : FoundationsRL.GeneralDM.totalVariationDiscrete p q = ∑ i, max (p i - q i) 0 := by
    rw [hTVA]; linarith
  have h1 : FoundationsRL.GeneralDM.totalVariationDiscrete p q =
      max (∑ i ∈ Finset.univ.erase i₀, max (q i-p i) 0)
        (∑ i ∈ Finset.univ.erase i₀, max (p i-q i) 0) := by
    have hA0 : 0 ≤ max (q i₀ - p i₀) 0 := le_max_right _ _
    have hB0 : 0 ≤ max (p i₀ - q i₀) 0 := le_max_right _ _
    rcases le_total (p i₀) (q i₀) with h | h
    · have h0 : max (p i₀ - q i₀) 0 = 0 := max_eq_right (by linarith)
      rw [max_eq_right (by linarith)]; linarith
    · have h0 : max (q i₀ - p i₀) 0 = 0 := max_eq_right (by linarith)
      rw [max_eq_left (by linarith)]; linarith
  have hSM : ∀ i, ScalarMoments (q i) (p i) ((p i - q i)^2) (max (p i - q i) 0)
      (max (q i - p i) 0) := by
    intro i
    refine ⟨Measure.dirac (p i), inferInstance, ?_, ?_, ?_, ?_, ?_⟩
    · exact (ae_dirac_iff (p := fun u => u ∈ Set.Icc (0:ℝ) 1) measurableSet_Icc).2
        ⟨hp0 i, hple i⟩
    all_goals simp only [integral_dirac]
  have hdt : ∀ Br : Branch ι, quadraticCoords Br = Finset.univ.erase i₀ → ∀ i,
      deterministicTuple q p Br i = if i = i₀ then ![p i, 0, 0, 0]
        else ![p i, (p i - q i)^2, max (p i - q i) 0, max (q i - p i) 0] := by
    intro Br hBr i
    unfold deterministicTuple
    rw [hBr]
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  have hmem : ∀ Br : Branch ι, quadraticCoords Br = Finset.univ.erase i₀ → ∀ ε : ℝ,
      (match Br with
        | .excess _ => ε ≤ ∑ i ∈ quadraticCoords Br, deterministicTuple q p Br i 2
        | _ => ε ≤ ∑ i ∈ quadraticCoords Br, deterministicTuple q p Br i 3) →
      deterministicTuple q p Br ∈ feasibleMoments q ε Br := by
    intro Br hBr ε hlast
    refine ⟨?_, ?_, ?_, ?_, hlast⟩
    · intro i hi
      rw [hBr] at hi
      have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rw [hdt Br hBr i, if_neg hne]
      exact hSM i
    · intro i
      rw [hdt Br hBr i]
      split_ifs <;> exact hp0 i
    · rw [← hp1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hdt Br hBr i]
      split_ifs <;> rfl
    · intro i hi
      rw [hBr] at hi
      have : i = i₀ := by
        by_contra hne
        exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
      rw [hdt Br hBr i, if_pos this]
      simp
  have hsum : ∀ Br : Branch ι, quadraticCoords Br = Finset.univ.erase i₀ →
      (∑ i ∈ quadraticCoords Br, deterministicTuple q p Br i 2
          = ∑ i ∈ Finset.univ.erase i₀, max (p i - q i) 0) ∧
      (∑ i ∈ quadraticCoords Br, deterministicTuple q p Br i 3
          = ∑ i ∈ Finset.univ.erase i₀, max (q i - p i) 0) := by
    intro Br hBr
    rw [hBr]
    constructor
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [hdt Br hBr i, if_neg (Finset.ne_of_mem_erase hi)]; rfl
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [hdt Br hBr i, if_neg (Finset.ne_of_mem_erase hi)]; rfl
  refine ⟨h1, ?_, ?_⟩
  · intro ε hε
    rw [h1] at hε
    rcases le_max_iff.1 hε with h | h
    · right
      apply hmem _ rfl
      show ε ≤ ∑ i ∈ quadraticCoords (Branch.deficit i₀), deterministicTuple q p (.deficit i₀) i 3
      rw [(hsum _ rfl).2]; exact h
    · left
      apply hmem _ rfl
      show ε ≤ ∑ i ∈ quadraticCoords (Branch.excess i₀), deterministicTuple q p (.excess i₀) i 2
      rw [(hsum _ rfl).1]; exact h
  · intro ε hε
    rw [h1] at hε
    rcases lt_max_iff.1 hε with h | h
    · right; exact h
    · left; exact h
