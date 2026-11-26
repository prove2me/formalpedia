-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_offLattice_chunk
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T09:24:38.926152+00:00
-- url     : https://prove2.me/submissions/25cc9553-daef-4615-94e8-4d493bca34ac

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 →
      ∃ a b : Real, 0 < a ∧ a ≤ b ∧
        (∀ z ∈ Set.Icc a b, ∀ n : Int, z ≠ (n : Real) * h) ∧
        0 < Pi (Set.Icc a b)) := by
  intro hfin h hh hne
  obtain ⟨-, -, hsupp, -, -⟩ := hTriplet
  set off : Set Real := {z : Real | ∀ n : Int, z ≠ (n : Real) * h} with hoff
  have hcover : off ⊆ (off ∩ Set.Ioi (0 : Real)) ∪ Set.Iic (0 : Real) := by
    intro z hz
    by_cases hz0 : 0 < z
    · exact Or.inl ⟨hz, hz0⟩
    · exact Or.inr (not_lt.mp hz0)
  have hle : Pi off ≤ Pi (off ∩ Set.Ioi (0 : Real)) := by
    calc Pi off ≤ Pi ((off ∩ Set.Ioi (0 : Real)) ∪ Set.Iic (0 : Real)) :=
        measure_mono hcover
    _ ≤ Pi (off ∩ Set.Ioi (0 : Real)) + Pi (Set.Iic (0 : Real)) :=
        measure_union_le _ _
    _ = Pi (off ∩ Set.Ioi (0 : Real)) := by rw [hsupp, add_zero]
  have hne2 : Pi (off ∩ Set.Ioi (0 : Real)) ≠ 0 := by
    intro h0
    rw [h0] at hle
    exact hne (le_antisymm hle bot_le)
  have hsub : off ∩ Set.Ioi (0 : Real) ⊆
      ⋃ n : Int, (Set.Ioo ((n : Real) * h) (((n : Real) + 1) * h) ∩ Set.Ioi (0 : Real)) := by
    intro z hz
    obtain ⟨hzoff, hz0⟩ := hz
    refine Set.mem_iUnion.mpr ⟨⌊z / h⌋, ⟨?_, hz0⟩⟩
    have h1 : ((⌊z / h⌋ : Int) : Real) ≤ z / h := Int.floor_le _
    have h2 : z / h < ((⌊z / h⌋ : Int) : Real) + 1 := Int.lt_floor_add_one _
    have hle1 : (⌊z / h⌋ : Real) * h ≤ z := (le_div_iff₀ hh).mp h1
    have hlt1 : z < ((⌊z / h⌋ : Real) + 1) * h := (div_lt_iff₀ hh).mp h2
    exact ⟨lt_of_le_of_ne hle1 (Ne.symm (hzoff ⌊z / h⌋)), hlt1⟩
  obtain ⟨n, hn⟩ : ∃ n : Int,
      Pi (Set.Ioo ((n : Real) * h) (((n : Real) + 1) * h) ∩ Set.Ioi (0 : Real)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle2 : Pi (off ∩ Set.Ioi (0 : Real)) ≤
        Pi (⋃ n : Int, (Set.Ioo ((n : Real) * h) (((n : Real) + 1) * h) ∩ Set.Ioi (0 : Real))) :=
      measure_mono hsub
    rw [measure_iUnion_null hall] at hle2
    exact hne2 (le_antisymm hle2 bot_le)
  set A : Real := (n : Real) * h with hA
  set B : Real := ((n : Real) + 1) * h with hB
  have hBAeq : B - A = h := by rw [hA, hB]; ring
  have hBA : 0 < B - A := by rw [hBAeq]; exact hh
  have hT : 0 < Pi (Set.Ioo A B ∩ Set.Ioi (0 : Real)) :=
    pos_iff_ne_zero.mpr hn
  set L : ℕ → Real := fun k => max (A + (B - A) / (k + 2)) (1 / (k + 1)) with hL
  set Uu : ℕ → Real := fun k => B - (B - A) / (k + 2) with hU
  have hdivanti : ∀ k k' : ℕ, k ≤ k' → (B - A) / (k' + 2) ≤ (B - A) / (k + 2) := by
    intro k k' hk
    have hkk : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
    rw [div_le_iff₀ (by positivity : (0 : Real) < (k' : Real) + 2), div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0 : Real) < (k : Real) + 2)]
    exact mul_le_mul_of_nonneg_left (by linarith : (k : Real) + 2 ≤ (k' : Real) + 2) hBA.le
  have hmono : Monotone (fun k => Set.Icc (L k) (Uu k)) := by
    intro k k' hk
    have hkk : (k : Real) ≤ (k' : Real) := by exact_mod_cast hk
    have hd := hdivanti k k' hk
    apply Set.Icc_subset_Icc
    · simp only [hL]
      apply max_le_max
      · linarith
      · exact one_div_le_one_div_of_le (by positivity : (0 : Real) < (k : Real) + 1)
          (by linarith : (k : Real) + 1 ≤ (k' : Real) + 1)
    · simp only [hU]
      linarith
  have hsub2 : ∀ k : ℕ, Set.Icc (L k) (Uu k) ⊆ Set.Ioo A B ∩ Set.Ioi (0 : Real) := by
    intro k z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hpos1 : (0 : Real) < 1 / ((k : Real) + 1) := by positivity
    have hpos2 : (0 : Real) < (B - A) / ((k : Real) + 2) := div_pos hBA (by positivity)
    have hL1 : A + (B - A) / ((k : Real) + 2) ≤ L k := le_max_left _ _
    have hL2 : 1 / ((k : Real) + 1) ≤ L k := le_max_right _ _
    have hUeq : Uu k = B - (B - A) / ((k : Real) + 2) := rfl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact lt_of_lt_of_le (lt_add_of_pos_right A hpos2) (le_trans hL1 hz1)
    · exact lt_of_le_of_lt hz2 (by rw [hUeq]; exact sub_lt_self B hpos2)
    · exact lt_of_lt_of_le hpos1 (le_trans hL2 hz1)
  have hcover2 : Set.Ioo A B ∩ Set.Ioi (0 : Real) ⊆
      ⋃ k : ℕ, Set.Icc (L k) (Uu k) := by
    intro z hz
    obtain ⟨⟨hzA, hzB⟩, hz0⟩ := hz
    obtain ⟨k1, hk1⟩ := exists_nat_one_div_lt (show (0 : Real) < z from hz0)
    obtain ⟨k2, hk2⟩ := exists_nat_one_div_lt
      (show (0 : Real) < (z - A) / (B - A) from div_pos (sub_pos.mpr hzA) hBA)
    obtain ⟨k3, hk3⟩ := exists_nat_one_div_lt
      (show (0 : Real) < (B - z) / (B - A) from div_pos (sub_pos.mpr hzB) hBA)
    set K : ℕ := max (max k1 k2) k3 with hKdef
    have hK1 : (k1 : Real) ≤ (K : Real) := by
      have h1 : k1 ≤ K := le_max_of_le_left (le_max_left _ _)
      exact_mod_cast h1
    have hK2 : (k2 : Real) ≤ (K : Real) := by
      have h2 : k2 ≤ K := le_max_of_le_left (le_max_right _ _)
      exact_mod_cast h2
    have hK3 : (k3 : Real) ≤ (K : Real) := by
      have h3 : k3 ≤ K := le_max_right _ _
      exact_mod_cast h3
    have hstep1 : 1 / ((K : Real) + 1) ≤ 1 / ((k1 : Real) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hdivK : ∀ j : ℕ, (j : Real) ≤ (K : Real) →
        (B - A) / ((K : Real) + 2) ≤ (B - A) / ((j : Real) + 1) := by
      intro j hj
      have e1 : (B - A) / ((K : Real) + 2) = (B - A) * (1 / ((K : Real) + 2)) := by
        rw [div_eq_mul_one_div]
      have e2 : (B - A) / ((j : Real) + 1) = (B - A) * (1 / ((j : Real) + 1)) := by
        rw [div_eq_mul_one_div]
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity) (by linarith)) hBA.le
    have hstep2 : (B - A) / ((K : Real) + 2) < z - A := by
      refine lt_of_le_of_lt (hdivK k2 hK2) ?_
      rw [div_eq_mul_one_div]
      have h4 := (lt_div_iff₀ hBA).mp hk2
      rw [mul_comm] at h4
      exact h4
    have hstep3 : (B - A) / ((K : Real) + 2) < B - z := by
      refine lt_of_le_of_lt (hdivK k3 hK3) ?_
      rw [div_eq_mul_one_div]
      have h4 := (lt_div_iff₀ hBA).mp hk3
      rw [mul_comm] at h4
      exact h4
    refine Set.mem_iUnion.mpr ⟨K, ?_, ?_⟩
    · simp only [hL]
      apply max_le
      · linarith
      · exact le_of_lt (lt_of_le_of_lt hstep1 hk1)
    · have hUeq : Uu K = B - (B - A) / ((K : Real) + 2) := rfl
      rw [hUeq]
      linarith
  have hTeq : Set.Ioo A B ∩ Set.Ioi (0 : Real) = ⋃ k : ℕ, Set.Icc (L k) (Uu k) :=
    Set.Subset.antisymm hcover2 (Set.iUnion_subset hsub2)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Pi (Set.Icc (L k) (Uu k)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle3 : Pi (Set.Ioo A B ∩ Set.Ioi (0 : Real)) ≤
        ∑' k : ℕ, Pi (Set.Icc (L k) (Uu k)) := by
      rw [hTeq]; exact measure_iUnion_le _
    rw [tsum_congr hall] at hle3
    simp only [tsum_zero] at hle3
    exact hn (le_antisymm hle3 bot_le)
  refine ⟨L k, Uu k, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity : (0 : Real) < 1 / ((k : Real) + 1)) (le_max_right _ _)
  · by_contra hcon
    have hempty : Set.Icc (L k) (Uu k) = ∅ := Set.Icc_eq_empty hcon
    rw [hempty, measure_empty] at hk
    exact hk rfl
  · intro z hz m hzm
    have hzT := hsub2 k hz
    obtain ⟨⟨hzA, hzB⟩, -⟩ := hzT
    have hzA' : (n : Real) * h < z := hzA
    have hzB' : z < ((n : Real) + 1) * h := hzB
    rw [hzm] at hzA' hzB'
    clear hzA hzB
    rename_i hzA hzB
    have h1 : (n : Real) < (m : Real) := by
      have hlt : (n : Real) * h < (m : Real) * h := hzA'
      exact lt_of_mul_lt_mul_right hlt hh.le
    have h2 : m ≤ n := by
      have hlt : (m : Real) * h < ((n : Real) + 1) * h := hzB'
      have hlt2 : (m : Real) < (n : Real) + 1 := lt_of_mul_lt_mul_right hlt hh.le
      have h3 : m < n + 1 := by exact_mod_cast hlt2
      exact Int.lt_add_one_iff.mp h3
    have h1' : n < m := by exact_mod_cast h1
    omega
  · exact pos_iff_ne_zero.mpr hk
