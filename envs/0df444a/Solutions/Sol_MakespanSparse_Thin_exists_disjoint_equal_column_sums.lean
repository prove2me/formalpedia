-- Prove2me | solution 1 for MakespanSparse.Thin.exists_disjoint_equal_column_sums
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:43:03.955928+00:00
-- url     : https://prove2.me/submissions/48381d50-d537-4024-9b1f-89ae4fbfc46e

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

open MakespanSparse.Thin

/-- The counting inequality of Lemma 2: `s > 2(d+1) log₂(4(d+1)T)` forces
`(sT+1)^(d+1) < 2^s`. -/
lemma MSThinL2_count (d T s : ℕ) (hT : 0 < T)
    (hs : (s : ℝ) > 2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T)) :
    (s * T + 1) ^ (d + 1) < 2 ^ s := by
  set D : ℝ := (d : ℝ) + 1 with hDdef
  have hD : (1 : ℝ) ≤ D := by simp [hDdef]
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set y : ℝ := (s : ℝ) / (2 * D) with hy
  have hsy : (s : ℝ) = 2 * D * y := by rw [hy]; field_simp
  have h4 : (1 : ℝ) < 4 * D * T := by nlinarith
  have hlog : Real.logb 2 (4 * D * T) < y := by
    rw [hy, lt_div_iff₀ (by positivity)]; linarith
  have hy0 : 0 < y := lt_trans (Real.logb_pos (by norm_num) h4) hlog
  have h2y : 4 * D * T < (2 : ℝ) ^ y :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).1 hlog
  have hexp : y / 2 + 1 ≤ (2 : ℝ) ^ y := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have := Real.add_one_le_exp (Real.log 2 * y)
    have hl := Real.log_two_gt_d9
    nlinarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ y := by positivity
  have hmain : (s : ℝ) * T + 1 < (2 : ℝ) ^ (2 * y) := by
    have e : (2 : ℝ) ^ (2 * y) = (2 : ℝ) ^ y * (2 : ℝ) ^ y := by
      rw [two_mul, Real.rpow_add (by norm_num)]
    rw [e, hsy]
    have h1 : 2 * D * y * T = (y / 2) * (4 * D * T) := by ring
    rw [h1]
    have h2 : (y / 2) * (4 * D * T) < (y / 2) * (2 : ℝ) ^ y :=
      mul_lt_mul_of_pos_left h2y (by positivity)
    nlinarith
  have hpow : ((s : ℝ) * T + 1) ^ (d + 1) < ((2 : ℝ) ^ (2 * y)) ^ (d + 1) :=
    pow_lt_pow_left₀ hmain (by positivity) (by omega)
  have e2 : ((2 : ℝ) ^ (2 * y)) ^ (d + 1) = (2 : ℝ) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
    congr 1
    rw [hsy]; push_cast; rw [hDdef]; ring
  rw [e2] at hpow
  exact_mod_cast hpow

theorem solution (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T)
    (x : (Fin d → ℕ) →₀ ℕ) (hx : ∀ c ∈ x.support, IsConfig π T c)
    (hs : (x.support.card : ℝ) > 2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T)) :
    ∃ A B : Finset (Fin d → ℕ), A ⊆ x.support ∧ B ⊆ x.support ∧ Disjoint A B ∧
      A.Nonempty ∧ B.Nonempty ∧ ∑ c ∈ A, c = ∑ c ∈ B, c ∧ A.card = B.card := by
  classical
  set s := x.support.card with hsdef
  have hcount := MSThinL2_count d T s hT hs
  -- each coordinate of a configuration is at most `T`
  have hcoord : ∀ c ∈ x.support, ∀ k, c k ≤ T := by
    intro c hc k
    have h1 : π k * c k ≤ ∑ j, π j * c j :=
      Finset.single_le_sum (f := fun j => π j * c j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : c k ≤ π k * c k := Nat.le_mul_of_pos_left _ (hπ k)
    exact le_trans h2 (le_trans h1 (hx c hc))
  let f : Finset (Fin d → ℕ) → (Fin d → ℕ) × ℕ := fun A => (∑ c ∈ A, c, A.card)
  let t : Finset ((Fin d → ℕ) × ℕ) :=
    Fintype.piFinset (fun _ => Finset.range (s * T + 1)) ×ˢ Finset.range (s * T + 1)
  have htcard : t.card = (s * T + 1) ^ (d + 1) := by
    simp [t, Finset.card_product, Fintype.card_piFinset, pow_succ]
  have hmaps : ∀ A ∈ x.support.powerset, f A ∈ t := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    have hAc : A.card ≤ s := Finset.card_le_card hA
    simp only [t, f, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun k => ?_, ?_⟩
    · rw [Finset.sum_apply]
      have : ∑ c ∈ A, c k ≤ ∑ c ∈ A, T := Finset.sum_le_sum fun c hc => hcoord c (hA hc) k
      rw [Finset.sum_const, smul_eq_mul] at this
      have : A.card * T ≤ s * T := Nat.mul_le_mul_right _ hAc
      omega
    · have : s ≤ s * T := Nat.le_mul_of_pos_right _ hT
      omega
  have hlt : t.card < x.support.powerset.card := by
    rw [htcard, Finset.card_powerset]; exact hcount
  obtain ⟨A', hA', B', hB', hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [Finset.mem_powerset] at hA' hB'
  simp only [f, Prod.mk.injEq] at hfeq
  obtain ⟨hsum, hcard⟩ := hfeq
  have splitS : ∀ P Q : Finset (Fin d → ℕ), ∑ c ∈ P, c = ∑ c ∈ P \ Q, c + ∑ c ∈ P ∩ Q, c := by
    intro P Q
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter P Q), Finset.sdiff_union_inter]
  have hcardA := Finset.card_sdiff_add_card_inter A' B'
  have hcardB := Finset.card_sdiff_add_card_inter B' A'
  rw [Finset.inter_comm] at hcardB
  have hsumAB : ∑ c ∈ A' \ B', c = ∑ c ∈ B' \ A', c := by
    have h1 := splitS A' B'
    have h2 := splitS B' A'
    rw [Finset.inter_comm] at h2
    rw [hsum, h2] at h1
    exact (add_right_cancel h1).symm
  have hcardAB : (A' \ B').card = (B' \ A').card := by omega
  refine ⟨A' \ B', B' \ A', fun c hc => hA' (Finset.mem_sdiff.1 hc).1,
    fun c hc => hB' (Finset.mem_sdiff.1 hc).1, disjoint_sdiff_sdiff, ?_, ?_, hsumAB, hcardAB⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have hsub : A' ⊆ B' := Finset.sdiff_eq_empty_iff_subset.1 hE
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  · rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have hsub : B' ⊆ A' := Finset.sdiff_eq_empty_iff_subset.1 hE
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
