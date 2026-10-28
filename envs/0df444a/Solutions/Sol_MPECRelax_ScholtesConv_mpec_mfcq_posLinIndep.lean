-- Prove2me | solution 1 for MPECRelax.ScholtesConv.mpec_mfcq_posLinIndep
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:58:15.806737+00:00
-- url     : https://prove2.me/submissions/a72042ca-4c79-4d5b-9f51-bc2259686258

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC

open MPECRelax.ScholtesConv in
theorem solution {n m p l : ℕ} (P : MPEC n m p l) (xs : E n)
    (hxs : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs)
    (lam : Fin m → ℝ) (mu : Fin p → ℝ) (γ ν : Fin l → ℝ)
    (hlam_nonneg : ∀ i, 0 ≤ lam i) (hlam_supp : ∀ i ∉ P.Ig xs, lam i = 0)
    (hγ_supp : ∀ i ∉ P.I00 xs ∪ P.I0p xs, γ i = 0)
    (hν_supp : ∀ i ∉ P.I00 xs ∪ P.Ip0 xs, ν i = 0)
    (hsum : ∑ i, lam i • gradient (P.g i) xs + ∑ i, mu i • gradient (P.h i) xs
      - ∑ i, γ i • gradient (P.G i) xs - ∑ i, ν i • gradient (P.H i) xs = 0) :
    lam = 0 ∧ mu = 0 ∧ γ = 0 ∧ ν = 0 := by
  classical
  obtain ⟨hLI, d, hd_act, hd_eq⟩ := hCQ
  have hh : ∀ i, inner ℝ (gradient (P.h i) xs) d = 0 := fun i => hd_eq (Sum.inl i)
  have hG : ∀ i ∈ P.I00 xs ∪ P.I0p xs, inner ℝ (gradient (P.G i) xs) d = 0 := fun i hi =>
    hd_eq (Sum.inr (Sum.inl ⟨i, (Set.union_comm _ _) ▸ hi⟩))
  have hH : ∀ i ∈ P.I00 xs ∪ P.Ip0 xs, inner ℝ (gradient (P.H i) xs) d = 0 := fun i hi =>
    hd_eq (Sum.inr (Sum.inr ⟨i, (Set.union_comm _ _) ▸ hi⟩))
  have hg : ∀ i ∈ P.Ig xs, inner ℝ (gradient (P.g i) xs) d < 0 := fun i hi =>
    hd_act (Sum.inl i) hi
  -- Step 1: lam = 0
  have hin := congrArg (fun v => inner ℝ v d) hsum
  simp only [inner_sub_left, inner_add_left, sum_inner, inner_smul_left, inner_zero_left,
    RCLike.conj_to_real] at hin
  have h2 : ∑ i, mu i * inner ℝ (gradient (P.h i) xs) d = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hh i, mul_zero]
  have h3 : ∑ i, γ i * inner ℝ (gradient (P.G i) xs) d = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hi : i ∈ P.I00 xs ∪ P.I0p xs
      · rw [hG i hi, mul_zero]
      · rw [hγ_supp i hi, zero_mul]
  have h4 : ∑ i, ν i * inner ℝ (gradient (P.H i) xs) d = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hi : i ∈ P.I00 xs ∪ P.Ip0 xs
      · rw [hH i hi, mul_zero]
      · rw [hν_supp i hi, zero_mul]
  have hnp : ∀ i, lam i * inner ℝ (gradient (P.g i) xs) d ≤ 0 := by
    intro i
    by_cases hi : i ∈ P.Ig xs
    · exact mul_nonpos_of_nonneg_of_nonpos (hlam_nonneg i) (hg i hi).le
    · rw [hlam_supp i hi, zero_mul]
  have h1 : ∑ i, lam i * inner ℝ (gradient (P.g i) xs) d = 0 := by linarith
  have hlam : lam = 0 := by
    funext i
    by_cases hi : i ∈ P.Ig xs
    · have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hnp i)).mp h1 i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (hg i hi).ne
    · exact hlam_supp i hi
  -- Step 2: linear independence
  rw [hlam] at hsum
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at hsum
  set S1 := P.I0p xs ∪ P.I00 xs
  set S2 := P.Ip0 xs ∪ P.I00 xs
  let c : (Fin p ⊕ ↥S1 ⊕ ↥S2) → ℝ := Sum.elim mu (Sum.elim (fun i => -γ i) (fun i => -ν i))
  have hsubG : ∑ i : ↥S1, (-γ i) • gradient (P.G i) xs = -∑ i, γ i • gradient (P.G i) xs := by
    rw [← Finset.sum_subtype (s := S1.toFinset) (p := fun i => i ∈ S1) (by simp)
      (fun i => (-γ i) • gradient (P.G i) xs)]
    rw [Finset.sum_subset (Finset.subset_univ _), ← Finset.sum_neg_distrib]
    · simp only [neg_smul]
    · intro i _ hi
      have : i ∉ P.I00 xs ∪ P.I0p xs := by
        rw [Set.union_comm]; simpa [S1] using hi
      rw [hγ_supp i this, neg_zero, zero_smul]
  have hsubH : ∑ i : ↥S2, (-ν i) • gradient (P.H i) xs = -∑ i, ν i • gradient (P.H i) xs := by
    rw [← Finset.sum_subtype (s := S2.toFinset) (p := fun i => i ∈ S2) (by simp)
      (fun i => (-ν i) • gradient (P.H i) xs)]
    rw [Finset.sum_subset (Finset.subset_univ _), ← Finset.sum_neg_distrib]
    · simp only [neg_smul]
    · intro i _ hi
      have : i ∉ P.I00 xs ∪ P.Ip0 xs := by
        rw [Set.union_comm]; simpa [S2] using hi
      rw [hν_supp i this, neg_zero, zero_smul]
  have hc : ∑ j, c j • gradient ((P.TNLP xs).h j) xs = 0 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr]
    change ∑ i, mu i • gradient (P.h i) xs + (∑ i : ↥S1, (-γ i) • gradient (P.G i) xs +
      ∑ i : ↥S2, (-ν i) • gradient (P.H i) xs) = 0
    rw [hsubG, hsubH, ← hsum]
    abel
  have hzero := Fintype.linearIndependent_iff.mp hLI c hc
  refine ⟨hlam, ?_, ?_, ?_⟩
  · funext i; exact hzero (Sum.inl i)
  · funext i
    by_cases hi : i ∈ S1
    · have := hzero (Sum.inr (Sum.inl ⟨i, hi⟩))
      simp only [c, Sum.elim_inr, Sum.elim_inl, neg_eq_zero] at this
      exact this
    · apply hγ_supp
      rw [Set.union_comm]; exact hi
  · funext i
    by_cases hi : i ∈ S2
    · have := hzero (Sum.inr (Sum.inr ⟨i, hi⟩))
      simp only [c, Sum.elim_inr, neg_eq_zero] at this
      exact this
    · apply hν_supp
      rw [Set.union_comm]; exact hi
