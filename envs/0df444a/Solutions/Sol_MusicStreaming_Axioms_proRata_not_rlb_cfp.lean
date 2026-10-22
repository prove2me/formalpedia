-- Prove2me | solution 1 for MusicStreaming.Axioms.proRata_not_rlb_cfp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:07:58.496423+00:00
-- url     : https://prove2.me/submissions/1a10be06-aa74-4518-bf33-afec71d4409d

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

section MSA2
variable {n : ℕ}

lemma msa2_two_supp (u v : Fin n → ℕ) (hu : u ≠ 0) (hv : v ≠ 0) :
    (Finsupp.single 0 u + Finsupp.single 1 v : Problem n).support = {0, 1} := by
  have h0 : (Finsupp.single (0:ℕ) u).support = {0} := Finsupp.support_single_ne_zero 0 hu
  have h1 : (Finsupp.single (1:ℕ) v).support = {1} := Finsupp.support_single_ne_zero 1 hv
  have hd : Disjoint (Finsupp.single (0:ℕ) u).support (Finsupp.single (1:ℕ) v).support := by
    rw [h0, h1]; simp
  rw [Finsupp.support_add_eq hd, h0, h1]; rfl

lemma msa2_two_pr (u v : Fin n → ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (i : Fin n) :
    proRata (Finsupp.single 0 u + Finsupp.single 1 v : Problem n) i = (u i : ℝ) + v i := by
  simp [proRata, artistTotal, msa2_two_supp u v hu hv]

lemma msa2_two_reward (u v : Fin n → ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (i : Fin n) :
    reward (proRata (n := n)) (Finsupp.single 0 u + Finsupp.single 1 v : Problem n) i
      = ((u i : ℝ) + v i) / (∑ i', ((u i' : ℝ) + v i')) * 2 := by
  unfold reward
  rw [msa2_two_pr u v hu hv, msa2_two_supp u v hu hv]
  simp only [msa2_two_pr u v hu hv]
  simp

end MSA2

theorem solution {n : ℕ} (hn : 2 ≤ n) :
    ¬ ReasonableLowerBound (proRata (n := n)) ∧ ¬ ClickFraudProof (proRata (n := n)) := by
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set a : Fin n → ℕ := Pi.single i0 10 with ha
  set b : Fin n → ℕ := Pi.single i1 90 with hb
  set b' : Fin n → ℕ := Pi.single i1 2 with hb'
  have ha0 : a ≠ 0 := by
    intro h; have := congrFun h i0; simp [ha] at this
  have hb0 : b ≠ 0 := by
    intro h; have := congrFun h i1; simp [hb] at this
  have hb0' : b' ≠ 0 := by
    intro h; have := congrFun h i1; simp [hb'] at this
  have hsum : ∑ i', ((a i' : ℝ) + b i') = 100 := by
    rw [Finset.sum_add_distrib]
    simp [ha, hb, Pi.single_apply]
    norm_num
  have hsum' : ∑ i', ((a i' : ℝ) + b' i') = 12 := by
    rw [Finset.sum_add_distrib]
    simp [ha, hb', Pi.single_apply]
    norm_num
  have ai0 : (a i0 : ℝ) = 10 := by simp [ha]
  have ai1 : (a i1 : ℝ) = 0 := by simp [ha, h01.symm]
  have bi1 : (b i1 : ℝ) = 90 := by simp [hb]
  have bi1' : (b' i1 : ℝ) = 2 := by simp [hb']
  have bi0 : (b i0 : ℝ) = 0 := by simp [hb, h01]
  constructor
  · intro h
    have := h (Finsupp.single 0 a + Finsupp.single 1 b) {0} (by
      rw [msa2_two_supp a b ha0 hb0]; simp)
    have hL : ({0} : Finset ℕ).biUnion (listened (Finsupp.single 0 a + Finsupp.single 1 b : Problem n)) = {i0} := by
      ext i
      simp [listened, ha, Pi.single_apply]
      by_cases h : i = i0 <;> simp [h]
    rw [hL, Finset.sum_singleton, msa2_two_reward a b ha0 hb0, hsum, ai0, bi0] at this
    norm_num at this
  · intro h
    have := h (Finsupp.single 0 a + Finsupp.single 1 b) (Finsupp.single 0 a + Finsupp.single 1 b') 1
      (by rw [msa2_two_supp a b ha0 hb0, msa2_two_supp a b' ha0 hb0'])
      (by rw [msa2_two_supp a b ha0 hb0]; simp) (by
        intro j' hj'
        simp [Finsupp.single_apply, Ne.symm hj']) i1
    rw [msa2_two_reward a b ha0 hb0, msa2_two_reward a b' ha0 hb0', hsum, hsum', ai1, bi1, bi1'] at this
    norm_num [abs_le] at this
