-- Prove2me | solution 1 for MusicStreaming.Axioms.proRata_axioms
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:23:13.081788+00:00
-- url     : https://prove2.me/submissions/4e139b2f-d0b7-47b4-8804-ddaae2d85700

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

section MSA2
variable {n : ℕ}

lemma msa2_wi_hom (ω : ℕ → (Fin n → ℕ) → ℝ) : Homogeneity (weightedIndex ω) := by
  intro t i i' c hc h
  unfold weightedIndex
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j hj]; ring

lemma msa2_wi_add (ω : ℕ → (Fin n → ℕ) → ℝ) : Additivity (weightedIndex ω) := by
  intro t₁ t₂ hd
  funext i
  have h1 : ∀ j ∈ t₁.support, (t₁ + t₂) j = t₁ j := fun j hj => by
    have : t₂ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hj)
    simp [this]
  have h2 : ∀ j ∈ t₂.support, (t₁ + t₂) j = t₂ j := fun j hj => by
    have : t₁ j = 0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd hj)
    simp [this]
  simp only [weightedIndex, Pi.add_apply]
  rw [Finsupp.support_add_eq hd, Finset.sum_union hd]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [h1 j hj]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [h2 j hj]

lemma msa2_proRata_eq : proRata (n := n) = weightedIndex (fun _ _ => 1) := by
  funext t i
  simp [proRata, artistTotal, weightedIndex, Nat.cast_sum]

lemma msa2_proRata_erase (t : Problem n) (j : ℕ) (hj : j ∈ t.support) (i : Fin n) :
    proRata (t.erase j) i = proRata t i - t j i := by
  simp only [proRata, artistTotal]
  rw [Finsupp.support_erase]
  push_cast
  rw [Finset.sum_congr rfl (fun k hk => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hk)])]
  have := Finset.add_sum_erase t.support (fun k => (t k i : ℝ)) hj
  linarith

lemma msa2_userTotal_pos (t : Problem n) (k : ℕ) (hk : k ∈ t.support) : 0 < userTotal t k := by
  by_contra h
  have h0 : userTotal t k = 0 := by omega
  unfold userTotal at h0
  have : t k = 0 := by
    funext i
    exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
  exact (Finsupp.mem_support_iff.mp hk) this

lemma msa2_uc_col (t : Problem n) (k : ℕ) (hk : k ∈ t.support) :
    ∑ i, (t k i : ℝ) / userTotal t k = 1 := by
  have hp : (0 : ℝ) < userTotal t k := by exact_mod_cast msa2_userTotal_pos t k hk
  rw [← Finset.sum_div]
  have : (∑ i, (t k i : ℝ)) = userTotal t k := by simp [userTotal]
  rw [this]; exact div_self hp.ne'

lemma msa2_uc_eq : userCentric (n := n) = weightedIndex (fun _ x => 1 / ∑ i', (x i' : ℝ)) := by
  funext t i
  simp only [userCentric, weightedIndex, userTotal]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [one_div, inv_mul_eq_div]

lemma msa2_uc_erase_sum (t : Problem n) (j : ℕ) (hj : j ∈ t.support) :
    ∑ i, userCentric (t.erase j) i = (t.support.card : ℝ) - 1 := by
  unfold userCentric
  rw [Finsupp.support_erase, Finset.sum_comm]
  have : ∀ k ∈ t.support.erase j, ∑ i, ((t.erase j) k i : ℝ) / userTotal (t.erase j) k = 1 := by
    intro k hk
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hkt : k ∈ t.support := Finset.mem_of_mem_erase hk
    have e : (t.erase j) k = t k := Finsupp.erase_ne hkj
    have e2 : userTotal (t.erase j) k = userTotal t k := by simp [userTotal, e]
    rw [e2]
    simp only [e]
    exact msa2_uc_col t k hkt
  rw [Finset.sum_congr rfl this]
  simp [Finset.card_erase_of_mem hj, Nat.cast_sub (Finset.card_pos.mpr ⟨j, hj⟩)]

end MSA2

theorem solution {n : ℕ} :
    Homogeneity (proRata (n := n)) ∧ Additivity (proRata (n := n)) ∧
      EqualIndividualImpact (proRata (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [msa2_proRata_eq]; exact msa2_wi_hom _
  · rw [msa2_proRata_eq]; exact msa2_wi_add _
  · intro t i j j' hj hj' h
    rw [msa2_proRata_erase t j hj, msa2_proRata_erase t j' hj', h]
