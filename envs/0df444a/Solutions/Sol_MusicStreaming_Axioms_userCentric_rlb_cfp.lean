-- Prove2me | solution 1 for MusicStreaming.Axioms.userCentric_rlb_cfp
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:12:50.017146+00:00
-- url     : https://prove2.me/submissions/ac1817d3-5908-4130-856b-abbcae66b2ec

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


lemma msa2_uc_total (t : Problem n) : ∑ i, userCentric t i = (t.support.card : ℝ) := by
  unfold userCentric
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun k hk => msa2_uc_col t k hk)]
  simp

lemma msa2_uc_reward (t : Problem n) (i : Fin n) : reward (userCentric (n := n)) t i = userCentric t i := by
  by_cases hc : t.support.card = 0
  · have : t.support = ∅ := Finset.card_eq_zero.mp hc
    simp [reward, userCentric, this]
  · unfold reward
    rw [msa2_uc_total]
    have : (t.support.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

end MSA2

theorem solution {n : ℕ} :
    ReasonableLowerBound (userCentric (n := n)) ∧ ClickFraudProof (userCentric (n := n)) := by
  constructor
  · intro t C hC
    simp only [msa2_uc_reward]
    set L := C.biUnion (listened t) with hL
    have hcol : ∀ j ∈ C, ∑ i ∈ L, (t j i : ℝ) / userTotal t j = 1 := by
      intro j hj
      have : ∑ i ∈ L, (t j i : ℝ) / userTotal t j = ∑ i, (t j i : ℝ) / userTotal t j := by
        refine Finset.sum_subset (Finset.subset_univ _) ?_
        intro i _ hiL
        have hi0 : ¬ (0 < t j i) := by
          intro hpos
          exact hiL (Finset.mem_biUnion.mpr ⟨j, hj, by simp [listened, hpos]⟩)
        have : t j i = 0 := by omega
        simp [this]
      rw [this]
      exact msa2_uc_col t j (hC hj)
    calc (C.card : ℝ) = ∑ j ∈ C, ∑ i ∈ L, (t j i : ℝ) / userTotal t j := by
          rw [Finset.sum_congr rfl hcol]; simp
      _ ≤ ∑ j ∈ t.support, ∑ i ∈ L, (t j i : ℝ) / userTotal t j := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hC ?_
          intro j _ _
          exact Finset.sum_nonneg fun i _ => by positivity
      _ = ∑ i ∈ L, userCentric t i := by
          rw [Finset.sum_comm]; rfl
  · intro t t' j hs hj hrest i
    rw [msa2_uc_reward, msa2_uc_reward]
    unfold userCentric
    rw [hs]
    rw [← Finset.add_sum_erase t.support _ hj, ← Finset.add_sum_erase t.support _ hj]
    have hr : ∑ k ∈ t.support.erase j, (t' k i : ℝ) / userTotal t' k
        = ∑ k ∈ t.support.erase j, (t k i : ℝ) / userTotal t k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hne := Finset.ne_of_mem_erase hk
      have e : userTotal t' k = userTotal t k := by unfold userTotal; rw [hrest k hne]
      rw [hrest k hne, e]
    rw [hr]
    have hb : ∀ s : Problem n, (s j i : ℝ) / userTotal s j ≤ 1 ∧ 0 ≤ (s j i : ℝ) / userTotal s j := by
      intro s
      refine ⟨?_, by positivity⟩
      by_cases h0 : userTotal s j = 0
      · simp [h0]
      · have hp : (0 : ℝ) < userTotal s j := by exact_mod_cast Nat.pos_of_ne_zero h0
        rw [div_le_one hp]
        have : s j i ≤ userTotal s j := Finset.single_le_sum (f := fun i => s j i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        exact_mod_cast this
    obtain ⟨a1, a2⟩ := hb t
    obtain ⟨b1, b2⟩ := hb t'
    rw [abs_le]
    constructor <;> linarith
