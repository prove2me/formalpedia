-- Prove2me | solution 1 for MusicStreaming.Axioms.theorem_1a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:58:13.058166+00:00
-- url     : https://prove2.me/submissions/e8170771-2b4a-415d-a8f1-4e81d2559fda

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

set_option autoImplicit false
open MusicStreaming.Axioms

section MSA2
variable {n : ℕ}

lemma msa2_I_zero (I : Index n) (hA : Additivity I) : I 0 = 0 := by
  funext i
  have h2 : I 0 i = I 0 i + I 0 i := by simpa using congrFun (hA 0 0 (by simp)) i
  show I 0 i = 0
  linarith

lemma msa2_decomp (I : Index n) (hA : Additivity I) :
    ∀ (N : ℕ) (t : Problem n), t.support.card = N → ∀ i,
      I t i = ∑ j ∈ t.support, I (Finsupp.single j (t j)) i := by
  intro N
  induction N with
  | zero =>
    intro t ht i
    have h1 : t.support = ∅ := Finset.card_eq_zero.mp ht
    have h2 : t = 0 := Finsupp.support_eq_empty.mp h1
    subst h2
    simp [msa2_I_zero I hA]
  | succ N ih =>
    intro t ht i
    obtain ⟨j, hj⟩ : t.support.Nonempty := Finset.card_pos.mp (by omega)
    have htj : t j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have hsplit : t = Finsupp.single j (t j) + t.erase j := (Finsupp.single_add_erase j t).symm
    have hd : Disjoint (Finsupp.single j (t j)).support (t.erase j).support := by
      rw [Finsupp.support_single_ne_zero j htj, Finsupp.support_erase]; simp
    have hcard : (t.erase j).support.card = N := by
      rw [Finsupp.support_erase, Finset.card_erase_of_mem hj]; omega
    have h1 := congrFun (hA _ _ hd) i
    rw [← hsplit] at h1
    simp only [Pi.add_apply] at h1
    rw [h1, ih (t.erase j) hcard i, ← Finset.add_sum_erase t.support _ hj, Finsupp.support_erase]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hk)]

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

lemma msa2_one_user {n : ℕ} (I : Index n) (hH : Homogeneity I) :
    ∀ (j : ℕ) (x : Fin n → ℕ), x ≠ 0 → ∀ i : Fin n,
      I (Finsupp.single j x) i =
        (∑ i', I (Finsupp.single j x) i') / (∑ i', (x i' : ℝ)) * x i := by
  intro j x hx i
  set t : Problem n := Finsupp.single j x with ht
  have hsupp : t.support = {j} := Finsupp.support_single_ne_zero j hx
  have hcol : ∀ j' ∈ t.support, t j' = x := by
    intro j' hj'
    rw [hsupp] at hj'
    have : j' = j := by simpa using hj'
    subst this
    simp [t]
  have hT : 0 < ∑ i', (x i' : ℝ) := by
    obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
      ⟨i0, Finset.mem_univ _, by exact_mod_cast Nat.pos_of_ne_zero hi0⟩
  have key : ∀ i i' : Fin n, I t i * x i' = I t i' * x i := by
    intro i i'
    by_cases h : x i' = 0
    · have h1 := hH t i' i 0 le_rfl (by
        intro j' hj'
        rw [hcol j' hj']
        simp [h])
      have : I t i' = 0 := by simpa using h1
      simp [h, this]
    · have hpos : (x i' : ℝ) ≠ 0 := by exact_mod_cast h
      have h1 := hH t i i' ((x i : ℝ) / x i') (by positivity) (by
        intro j' hj'
        rw [hcol j' hj']
        field_simp)
      rw [h1]
      field_simp
  rw [div_mul_eq_mul_div, eq_div_iff hT.ne', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => key i i'

end MSA2

theorem solution {n : ℕ} (I : Index n) (hI : IsIndex I) :
    Homogeneity I ∧ Additivity I ↔
      ∃ ω : ℕ → (Fin n → ℕ) → ℝ, (∀ j x, 0 < ω j x) ∧ ∀ t, I t = weightedIndex ω t := by
  constructor
  · rintro ⟨hH, hA⟩
    classical
    refine ⟨fun j x => if x = 0 then 1 else (∑ i', I (Finsupp.single j x) i') / (∑ i', (x i' : ℝ)), ?_, ?_⟩
    · intro j x
      by_cases hx : x = 0
      · simp [hx]
      · simp only [hx, if_false]
        have h1 : 0 < ∑ i', I (Finsupp.single j x) i' :=
          (hI _ (by
            intro h
            have := congrArg (fun f => f j) h
            simp at this
            exact hx this)).2
        have h2 : 0 < ∑ i', (x i' : ℝ) := by
          obtain ⟨i0, hi0⟩ : ∃ i0, x i0 ≠ 0 := by
            by_contra h
            push_neg at h
            exact hx (funext h)
          exact Finset.sum_pos' (fun _ _ => Nat.cast_nonneg _)
            ⟨i0, Finset.mem_univ _, by exact_mod_cast Nat.pos_of_ne_zero hi0⟩
        exact div_pos h1 h2
    · intro t
      funext i
      rw [msa2_decomp I hA _ t rfl i]
      unfold weightedIndex
      refine Finset.sum_congr rfl fun j hj => ?_
      have hx : t j ≠ 0 := Finsupp.mem_support_iff.mp hj
      rw [msa2_one_user I hH j (t j) hx i]
      simp [hx]
  · rintro ⟨ω, -, hω⟩
    have : I = weightedIndex ω := funext hω
    subst this
    exact ⟨msa2_wi_hom ω, msa2_wi_add ω⟩
