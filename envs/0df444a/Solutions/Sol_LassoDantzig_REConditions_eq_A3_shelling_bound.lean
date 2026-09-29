-- Prove2me | solution 1 for LassoDantzig.REConditions.eq_A3_shelling_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:08:24.029802+00:00
-- url     : https://prove2.me/submissions/4046fe78-eaae-4c59-bf1f-988c1cc38f57

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

theorem aux_a3sh_l1_nonneg {M : ℕ} (δ : Fin M → ℝ) (S : Finset (Fin M)) : 0 ≤ l1On δ S :=
  Finset.sum_nonneg (fun j _ => abs_nonneg (δ j))

theorem aux_a3sh_l2_nonneg {M : ℕ} (δ : Fin M → ℝ) (S : Finset (Fin M)) : 0 ≤ l2On δ S :=
  Real.sqrt_nonneg _

/-- Block bound: if every coordinate of `B` is dominated by every coordinate of `A`,
`|A| = m ≥ 1`, `|B| ≤ m`, then `|δ_B|₂ ≤ |δ_A|₁/√m`. -/
theorem aux_a3sh_block {M : ℕ} (δ : Fin M → ℝ) (A B : Finset (Fin M)) (m : ℕ) (hm : 1 ≤ m)
    (hA : A.card = m) (hB : B.card ≤ m)
    (hdom : ∀ a ∈ A, ∀ b ∈ B, |δ b| ≤ |δ a|) :
    l2On δ B ≤ l1On δ A / Real.sqrt m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set t : ℝ := l1On δ A / m with ht
  have hbt : ∀ b ∈ B, |δ b| ≤ t := by
    intro b hb
    rw [ht, le_div_iff₀ hmpos]
    have h1 : ∑ a ∈ A, |δ b| ≤ ∑ a ∈ A, |δ a| :=
      Finset.sum_le_sum (fun a ha => hdom a ha b hb)
    rw [Finset.sum_const, hA, nsmul_eq_mul] at h1
    unfold l1On
    linarith
  have hsum : ∑ j ∈ B, δ j ^ 2 ≤ (l1On δ A) ^ 2 / m := by
    calc ∑ j ∈ B, δ j ^ 2 ≤ ∑ j ∈ B, t ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hbt j hj) 2
      _ = (B.card : ℝ) * t ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * t ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact_mod_cast hB
      _ = (l1On δ A) ^ 2 / m := by
          rw [ht]; field_simp
  unfold l2On
  rw [Real.sqrt_le_iff]
  refine ⟨div_nonneg (aux_a3sh_l1_nonneg δ A) (Real.sqrt_nonneg _), ?_⟩
  rw [div_pow, Real.sq_sqrt hmpos.le]
  exact hsum

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s m : ℕ) (hm : 1 ≤ m) (c0 : ℝ) (hc0 : 0 < c0)
    (δ : Fin M → ℝ) (J0 : Finset (Fin M)) (J : ℕ → Finset (Fin M)) (K : ℕ)
    (hsh : IsShelling δ J0 m J K) :
    (∀ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1)) ≤ l1On δ (J k) / Real.sqrt m) ∧
    ∑ k ∈ Finset.Icc 2 K, l2On δ (J k) ≤ l1On δ J0ᶜ / Real.sqrt m ∧
    (J0.card ≤ s → ConeCond c0 J0 δ →
      l1On δ J0ᶜ / Real.sqrt m ≤ c0 * l1On δ J0 / Real.sqrt m ∧
      c0 * l1On δ J0 / Real.sqrt m ≤ c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ∧
      c0 * Real.sqrt ((s : ℝ) / m) * l2On δ J0 ≤
        c0 * Real.sqrt ((s : ℝ) / m) * l2On δ (J0 ∪ J 1)) := by
  obtain ⟨⟨hK, hdisj, hunion⟩, hcard, hcardK, hmono⟩ := hsh
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  -- Part 1
  have P1 : ∀ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1)) ≤ l1On δ (J k) / Real.sqrt m := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    apply aux_a3sh_block δ (J k) (J (k + 1)) m hm (hcard k hk)
    · by_cases h : k + 1 < K
      · exact le_of_eq (hcard (k + 1) (Finset.mem_Ico.mpr ⟨by omega, h⟩))
      · have : k + 1 = K := by omega
        rw [this]; exact hcardK
    · intro a ha b hb
      exact hmono k (Finset.mem_Icc.mpr ⟨hk'.1, hk'.2.le⟩) (k + 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by omega) a ha b hb
  refine ⟨P1, ?_, ?_⟩
  · -- Part 2
    have hre : ∑ k ∈ Finset.Icc 2 K, l2On δ (J k) = ∑ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1)) := by
      rw [Finset.sum_Ico_add' (fun k => l2On δ (J k)) 1 K 1, Finset.Ico_add_one_right_eq_Icc]
    have hl1 : l1On δ J0ᶜ = ∑ k ∈ Finset.Icc 1 K, l1On δ (J k) := by
      rw [← hunion]
      unfold l1On
      rw [Finset.sum_biUnion]
      intro k hk l hl hkl
      exact hdisj k hk l hl hkl
    rw [hre, hl1, Finset.sum_div]
    calc ∑ k ∈ Finset.Ico 1 K, l2On δ (J (k + 1))
        ≤ ∑ k ∈ Finset.Ico 1 K, l1On δ (J k) / Real.sqrt m := Finset.sum_le_sum P1
      _ ≤ ∑ k ∈ Finset.Icc 1 K, l1On δ (J k) / Real.sqrt m := by
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.Ico_subset_Icc_self
          intro i _ _
          exact div_nonneg (aux_a3sh_l1_nonneg δ _) hsqm.le
  · -- Part 3
    intro hs hcone
    unfold ConeCond at hcone
    refine ⟨?_, ?_, ?_⟩
    · exact div_le_div_of_nonneg_right hcone hsqm.le
    · -- Cauchy–Schwarz
      have hcs : l1On δ J0 ≤ Real.sqrt s * l2On δ J0 := by
        have h1 := sq_sum_le_card_mul_sum_sq (s := J0) (f := fun j => |δ j|)
        simp only [sq_abs] at h1
        have h2 : (l1On δ J0) ^ 2 ≤ (s : ℝ) * ∑ j ∈ J0, δ j ^ 2 := by
          unfold l1On
          refine h1.trans ?_
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun j _ => sq_nonneg (δ j)))
          exact_mod_cast hs
        unfold l2On
        rw [← Real.sqrt_mul (Nat.cast_nonneg s)]
        apply Real.le_sqrt_of_sq_le h2
      rw [Real.sqrt_div' _ (Nat.cast_nonneg m)]
      have : c0 * (Real.sqrt s / Real.sqrt m) * l2On δ J0
          = c0 * ((Real.sqrt s * l2On δ J0) / Real.sqrt m) := by ring
      rw [this, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hc0.le
      exact div_le_div_of_nonneg_right hcs hsqm.le
    · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc0.le (Real.sqrt_nonneg _))
      unfold l2On
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro i _ _
      exact sq_nonneg _
