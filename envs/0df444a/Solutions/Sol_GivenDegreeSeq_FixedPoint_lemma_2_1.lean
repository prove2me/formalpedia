-- Prove2me | solution 1 for GivenDegreeSeq.FixedPoint.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:54:33.307516+00:00
-- url     : https://prove2.me/submissions/ba65f9db-8aa9-443e-9200-8c4e914a5558

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_ClassLn

set_option autoImplicit false
open GivenDegreeSeq.FixedPoint

lemma gdf_split {n : ℕ} (f : Fin n → ℝ) (i k : Fin n) (h : k ≠ i) :
    ∑ j, f j = f i + f k + ∑ j ∈ (Finset.univ.erase i).erase k, f j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ k⟩)]
  ring

lemma gdf_L21 {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA1 : ∀ i, ∑ j, |A i j| ≤ 1) (hAd : ∀ i, δ ≤ A i i)
    (hAo : ∀ i j, i ≠ j → A i j ≤ -δ / ((n : ℝ) - 1))
    (hB1 : ∀ i, ∑ j, |B i j| ≤ 1) (hBd : ∀ i, δ ≤ B i i)
    (hBo : ∀ i j, i ≠ j → B i j ≤ -δ / ((n : ℝ) - 1)) (i : Fin n) :
    ∑ k, |(A * B) i k| ≤ 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  set ε : ℝ := δ / ((n:ℝ) - 1) with hε
  have hεpos : 0 < ε := div_pos hδ hn1
  have hεδ : ((n:ℝ) - 2) * ε ≤ δ := by
    have : ((n:ℝ) - 2) * ε = ((n:ℝ) - 2) / ((n:ℝ) - 1) * δ := by rw [hε]; ring
    rw [this]
    have : ((n:ℝ) - 2) / ((n:ℝ) - 1) ≤ 1 := by
      rw [div_le_one hn1]; linarith
    nlinarith
  have hAo' : ∀ i j, i ≠ j → A i j ≤ -ε := fun i j h => by
    have := hAo i j h; rw [hε]; rw [neg_div] at this; exact this
  have hBo' : ∀ i j, i ≠ j → B i j ≤ -ε := fun i j h => by
    have := hBo i j h; rw [hε]; rw [neg_div] at this; exact this
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n:ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
    rw [Nat.cast_sub (by omega)]; simp
  have key : ∀ k, k ≠ i → |(A * B) i k| ≤ ∑ j, |A i j| * |B j k| - 2 * (((n:ℝ) - 2) * ε ^ 2) := by
    intro k hk
    have hcc : ((((Finset.univ.erase i).erase k).card : ℕ) : ℝ) = (n:ℝ) - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp; ring
    have e1 : (A * B) i k = ∑ j, A i j * B j k := rfl
    rw [e1, gdf_split (fun j => A i j * B j k) i k hk,
      gdf_split (fun j => |A i j| * |B j k|) i k hk]
    have rest : ∀ j ∈ (Finset.univ.erase i).erase k, ε ^ 2 ≤ A i j * B j k := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
      have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
      have a := hAo' i j (Ne.symm hji)
      have b := hBo' j k hjk
      nlinarith
    have restabs : ∑ j ∈ (Finset.univ.erase i).erase k, |A i j| * |B j k| =
        ∑ j ∈ (Finset.univ.erase i).erase k, A i j * B j k := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← abs_mul, abs_of_nonneg]
      exact le_trans (by positivity) (rest j hj)
    have hP : ((n:ℝ) - 2) * ε ^ 2 ≤ ∑ j ∈ (Finset.univ.erase i).erase k, A i j * B j k := by
      calc ((n:ℝ) - 2) * ε ^ 2 = ∑ j ∈ (Finset.univ.erase i).erase k, ε ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul, hcc]
        _ ≤ _ := Finset.sum_le_sum rest
    rw [restabs]
    have ti : A i i * B i k ≤ -(δ * ε) := by
      have a := hAd i
      have b := hBo' i k (Ne.symm hk)
      nlinarith
    have tk : A i k * B k k ≤ -(δ * ε) := by
      have a := hAo' i k (Ne.symm hk)
      have b := hBd k
      nlinarith
    have hm : ((n:ℝ) - 2) * ε ^ 2 ≤ δ * ε := by nlinarith
    have hde : 0 < δ * ε := mul_pos hδ hεpos
    rw [← abs_mul, ← abs_mul, abs_of_nonpos (by linarith : A i i * B i k ≤ 0),
      abs_of_nonpos (by linarith : A i k * B k k ≤ 0), abs_le]
    constructor <;> linarith
  set m' : ℝ := ((n:ℝ) - 2) * ε ^ 2 with hm'
  have hii : |(A * B) i i| ≤ ∑ j, |A i j| * |B j i| := by
    have e1 : (A * B) i i = ∑ j, A i j * B j i := rfl
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => abs_mul _ _))
  set W : Fin n → ℝ := fun k => ∑ j, |A i j| * |B j k| with hW
  have hWsum : ∑ k, W k ≤ 1 := by
    have : ∑ k, W k = ∑ j, |A i j| * ∑ k, |B j k| := by
      simp only [hW]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
    rw [this]
    calc ∑ j, |A i j| * ∑ k, |B j k| ≤ ∑ j, |A i j| * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hB1 j) (abs_nonneg _))
      _ ≤ 1 := by simpa using hA1 i
  have h1 : ∑ k, |(A * B) i k| ≤ ∑ k, W k - ((n:ℝ) - 1) * (2 * m') := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have h2 : ∑ k ∈ Finset.univ.erase i, |(A * B) i k| ≤
        ∑ k ∈ Finset.univ.erase i, (W k - 2 * m') :=
      Finset.sum_le_sum (fun k hk => key k (Finset.ne_of_mem_erase hk))
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at h2
    have h3 : |(A * B) i i| ≤ W i := hii
    linarith
  have h4 : ((n:ℝ) - 1) * (2 * m') = 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
    rw [hm', hε]
    field_simp
  linarith

lemma gdf_row_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h : matNormInf A ≤ 1) (i : Fin n) :
    ∑ j, |A i j| ≤ 1 :=
  le_trans (le_ciSup (f := fun i => ∑ j, |A i j|) (Finite.bddAbove_range _) i) h

theorem solution {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : classLn n δ A) (hB : classLn n δ B) :
    matNormInf (A * B) ≤ 1 - 2 * ((n : ℝ) - 2) * δ ^ 2 / ((n : ℝ) - 1) := by
  obtain ⟨hA1, hAd, hAo⟩ := hA
  obtain ⟨hB1, hBd, hBo⟩ := hB
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold matNormInf
  apply ciSup_le
  intro i
  exact gdf_L21 hn hδ (gdf_row_le hA1) hAd hAo (gdf_row_le hB1) hBd hBo i
