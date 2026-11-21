-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_B_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:01:50.557824+00:00
-- url     : https://prove2.me/submissions/43596497-e5c5-47ee-9ace-675360dc12c6

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction

section
namespace MulticlassOmni.Dev.B3
open MulticlassOmni.Lipschitz

theorem eOne_eq {k : ℕ} (h : 0 < k) : eOne k = Pi.single (⟨0, h⟩ : Fin k) (1:ℝ) := by
  funext y
  by_cases hy : (y : ℕ) = 0
  · have : y = ⟨0, h⟩ := Fin.ext hy
    subst this; simp [eOne]
  · have : y ≠ ⟨0, h⟩ := fun e => hy (by simp [e])
    simp [eOne, hy, Pi.single_apply, this]

theorem dot_eOne {k : ℕ} (h : 0 < k) (v : Fin k → ℝ) : dot (eOne k) v = v ⟨0, h⟩ := by
  rw [eOne_eq h]
  simp only [dot]
  rw [Finset.sum_eq_single (⟨0, h⟩ : Fin k)]
  · simp
  · intro y _ hy; simp [Pi.single_apply, hy]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem sum_eOne {k : ℕ} (h : 0 < k) : ∑ y, eOne k y = 1 := by
  rw [eOne_eq h]; simp

/-- coordinate facts of a packing point -/
theorem coord_bounds {k : ℕ} (hk : 0 < k) {x : Fin k → ℝ} (y : Fin k)
    (h : 7 / (8 * (k : ℝ)) ≤ x y ∧ x y ≤ 9 / (8 * (k : ℝ))) :
    7 / 8 ≤ (k:ℝ) * x y ∧ (k:ℝ) * x y ≤ 9 / 8 := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨h1, h2⟩ := h
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  constructor <;> nlinarith

theorem cost_range {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 32)
    (hb : ∀ i y, 7 / (8 * (k : ℝ)) ≤ x i y ∧ x i y ≤ 9 / (8 * (k : ℝ)))
    (a : Option (Fin N)) (y : Fin k) : cost x η a y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  cases a with
  | none => simp [cost, costA]; constructor <;> norm_num
  | some i =>
    obtain ⟨h1, h2⟩ := coord_bounds hk y (hb i y)
    have : (k:ℝ) * (x i y - vbar k y) = (k:ℝ) * x i y - 1 := by
      simp [vbar]; field_simp
    simp only [cost, costB, costA, this]
    constructor <;> nlinarith

theorem qLip_mem {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 16384)
    (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (hb : ∀ i y, 7 / (8 * (k : ℝ)) ≤ x i y ∧ x i y ≤ 9 / (8 * (k : ℝ)))
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)))
    (i : Fin N) (b : Fin 2) : qLip x η b i ∈ stdSimplex ℝ (Fin k) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx1 : (k:ℝ) * x i ⟨0, hk⟩ ≤ 15 / 16 := by
    have := h1 i ⟨0, hk⟩ rfl
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hD : dot (eOne k) (costB x η i - costA k) + 2 * η = 1 / 256 + 1 - (k:ℝ) * x i ⟨0, hk⟩ := by
    rw [dot_eOne hk]
    simp [costB, costA, vbar]
    field_simp
    ring
  have hDpos : 17 / 256 ≤ dot (eOne k) (costB x η i - costA k) + 2 * η := by
    rw [hD]; linarith
  have hbl : ((b : ℕ) : ℝ) = 0 ∨ ((b : ℕ) : ℝ) = 1 := by
    have := b.isLt
    interval_cases hb : (b : ℕ) <;> simp
  have hα0 : 0 ≤ alpha x η b i := by
    unfold alpha
    apply div_nonneg
    · rcases hbl with h | h <;> rw [h] <;> nlinarith
    · linarith
  have hα1 : alpha x η b i ≤ 1 := by
    unfold alpha
    rw [div_le_one (by linarith)]
    rcases hbl with h | h <;> rw [h] <;> nlinarith
  obtain ⟨hs0, hs1⟩ := hs i
  refine ⟨fun y => ?_, ?_⟩
  · simp only [qLip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : 0 ≤ eOne k y := by simp only [eOne]; split_ifs <;> norm_num
    have h2 := hs0 y
    nlinarith [mul_nonneg hα0 this, mul_nonneg (sub_nonneg.2 hα1) h2]
  · simp only [qLip, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_eOne hk, hs1]
    ring


theorem count_bounds (Cpack : ℝ) (hC : 0 < Cpack) {k : ℕ} (hk : 3 ≤ k) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2)
    (c : ℕ) (hc : (2:ℝ) ^ (-Cpack * k) * (16 * η / 125) ^ (-((k : ℝ) - 2) / 2) ≤ (c : ℝ)) :
    (((2:ℝ) ^ (Cpack + 1)) ^ (-(k : ℝ)) * η ^ (-((k : ℝ) - 2) / 2) ≤ (min c ⌊η ^ (-((k : ℝ) - 2) / 2)⌋₊ : ℕ) ∧
     ((min c ⌊η ^ (-((k : ℝ) - 2) / 2)⌋₊ : ℕ) : ℝ) ≤ η ^ (-((k : ℝ) - 2) / 2) ∧
     128 ≤ min c ⌊η ^ (-((k : ℝ) - 2) / 2)⌋₊) := by
  set T := η ^ (-((k : ℝ) - 2) / 2) with hT
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hη1 : η ≤ 1 := by
    have : (2:ℝ) ^ (3 * Cpack + 7) ≥ 1 := Real.one_le_rpow (by norm_num) (by linarith)
    have h2 : ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
    have h3 : ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2 ≤ 1 := by
      have : 0 ≤ ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ := by positivity
      nlinarith
    linarith
  -- T ≥ 1
  have hT1 : 1 ≤ T := by
    apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hη0 hη1
    linarith
  -- 16η/125 ≤ η so its power is ≥ T
  have hP : T ≤ (16 * η / 125) ^ (-((k : ℝ) - 2) / 2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hc2 : (2:ℝ) ^ (-Cpack * k) * T ≤ c := le_trans (by gcongr) hc
  -- floor facts
  have hfl : T / 2 ≤ (⌊T⌋₊ : ℝ) := by
    have h1 := Nat.lt_floor_add_one T
    have h2 : (1:ℝ) ≤ ⌊T⌋₊ := by exact_mod_cast Nat.floor_pos.2 hT1
    linarith
  have hfl2 : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hpos : 0 < (2:ℝ) ^ (-Cpack * k) := by positivity
  have hle1 : (2:ℝ) ^ (-Cpack * k) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  refine ⟨?_, ?_, ?_⟩
  · have e : ((2:ℝ) ^ (Cpack + 1)) ^ (-(k : ℝ)) = (2:ℝ) ^ (-(Cpack + 1) * k) := by
      rw [← Real.rpow_mul (by norm_num)]; ring_nf
    rw [e]
    have hm : (2:ℝ) ^ (-(Cpack + 1) * k) * T ≤ (min c ⌊T⌋₊ : ℕ) := by
      rw [Nat.cast_min]
      apply le_min
      · refine le_trans ?_ hc2
        gcongr
        · norm_num
        · nlinarith
      · have : (2:ℝ) ^ (-(Cpack + 1) * k) ≤ 1 / 2 := by
          have : (2:ℝ) ^ (-(Cpack + 1) * k) ≤ (2:ℝ) ^ (-1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num); nlinarith
          simpa [Real.rpow_neg_one] using this
        nlinarith
    exact hm
  · rw [Nat.cast_min]; exact le_trans (min_le_right _ _) hfl2
  · -- 128 ≤ min
    have hB : (2:ℝ) ^ (3 * Cpack + 7) ≤ η ^ (-(1/2 : ℝ)) := by
      have h1 : η ^ (-(1/2:ℝ)) = (η ^ (1/2:ℝ))⁻¹ := Real.rpow_neg hη0.le _
      have h2 : η ^ (1/2:ℝ) ≤ ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ := by
        have : η ^ (1/2:ℝ) ≤ ((((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow hη0.le hη (by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
        norm_num at this
        exact this
      rw [h1]
      have hp : 0 < η ^ (1/2:ℝ) := by positivity
      rw [le_inv_comm₀ (by positivity) hp]
      simpa using h2
    have hTB : T = (η ^ (-(1/2 : ℝ))) ^ (((k - 2 : ℕ)) : ℝ) := by
      rw [← Real.rpow_mul hη0.le, hT]
      congr 1
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hB1 : (1:ℝ) ≤ (2:ℝ) ^ (3 * Cpack + 7) := Real.one_le_rpow (by norm_num) (by linarith)
    have hT2 : (2:ℝ) ^ ((3 * Cpack + 7) * ((k - 2 : ℕ) : ℝ)) ≤ T := by
      rw [hTB, Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) hB (by positivity)
    have hk' : ((k - 2 : ℕ) : ℝ) = (k:ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hk1 : (1:ℝ) ≤ (k:ℝ) - 2 := by linarith
    have hsplit : (2:ℝ) ^ ((3 * Cpack + 7) * ((k - 2 : ℕ) : ℝ)) =
        (2:ℝ) ^ (3 * Cpack * ((k:ℝ) - 2)) * (2:ℝ) ^ (7 * ((k:ℝ) - 2)) := by
      rw [← Real.rpow_add (by norm_num), hk']; ring_nf
    have hA : (2:ℝ) ^ (Cpack * k) ≤ (2:ℝ) ^ (3 * Cpack * ((k:ℝ) - 2)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num); nlinarith
    have h7 : (2:ℝ) ^ (7:ℝ) ≤ (2:ℝ) ^ (7 * ((k:ℝ) - 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h128 : (2:ℝ) ^ (7:ℝ) = 128 := by norm_num
    have hnn : (2:ℝ) ^ (Cpack * k) * (2:ℝ) ^ (-Cpack * k) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have hTbig : (2:ℝ) ^ (Cpack * k) * 128 ≤ T := by
      refine le_trans ?_ hT2
      rw [hsplit]
      rw [← h128]
      gcongr
    apply le_min
    · have : (128:ℝ) ≤ c := by
        have := mul_le_mul_of_nonneg_left hTbig hpos.le
        nlinarith
      exact_mod_cast this
    · apply Nat.le_floor
      have : (1:ℝ) ≤ (2:ℝ) ^ (Cpack * k) := Real.one_le_rpow (by norm_num) (by nlinarith)
      push_cast
      nlinarith

end MulticlassOmni.Dev.B3
end

section
namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.B3

theorem chk_lemma_B_3 :
    ∀ Cpack : ℝ, 0 < Cpack → ∃ C₁ η₀ : ℝ, 2 ≤ C₁ ∧ 0 < η₀ ∧
      ∀ k : ℕ, 3 ≤ k → ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k η x →
          (C₁ ^ (-(k : ℝ)) * η ^ (-((k : ℝ) - 2) / 2) ≤ (N : ℝ) ∧
            (N : ℝ) ≤ η ^ (-((k : ℝ) - 2) / 2) ∧ 128 ≤ N) ∧
          (∀ (a : Option (Fin N)) (y : Fin k), cost x η a y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4)) ∧
          (∀ (i : Fin N) (b : Fin 2), qLip x η b i ∈ stdSimplex ℝ (Fin k)) := by
  intro Cpack hC
  have hpos : (0:ℝ) < ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2 := by positivity
  refine ⟨(2:ℝ) ^ (Cpack + 1), min (1 / 16384) (((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2), ?_, ?_, ?_⟩
  · have : (2:ℝ) ^ (1:ℝ) ≤ (2:ℝ) ^ (Cpack + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using this
  · exact lt_min (by norm_num) hpos
  · intro k hk η hη0 hη N x hx
    obtain ⟨X₀, hX, _, hmem, hN⟩ := hx
    have hk0 : 0 < k := by omega
    have hη1 : η ≤ 1 / 16384 := le_trans hη (min_le_left _ _)
    have hη2 : η ≤ ((2:ℝ) ^ (3 * Cpack + 7))⁻¹ ^ 2 := le_trans hη (min_le_right _ _)
    obtain ⟨hcard, hsimp, hcoord, hfirst, _, _⟩ := hX
    have hb : ∀ i y, 7 / (8 * (k : ℝ)) ≤ x i y ∧ x i y ≤ 9 / (8 * (k : ℝ)) :=
      fun i y => hcoord _ (hmem i) y
    obtain ⟨c1, c2, c3⟩ := count_bounds Cpack hC hk η hη0 hη2 X₀.card hcard
    rw [← hN] at c1 c2 c3
    refine ⟨⟨c1, c2, c3⟩, ?_, ?_⟩
    · exact cost_range hk0 x η hη0 (by linarith) hb
    · intro i b
      exact qLip_mem hk0 x η hη0 hη1 (fun i => hsimp _ (hmem i)) hb
        (fun i y hy => hfirst _ (hmem i) y hy) i b

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_B_3 := @MulticlassOmni.Lipschitz.chk_lemma_B_3
