-- Prove2me | solution 1 for MasulloRH.height_two_exterior_energy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:26:38.268688+00:00
-- url     : https://prove2.me/submissions/7247651f-7054-4b10-b33c-d435f308c6d8

import Definitions.Def_MasulloRH_HeightTwoComputedGrid
import Definitions.Def_MasulloRH_HeightTwoBlockBudgets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.DyadicExp MasulloRH.ComputedGrid MasulloRH.HeightTwoScalar MasulloRH.BlockBudgets
open scoped BigOperators

/- The rounded Taylor-base estimates are reused from the accepted uniform Gaussian proof:
https://prove2.me/submissions/ed994430-fead-44ff-b31a-2519cd7b48a5 . -/

private theorem down_mono' {x y : ℚ} (h : x ≤ y) : down x ≤ down y := by
  apply div_le_div_of_nonneg_right _ (by norm_num [scale])
  exact_mod_cast Int.floor_le_floor (mul_le_mul_of_nonneg_right h (by norm_num [scale] : 0 ≤ scale))

private theorem up_mono' {x y : ℚ} (h : x ≤ y) : up x ≤ up y := by
  apply div_le_div_of_nonneg_right _ (by norm_num [scale])
  exact_mod_cast Int.ceil_le_ceil (mul_le_mul_of_nonneg_right h (by norm_num [scale] : 0 ≤ scale))

private theorem base_bounds (t : ℚ) :
    let p := max 1 ⌈4*|t|⌉₊
    let x := |t|/(p:ℚ)
    let a := max (1/2) (down (taylorRat x 9-remainderRat x 9))
    let b := up (taylorRat x 9+remainderRat x 9)
    1 ≤ a ∧ 1 ≤ b ∧ b ≤ 3/2 ∧
      (1/65536 ≤ x → 1+1/131072 ≤ a) := by
  intro p x a b
  have hp : 0 < p := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hp' : (0:ℚ) < p := by exact_mod_cast hp
  have hx0 : 0 ≤ x := div_nonneg (abs_nonneg _) hp'.le
  have hceil : 4*|t| ≤ (p:ℚ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 1 ⌈4*|t|⌉₊))
  have hx : x ≤ 1/4 := (div_le_iff₀ hp').2 (by linarith)
  have h9 : x^9 ≤ x := calc
    x^9 = x^8*x := by ring
    _ ≤ 1*x := mul_le_mul_of_nonneg_right (pow_le_one₀ hx0 (by linarith)) hx0
    _ = x := one_mul _
  have hT : 1+x ≤ taylorRat x 9 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j:ℕ => x^j/(j.factorial:ℚ))
      (Finset.range_mono (show 2 ≤ 9 by decide)) (fun i _ _ => div_nonneg (pow_nonneg hx0 _) (Nat.cast_nonneg _))
    calc 1+x = taylorRat x 2 := by norm_num [taylorRat, Finset.sum_range_succ]
         _ ≤ _ := h
  have hT' : taylorRat x 9 ≤ taylorRat (1/4) 9 := by
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hx _) (Nat.cast_nonneg _)
  have hR : 0 ≤ remainderRat x 9 := by unfold remainderRat; positivity
  have hRx : remainderRat x 9 ≤ x := by
    norm_num [remainderRat,Nat.factorial]
    linarith
  have hRsmall : remainderRat x 9 ≤ 1/262144 := by
    have h : x^9 ≤ 1 := pow_le_one₀ hx0 (by linarith)
    norm_num [remainderRat,Nat.factorial]
    linarith
  have ha : 1 ≤ a := calc
    1 = down 1 := by decide +kernel
    _ ≤ down (taylorRat x 9-remainderRat x 9) := down_mono' (by linarith)
    _ ≤ a := le_max_right _ _
  have hB : 1 ≤ b := calc
    1 = up 1 := by decide +kernel
    _ ≤ b := up_mono' (by linarith)
  have hb : b ≤ 3/2 := calc
    b ≤ up (3/2) := up_mono' ((add_le_add hT' hRsmall).trans (by decide +kernel))
    _ = 3/2 := by decide +kernel
  refine ⟨ha,hB,hb,?_⟩
  intro hmin
  calc 1+1/131072 = down (1+1/131072) := by decide +kernel
       _ ≤ down (taylorRat x 9-remainderRat x 9) := down_mono' (by linarith)
       _ ≤ a := le_max_right _ _

private theorem row_upper_of_le_eight (t : ℚ) (ht : t ≤ 8) : (row t).upper ≤ 500000 := by
  by_cases hz : t = 0
  · subst t
    norm_num [row]
  by_cases hcut : t ≤ -64
  · simp only [row, if_neg hz, if_pos hcut]
    norm_num
  let p := max 1 ⌈4*|t|⌉₊
  let x := |t|/(p:ℚ)
  let a := max (1/2) (down (taylorRat x 9-remainderRat x 9))
  let b := up (taylorRat x 9+remainderRat x 9)
  obtain ⟨ha,hb,hb',_⟩ := base_bounds t
  change 1 ≤ a at ha
  change 1 ≤ b at hb
  change b ≤ 3/2 at hb'
  by_cases hp : 0 < t
  · have hp32 : p ≤ 32 := max_le (by decide) (Nat.ceil_le.mpr (by
      rw [abs_of_pos hp]; norm_num; linarith))
    have hpow : b^p ≤ (3/2:ℚ)^32 := (pow_le_pow_left₀ (by linarith) hb' _).trans
      (pow_le_pow_right₀ (by norm_num) hp32)
    simp only [row, if_neg hz, if_neg hcut, if_pos hp]
    change up (b^p) ≤ 500000
    exact (up_mono' hpow).trans (by decide +kernel)
  · simp only [row, if_neg hz, if_neg hcut, if_neg hp]
    change up (1/a^p) ≤ 500000
    have hpow : 1 ≤ a^p := one_le_pow₀ ha
    have hinv : 1/a^p ≤ 1 := (div_le_iff₀ (by linarith : 0<a^p)).2 (by linarith)
    exact (up_mono' hinv).trans (by decide +kernel)

private theorem edges_in_grid (j : ℕ) (hj : j < 65536) :
    -4 ≤ edge j ∧ edge j ≤ edge ((j:ℤ)+1) ∧ edge ((j:ℤ)+1) ≤ 4 := by
  have h0 : (0:ℚ) ≤ j := Nat.cast_nonneg j
  have h1 : (j:ℚ) ≤ 65535 := by exact_mod_cast (show j ≤ 65535 by omega)
  simp only [edge, Int.cast_natCast, Int.cast_add, Int.cast_one]
  constructor
  · linarith
  constructor <;> linarith

private theorem weight_bound (j : ℕ) (hj : j < 65536) : weightAt j ≤ 500000 := by
  obtain ⟨hl,_,hu⟩ := edges_in_grid j hj
  have hmax : amax (edge j) (edge ((j:ℤ)+1)) ≤ 4 := max_le (by linarith) hu
  apply row_upper_of_le_eight
  linarith

private def tailPulse : Disk := enclose 0 ((1692569/1000000)*(1/(2:ℚ)^64))
private def tailAmplitude : ℚ :=
  |tailPulse.center| + (tailPulse.radius +
    ∑ i : Fin 11, |MasulloRH.HeightTwoWitness.coeffsQ i| * (1/(2:ℚ)^64))

private theorem pulse_at_ends (j : ℕ) (hj : j < 65536) (he : j < 5120 ∨ 64512 ≤ j) :
    pulseAt j = tailPulse := by
  let l := edge (j:ℤ)
  let u := edge ((j:ℤ)+1)
  have hlu : l ≤ u := (edges_in_grid j hj).2.1
  have hside : u ≤ -3 ∨ 3 ≤ l := by
    rcases he with h | h
    · left
      have hk : (j:ℚ) ≤ 5119 := by exact_mod_cast (show j≤5119 by omega)
      dsimp [u,edge]
      push_cast
      linarith
    · right
      have hk : (64512:ℚ) ≤ j := by exact_mod_cast h
      dsimp [l,edge]
      push_cast
      linarith
  have hmin : 3 ≤ amin l u := by
    unfold amin
    apply le_trans _ (le_max_right _ _)
    rcases hside with h | h
    · exact le_trans (by linarith : (3:ℚ) ≤ -u) (le_max_right _ _)
    · exact h.trans (le_max_left _ _)
  have hmax : 3 ≤ amax l u := by
    unfold amax
    rcases hside with h | h
    · exact le_trans (by linarith : (3:ℚ) ≤ -l) (le_max_left _ _)
    · exact (h.trans hlu).trans (le_max_right _ _)
  have cutoff (z : ℚ) (hz : 3 ≤ z) : -9*z^2 ≤ -64 := by nlinarith [sq_nonneg (z-3)]
  have low : (row (-9*(amax l u)^2)).lower = 0 := by
    have H := cutoff _ hmax
    have H0 : -9*(amax l u)^2 ≠ 0 := by linarith
    simp only [row, if_neg H0, if_pos H]
  have high : (row (-9*(amin l u)^2)).upper = 1/(2:ℚ)^64 := by
    have H := cutoff _ hmin
    have H0 : -9*(amin l u)^2 ≠ 0 := by linarith
    simp only [row, if_neg H0, if_pos H]
  change enclose (_ * (row (-9*(amax l u)^2)).lower) (_ * (row (-9*(amin l u)^2)).upper) = _
  rw [low,high,mul_zero]
  rfl

private theorem shift_range : ∀ i : Fin 11, -3072 ≤ shifts i ∧ shifts i ≤ 19456 := by
  decide +kernel

private theorem all_tail (j : ℕ) (he : j < 5120 ∨ 64512 ≤ j) (i : Fin 11) :
    fullTheta ((j:ℤ)-shifts i) = ⟨0,1/(2:ℚ)^64⟩ := by
  have h := shift_range i
  have ht : (j:ℤ)-shifts i < 8192 ∨ 45056 ≤ (j:ℤ)-shifts i := by omega
  exact if_pos ht

private theorem point_bound (j : ℕ) (hj : j < 65536) (he : j < 5120 ∨ 64512 ≤ j) :
    energyTerm j ≤ 1/(2:ℚ)^110 := by
  have ident : energyTerm j = (1/8192)*(weightAt j*tailAmplitude^2) := by
    simp [energyTerm,pulse_at_ends j hj he,all_tail j he,tailAmplitude]
  rw [ident]
  calc
    _ ≤ (1/8192:ℚ)*(500000*tailAmplitude^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (weight_bound j hj) (sq_nonneg _)) (by norm_num)
    _ ≤ _ := by decide +kernel

private theorem cap_ends :
    (∀ b : Fin 80, cap b = 1/(2:ℚ)^40) ∧
    (∀ b : Fin 16, cap (1008+b) = 1/(2:ℚ)^40) := by
  decide +kernel

private theorem block_bound (b : ℕ) (hb : b ∈ Finset.range 1024) (he : b < 80 ∨ 1008 ≤ b) :
    (∑ j ∈ Finset.range 64, energyTerm (b*64+j)) ≤ cap b := by
  have hb' := Finset.mem_range.mp hb
  have hc : cap b = 1/(2:ℚ)^40 := by
    rcases he with hl | hr
    · exact cap_ends.1 ⟨b,hl⟩
    · have hh := cap_ends.2 ⟨b-1008,by omega⟩
      simpa only [Nat.add_sub_of_le hr] using hh
  rw [hc]
  calc
    _ ≤ ∑ _j ∈ Finset.range 64, (1/(2:ℚ)^110) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Finset.mem_range.mp hj
      exact point_bound _ (by omega) (by omega)
    _ ≤ _ := by norm_num

set_option maxRecDepth 16384 in
theorem solution :
    (∀ j : ℕ, j < 65536 → (j < 5120 ∨ 64512 ≤ j) →
        energyTerm j ≤ 1 / (2 : ℚ)^110) ∧
    (∀ b ∈ Finset.range 1024, (b < 80 ∨ 1008 ≤ b) →
        (∑ j ∈ Finset.range 64, energyTerm (b * 64 + j)) ≤ cap b) ∧
    (∑ j ∈ Finset.range 5120, energyTerm j) +
        (∑ j ∈ Finset.range 1024, energyTerm (64512 + j)) ≤ 3 / (2 : ℚ)^99 := by
  refine ⟨point_bound,block_bound,?_⟩
  have hl : (∑ j ∈ Finset.range 5120, energyTerm j) ≤
      ∑ _j ∈ Finset.range 5120, (1/(2:ℚ)^110) := by
    apply Finset.sum_le_sum
    intro j hj
    have h := Finset.mem_range.mp hj
    exact point_bound j (by omega) (Or.inl h)
  have hr : (∑ j ∈ Finset.range 1024, energyTerm (64512+j)) ≤
      ∑ _j ∈ Finset.range 1024, (1/(2:ℚ)^110) := by
    apply Finset.sum_le_sum
    intro j hj
    have h := Finset.mem_range.mp hj
    exact point_bound _ (by omega) (Or.inr (by omega))
  have h := add_le_add hl hr
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
  exact h.trans (by norm_num)
