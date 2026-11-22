-- Prove2me | solution 1 for MultiplierAssoc206.Resolution.observation_4_5
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T15:28:37.072785+00:00
-- url     : https://prove2.me/submissions/9c87faf9-e727-47e2-9924-8876b27be6a5

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Multiplier
set_option autoImplicit false
namespace MultiplierAssoc206.Resolution

theorem bitsVal_product_expanded {n : ℕ} (x y : Fin n → Bool) :
    bitsVal x * bitsVal y =
      ∑ i : Fin n, ∑ j : Fin n,
        if partialProduct x y i j then 2 ^ ((i : ℕ) + j) else 0 := by
  simp only [bitsVal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x i <;> cases hy : y j <;> simp [hx, hy, partialProduct, pow_add]

#print axioms bitsVal_product_expanded
theorem count_le_free {n : ℕ} (r : InputRestr n) (x y : Fin n → Bool)
    (hxy : ConsistentInputs r x y) (c : ℕ) :
    columnCount x y c ≤ (freeInColumn r c).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  simp only [columnCount, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [freeInColumn, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, hp.1⟩
  intro hzero
  change r.1 p.1 = some false ∨ r.2 p.2 = some false at hzero
  rcases hzero with h | h
  · have hx := hxy.1 p.1 false h
    simp [partialProduct, hx] at hp
  · have hy := hxy.2 p.2 false h
    simp [partialProduct, hy] at hp

theorem sparse_column_zero {n g : ℕ} (r : InputRestr n) (x y : Fin n → Bool)
    (hxy : ConsistentInputs r x y) (hr : IsGSparse g r) (c : ℕ) (hc : ¬ g ∣ c) :
    columnCount x y c = 0 := by
  classical
  have hfree : freeInColumn r c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    simp only [freeInColumn, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hc (hp.2 ▸ hr.1 p.1 p.2 hp.1)
  have bound := count_le_free r x y hxy c
  rw [hfree] at bound
  simpa using bound

theorem sparse_column_lt {n g : ℕ} (r : InputRestr n) (x y : Fin n → Bool)
    (hxy : ConsistentInputs r x y) (hr : IsGSparse g r) (c : ℕ) (hc : g ∣ c) :
    columnCount x y c < 2 ^ (g - 1) :=
  lt_of_le_of_lt (count_le_free r x y hxy c) (hr.2 c hc)

theorem weighted_blocks_no_carry (g b : ℕ) (a : ℕ → ℕ)
    (ha : ∀ i < b, a i < 2 ^ g) :
    (∑ i ∈ Finset.range b, a i * 2 ^ (i * g)) < 2 ^ (b * g) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hprev := ih (fun i hi => ha i (by omega))
    have hc : a b + 1 ≤ 2 ^ g := by have := ha b (by omega); omega
    have hmul := Nat.mul_le_mul_right (2 ^ (b * g)) hc
    rw [Finset.sum_range_succ, Nat.succ_mul, pow_add]
    nlinarith

theorem sparse_blocks_bit (g b t low a high : ℕ) (ht : t < g)
    (hlow : low < 2 ^ (b * g)) (ha : a < 2 ^ g) :
    Nat.testBit (2 ^ ((b + 1) * g) * high + 2 ^ (b * g) * a + low) (b * g + t)
      = Nat.testBit a t := by
  have heq : 2 ^ ((b + 1) * g) * high + 2 ^ (b * g) * a + low =
      2 ^ (b * g) * (2 ^ g * high + a) + low := by
    rw [Nat.add_mul, one_mul, pow_add]
    ring
  rw [heq, Nat.testBit_two_pow_mul_add _ hlow]
  simp only [Nat.not_lt_of_ge (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left]
  rw [Nat.testBit_two_pow_mul_add _ ha]
  simp [ht]

#print axioms sparse_blocks_bit
#print axioms weighted_blocks_no_carry
#print axioms sparse_column_zero
#print axioms sparse_column_lt
theorem column_sum {n : ℕ} (x y : Fin n → Bool) (c : ℕ) :
    (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => (p.1 : ℕ) + p.2 = c),
        if partialProduct x y p.1 p.2 then 2 ^ ((p.1 : ℕ) + p.2) else 0)
      = columnCount x y c * 2 ^ c := by
  classical
  calc
    _ = ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
        if (p.1 : ℕ) + p.2 = c ∧ partialProduct x y p.1 p.2 = true then 2 ^ c else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hc : (p.1 : ℕ) + p.2 = c <;>
        cases hp : partialProduct x y p.1 p.2 <;> simp [hc, hp]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [columnCount, Finset.sum_const, nsmul_eq_mul]

#print axioms column_sum
theorem product_by_column {n : ℕ} (x y : Fin n → Bool) :
    bitsVal x * bitsVal y =
      ∑ c ∈ Finset.range (2 * n), columnCount x y c * 2 ^ c := by
  classical
  rw [bitsVal_product_expanded]
  let f : Fin n × Fin n → ℕ := fun p =>
    if partialProduct x y p.1 p.2 then 2 ^ ((p.1 : ℕ) + p.2) else 0
  have hm : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
      (p.1 : ℕ) + p.2 ∈ Finset.range (2 * n) := by
    intro p _
    simp only [Finset.mem_range]
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    omega
  have hf := Finset.sum_fiberwise_of_maps_to hm f
  dsimp [f] at hf
  simp only [column_sum] at hf
  have hp : (∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), f p) =
      ∑ i : Fin n, ∑ j : Fin n,
        if partialProduct x y i j then 2 ^ ((i : ℕ) + j) else 0 := by
    simpa [f] using (Finset.sum_product (Finset.univ : Finset (Fin n))
      (Finset.univ : Finset (Fin n)) f)
  rw [hp] at hf
  exact hf.symm

#print axioms product_by_column
theorem sparse_range_block (g b : ℕ) (hg : 0 < g) (f : ℕ → ℕ)
    (hf : ∀ c, ¬ g ∣ c → f c = 0) :
    (∑ t ∈ Finset.range g, f (b * g + t)) = f (b * g) := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t ht hne
    have htlt : t < g := Finset.mem_range.mp ht
    have htpos : 0 < t := Nat.pos_of_ne_zero hne
    have hnot : ¬ g ∣ b * g + t := by
      intro hd
      have hd' : g ∣ t := (Nat.dvd_add_iff_right (dvd_mul_left g b)).mpr hd
      exact (Nat.not_dvd_of_pos_of_lt htpos htlt) hd'
    exact hf _ hnot
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hg))

theorem sparse_range_blocks (g b : ℕ) (hg : 0 < g) (f : ℕ → ℕ)
    (hf : ∀ c, ¬ g ∣ c → f c = 0) :
    (∑ c ∈ Finset.range (b * g), f c) =
      ∑ i ∈ Finset.range b, f (i * g) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
    rw [sparse_range_block g b hg f hf]

#print axioms sparse_range_blocks
theorem columnCount_zero_large {n : ℕ} (x y : Fin n → Bool) (c : ℕ)
    (hc : 2 * n ≤ c) : columnCount x y c = 0 := by
  classical
  unfold columnCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

theorem product_extended {n : ℕ} (x y : Fin n → Bool) (N : ℕ) (hN : 2*n ≤ N) :
    bitsVal x * bitsVal y = ∑ c ∈ Finset.range N, columnCount x y c * 2^c := by
  rw [product_by_column]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range k, columnCount x y (2*n+i) * 2^(2*n+i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [columnCount_zero_large x y _ (by omega)]
    simp
  rw [hz, add_zero]

#print axioms product_extended
theorem product_sparse_decomposition {n g : ℕ} (hg : 0 < g)
    (r : InputRestr n) (x y : Fin n → Bool)
    (hr : IsGSparse g r) (hxy : ConsistentInputs r x y) (b : ℕ) :
    ∃ low high : ℕ, low < 2^(b*g) ∧
      columnCount x y (b*g) < 2^g ∧
      bitsVal x * bitsVal y = 2^((b+1)*g)*high + 2^(b*g)*columnCount x y (b*g) + low := by
  classical
  let f : ℕ → ℕ := fun c => columnCount x y c * 2^c
  have hf : ∀ c, ¬ g ∣ c → f c = 0 := by
    intro c hc
    simp [f, sparse_column_zero r x y hxy hr c hc]
  have hcol : ∀ i, columnCount x y (i*g) < 2^g := by
    intro i
    have h := sparse_column_lt r x y hxy hr (i*g) (dvd_mul_left g i)
    exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (Nat.sub_le g 1))
  let low := ∑ c ∈ Finset.range (b*g), f c
  have hlow : low < 2^(b*g) := by
    dsimp [low]
    rw [sparse_range_blocks g b hg f hf]
    exact weighted_blocks_no_carry g b (fun i => columnCount x y (i*g)) (by
      intro i hi
      exact hcol i)
  let highsum := ∑ i ∈ Finset.range (2*n), f ((b+1)*g+i)
  have hdiv : 2^((b+1)*g) ∣ highsum := by
    apply Finset.dvd_sum
    intro i hi
    exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _
  obtain ⟨high, hhigh⟩ := hdiv
  refine ⟨low, high, hlow, hcol b, ?_⟩
  have he := product_extended x y ((b+1)*g + 2*n) (by omega)
  rw [Finset.sum_range_add] at he
  rw [show (b+1)*g = b*g+g by simp [Nat.add_mul], Finset.sum_range_add] at he
  have hblock := sparse_range_block g b hg f hf
  change (∑ t ∈ Finset.range g, f (b*g+t)) = f (b*g) at hblock
  have he' : bitsVal x * bitsVal y = low + (∑ t ∈ Finset.range g, f (b*g+t)) + highsum := by
    simpa [low, highsum, f, Nat.add_mul] using he
  rw [hblock, hhigh] at he'
  change bitsVal x * bitsVal y = low + columnCount x y (b*g) * 2^(b*g) + 2^((b+1)*g)*high at he'
  nlinarith [he']

#print axioms product_sparse_decomposition
end MultiplierAssoc206.Resolution

open MultiplierAssoc206.Resolution

theorem solution {n : ℕ} (Mn : MulEncoding n) (hMn : Mn.IsExact) (g : ℕ) (hg : 1 ≤ g)
    (r : InputRestr n) (hr : IsGSparse g r) (x y : Fin n → Bool)
    (hxy : ConsistentInputs r x y) (b t : ℕ) (ht : t < g) (hk : b * g + t < 2 * n) :
    Mn.fn (Mn.out ⟨b * g + t, hk⟩) x y = Nat.testBit (columnCount x y (b * g)) t := by
  rw [hMn.2 x y ⟨b*g+t, hk⟩]
  obtain ⟨low, high, hlow, ha, he⟩ := product_sparse_decomposition (by omega) r x y hr hxy b
  rw [he]
  exact sparse_blocks_bit g b t low (columnCount x y (b*g)) high ht hlow ha

#print axioms solution
