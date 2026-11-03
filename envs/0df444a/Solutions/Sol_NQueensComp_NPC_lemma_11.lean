-- Prove2me | solution 1 for NQueensComp.NPC.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T03:11:12.740099+00:00
-- url     : https://prove2.me/submissions/7797dbd3-9589-4191-8eff-eb1b0b85b158

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

namespace NQueensComp.NPC.Def10Proof

/-! ### Generic facts about queens -/

theorem fits_mk {N a b : ℕ} (ha : a < N) (hb : b < N) : FitsOn N ((a, b) : Queen) := by
  simp only [FitsOn, size]; exact max_lt ha hb

theorem fits_lt {N : ℕ} {q : Queen} (h : FitsOn N q) : q.1 < N ∧ q.2 < N := by
  simp only [FitsOn, size] at h; exact max_lt_iff.mp h

theorem fits_of_lt {N : ℕ} {q : Queen} (h1 : q.1 < N) (h2 : q.2 < N) : FitsOn N q := by
  simp only [FitsOn, size]; exact max_lt h1 h2

theorem image_col_eq_range {n : ℕ} {Q : Finset Queen} (h : IsNQueensSol n Q) :
    Q.image col = Finset.range n := by
  obtain ⟨_, hfit, hcard, hNA⟩ := h
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (fits_lt (hfit q hq)).1
  · rw [Finset.card_range, Finset.card_image_of_injOn, hcard]
    intro q hq q' hq' he
    by_contra hne
    exact hNA q hq q' hq' ⟨hne, Or.inl he⟩

theorem image_row_eq_range {n : ℕ} {Q : Finset Queen} (h : IsNQueensSol n Q) :
    Q.image row = Finset.range n := by
  obtain ⟨_, hfit, hcard, hNA⟩ := h
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_range.mpr (fits_lt (hfit q hq)).2
  · rw [Finset.card_range, Finset.card_image_of_injOn, hcard]
    intro q hq q' hq' he
    by_contra hne
    exact hNA q hq q' hq' ⟨hne, Or.inr (Or.inl he)⟩

/-! ### Arithmetic of `n′` -/

theorem np_facts (n : ℕ) (hn : 1 ≤ n) :
    def10_nprime n % 2 = 1 ∧ n ≤ def10_nprime n ∧ 2 * n ≤ def10_nprime n + 1 ∧
      (def10_nprime n % 6 = 1 ∨ def10_nprime n % 6 = 5) := by
  unfold def10_nprime
  split_ifs with h <;> omega

theorem half_exists {N j : ℕ} (hN : N % 2 = 1) (hj : j < N) : ∃ i < N, 2 * i % N = j := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨k, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · refine ⟨k + (N + 1) / 2, by omega, ?_⟩
    have h2 : 2 * (k + (N + 1) / 2) = j + N := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

theorem half_inj {N i c : ℕ} (hN : N % 2 = 1) (hi : i < N) (hc : 2 * c < N)
    (h : 2 * i % N = 2 * c) : i = c := by
  by_cases h2 : 2 * i < N
  · rw [Nat.mod_eq_of_lt h2] at h; omega
  · have h3 : 2 * i % N = 2 * i - N := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### Facts about `Q₁₉` -/

theorem q19_facts :
    ((17, 0) : Queen) ∈ Q19 ∧ ((0, 8) : Queen) ∈ Q19 ∧
    (∀ v ∈ Q19, v.1 < 19 ∧ v.2 < 19) ∧
    (∀ v ∈ Q19, v.1 = 17 → v = (17, 0)) ∧
    (∀ v ∈ Q19, v.2 = 0 → v = (17, 0)) ∧
    (∀ v ∈ Q19, v.1 = 0 → v = (0, 8)) ∧
    (∀ v ∈ Q19, v.2 = 8 → v = (0, 8)) ∧
    (∀ a < 19, ∃ v ∈ Q19, v.1 = a) ∧
    (∀ b < 19, ∃ v ∈ Q19, v.2 = b) := by
  unfold Q19
  decide +kernel

/-! ### The board `Q₂` -/

theorem mem_sumSet {Q Q₁ : Finset Queen} {x : Queen} :
    x ∈ sumSet Q Q₁ ↔ ∃ a ∈ Q, ∃ b ∈ Q₁, a + b = x := by
  unfold sumSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product] at hab
    exact ⟨a, hab.1, b, hab.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

theorem mem_A {N : ℕ} {a : Queen} (h : a ∈ A N) : ∃ i < N, a = (i, 2 * i % N) := by
  unfold A at h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
  exact ⟨i, Finset.mem_range.mp hi, rfl⟩

theorem A_mem {N i : ℕ} (hi : i < N) : ((i, 2 * i % N) : Queen) ∈ A N := by
  unfold A
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem mem_B {N : ℕ} {a : Queen} (h : a ∈ B N) : ∃ i < N, a = (2 * i % N, i) := by
  unfold B at h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
  exact ⟨i, Finset.mem_range.mp hi, rfl⟩

theorem B_mem {N i : ℕ} (hi : i < N) : ((2 * i % N, i) : Queen) ∈ B N := by
  unfold B
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem Q2_cases {N : ℕ} {x : Queen} (hx : x ∈ def10_Q2 N) :
    (∃ i < N, ∃ v ∈ Q19, v ≠ (17, 0) ∧ x = ((i, 2 * i % N) : Queen) + N • v) ∨
    (∃ i < N, x = ((2 * i % N, i) : Queen) + N • ((17, 0) : Queen)) := by
  unfold def10_Q2 at hx
  rcases Finset.mem_union.mp hx with h | h
  · left
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sumSet.mp h
    obtain ⟨i, hi, rfl⟩ := mem_A ha
    unfold scaleSet at hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_erase] at hv
    exact ⟨i, hi, v, hv.2, hv.1, rfl⟩
  · right
    unfold shiftSet at h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨i, hi, rfl⟩ := mem_B hb
    exact ⟨i, hi, rfl⟩

theorem A_block_mem {N i : ℕ} {v : Queen} (hi : i < N) (hv : v ∈ Q19) (hv' : v ≠ (17, 0)) :
    ((i, 2 * i % N) : Queen) + N • v ∈ def10_Q2 N := by
  unfold def10_Q2
  apply Finset.mem_union_left
  apply mem_sumSet.mpr
  refine ⟨_, A_mem hi, N • v, ?_, rfl⟩
  unfold scaleSet
  exact Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hv', hv⟩, rfl⟩

theorem B_block_mem {N i : ℕ} (hi : i < N) :
    ((2 * i % N, i) : Queen) + N • ((17, 0) : Queen) ∈ def10_Q2 N := by
  unfold def10_Q2 shiftSet
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, B_mem hi, rfl⟩)

/-! ### Instances of Problem 3 -/

theorem valid_unpack {M : Inst3} (hM : M.Valid) :
    1 ≤ M.n ∧ (∀ q ∈ M.P, FitsOn M.n q) ∧ DistinctRowsCols M.P ∧ M.C.card = M.R.card ∧
    (∀ q ∈ M.P, col q ∉ M.C ∧ row q ∉ M.R) ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7⟩ := hM
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem colP_mem_C' {M : Inst3} {q : Queen} (h : q ∈ M.P) : col q ∈ def10_C' M := by
  unfold def10_C'; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem rowP_mem_R' {M : Inst3} {q : Queen} (h : q ∈ M.P) : row q ∈ def10_R' M := by
  unfold def10_R'; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem C_sub_C' {M : Inst3} {c : ℕ} (h : c ∈ M.C) : c ∈ def10_C' M := by
  unfold def10_C'; exact Finset.mem_union_left _ h

theorem R_sub_R' {M : Inst3} {r : ℕ} (h : r ∈ M.R) : r ∈ def10_R' M := by
  unfold def10_R'; exact Finset.mem_union_left _ h

theorem C'_lt {M : Inst3} (hM : M.Valid) : ∀ c ∈ def10_C' M, c < M.n := by
  obtain ⟨_, hfit, _, _, _, hC, _⟩ := valid_unpack hM
  intro c hc
  unfold def10_C' at hc
  rcases Finset.mem_union.mp hc with h | h
  · exact hC c h
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    exact (fits_lt (hfit q hq)).1

theorem R'_lt {M : Inst3} (hM : M.Valid) : ∀ r ∈ def10_R' M, r < M.n := by
  obtain ⟨_, hfit, _, _, _, _, hR⟩ := valid_unpack hM
  intro r hr
  unfold def10_R' at hr
  rcases Finset.mem_union.mp hr with h | h
  · exact hR r h
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    exact (fits_lt (hfit q hq)).2

theorem card_C' {M : Inst3} (hM : M.Valid) : (def10_C' M).card = M.C.card + M.P.card := by
  obtain ⟨_, _, hdist, _, hPCR, _, _⟩ := valid_unpack hM
  have hinj : Set.InjOn col (M.P : Set Queen) := by
    intro q hq q' hq' he
    by_contra hne
    exact (hdist q hq q' hq' hne).1 he
  have hdisj : Disjoint M.C (M.P.image col) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc'
    exact (hPCR q hq).1 hc
  unfold def10_C'
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

theorem card_R' {M : Inst3} (hM : M.Valid) : (def10_R' M).card = M.R.card + M.P.card := by
  obtain ⟨_, _, hdist, _, hPCR, _, _⟩ := valid_unpack hM
  have hinj : Set.InjOn row (M.P : Set Queen) := by
    intro q hq q' hq' he
    by_contra hne
    exact (hdist q hq q' hq' hne).2 he
  have hdisj : Disjoint M.R (M.P.image row) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc'
    exact (hPCR q hq).2 hc
  unfold def10_R'
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

/-- The numerical facts used throughout. -/
theorem ctx {M : Inst3} (hM : M.Valid) :
    1 ≤ M.n ∧ def10_nprime M.n % 2 = 1 ∧ M.n ≤ def10_nprime M.n ∧
    2 * M.n ≤ def10_nprime M.n + 1 ∧
    (∀ c ∈ def10_C' M, c < M.n) ∧ (∀ r ∈ def10_R' M, r < M.n) ∧
    (def10_C' M).card ≤ M.n ∧ (def10_R' M).card = (def10_C' M).card := by
  obtain ⟨hn, -, -, hCR, -, -, -⟩ := valid_unpack hM
  obtain ⟨h1, h2, h3, -⟩ := np_facts M.n hn
  have hC' := C'_lt hM
  refine ⟨hn, h1, h2, h3, hC', R'_lt hM, ?_, ?_⟩
  · calc (def10_C' M).card ≤ (Finset.range M.n).card :=
          Finset.card_le_card (fun c hc => Finset.mem_range.mpr (hC' c hc))
      _ = M.n := Finset.card_range _
  · rw [card_C' hM, card_R' hM, hCR]

/-! ### The pieces of `P₂` -/

/-- `Q_C + n′(19, 8)`. -/
noncomputable def QCs (M : Inst3) : Finset Queen :=
  shiftSet (def10_QC M) (def10_nprime M.n • ((19, 8) : Queen))

/-- `Q_R + n′(17, 19)`. -/
noncomputable def QRs (M : Inst3) : Finset Queen :=
  shiftSet (def10_QR M) (def10_nprime M.n • ((17, 19) : Queen))

/-- `P₂ = Q₃ ∪ (Q_C + n′(19, 8)) ∪ (Q_R + n′(17, 19)) ∪ P₃`. -/
noncomputable def P2 (M : Inst3) : Finset Queen := def10_Q3 M ∪ QCs M ∪ QRs M ∪ M.P

/-- `n₂ = 19n′ + |C′|`. -/
def n2 (M : Inst3) : ℕ := 19 * def10_nprime M.n + (def10_C' M).card

theorem def10_eq (M : Inst3) (h : ¬ SelfAttacking M.P) : def10 M = ⟨n2 M, P2 M⟩ := by
  rw [def10, if_neg h]; rfl

theorem mem_P2_Q3 {M : Inst3} {q : Queen} (h : q ∈ def10_Q3 M) : q ∈ P2 M := by
  unfold P2; simp only [Finset.mem_union]; tauto

theorem mem_P2_QC {M : Inst3} {q : Queen} (h : q ∈ QCs M) : q ∈ P2 M := by
  unfold P2; simp only [Finset.mem_union]; tauto

theorem mem_P2_QR {M : Inst3} {q : Queen} (h : q ∈ QRs M) : q ∈ P2 M := by
  unfold P2; simp only [Finset.mem_union]; tauto

theorem mem_P2_P {M : Inst3} {q : Queen} (h : q ∈ M.P) : q ∈ P2 M := by
  unfold P2; simp only [Finset.mem_union]; tauto

theorem mem_Q3 {M : Inst3} {x : Queen} :
    x ∈ def10_Q3 M ↔
      x ∈ def10_Q2 (def10_nprime M.n) ∧ col x ∉ def10_C' M ∧ row x ∉ def10_R' M := by
  unfold def10_Q3; rw [Finset.mem_filter]

theorem exists_idx {s : Finset ℕ} {j : ℕ} (hj : j ∈ s) :
    ∃ k : Fin s.card, s.orderEmbOfFin rfl k = j := by
  have h : j ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hj
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

theorem mem_QCs {M : Inst3} {x : Queen} (hx : x ∈ QCs M) :
    ∃ k : Fin (def10_C' M).card,
      x = (((k : ℕ), 2 * (def10_C' M).orderEmbOfFin rfl k) : Queen) +
        def10_nprime M.n • ((19, 8) : Queen) := by
  unfold QCs shiftSet def10_QC at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨k, rfl⟩

theorem QCs_mem (M : Inst3) (k : Fin (def10_C' M).card) :
    (((k : ℕ), 2 * (def10_C' M).orderEmbOfFin rfl k) : Queen) +
      def10_nprime M.n • ((19, 8) : Queen) ∈ QCs M := by
  unfold QCs shiftSet def10_QC
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, rfl⟩

theorem mem_QCs' {M : Inst3} {x : Queen} (hx : x ∈ QCs M) :
    ∃ k < (def10_C' M).card, ∃ c ∈ def10_C' M,
      x = ((k, 2 * c) : Queen) + def10_nprime M.n • ((19, 8) : Queen) := by
  obtain ⟨k, rfl⟩ := mem_QCs hx
  exact ⟨k, k.2, _, Finset.orderEmbOfFin_mem _ _ _, rfl⟩

theorem QCs_mem_of {M : Inst3} {c : ℕ} (hc : c ∈ def10_C' M) :
    ∃ k < (def10_C' M).card,
      ((k, 2 * c) : Queen) + def10_nprime M.n • ((19, 8) : Queen) ∈ QCs M := by
  obtain ⟨k, hk⟩ := exists_idx hc
  refine ⟨k, k.2, ?_⟩
  have h := QCs_mem M k
  rw [hk] at h
  exact h

theorem QCs_mem_of_idx {M : Inst3} {k : ℕ} (hk : k < (def10_C' M).card) :
    ∃ c ∈ def10_C' M, ((k, 2 * c) : Queen) + def10_nprime M.n • ((19, 8) : Queen) ∈ QCs M :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ ⟨k, hk⟩, QCs_mem M ⟨k, hk⟩⟩

theorem mem_QRs {M : Inst3} {x : Queen} (hx : x ∈ QRs M) :
    ∃ k : Fin (def10_R' M).card,
      x = ((2 * (def10_R' M).orderEmbOfFin rfl k, (k : ℕ)) : Queen) +
        def10_nprime M.n • ((17, 19) : Queen) := by
  unfold QRs shiftSet def10_QR at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
  exact ⟨k, rfl⟩

theorem QRs_mem (M : Inst3) (k : Fin (def10_R' M).card) :
    ((2 * (def10_R' M).orderEmbOfFin rfl k, (k : ℕ)) : Queen) +
      def10_nprime M.n • ((17, 19) : Queen) ∈ QRs M := by
  unfold QRs shiftSet def10_QR
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, rfl⟩

theorem mem_QRs' {M : Inst3} {x : Queen} (hx : x ∈ QRs M) :
    ∃ k < (def10_R' M).card, ∃ c ∈ def10_R' M,
      x = ((2 * c, k) : Queen) + def10_nprime M.n • ((17, 19) : Queen) := by
  obtain ⟨k, rfl⟩ := mem_QRs hx
  exact ⟨k, k.2, _, Finset.orderEmbOfFin_mem _ _ _, rfl⟩

theorem QRs_mem_of {M : Inst3} {c : ℕ} (hc : c ∈ def10_R' M) :
    ∃ k < (def10_R' M).card,
      ((2 * c, k) : Queen) + def10_nprime M.n • ((17, 19) : Queen) ∈ QRs M := by
  obtain ⟨k, hk⟩ := exists_idx hc
  refine ⟨k, k.2, ?_⟩
  have h := QRs_mem M k
  rw [hk] at h
  exact h

theorem QRs_mem_of_idx {M : Inst3} {k : ℕ} (hk : k < (def10_R' M).card) :
    ∃ c ∈ def10_R' M, ((2 * c, k) : Queen) + def10_nprime M.n • ((17, 19) : Queen) ∈ QRs M :=
  ⟨_, Finset.orderEmbOfFin_mem _ _ ⟨k, hk⟩, QRs_mem M ⟨k, hk⟩⟩

/-! ### Columns covered by `P₂` -/

/-- Every column `c < n₂` outside `C` is used by a queen of `P₂`. -/
theorem P2_cover_col {M : Inst3} (hM : M.Valid) (c : ℕ) (hc : c < n2 M) (hcC : c ∉ M.C) :
    ∃ p ∈ P2 M, col p = c := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, h08, hlt, hc17, hr0, hc0, hr8, hexc, hexr⟩ := q19_facts
  have hN0 : 0 < def10_nprime M.n := by omega
  unfold n2 at hc
  by_cases h1 : c < def10_nprime M.n
  · by_cases hcm : c ∈ def10_C' M
    · have hcm' := hcm
      unfold def10_C' at hcm'
      rcases Finset.mem_union.mp hcm' with h | h
      · exact absurd h hcC
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
        exact ⟨q, mem_P2_P hq, rfl⟩
    · refine ⟨((c, 2 * c % def10_nprime M.n) : Queen) + def10_nprime M.n • ((0, 8) : Queen),
        mem_P2_Q3 (mem_Q3.mpr ⟨A_block_mem h1 h08 (by decide), ?_, ?_⟩), ?_⟩
      · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero]
        exact hcm
      · intro hr
        have := hR' _ hr
        simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
        omega
      · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero]
  · by_cases h2 : c < 19 * def10_nprime M.n
    · have hdm := Nat.mod_add_div c (def10_nprime M.n)
      have hi := Nat.mod_lt c hN0
      have ha19 : c / def10_nprime M.n < 19 := Nat.div_lt_of_lt_mul (by omega)
      obtain ⟨v, hv, hva⟩ := hexc _ ha19
      by_cases hv17 : v = (17, 0)
      · subst hv17
        have hva' : c / def10_nprime M.n = 17 := hva.symm
        rw [hva'] at hdm
        obtain ⟨j, hj, hjc⟩ := half_exists hNodd hi
        by_cases hjR : j ∈ def10_R' M
        · obtain ⟨k, hk, hmem⟩ := QRs_mem_of hjR
          refine ⟨_, mem_P2_QR hmem, ?_⟩
          have := hR' j hjR
          rw [Nat.mod_eq_of_lt (by omega : 2 * j < def10_nprime M.n)] at hjc
          simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          omega
        · refine ⟨((2 * j % def10_nprime M.n, j) : Queen) + def10_nprime M.n • ((17, 0) : Queen),
            mem_P2_Q3 (mem_Q3.mpr ⟨B_block_mem hj, ?_, ?_⟩), ?_⟩
          · intro hcm
            have := hC' _ hcm
            simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
            omega
          · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
            exact hjR
          · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
            omega
      · refine ⟨((c % def10_nprime M.n, 2 * (c % def10_nprime M.n) % def10_nprime M.n) : Queen) +
            def10_nprime M.n • v, mem_P2_Q3 (mem_Q3.mpr ⟨A_block_mem hi hv hv17, ?_, ?_⟩), ?_⟩
        · intro hcm
          have := hC' _ hcm
          simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
          rw [hva] at this
          omega
        · intro hrm
          have := hR' _ hrm
          simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
          have hv2 : 1 ≤ v.2 := by
            by_contra h0
            exact hv17 (hr0 v hv (by omega))
          have := Nat.mul_le_mul_left (def10_nprime M.n) hv2
          omega
        · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          rw [hva]; exact hdm
    · have hk : c - 19 * def10_nprime M.n < (def10_C' M).card := by omega
      obtain ⟨c', hc', hmem⟩ := QCs_mem_of_idx hk
      refine ⟨_, mem_P2_QC hmem, ?_⟩
      simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      omega


/-! ### Rows covered by `P₂` -/

/-- Every row `r < n₂` outside `R` is used by a queen of `P₂`. -/
theorem P2_cover_row {M : Inst3} (hM : M.Valid) (r : ℕ) (hr : r < n2 M) (hrR : r ∉ M.R) :
    ∃ p ∈ P2 M, row p = r := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, h08, hlt, hc17, hr0, hc0, hr8, hexc, hexr⟩ := q19_facts
  have hN0 : 0 < def10_nprime M.n := by omega
  unfold n2 at hr
  by_cases h1 : r < def10_nprime M.n
  · by_cases hrm : r ∈ def10_R' M
    · have hrm' := hrm
      unfold def10_R' at hrm'
      rcases Finset.mem_union.mp hrm' with h | h
      · exact absurd h hrR
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
        exact ⟨q, mem_P2_P hq, rfl⟩
    · refine ⟨((2 * r % def10_nprime M.n, r) : Queen) + def10_nprime M.n • ((17, 0) : Queen),
        mem_P2_Q3 (mem_Q3.mpr ⟨B_block_mem h1, ?_, ?_⟩), ?_⟩
      · intro hc
        have := hC' _ hc
        simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
        omega
      · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
        exact hrm
      · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
  · by_cases h2 : r < 19 * def10_nprime M.n
    · have hdm := Nat.mod_add_div r (def10_nprime M.n)
      have hj := Nat.mod_lt r hN0
      have hb19 : r / def10_nprime M.n < 19 := Nat.div_lt_of_lt_mul (by omega)
      have hb1 : 1 ≤ r / def10_nprime M.n := Nat.div_pos (by omega) hN0
      have hbN := Nat.mul_le_mul_left (def10_nprime M.n) hb1
      obtain ⟨v, hv, hvb⟩ := hexr _ hb19
      have hv17 : v ≠ (17, 0) := by
        intro e
        have h0 : v.2 = 0 := by rw [e]
        omega
      obtain ⟨i, hi, hij⟩ := half_exists hNodd hj
      by_cases hv0 : v.1 = 0
      · have hv08 := hc0 v hv hv0
        subst hv08
        have hvb' : r / def10_nprime M.n = 8 := hvb.symm
        rw [hvb'] at hdm
        by_cases hiC : i ∈ def10_C' M
        · obtain ⟨k, hk, hmem⟩ := QCs_mem_of hiC
          refine ⟨_, mem_P2_QC hmem, ?_⟩
          have := hC' i hiC
          rw [Nat.mod_eq_of_lt (by omega : 2 * i < def10_nprime M.n)] at hij
          simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          omega
        · refine ⟨((i, 2 * i % def10_nprime M.n) : Queen) + def10_nprime M.n • ((0, 8) : Queen),
            mem_P2_Q3 (mem_Q3.mpr ⟨A_block_mem hi h08 (by decide), ?_, ?_⟩), ?_⟩
          · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero]
            exact hiC
          · intro hrm
            have := hR' _ hrm
            simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
            omega
          · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            omega
      · refine ⟨((i, 2 * i % def10_nprime M.n) : Queen) + def10_nprime M.n • v,
          mem_P2_Q3 (mem_Q3.mpr ⟨A_block_mem hi hv hv17, ?_, ?_⟩), ?_⟩
        · intro hcm
          have := hC' _ hcm
          simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this
          have hv1 : 1 ≤ v.1 := by omega
          have := Nat.mul_le_mul_left (def10_nprime M.n) hv1
          omega
        · intro hrm
          have := hR' _ hrm
          simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at this
          rw [hvb] at this
          omega
        · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [hvb, hij]; exact hdm
    · have hk : r - 19 * def10_nprime M.n < (def10_R' M).card := by omega
      obtain ⟨c', hc', hmem⟩ := QRs_mem_of_idx hk
      refine ⟨_, mem_P2_QR hmem, ?_⟩
      simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      omega

/-! ### The queens of `P₂ \ P₃` are large -/

theorem big_Q3 {M : Inst3} (hM : M.Valid) {q : Queen} (hq : q ∈ def10_Q3 M) :
    M.n ≤ size q ∧ col q ∉ M.C := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, h08, hlt, hc17, hr0, hc0, hr8, -, -⟩ := q19_facts
  obtain ⟨hxQ2, hxc, hxr⟩ := mem_Q3.mp hq
  refine ⟨?_, fun h => hxc (C_sub_C' h)⟩
  simp only [size]
  rcases Q2_cases hxQ2 with ⟨i, hi, v, hv, hv17, rfl⟩ | ⟨i, hi, rfl⟩
  · by_cases hv0 : v.1 = 0
    · obtain rfl := hc0 v hv hv0
      apply le_max_of_le_right
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      omega
    · apply le_max_of_le_left
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      have hv1 : 1 ≤ v.1 := by omega
      have := Nat.mul_le_mul_left (def10_nprime M.n) hv1
      omega
  · apply le_max_of_le_left
    simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    omega

theorem big_QC {M : Inst3} (hM : M.Valid) {q : Queen} (hq : q ∈ QCs M) :
    M.n ≤ size q ∧ col q ∉ M.C := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QCs' hq
  have hcol : M.n ≤ col (((k, 2 * c) : Queen) + def10_nprime M.n • ((19, 8) : Queen)) := by
    simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; omega
  refine ⟨?_, fun h => ?_⟩
  · simp only [size]; exact le_max_of_le_left hcol
  · have := hC' _ (C_sub_C' h)
    omega

theorem big_QR {M : Inst3} (hM : M.Valid) {q : Queen} (hq : q ∈ QRs M) :
    M.n ≤ size q ∧ col q ∉ M.C := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QRs' hq
  have hcol : M.n ≤ col (((2 * c, k) : Queen) + def10_nprime M.n • ((17, 19) : Queen)) := by
    simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; omega
  refine ⟨?_, fun h => ?_⟩
  · simp only [size]; exact le_max_of_le_left hcol
  · have := hC' _ (C_sub_C' h)
    omega

theorem big_P2 {M : Inst3} (hM : M.Valid) :
    ∀ q ∈ P2 M, q ∉ M.P → M.n ≤ size q ∧ col q ∉ M.C := by
  intro q hq hqP
  unfold P2 at hq
  simp only [Finset.mem_union] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · exact big_Q3 hM hq
  · exact big_QC hM hq
  · exact big_QR hM hq
  · exact absurd hq hqP

/-- In a completion of `P₂`, every queen outside `P₂` uses a column of `C` and a row of `R`. -/
theorem outside_P2 {M : Inst3} (hM : M.Valid) {S₂ : Finset Queen}
    (hS : IsNQueensSol (n2 M) S₂) (hPS : P2 M ⊆ S₂) :
    ∀ q ∈ S₂, q ∉ P2 M → col q ∈ M.C ∧ row q ∈ M.R := by
  obtain ⟨_, hfit2, _, hNA2⟩ := hS
  intro q hq hqP
  have hf := fits_lt (hfit2 q hq)
  constructor
  · by_contra hcC
    obtain ⟨p, hp, hpc⟩ := P2_cover_col hM (col q) hf.1 hcC
    exact hNA2 p (hPS hp) q hq ⟨fun e => hqP (e ▸ hp), Or.inl hpc⟩
  · by_contra hrR
    obtain ⟨p, hp, hpr⟩ := P2_cover_row hM (row q) hf.2 hrR
    exact hNA2 p (hPS hp) q hq ⟨fun e => hqP (e ▸ hp), Or.inr (Or.inl hpr)⟩

theorem isSol_def10 {M : Inst3} (h : ¬ SelfAttacking M.P) (S : Finset Queen) :
    (def10 M).IsSol S ↔ IsNQueensSol (n2 M) S ∧ P2 M ⊆ S := by
  rw [def10_eq M h]; rfl

/-- Lemma 11. -/
theorem lemma11_proof (M : Inst3) (hM : M.Valid) (S₂ : Finset Queen) (hS : (def10 M).IsSol S₂) :
    M.IsSol (S₂.filter (fun q => size q < M.n)) := by
  obtain ⟨hn, hfitP, hdist, hCR, hPCR, hC, hR⟩ := valid_unpack hM
  by_cases hsa : SelfAttacking M.P
  · exfalso
    rw [def10, if_pos hsa] at hS
    obtain ⟨⟨_, _, _, hNA⟩, hPS⟩ := hS
    obtain ⟨q₁, h₁, q₂, h₂, hatt⟩ := hsa
    exact hNA q₁ (hPS h₁) q₂ (hPS h₂) hatt
  have hS2 := (isSol_def10 hsa S₂).mp hS
  obtain ⟨⟨hn2, hfit2, hcard2, hNA2⟩, hPS⟩ := hS2
  have hA := outside_P2 hM ⟨hn2, hfit2, hcard2, hNA2⟩ hPS
  have hB := big_P2 hM
  have hPT : M.P ⊆ S₂.filter (fun q => size q < M.n) := by
    intro q hq
    rw [Finset.mem_filter]
    exact ⟨hPS (mem_P2_P hq), hfitP q hq⟩
  have hTP : ∀ q ∈ S₂.filter (fun q => size q < M.n) \ M.P, q ∈ S₂ ∧ q ∉ P2 M := by
    intro q hq
    rw [Finset.mem_sdiff, Finset.mem_filter] at hq
    obtain ⟨⟨hqS, hqs⟩, hqP⟩ := hq
    refine ⟨hqS, fun hq2 => ?_⟩
    have := (hB q hq2 hqP).1
    omega
  refine ⟨?_, hPT, fun q₁ h₁ q₂ h₂ =>
    hNA2 q₁ (Finset.mem_filter.mp h₁).1 q₂ (Finset.mem_filter.mp h₂).1, ?_⟩
  · have hinj : Set.InjOn col
        ((S₂.filter (fun q => size q < M.n) \ M.P : Finset Queen) : Set Queen) := by
      intro q hq q' hq' he
      by_contra hne
      exact hNA2 q (hTP q (Finset.mem_coe.mp hq)).1 q' (hTP q' (Finset.mem_coe.mp hq')).1
        ⟨hne, Or.inl he⟩
    have himg : (S₂.filter (fun q => size q < M.n) \ M.P).image col = M.C := by
      apply Finset.Subset.antisymm
      · intro c hc
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
        have := hTP q hq
        exact (hA q this.1 this.2).1
      · intro c hc
        have hc2 : c < n2 M := by
          have := hC c hc
          have := (np_facts M.n hn).2.1
          unfold n2; omega
        have hcr : c ∈ S₂.image col := by
          rw [image_col_eq_range ⟨hn2, hfit2, hcard2, hNA2⟩]
          exact Finset.mem_range.mpr hc2
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hcr
        have hqP2 : q ∉ P2 M := by
          intro hq2
          by_cases hqP : q ∈ M.P
          · exact (hPCR q hqP).1 hc
          · exact (hB q hq2 hqP).2 hc
        have hqA := hA q hq hqP2
        have hsz : size q < M.n := fits_of_lt (hC _ hqA.1) (hR _ hqA.2)
        refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
        rw [Finset.mem_sdiff, Finset.mem_filter]
        exact ⟨⟨hq, hsz⟩, fun hqP => hqP2 (mem_P2_P hqP)⟩
    have h1 := Finset.card_image_of_injOn hinj
    rw [himg] at h1
    have h2 := Finset.card_sdiff_add_card_eq_card hPT
    omega
  · intro q hq
    have := hTP q hq
    exact hA q this.1 this.2

end NQueensComp.NPC.Def10Proof

open NQueensComp.NPC.Def10Proof

theorem solution (M : Inst3) (hM : M.Valid) (S₂ : Finset Queen) (hS : (def10 M).IsSol S₂) :
    M.IsSol (S₂.filter (fun q => size q < M.n)) :=
  lemma11_proof M hM S₂ hS
