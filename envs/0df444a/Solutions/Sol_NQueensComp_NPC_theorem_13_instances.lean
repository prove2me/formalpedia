-- Prove2me | solution 1 for NQueensComp.NPC.theorem_13_instances
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T03:18:32.133467+00:00
-- url     : https://prove2.me/submissions/6954de53-57ca-4814-9fa7-e08e45dc15ea

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions
import Theorems.Thm_NQueensComp_NPC_theorem_2
import Theorems.Thm_NQueensComp_NPC_lemma_7
import Theorems.Thm_NQueensComp_NPC_lemma_8
import Theorems.Thm_NQueensComp_NPC_lemma_9
import Theorems.Thm_NQueensComp_NPC_observation_6

open NQueensComp.NPC

namespace NQueensComp.NPC.Def10Proof

/-! ### Generic facts about queens -/

theorem attacks_symm {q₁ q₂ : Queen} (h : Attacks q₁ q₂) : Attacks q₂ q₁ := by
  obtain ⟨hne, h⟩ := h
  refine ⟨fun e => hne e.symm, ?_⟩
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr h.symm))

theorem attacks_shift {a b t : Queen} (h : Attacks (a + t) (b + t)) : Attacks a b := by
  obtain ⟨hne, h⟩ := h
  refine ⟨fun e => hne (by rw [e]), ?_⟩
  simp only [col, row, sumDiag, diffDiag, Prod.fst_add, Prod.snd_add] at h ⊢
  push_cast at h
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

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

/-- Two numbers below `n` plus distinct multiples of `n` differ. -/
theorem key_col (n x y u v : ℕ) (hx : x < n) (hy : y < n) (huv : u ≠ v) :
    x + n * u ≠ y + n * v := by
  intro heq
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have : n * (u + 1) ≤ n * v := Nat.mul_le_mul_left n h
    nlinarith
  · have : n * (v + 1) ≤ n * u := Nat.mul_le_mul_left n h
    nlinarith

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

theorem q19_diag :
    ∀ v ∈ Q19, ∀ m ∈ ({(0, 0), (19, 8), (17, 19)} : Finset Queen),
      1 < |((sumDiag v : ℕ) : ℤ) - ((sumDiag m : ℕ) : ℤ)| ∧ 1 < |diffDiag v - diffDiag m| := by
  unfold sumDiag diffDiag Q19
  decide +kernel

theorem blk_diag :
    (1 < |((sumDiag ((19, 8) : Queen) : ℕ) : ℤ) - ((sumDiag ((17, 19) : Queen) : ℕ) : ℤ)| ∧
      1 < |diffDiag ((19, 8) : Queen) - diffDiag ((17, 19) : Queen)|) ∧
    (1 < |((sumDiag ((19, 8) : Queen) : ℕ) : ℤ) - ((sumDiag ((0, 0) : Queen) : ℕ) : ℤ)| ∧
      1 < |diffDiag ((19, 8) : Queen) - diffDiag ((0, 0) : Queen)|) ∧
    (1 < |((sumDiag ((17, 19) : Queen) : ℕ) : ℤ) - ((sumDiag ((0, 0) : Queen) : ℕ) : ℤ)| ∧
      1 < |diffDiag ((17, 19) : Queen) - diffDiag ((0, 0) : Queen)|) := by
  unfold sumDiag diffDiag
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

theorem image_shift {β : Type*} [DecidableEq β] [Add β] (f : Queen → β)
    (hf : ∀ q t : Queen, f (q + t) = f q + f t) (X : Finset Queen) (t : Queen) :
    (shiftSet X t).image f = (X.image f).image (· + f t) := by
  unfold shiftSet
  rw [Finset.image_image, Finset.image_image]
  congr 1
  funext q
  exact hf q t

theorem col_add (q t : Queen) : col (q + t) = col q + col t := rfl

theorem row_add (q t : Queen) : row (q + t) = row q + row t := rfl

theorem sumDiag_add (q t : Queen) : sumDiag (q + t) = sumDiag q + sumDiag t := by
  simp only [sumDiag, Prod.fst_add, Prod.snd_add]; ring

theorem diffDiag_add (q t : Queen) : diffDiag (q + t) = diffDiag q + diffDiag t := by
  simp only [diffDiag, Prod.fst_add, Prod.snd_add]; push_cast; ring

/-- Pólya's construction with the Rivin–Zabih exchange: `Q₂` is non-attacking and fits on
board size `19n′`. -/
theorem Q2_good {N : ℕ} (hN : N % 6 = 1 ∨ N % 6 = 5) :
    NonAttacking (def10_Q2 N) ∧ ∀ q ∈ def10_Q2 N, FitsOn (N * 19) q := by
  obtain ⟨hA, hB, hsd, hdd⟩ := lemma_7 N hN
  have h6 := observation_6
  have hPol := theorem_2 N 19 (A N) Q19 hA h6.1
  obtain ⟨h17, -, -, hc17, -⟩ := q19_facts
  have hsub : shiftSet (A N) (N • ((17, 0) : Queen)) ⊆ sumSet (A N) (scaleSet N Q19) := by
    intro x hx
    unfold shiftSet at hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    refine mem_sumSet.mpr ⟨a, ha, N • ((17, 0) : Queen), ?_, rfl⟩
    unfold scaleSet
    exact Finset.mem_image.mpr ⟨_, h17, rfl⟩
  have hcard : (shiftSet (B N) (N • ((17, 0) : Queen))).card =
      (shiftSet (A N) (N • ((17, 0) : Queen))).card := by
    unfold shiftSet
    rw [Finset.card_image_of_injective _ (add_left_injective _),
      Finset.card_image_of_injective _ (add_left_injective _), hA.1.2.2.1, hB.1.2.2.1]
  have hrow : (shiftSet (B N) (N • ((17, 0) : Queen))).image row =
      (shiftSet (A N) (N • ((17, 0) : Queen))).image row := by
    rw [image_shift row row_add, image_shift row row_add, image_row_eq_range hA.1,
      image_row_eq_range hB.1]
  have hcol : (shiftSet (B N) (N • ((17, 0) : Queen))).image col =
      (shiftSet (A N) (N • ((17, 0) : Queen))).image col := by
    rw [image_shift col col_add, image_shift col col_add, image_col_eq_range hA.1,
      image_col_eq_range hB.1]
  have hsum : (shiftSet (B N) (N • ((17, 0) : Queen))).image sumDiag =
      (shiftSet (A N) (N • ((17, 0) : Queen))).image sumDiag := by
    rw [image_shift sumDiag sumDiag_add, image_shift sumDiag sumDiag_add, hsd]
  have hdiff : (shiftSet (B N) (N • ((17, 0) : Queen))).image diffDiag =
      (shiftSet (A N) (N • ((17, 0) : Queen))).image diffDiag := by
    rw [image_shift diffDiag diffDiag_add, image_shift diffDiag diffDiag_add, hdd]
  have h8 := lemma_8 (N * 19) _ _ _ hPol hsub hcard hrow hcol hsum hdiff
  have hQ2 : def10_Q2 N ⊆ (sumSet (A N) (scaleSet N Q19) \ shiftSet (A N) (N • ((17, 0) : Queen)))
      ∪ shiftSet (B N) (N • ((17, 0) : Queen)) := by
    intro x hx
    rcases Q2_cases hx with ⟨i, hi, v, hv, hv17, rfl⟩ | ⟨i, hi, rfl⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_sdiff]
      refine ⟨mem_sumSet.mpr ⟨_, A_mem hi, N • v, ?_, rfl⟩, ?_⟩
      · unfold scaleSet
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      · intro hx
        unfold shiftSet at hx
        obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hx
        obtain ⟨i', hi', rfl⟩ := mem_A ha
        have h1 := congrArg Prod.fst he
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] at h1
        have h1' : v.1 = 17 := by
          by_contra hne
          exact key_col N i' i 17 v.1 hi' hi (Ne.symm hne) h1
        exact hv17 (hc17 v hv h1')
    · apply Finset.mem_union_right
      unfold shiftSet
      exact Finset.mem_image.mpr ⟨_, B_mem hi, rfl⟩
  exact ⟨fun q₁ h₁ q₂ h₂ => h8.2.2.2 q₁ (hQ2 h₁) q₂ (hQ2 h₂), fun q hq => h8.2.1 q (hQ2 hq)⟩

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

/-! ### Non-attacking -/

/-- Lemma 9 packaged: scaled blocks with separated lines do not attack. -/
theorem na_blocks {N : ℕ} {u₁ u₂ v₁ v₂ : Queen} (h₁ : FitsOn N u₁) (h₂ : FitsOn N u₂)
    (hc : col (u₁ + N • v₁) ≠ col (u₂ + N • v₂)) (hr : row (u₁ + N • v₁) ≠ row (u₂ + N • v₂))
    (hs : 1 < |((sumDiag v₁ : ℕ) : ℤ) - ((sumDiag v₂ : ℕ) : ℤ)|)
    (hd : 1 < |diffDiag v₁ - diffDiag v₂|) : ¬ Attacks (u₁ + N • v₁) (u₂ + N • v₂) := by
  have h9 := lemma_9 N u₁ u₂ v₁ v₂ h₁ h₂
  rintro ⟨_, h | h | h | h⟩
  · exact hc h
  · exact hr h
  · exact h9.2.2.1 hs h
  · exact h9.2.2.2.1 hd h

theorem na_blocks0 {N : ℕ} {u₁ v₁ s : Queen} (h₁ : FitsOn N u₁) (hs : FitsOn N s)
    (hc : col (u₁ + N • v₁) ≠ col s) (hr : row (u₁ + N • v₁) ≠ row s)
    (hsd : 1 < |((sumDiag v₁ : ℕ) : ℤ) - ((sumDiag ((0, 0) : Queen) : ℕ) : ℤ)|)
    (hd : 1 < |diffDiag v₁ - diffDiag ((0, 0) : Queen)|) : ¬ Attacks (u₁ + N • v₁) s := by
  have e : s + N • ((0, 0) : Queen) = s := Prod.ext (by simp) (by simp)
  have h := na_blocks (v₂ := ((0, 0) : Queen)) h₁ hs (by rw [e]; exact hc) (by rw [e]; exact hr)
    hsd hd
  rwa [e] at h

theorem na_Q3_QC {M : Inst3} (hM : M.Valid) {x y : Queen} (hx : x ∈ def10_Q3 M)
    (hy : y ∈ QCs M) : ¬ Attacks x y := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, h08, hlt, hc17, hr0, hc0, hr8, -, -⟩ := q19_facts
  obtain ⟨hxQ2, hxc, hxr⟩ := mem_Q3.mp hx
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QCs' hy
  have hc' := hC' c hc
  have hfu₂ : FitsOn (def10_nprime M.n) ((k, 2 * c) : Queen) := fits_mk (by omega) (by omega)
  rcases Q2_cases hxQ2 with ⟨i, hi, v, hv, hv17, rfl⟩ | ⟨i, hi, rfl⟩
  · have hfu₁ : FitsOn (def10_nprime M.n) ((i, 2 * i % def10_nprime M.n) : Queen) :=
      fits_mk hi (Nat.mod_lt _ (by omega))
    have h9 := lemma_9 _ _ _ v ((19, 8) : Queen) hfu₁ hfu₂
    have hd := q19_diag v hv (19, 8) (by simp)
    refine na_blocks hfu₁ hfu₂ (h9.1 ?_) ?_ hd.1 hd.2
    · have := (hlt v hv).1
      simp only [col]; omega
    · by_cases hv8 : v.2 = 8
      · obtain rfl := hr8 v hv hv8
        intro hrow
        simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hrow
        have hie : i = c := half_inj hNodd hi (by omega) (Nat.add_right_cancel hrow)
        apply hxc
        simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_zero, add_zero]
        rw [hie]; exact hc
      · exact h9.2.1 (by simp only [row]; omega)
  · have hfu₁ : FitsOn (def10_nprime M.n) ((2 * i % def10_nprime M.n, i) : Queen) :=
      fits_mk (Nat.mod_lt _ (by omega)) hi
    have h9 := lemma_9 _ _ _ ((17, 0) : Queen) ((19, 8) : Queen) hfu₁ hfu₂
    have hd := q19_diag _ h17 (19, 8) (by simp)
    exact na_blocks hfu₁ hfu₂ (h9.1 (by decide)) (h9.2.1 (by decide)) hd.1 hd.2

theorem na_Q3_QR {M : Inst3} (hM : M.Valid) {x y : Queen} (hx : x ∈ def10_Q3 M)
    (hy : y ∈ QRs M) : ¬ Attacks x y := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, h08, hlt, hc17, hr0, hc0, hr8, -, -⟩ := q19_facts
  obtain ⟨hxQ2, hxc, hxr⟩ := mem_Q3.mp hx
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QRs' hy
  have hc' := hR' c hc
  have hfu₂ : FitsOn (def10_nprime M.n) ((2 * c, k) : Queen) := fits_mk (by omega) (by omega)
  rcases Q2_cases hxQ2 with ⟨i, hi, v, hv, hv17, rfl⟩ | ⟨i, hi, rfl⟩
  · have hfu₁ : FitsOn (def10_nprime M.n) ((i, 2 * i % def10_nprime M.n) : Queen) :=
      fits_mk hi (Nat.mod_lt _ (by omega))
    have h9 := lemma_9 _ _ _ v ((17, 19) : Queen) hfu₁ hfu₂
    have hd := q19_diag v hv (17, 19) (by simp)
    refine na_blocks hfu₁ hfu₂ (h9.1 ?_) (h9.2.1 ?_) hd.1 hd.2
    · intro h
      exact hv17 (hc17 v hv h)
    · have := (hlt v hv).2
      simp only [row]; omega
  · have hfu₁ : FitsOn (def10_nprime M.n) ((2 * i % def10_nprime M.n, i) : Queen) :=
      fits_mk (Nat.mod_lt _ (by omega)) hi
    have h9 := lemma_9 _ _ _ ((17, 0) : Queen) ((17, 19) : Queen) hfu₁ hfu₂
    have hd := q19_diag _ h17 (17, 19) (by simp)
    refine na_blocks hfu₁ hfu₂ ?_ (h9.2.1 (by decide)) hd.1 hd.2
    intro hcol
    simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at hcol
    have hic : i = c := half_inj hNodd hi (by omega) (Nat.add_right_cancel hcol)
    apply hxr
    simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero]
    rw [hic]; exact hc

theorem na_Q3_T {M : Inst3} (hM : M.Valid) {x s : Queen} (hx : x ∈ def10_Q3 M)
    (hsc : col s ∈ def10_C' M) (hsr : row s ∈ def10_R' M) : ¬ Attacks x s := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨h17, -⟩ := q19_facts
  obtain ⟨hxQ2, hxc, hxr⟩ := mem_Q3.mp hx
  have h1 := hC' _ hsc
  have h2 := hR' _ hsr
  simp only [col, row] at h1 h2
  have hfs : FitsOn (def10_nprime M.n) s := fits_of_lt (by omega) (by omega)
  have hcol : col x ≠ col s := fun h => hxc (by rw [h]; exact hsc)
  have hrow : row x ≠ row s := fun h => hxr (by rw [h]; exact hsr)
  rcases Q2_cases hxQ2 with ⟨i, hi, v, hv, hv17, rfl⟩ | ⟨i, hi, rfl⟩
  · have hfu₁ : FitsOn (def10_nprime M.n) ((i, 2 * i % def10_nprime M.n) : Queen) :=
      fits_mk hi (Nat.mod_lt _ (by omega))
    have hd := q19_diag v hv (0, 0) (by simp)
    exact na_blocks0 hfu₁ hfs hcol hrow hd.1 hd.2
  · have hfu₁ : FitsOn (def10_nprime M.n) ((2 * i % def10_nprime M.n, i) : Queen) :=
      fits_mk (Nat.mod_lt _ (by omega)) hi
    have hd := q19_diag _ h17 (0, 0) (by simp)
    exact na_blocks0 hfu₁ hfs hcol hrow hd.1 hd.2

theorem na_QC_QR {M : Inst3} (hM : M.Valid) {x y : Queen} (hx : x ∈ QCs M) (hy : y ∈ QRs M) :
    ¬ Attacks x y := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QCs' hx
  obtain ⟨k', hk', c', hc', rfl⟩ := mem_QRs' hy
  have := hC' c hc
  have := hR' c' hc'
  have hfu₁ : FitsOn (def10_nprime M.n) ((k, 2 * c) : Queen) := fits_mk (by omega) (by omega)
  have hfu₂ : FitsOn (def10_nprime M.n) ((2 * c', k') : Queen) := fits_mk (by omega) (by omega)
  have h9 := lemma_9 _ _ _ ((19, 8) : Queen) ((17, 19) : Queen) hfu₁ hfu₂
  exact h9.2.2.2.2 (by decide) (by decide) blk_diag.1.1 blk_diag.1.2

theorem na_QC_T {M : Inst3} (hM : M.Valid) {x s : Queen} (hx : x ∈ QCs M)
    (hsc : col s ∈ def10_C' M) (hsr : row s ∈ def10_R' M) : ¬ Attacks x s := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QCs' hx
  have := hC' c hc
  have h1 := hC' _ hsc
  have h2 := hR' _ hsr
  simp only [col, row] at h1 h2
  have hfu₁ : FitsOn (def10_nprime M.n) ((k, 2 * c) : Queen) := fits_mk (by omega) (by omega)
  have hfs : FitsOn (def10_nprime M.n) s := fits_of_lt (by omega) (by omega)
  refine na_blocks0 hfu₁ hfs ?_ ?_ blk_diag.2.1.1 blk_diag.2.1.2
  · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; omega
  · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; omega

theorem na_QR_T {M : Inst3} (hM : M.Valid) {x s : Queen} (hx : x ∈ QRs M)
    (hsc : col s ∈ def10_C' M) (hsr : row s ∈ def10_R' M) : ¬ Attacks x s := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  obtain ⟨k, hk, c, hc, rfl⟩ := mem_QRs' hx
  have := hR' c hc
  have h1 := hC' _ hsc
  have h2 := hR' _ hsr
  simp only [col, row] at h1 h2
  have hfu₁ : FitsOn (def10_nprime M.n) ((2 * c, k) : Queen) := fits_mk (by omega) (by omega)
  have hfs : FitsOn (def10_nprime M.n) s := fits_of_lt (by omega) (by omega)
  refine na_blocks0 hfu₁ hfs ?_ ?_ blk_diag.2.2.1 blk_diag.2.2.2
  · simp only [col, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; omega
  · simp only [row, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; omega

/-- A strictly increasing sequence of naturals grows by at least one per step. -/
theorem gap {k : ℕ} (f : Fin k → ℕ) (hf : StrictMono f) :
    ∀ d : ℕ, ∀ i j : Fin k, (j : ℕ) = i + d → f i + d ≤ f j := by
  intro d
  induction d with
  | zero =>
    intro i j h
    have : i = j := Fin.ext (by omega)
    subst this; simp
  | succ d ih =>
    intro i j h
    have hj : (j : ℕ) - 1 < k := by omega
    have h1 := ih i ⟨(j : ℕ) - 1, hj⟩ (by simp only; omega)
    have h2 : f ⟨(j : ℕ) - 1, hj⟩ < f j := hf (by rw [Fin.lt_def]; simp only; omega)
    omega

theorem na_graph_C {k : ℕ} (f : Fin k → ℕ) (hf : StrictMono f) (i j : Fin k) :
    ¬ Attacks (((i : ℕ), 2 * f i) : Queen) ((j : ℕ), 2 * f j) := by
  rintro ⟨hne, h⟩
  simp only [col, row, sumDiag, diffDiag] at h
  rcases lt_trichotomy i j with hij | hij | hij
  · have h1 := gap f hf ((j : ℕ) - i) i j (by rw [Fin.lt_def] at hij; omega)
    have h2 := hf hij
    rw [Fin.lt_def] at hij
    rcases h with h | h | h | h <;> push_cast at h <;> omega
  · exact hne (by rw [hij])
  · have h1 := gap f hf ((i : ℕ) - j) j i (by rw [Fin.lt_def] at hij; omega)
    have h2 := hf hij
    rw [Fin.lt_def] at hij
    rcases h with h | h | h | h <;> push_cast at h <;> omega

theorem na_graph_R {k : ℕ} (f : Fin k → ℕ) (hf : StrictMono f) (i j : Fin k) :
    ¬ Attacks ((2 * f i, (i : ℕ)) : Queen) (2 * f j, (j : ℕ)) := by
  rintro ⟨hne, h⟩
  simp only [col, row, sumDiag, diffDiag] at h
  rcases lt_trichotomy i j with hij | hij | hij
  · have h1 := gap f hf ((j : ℕ) - i) i j (by rw [Fin.lt_def] at hij; omega)
    have h2 := hf hij
    rw [Fin.lt_def] at hij
    rcases h with h | h | h | h <;> push_cast at h <;> omega
  · exact hne (by rw [hij])
  · have h1 := gap f hf ((i : ℕ) - j) j i (by rw [Fin.lt_def] at hij; omega)
    have h2 := hf hij
    rw [Fin.lt_def] at hij
    rcases h with h | h | h | h <;> push_cast at h <;> omega

theorem na_QC_QC {M : Inst3} {x y : Queen} (hx : x ∈ QCs M) (hy : y ∈ QCs M) :
    ¬ Attacks x y := by
  obtain ⟨k₁, rfl⟩ := mem_QCs hx
  obtain ⟨k₂, rfl⟩ := mem_QCs hy
  intro h
  exact na_graph_C ((def10_C' M).orderEmbOfFin rfl) ((def10_C' M).orderEmbOfFin rfl).strictMono
    k₁ k₂ (attacks_shift h)

theorem na_QR_QR {M : Inst3} {x y : Queen} (hx : x ∈ QRs M) (hy : y ∈ QRs M) :
    ¬ Attacks x y := by
  obtain ⟨k₁, rfl⟩ := mem_QRs hx
  obtain ⟨k₂, rfl⟩ := mem_QRs hy
  intro h
  exact na_graph_R ((def10_R' M).orderEmbOfFin rfl) ((def10_R' M).orderEmbOfFin rfl).strictMono
    k₁ k₂ (attacks_shift h)

/-- `Q₃ ∪ (Q_C + n′(19,8)) ∪ (Q_R + n′(17,19)) ∪ T` is non-attacking for every non-attacking
`T` whose queens use columns of `C′` and rows of `R′`. -/
theorem na_union {M : Inst3} (hM : M.Valid) (T : Finset Queen) (hTna : NonAttacking T)
    (hT : ∀ s ∈ T, col s ∈ def10_C' M ∧ row s ∈ def10_R' M) :
    NonAttacking (def10_Q3 M ∪ QCs M ∪ QRs M ∪ T) := by
  obtain ⟨hn, -⟩ := ctx hM
  have hQ2 := (Q2_good (np_facts M.n hn).2.2.2).1
  intro x hx y hy
  simp only [Finset.mem_union] at hx hy
  rcases hx with ((hx | hx) | hx) | hx <;> rcases hy with ((hy | hy) | hy) | hy
  · exact hQ2 x (mem_Q3.mp hx).1 y (mem_Q3.mp hy).1
  · exact na_Q3_QC hM hx hy
  · exact na_Q3_QR hM hx hy
  · exact na_Q3_T hM hx (hT y hy).1 (hT y hy).2
  · exact fun h => na_Q3_QC hM hy hx (attacks_symm h)
  · exact na_QC_QC hx hy
  · exact na_QC_QR hM hx hy
  · exact na_QC_T hM hx (hT y hy).1 (hT y hy).2
  · exact fun h => na_Q3_QR hM hy hx (attacks_symm h)
  · exact fun h => na_QC_QR hM hy hx (attacks_symm h)
  · exact na_QR_QR hx hy
  · exact na_QR_T hM hx (hT y hy).1 (hT y hy).2
  · exact fun h => na_Q3_T hM hy (hT x hx).1 (hT x hx).2 (attacks_symm h)
  · exact fun h => na_QC_T hM hy (hT x hx).1 (hT x hx).2 (attacks_symm h)
  · exact fun h => na_QR_T hM hy (hT x hx).1 (hT x hx).2 (attacks_symm h)
  · exact hTna x hx y hy

/-- Every queen of `Q₃ ∪ (Q_C + n′(19,8)) ∪ (Q_R + n′(17,19)) ∪ T` fits on board size `n₂`. -/
theorem fits_union {M : Inst3} (hM : M.Valid) (T : Finset Queen)
    (hT : ∀ s ∈ T, col s ∈ def10_C' M ∧ row s ∈ def10_R' M) :
    ∀ q ∈ def10_Q3 M ∪ QCs M ∪ QRs M ∪ T, FitsOn (n2 M) q := by
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  have hQ2 := (Q2_good (np_facts M.n hn).2.2.2).2
  intro q hq
  simp only [Finset.mem_union] at hq
  unfold n2
  rcases hq with ((hq | hq) | hq) | hq
  · have := fits_lt (hQ2 q (mem_Q3.mp hq).1)
    exact fits_of_lt (by omega) (by omega)
  · obtain ⟨k, hk, c, hc, rfl⟩ := mem_QCs' hq
    have := hC' c hc
    apply fits_of_lt <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> omega
  · obtain ⟨k, hk, c, hc, rfl⟩ := mem_QRs' hq
    have := hR' c hc
    apply fits_of_lt <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> omega
  · have h1 := hC' _ (hT q hq).1
    have h2 := hR' _ (hT q hq).2
    simp only [col, row] at h1 h2
    exact fits_of_lt (by omega) (by omega)

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

/-- The non-prescribed queens of a solution of `M` use every column of `C`. -/
theorem cover_C {M : Inst3} {S₃ : Finset Queen} (hS : M.IsSol S₃) :
    ∀ c ∈ M.C, ∃ q ∈ S₃, col q = c := by
  obtain ⟨hcard, hPS, hNA, hcr⟩ := hS
  have hinj : Set.InjOn col ((S₃ \ M.P : Finset Queen) : Set Queen) := by
    intro q hq q' hq' he
    by_contra hne
    exact hNA q (Finset.mem_sdiff.mp (Finset.mem_coe.mp hq)).1 q'
      (Finset.mem_sdiff.mp (Finset.mem_coe.mp hq')).1 ⟨hne, Or.inl he⟩
  have hsub : (S₃ \ M.P).image col ⊆ M.C := by
    intro c hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
    exact (hcr q hq).1
  have hc2 : (S₃ \ M.P).card = M.C.card := by
    have := Finset.card_sdiff_add_card_eq_card hPS
    omega
  have heq : (S₃ \ M.P).image col = M.C :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj, hc2])
  intro c hc
  rw [← heq] at hc
  obtain ⟨q, hq, hqc⟩ := Finset.mem_image.mp hc
  exact ⟨q, (Finset.mem_sdiff.mp hq).1, hqc⟩


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


/-- Lemma 12. -/
theorem lemma12_proof (M : Inst3) (hM : M.Valid) (S₃ : Finset Queen) (hS : M.IsSol S₃) :
    (def10 M).IsSol (S₃ ∪ (def10 M).P) := by
  have hS' := hS
  obtain ⟨hcard, hPS, hNA, hcr⟩ := hS
  by_cases hsa : SelfAttacking M.P
  · exfalso
    obtain ⟨q₁, h₁, q₂, h₂, hatt⟩ := hsa
    exact hNA q₁ (hPS h₁) q₂ (hPS h₂) hatt
  obtain ⟨hn, hNodd, hnN, h2n, hC', hR', hcC', hRC⟩ := ctx hM
  rw [def10_eq M hsa]
  show IsNQueensSol (n2 M) (S₃ ∪ P2 M) ∧ P2 M ⊆ S₃ ∪ P2 M
  have hT : ∀ s ∈ S₃, col s ∈ def10_C' M ∧ row s ∈ def10_R' M := by
    intro s hs
    by_cases hsP : s ∈ M.P
    · exact ⟨colP_mem_C' hsP, rowP_mem_R' hsP⟩
    · have := hcr s (Finset.mem_sdiff.mpr ⟨hs, hsP⟩)
      exact ⟨C_sub_C' this.1, R_sub_R' this.2⟩
  have hU : S₃ ∪ P2 M = def10_Q3 M ∪ QCs M ∪ QRs M ∪ S₃ := by
    ext q
    have h := @hPS q
    simp only [P2, Finset.mem_union]
    tauto
  have hna : NonAttacking (S₃ ∪ P2 M) := by
    rw [hU]; exact na_union hM S₃ hNA hT
  have hfit : ∀ q ∈ S₃ ∪ P2 M, FitsOn (n2 M) q := by
    rw [hU]; exact fits_union hM S₃ hT
  have himg : (S₃ ∪ P2 M).image col = Finset.range (n2 M) := by
    apply Finset.Subset.antisymm
    · intro c hc
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_range.mpr (fits_lt (hfit q hq)).1
    · intro c hc
      rw [Finset.mem_range] at hc
      by_cases hcC : c ∈ M.C
      · obtain ⟨q, hq, hqc⟩ := cover_C hS' c hcC
        exact Finset.mem_image.mpr ⟨q, Finset.mem_union_left _ hq, hqc⟩
      · obtain ⟨p, hp, hpc⟩ := P2_cover_col hM c hc hcC
        exact Finset.mem_image.mpr ⟨p, Finset.mem_union_right _ hp, hpc⟩
  have hcard2 : (S₃ ∪ P2 M).card = n2 M := by
    have h := Finset.card_image_of_injOn (f := col) (s := S₃ ∪ P2 M) (by
      intro q hq q' hq' he
      by_contra hne
      exact hna q hq q' hq' ⟨hne, Or.inl he⟩)
    rw [himg, Finset.card_range] at h
    exact h.symm
  refine ⟨⟨?_, hfit, hcard2, hna⟩, Finset.subset_union_right⟩
  unfold n2; omega

/-- Every solution of `M₂` is recovered from its small queens and `P₂`. -/
theorem decomp {M : Inst3} (hM : M.Valid) (hsa : ¬ SelfAttacking M.P) {S₂ : Finset Queen}
    (hS : (def10 M).IsSol S₂) : S₂ = S₂.filter (fun q => size q < M.n) ∪ P2 M := by
  obtain ⟨⟨hn2, hfit2, hcard2, hNA2⟩, hPS⟩ := (isSol_def10 hsa S₂).mp hS
  obtain ⟨hn, hfitP, hdist, hCR, hPCR, hC, hR⟩ := valid_unpack hM
  have hA := outside_P2 hM ⟨hn2, hfit2, hcard2, hNA2⟩ hPS
  ext q
  rw [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hq
    by_cases hq2 : q ∈ P2 M
    · exact Or.inr hq2
    · have := hA q hq hq2
      exact Or.inl ⟨hq, fits_of_lt (hC _ this.1) (hR _ this.2)⟩
  · rintro (⟨hq, -⟩ | hq)
    · exact hq
    · exact hPS hq

/-- The small queens of `S₃ ∪ P₂` are exactly `S₃`. -/
theorem filter_union {M : Inst3} (hM : M.Valid) {S₃ : Finset Queen} (hS : M.IsSol S₃) :
    (S₃ ∪ P2 M).filter (fun q => size q < M.n) = S₃ := by
  obtain ⟨hcard, hPS, hNA, hcr⟩ := hS
  obtain ⟨hn, hfitP, hdist, hCR, hPCR, hC, hR⟩ := valid_unpack hM
  ext q
  rw [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hq | hq, hs⟩
    · exact hq
    · by_cases hqP : q ∈ M.P
      · exact hPS hqP
      · have := (big_P2 hM q hq hqP).1
        omega
  · intro hq
    refine ⟨Or.inl hq, ?_⟩
    by_cases hqP : q ∈ M.P
    · exact hfitP q hqP
    · have := hcr q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)
      exact fits_of_lt (hC _ this.1) (hR _ this.2)

/-- `def10 M` is an instance of Problem 2. -/
theorem valid_def10 (M : Inst3) (hM : M.Valid) : (def10 M).Valid := by
  obtain ⟨hn, hfitP, hdist, hCR, hPCR, hC, hR⟩ := valid_unpack hM
  by_cases hsa : SelfAttacking M.P
  · rw [def10, if_pos hsa]
    exact ⟨hn, hfitP, hdist⟩
  · rw [def10_eq M hsa]
    have hPna : NonAttacking M.P := fun q₁ h₁ q₂ h₂ hatt => hsa ⟨q₁, h₁, q₂, h₂, hatt⟩
    have hT : ∀ s ∈ M.P, col s ∈ def10_C' M ∧ row s ∈ def10_R' M :=
      fun s hs => ⟨colP_mem_C' hs, rowP_mem_R' hs⟩
    have hna := na_union hM M.P hPna hT
    have hfit := fits_union hM M.P hT
    show 1 ≤ n2 M ∧ (∀ q ∈ P2 M, FitsOn (n2 M) q) ∧ DistinctRowsCols (P2 M)
    refine ⟨?_, hfit, ?_⟩
    · have := (np_facts M.n hn).2.1
      unfold n2; omega
    · intro q₁ h₁ q₂ h₂ hne
      exact ⟨fun h => hna q₁ h₁ q₂ h₂ ⟨hne, Or.inl h⟩,
        fun h => hna q₁ h₁ q₂ h₂ ⟨hne, Or.inr (Or.inl h)⟩⟩

/-- Definition 10 preserves the number of solutions. -/
theorem ncard_eq (M : Inst3) (hM : M.Valid) :
    _root_.Set.ncard {S : Finset Queen | (def10 M).IsSol S} =
      _root_.Set.ncard {S : Finset Queen | M.IsSol S} := by
  by_cases hsa : SelfAttacking M.P
  · have h1 : {S : Finset Queen | (def10 M).IsSol S} = ∅ := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hS
      rw [def10, if_pos hsa] at hS
      obtain ⟨⟨_, _, _, hNA⟩, hPS⟩ := hS
      obtain ⟨q₁, h₁, q₂, h₂, hatt⟩ := hsa
      exact hNA q₁ (hPS h₁) q₂ (hPS h₂) hatt
    have h2 : {S : Finset Queen | M.IsSol S} = ∅ := by
      ext S
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hPS, hNA, _⟩
      obtain ⟨q₁, h₁, q₂, h₂, hatt⟩ := hsa
      exact hNA q₁ (hPS h₁) q₂ (hPS h₂) hatt
    rw [h1, h2]
  · have hP : (def10 M).P = P2 M := by rw [def10_eq M hsa]
    apply _root_.Set.ncard_congr (fun S₂ _ => S₂.filter (fun q => size q < M.n))
    · intro S₂ hS₂
      exact lemma11_proof M hM S₂ hS₂
    · intro S₂ S₂' hS₂ hS₂' he
      have he' : S₂.filter (fun q => size q < M.n) = S₂'.filter (fun q => size q < M.n) := he
      calc S₂ = S₂.filter (fun q => size q < M.n) ∪ P2 M := decomp hM hsa hS₂
        _ = S₂'.filter (fun q => size q < M.n) ∪ P2 M := by rw [he']
        _ = S₂' := (decomp hM hsa hS₂').symm
    · intro S₃ hS₃
      have h12 := lemma12_proof M hM S₃ hS₃
      rw [hP] at h12
      exact ⟨S₃ ∪ P2 M, h12, filter_union hM hS₃⟩

end NQueensComp.NPC.Def10Proof

open NQueensComp.NPC.Def10Proof

theorem solution :
    ∀ M : Inst3, M.Valid →
      (def10 M).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def10 M).IsSol S} =
          _root_.Set.ncard {S : Finset Queen | M.IsSol S} :=
  fun M hM => ⟨valid_def10 M hM, ncard_eq M hM⟩
