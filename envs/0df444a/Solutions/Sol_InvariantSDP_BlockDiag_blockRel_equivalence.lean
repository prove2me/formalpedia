-- Prove2me | solution 1 for InvariantSDP.BlockDiag.blockRel_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:08:50.190843+00:00
-- url     : https://prove2.me/submissions/80f0cb20-b679-4944-815c-0f9667c3b66b

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

open InvariantSDP.BlockDiag Matrix
open scoped ComplexOrder

variable {n k : ℕ}

lemma ImulX (S : Fin n → Option (Fin k)) (a b : Option (Fin k)) :
    zeroOneDiag S a * zeroOneDiag S b = if a = b then zeroOneDiag S a else 0 := by
  unfold zeroOneDiag
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · subst h; congr 1; funext x; split_ifs <;> simp_all
  · rw [← diagonal_zero]; congr 1; funext x
    split_ifs with h1 h2 <;> simp
    exact h (h1.symm.trans h2)

lemma IhX (S : Fin n → Option (Fin k)) (a : Option (Fin k)) :
    (zeroOneDiag S a)ᴴ = zeroOneDiag S a := by
  unfold zeroOneDiag
  rw [diagonal_conjTranspose]; congr 1; funext x; split_ifs <;> simp_all

theorem solution (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (hB : IsMaxCommutative A B) (hS : IsDiagForm B S) :
    Equivalence (blockRel A S) := by
  obtain ⟨hBA, hBc, hmax⟩ := hB
  obtain ⟨hne, hBset⟩ := hS
  set I : Fin k → Matrix (Fin n) (Fin n) ℂ := fun m => zeroOneDiag S (some m) with hI
  have Imul : ∀ a b, I a * I b = if a = b then I a else 0 := by
    intro a b; simp only [hI, ImulX, Option.some_inj]
  have Iself : ∀ a, I a * I a = I a := by intro a; rw [Imul, if_pos rfl]
  have Ioff : ∀ a b, a ≠ b → I a * I b = 0 := by intro a b h; rw [Imul, if_neg h]
  have Ih : ∀ a, (I a)ᴴ = I a := fun a => IhX S _
  have IB : ∀ a, I a ∈ B := by
    intro a
    have : I a ∈ (B : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hBset]
      refine ⟨Pi.single a 1, ?_⟩
      simp [Pi.single_apply, hI]
    exact this
  have IA : ∀ a, I a ∈ A := fun a => hBA (IB a)
  have Ine : ∀ a, I a ≠ 0 := by
    intro a h
    obtain ⟨j, hj⟩ := hne a
    have := congrFun (congrFun h j) j
    simp [hI, zeroOneDiag, hj] at this
  -- key: compressions of hermitian elements to a block are scalar
  have key : ∀ j, ∀ H ∈ A, Hᴴ = H → I j * H * I j = H → ∃ c : ℂ, H = c • I j := by
    intro j H hHA hHh hHj
    have hHB : ∀ b ∈ B, H * b = b * H := by
      intro b hb
      have : b ∈ (B : Set (Matrix (Fin n) (Fin n) ℂ)) := hb
      rw [hBset] at this
      obtain ⟨l, rfl⟩ := this
      have r1 : ∀ m, H * I m = if j = m then H else 0 := by
        intro m
        calc H * I m = I j * H * (I j * I m) := by rw [← mul_assoc, hHj]
          _ = _ := by rw [Imul]; split_ifs <;> simp [hHj]
      have r2 : ∀ m, I m * H = if m = j then H else 0 := by
        intro m
        calc I m * H = (I m * I j) * H * I j := by
              conv_lhs => rw [← hHj]
              simp only [mul_assoc]
          _ = _ := by
              rw [Imul]; split_ifs with h
              · subst h; exact hHj
              · simp
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, r1, r2]
      by_cases h : j = m
      · subst h; simp
      · simp [h, Ne.symm h]
    let s : Set (Matrix (Fin n) (Fin n) ℂ) := (B : Set _) ∪ {H}
    have hs_comm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
      rintro a (ha | ha) b (hb | hb)
      · exact hBc a ha b hb
      · rw [Set.mem_singleton_iff] at hb; rw [hb]; exact (hHB a ha).symm
      · rw [Set.mem_singleton_iff] at ha; rw [ha]; exact hHB b hb
      · rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
    have hs_star : ∀ a ∈ s, star a ∈ s := by
      rintro a (ha | ha)
      · exact Or.inl (star_mem ha)
      · rw [Set.mem_singleton_iff] at ha; rw [ha]
        right; show star H = H; exact hHh
    have hcomm := NonUnitalStarAlgebra.isMulCommutative_adjoin ℂ hs_comm
      (fun a ha b hb => hs_comm a ha _ (hs_star b hb))
    set B' := NonUnitalStarAlgebra.adjoin ℂ s
    have hBB' : B ≤ B' := fun x hx => NonUnitalStarAlgebra.subset_adjoin ℂ s (Or.inl hx)
    have hB'A : B' ≤ A := by
      apply NonUnitalStarAlgebra.adjoin_le
      rintro x (hx | hx)
      · exact hBA hx
      · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hHA
    have hB'c : IsCommutative B' := by
      intro x hx y hy
      have := hcomm.is_comm.comm (⟨x, hx⟩ : B') ⟨y, hy⟩
      simpa using congrArg Subtype.val this
    have hEq := hmax B' hBB' hB'A hB'c
    have hHB' : H ∈ B' := NonUnitalStarAlgebra.subset_adjoin ℂ s (Or.inr rfl)
    rw [hEq] at hHB'
    have : H ∈ (B : Set (Matrix (Fin n) (Fin n) ℂ)) := hHB'
    rw [hBset] at this
    obtain ⟨l, hl⟩ := this
    refine ⟨l j, ?_⟩
    rw [← hHj, ← hl, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single j]
    · rw [Matrix.mul_smul, Matrix.smul_mul, Iself, Iself]
    · intro m _ hm
      rw [Matrix.mul_smul, Matrix.smul_mul, Ioff j m (Ne.symm hm), zero_mul, smul_zero]
    · simp
  refine ⟨fun i => ⟨I i, IA i, ?_⟩, ?_, ?_⟩
  · show I i * I i * I i ≠ 0
    rw [Iself, Iself]; exact Ine i
  · rintro i j ⟨X, hX, hne'⟩
    refine ⟨star X, star_mem hX, ?_⟩
    intro h
    apply hne'
    have := congrArg Matrix.conjTranspose h
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] at this
    rw [show (star X)ᴴ = X from star_star X, Ih, Ih] at this
    show I i * X * I j = 0
    rw [← this]; simp only [mul_assoc]
  · rintro i j l ⟨X, hX, hXne⟩ ⟨Y, hY, hYne⟩
    set M := I i * X * I j
    set N := I j * Y * I l
    have hMj : M * I j = M := by simp only [M, mul_assoc, Iself]
    have hjN : I j * N = N := by simp only [N, ← mul_assoc, Iself]
    -- H = Mᴴ M
    have hHA : Mᴴ * M ∈ A := by
      have hMA : M ∈ A := mul_mem (mul_mem (IA i) hX) (IA j)
      exact mul_mem (star_mem hMA) hMA
    have hHh : (Mᴴ * M)ᴴ = Mᴴ * M := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hHj : I j * (Mᴴ * M) * I j = Mᴴ * M := by
      have h1 : I j * Mᴴ = Mᴴ := by
        have := congrArg Matrix.conjTranspose hMj
        rwa [Matrix.conjTranspose_mul, Ih] at this
      rw [← mul_assoc, h1, mul_assoc, hMj]
    obtain ⟨c, hc⟩ := key j _ hHA hHh hHj
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul, Matrix.conjTranspose_mul_self_eq_zero] at hc
      exact hXne hc
    refine ⟨X * I j * Y, mul_mem (mul_mem hX (IA j)) hY, ?_⟩
    intro h
    have hMN : M * N = 0 := by
      rw [← h]; simp only [M, N, mul_assoc]; rw [← mul_assoc (I j) (I j), Iself]
    apply hYne
    have : Mᴴ * M * N = c • N := by rw [hc, Matrix.smul_mul, hjN]
    rw [mul_assoc, hMN, mul_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left hc0
