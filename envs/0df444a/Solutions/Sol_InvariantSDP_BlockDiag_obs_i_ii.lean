-- Prove2me | solution 1 for InvariantSDP.BlockDiag.obs_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:30:32.397471+00:00
-- url     : https://prove2.me/submissions/284cc95a-f3a1-4c18-8906-f6f2aa650d55

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

open InvariantSDP.BlockDiag Matrix
open scoped ComplexOrder

lemma hermInX {n : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hB : IsMaxCommutative A B) (H : Matrix (Fin n) (Fin n) ℂ) (hHA : H ∈ A) (hHh : star H = H)
    (hHB : ∀ b ∈ B, H * b = b * H) : H ∈ B := by
  obtain ⟨hBA, hBc, hmax⟩ := hB
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
      right; exact hHh
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
  rwa [hEq] at hHB'

theorem maxCommX {n : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hB : IsMaxCommutative A B) :
    ∀ X ∈ A, (∀ Y ∈ B, X * Y = Y * X) → X ∈ B := by
  intro X hXA hXB
  have hXsB : ∀ Y ∈ B, star X * Y = Y * star X := by
    intro Y hY
    have := hXB (star Y) (star_mem hY)
    have := congrArg star this
    simpa [star_mul] using this.symm
  set H := (1/2 : ℂ) • (X + star X)
  set K := (-(Complex.I) / 2) • (X - star X)
  have hX : X = H + Complex.I • K := by
    simp only [H, K, smul_smul]
    have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      field_simp; simp [Complex.I_sq]
    rw [hI, ← smul_add]
    rw [add_add_sub_cancel, ← two_smul ℂ X, smul_smul]; norm_num
  have hHA : H ∈ A := SMulMemClass.smul_mem _ (add_mem hXA (star_mem hXA))
  have hKA : K ∈ A := SMulMemClass.smul_mem _ (sub_mem hXA (star_mem hXA))
  have hHh : star H = H := by
    simp only [H, star_smul, star_add, star_star]
    rw [add_comm]; congr 1; simp
  have hKh : star K = K := by
    simp only [K, star_smul, star_sub, star_star]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp [Complex.conj_I]]
    rw [show X - star X = -(star X - X) by abel, smul_neg, ← neg_smul]
    congr 1; ring
  have hHB : ∀ b ∈ B, H * b = b * H := by
    intro b hb
    simp only [H, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hXB b hb, hXsB b hb]
  have hKB : ∀ b ∈ B, K * b = b * K := by
    intro b hb
    simp only [K, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hXB b hb, hXsB b hb]
  have h1 := hermInX A B hB H hHA hHh hHB
  have h2 := hermInX A B hB K hKA hKh hKB
  rw [hX]
  exact add_mem h1 (SMulMemClass.smul_mem _ h2)
lemma ImulX {n k : ℕ} (S : Fin n → Option (Fin k)) (a b : Option (Fin k)) :
    zeroOneDiag S a * zeroOneDiag S b = if a = b then zeroOneDiag S a else 0 := by
  unfold zeroOneDiag
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · subst h; congr 1; funext x; split_ifs <;> simp_all
  · rw [← diagonal_zero]; congr 1; funext x
    split_ifs with h1 h2 <;> simp
    exact h (h1.symm.trans h2)

lemma IhX {n k : ℕ} (S : Fin n → Option (Fin k)) (a : Option (Fin k)) :
    (zeroOneDiag S a)ᴴ = zeroOneDiag S a := by
  unfold zeroOneDiag
  rw [diagonal_conjTranspose]; congr 1; funext x; split_ifs <;> simp_all

theorem solution {n k : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (hB : IsMaxCommutative A B) (hS : IsDiagForm B S)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ A) :
    ((∀ i : Fin k, ∃ c : ℂ,
        zeroOneDiag S (some i) * X * zeroOneDiag S (some i) = c • zeroOneDiag S (some i)) ∧
      zeroOneDiag S none * X * zeroOneDiag S none = 0) ∧
    (zeroOneDiag S none * X = 0 ∧ X * zeroOneDiag S none = 0) := by
  have hBA := hB.1
  obtain ⟨hne, hBset⟩ := hS
  set I : Option (Fin k) → Matrix (Fin n) (Fin n) ℂ := fun m => zeroOneDiag S m with hI
  have Imul : ∀ a b, I a * I b = if a = b then I a else 0 := fun a b => ImulX S a b
  have Ih : ∀ a, (I a)ᴴ = I a := fun a => IhX S a
  have IB : ∀ a : Fin k, I (some a) ∈ B := by
    intro a
    have : I (some a) ∈ (B : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hBset]
      refine ⟨Pi.single a 1, ?_⟩
      simp [Pi.single_apply, hI]
    exact this
  have hE : I none = 1 - ∑ m : Fin k, I (some m) := by
    ext a b
    simp only [hI, zeroOneDiag, Matrix.sub_apply, Matrix.one_apply, Matrix.sum_apply,
      Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp only [if_true]
      rcases hSa : S a with _ | m
      · simp
      · rw [Finset.sum_eq_single m]
        · simp
        · intro m' _ hm'; simp [Ne.symm hm']
        · simp
    · simp [hab]
  have hEA : (∑ m : Fin k, I (some m)) ∈ A := sum_mem fun m _ => hBA (IB m)
  have hI0X : ∀ Y ∈ A, I none * Y ∈ A := by
    intro Y hY; rw [hE, sub_mul, one_mul]; exact sub_mem hY (mul_mem hEA hY)
  have hXI0 : ∀ Y ∈ A, Y * I none ∈ A := by
    intro Y hY; rw [hE, mul_sub, mul_one]; exact sub_mem hY (mul_mem hY hEA)
  -- elements of B are block-diagonal combinations
  have hBform : ∀ b ∈ B, ∃ l : Fin k → ℂ, b = ∑ m, l m • I (some m) := by
    intro b hb
    have : b ∈ (B : Set (Matrix (Fin n) (Fin n) ℂ)) := hb
    rw [hBset] at this
    obtain ⟨l, rfl⟩ := this
    exact ⟨l, rfl⟩
  -- block supported elements commute with B
  have hcomm : ∀ (a : Option (Fin k)) (Y : Matrix (Fin n) (Fin n) ℂ), I a * Y * I a = Y →
      ∀ b ∈ B, Y * b = b * Y := by
    intro a Y hY b hb
    obtain ⟨l, rfl⟩ := hBform b hb
    have r1 : ∀ m, Y * I (some m) = if a = some m then Y else 0 := by
      intro m
      calc Y * I (some m) = I a * Y * (I a * I (some m)) := by rw [← Matrix.mul_assoc, hY]
        _ = _ := by rw [Imul]; split_ifs <;> simp [hY]
    have r2 : ∀ m, I (some m) * Y = if some m = a then Y else 0 := by
      intro m
      calc I (some m) * Y = (I (some m) * I a) * Y * I a := by
            conv_lhs => rw [← hY]
            simp only [Matrix.mul_assoc]
        _ = _ := by
            rw [Imul]; split_ifs with h
            · rw [h]; exact hY
            · simp
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, r1, r2]
    by_cases h : a = some m
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hblock : ∀ (a : Option (Fin k)) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ A → I a * Y * I a = Y →
      ∃ l : Fin k → ℂ, Y = I a * (∑ m, l m • I (some m)) * I a := by
    intro a Y hYA hY
    have hYB := maxCommX A B hB Y hYA (hcomm a Y hY)
    obtain ⟨l, hl⟩ := hBform Y hYB
    exact ⟨l, by rw [← hl, hY]⟩
  have hII : ∀ a, I a * I a = I a := fun a => by rw [Imul, if_pos rfl]
  -- (ii)
  have hii : ∀ W ∈ A, I none * W * I none = 0 := by
    intro W hW
    have hYA : I none * W * I none ∈ A := hXI0 _ (hI0X W hW)
    have hY : I none * (I none * W * I none) * I none = I none * W * I none := by
      simp only [← Matrix.mul_assoc, hII]; rw [Matrix.mul_assoc _ (I none) (I none), hII]
    obtain ⟨l, hl⟩ := hblock none _ hYA hY
    rw [hl, Matrix.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro m _
    rw [Matrix.mul_smul, Matrix.smul_mul, Imul, if_neg (by simp), Matrix.zero_mul, smul_zero]
  refine ⟨⟨fun i => ?_, hii X hX⟩, ?_, ?_⟩
  · have hYA : I (some i) * X * I (some i) ∈ A := mul_mem (mul_mem (hBA (IB i)) hX) (hBA (IB i))
    have hY : I (some i) * (I (some i) * X * I (some i)) * I (some i) = I (some i) * X * I (some i) := by
      simp only [← Matrix.mul_assoc, hII]; rw [Matrix.mul_assoc _ (I (some i)) (I (some i)), hII]
    obtain ⟨l, hl⟩ := hblock (some i) _ hYA hY
    refine ⟨l i, ?_⟩
    show I (some i) * X * I (some i) = l i • I (some i)
    rw [hl, Matrix.mul_sum, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [Matrix.mul_smul, Matrix.smul_mul, hII, hII]
    · intro m _ hm
      rw [Matrix.mul_smul, Matrix.smul_mul, Imul, if_neg (by simpa using Ne.symm hm),
        Matrix.zero_mul, smul_zero]
    · simp
  · have hW : X * Xᴴ ∈ A := mul_mem hX (star_mem hX)
    have h0 := hii _ hW
    have : (I none * X) * (I none * X)ᴴ = 0 := by
      rw [Matrix.conjTranspose_mul, Ih, ← Matrix.mul_assoc, Matrix.mul_assoc (I none) X]
      exact h0
    have h2 : ((I none * X)ᴴ)ᴴ * (I none * X)ᴴ = 0 := by rwa [Matrix.conjTranspose_conjTranspose]
    have h3 := Matrix.conjTranspose_mul_self_eq_zero.mp h2
    simpa using congrArg Matrix.conjTranspose h3
  · have hW : Xᴴ * X ∈ A := mul_mem (star_mem hX) hX
    have h0 := hii _ hW
    have : (X * I none)ᴴ * (X * I none) = 0 := by
      rw [Matrix.conjTranspose_mul, Ih, ← Matrix.mul_assoc, Matrix.mul_assoc (I none) (Xᴴ)]
      exact h0
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
