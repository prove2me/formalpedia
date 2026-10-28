-- Prove2me | solution 1 for InvariantSDP.BlockDiag.maxComm_commutant_subset
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:12:02.004411+00:00
-- url     : https://prove2.me/submissions/2dd0fd03-52b9-4e7c-a839-e3ba694f7dff

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

open InvariantSDP.BlockDiag Matrix

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

theorem solution {n : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
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
