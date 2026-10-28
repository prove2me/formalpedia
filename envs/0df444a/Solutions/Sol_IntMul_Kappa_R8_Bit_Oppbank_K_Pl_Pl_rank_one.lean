-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.K_Pl_Pl_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:42:32.52555+00:00
-- url     : https://prove2.me/submissions/9fd8c7c0-aa1d-4789-92a4-38f6b667b158

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankKAlgebra
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Matrix
open scoped Kronecker
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NetFB

private theorem Pl_eq (T : ℕ) : Pnd.Pl T = ProjB.Pl T := rfl
private theorem xv_eq (T : ℕ) : Pnd.xv T = ProjB.xv T := rfl
private theorem yv_eq (T : ℕ) : Pnd.yv T = ProjB.yv T := rfl

private theorem mulVec_Pl (T : ℕ) (hT : T < 1771) :
    (ProjB.Pl T) *ᵥ ProjB.xv T = ProjB.xv T := by
  have hyx : ProjB.yv T ⬝ᵥ ProjB.xv T = 1 := yx hT
  ext i
  simp only [ProjB.Pl, mulVec, vecMulVec, dotProduct]
  calc ∑ j, ProjB.xv T i * ProjB.yv T j * ProjB.xv T j
      = ProjB.xv T i * ∑ j, ProjB.yv T j * ProjB.xv T j := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
    _ = ProjB.xv T i * (ProjB.yv T ⬝ᵥ ProjB.xv T) := rfl
    _ = ProjB.xv T i := by rw [hyx, mul_one]

private theorem xv_ne_zero (T : ℕ) (hT : T < 1771) : ProjB.xv T ≠ 0 := by
  intro h0
  have hyx := yx hT
  rw [h0] at hyx
  simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hyx
  exact absurd hyx (by decide : (0 : ℚ) ≠ 1)

private theorem yv_ne_zero (T : ℕ) (hT : T < 1771) : ProjB.yv T ≠ 0 := by
  intro h0
  have hyx := yx hT
  rw [h0] at hyx
  simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hyx
  exact absurd hyx (by decide : (0 : ℚ) ≠ 1)

private theorem rank_Pl (T : ℕ) (hT : T < 1771) : (ProjB.Pl T).rank = 1 := by
  have hle : (ProjB.Pl T).rank ≤ 1 := by
    change (vecMulVec (ProjB.xv T) (ProjB.yv T)).rank ≤ 1
    exact rank_vecMulVec_le _ _
  have hx := xv_ne_zero T hT
  have hpos : 0 < (ProjB.Pl T).rank := by
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨(ProjB.Pl T) *ᵥ ProjB.xv T, ⟨ProjB.xv T, rfl⟩⟩, ?_⟩
    intro h0
    have : (ProjB.Pl T) *ᵥ ProjB.xv T = 0 := Subtype.ext_iff.mp h0
    exact hx (by simpa [mulVec_Pl T hT] using this)
  omega

private theorem kronecker_vecMulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y u v : ι → ℚ) :
    vecMulVec x y ⊗ₖ vecMulVec u v =
      vecMulVec (fun p : ι × ι => x p.1 * u p.2) (fun p : ι × ι => y p.1 * v p.2) := by
  ext i j
  dsimp [kroneckerMap, vecMulVec]
  ring

private theorem vecMulVec_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w v : ι → ℚ) (hw : w ≠ 0) (hv : v ≠ 0) : vecMulVec w v ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  intro h0
  have : w i * v j = 0 := by
    have := congr_fun (congr_fun h0 i) j
    simpa [vecMulVec] using this
  exact mul_ne_zero hi hj this

private theorem rank_Pl_kronecker_Pl (a s : ℕ) (ha : a < 1771) (hs : s < 1771) :
    (ProjB.Pl a ⊗ₖ ProjB.Pl s).rank = 1 := by
  have heq : ProjB.Pl a ⊗ₖ ProjB.Pl s =
      vecMulVec (fun p : Fin 23 × Fin 23 => ProjB.xv a p.1 * ProjB.xv s p.2)
        (fun p : Fin 23 × Fin 23 => ProjB.yv a p.1 * ProjB.yv s p.2) := by
    simpa [ProjB.Pl] using kronecker_vecMulVec (ProjB.xv a) (ProjB.yv a) (ProjB.xv s) (ProjB.yv s)
  have hle : (ProjB.Pl a ⊗ₖ ProjB.Pl s).rank ≤ 1 := by
    rw [heq]; exact rank_vecMulVec_le _ _
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (xv_ne_zero a ha)
  obtain ⟨k, hk⟩ := Function.ne_iff.mp (xv_ne_zero s hs)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (yv_ne_zero a ha)
  obtain ⟨l, hl⟩ := Function.ne_iff.mp (yv_ne_zero s hs)
  have hw : (fun p : Fin 23 × Fin 23 => ProjB.xv a p.1 * ProjB.xv s p.2) ≠ 0 := by
    intro h0; exact mul_ne_zero hi hk (by simpa using congr_fun h0 (i, k))
  have hv : (fun p : Fin 23 × Fin 23 => ProjB.yv a p.1 * ProjB.yv s p.2) ≠ 0 := by
    intro h0; exact mul_ne_zero hj hl (by simpa using congr_fun h0 (j, l))
  have hne : ProjB.Pl a ⊗ₖ ProjB.Pl s ≠ 0 := by
    rw [heq]; exact vecMulVec_ne_zero _ _ hw hv
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hp
  let e : Fin 23 × Fin 23 → ℚ := fun r => if r = q then 1 else 0
  have hcol : (ProjB.Pl a ⊗ₖ ProjB.Pl s) *ᵥ e ≠ 0 := by
    intro hz
    have hsum :
        ((ProjB.Pl a ⊗ₖ ProjB.Pl s) *ᵥ e) p = (ProjB.Pl a ⊗ₖ ProjB.Pl s) p q := by
      change ∑ r, (ProjB.Pl a ⊗ₖ ProjB.Pl s) p r * (if r = q then (1:ℚ) else 0) = _
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single q]
      · simp
      · intro r _ hr; simp [hr]
      · intro hnotin; exact absurd (Finset.mem_univ q) hnotin
    exact hq (hsum ▸ congr_fun hz p)
  have hpos : 0 < (ProjB.Pl a ⊗ₖ ProjB.Pl s).rank := by
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨(ProjB.Pl a ⊗ₖ ProjB.Pl s) *ᵥ e, ⟨e, rfl⟩⟩, ?_⟩
    intro hz; exact hcol (Subtype.ext_iff.mp hz)
  omega

private theorem rank_conj_eq
    (S : Matrix (Fin 529) Pnd.Pr23 ℚ) (Si : Matrix Pnd.Pr23 (Fin 529) ℚ)
    (M : Matrix Pnd.Pr23 Pnd.Pr23 ℚ)
    (_hS : S * Si = 1) (hSi : Si * S = 1) :
    (S * M * Si).rank = M.rank := by
  apply le_antisymm
  · have h1 : (S * M * Si).rank = (S * (M * Si)).rank := by
      rw [Matrix.mul_assoc]
    have h2 : (S * (M * Si)).rank ≤ (M * Si).rank :=
      rank_mul_le_right (R := ℚ) S (M * Si)
    have h3 : (M * Si).rank ≤ M.rank :=
      rank_mul_le_left (R := ℚ) M Si
    exact h1 ▸ le_trans h2 h3
  · -- M = Si * S * M * Si * S = Si * (S * M * Si) * S
    let N := S * M * Si
    have hN : Si * N * S = M := by
      change Si * (S * M * Si) * S = M
      -- rewrite to (Si * S) * M * (Si * S)
      have ha : Si * (S * M * Si) = (Si * S) * M * Si := by
        calc Si * (S * M * Si)
            = Si * (S * (M * Si)) := by rw [Matrix.mul_assoc S M Si]
          _ = (Si * S) * (M * Si) := by rw [Matrix.mul_assoc Si S (M * Si)]
          _ = ((Si * S) * M) * Si := (Matrix.mul_assoc (Si * S) M Si).symm
      calc Si * (S * M * Si) * S
          = ((Si * S) * M * Si) * S := by rw [ha]
        _ = (Si * S) * M * (Si * S) := by rw [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ ℚ) * M * 1 := by rw [hSi]
        _ = M := by simp
    have h1 : (Si * N * S).rank ≤ (N * S).rank := by
      have : Si * N * S = Si * (N * S) := by rw [Matrix.mul_assoc]
      rw [this]; exact rank_mul_le_right (R := ℚ) Si (N * S)
    have h2 : (N * S).rank ≤ N.rank :=
      rank_mul_le_left (R := ℚ) N S
    -- goal: M.rank ≤ N.rank
    have : M.rank = (Si * N * S).rank := by rw [hN]
    exact this ▸ le_trans h1 h2

theorem solution (S : Matrix (Fin 529) Pnd.Pr23 ℚ) (Si : Matrix Pnd.Pr23 (Fin 529) ℚ)
    (hS : S * Si = 1) (hSi : Si * S = 1) {a s : ℕ} (ha : a < 1771) (hs : s < 1771) :
    (Pnd.K S Si (Pnd.Pl a) (Pnd.Pl s)).rank = 1 := by
  unfold Pnd.K
  change (S * (Pnd.Pl a ⊗ₖ Pnd.Pl s) * Si).rank = 1
  rw [Pl_eq a, Pl_eq s]
  rw [rank_conj_eq S Si (ProjB.Pl a ⊗ₖ ProjB.Pl s) hS hSi]
  exact rank_Pl_kronecker_Pl a s ha hs
