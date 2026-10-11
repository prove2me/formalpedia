-- Prove2me | solution 1 for HarlowTASI.blockAlgebraLeft_inter_right
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T15:21:16.301992+00:00
-- url     : https://prove2.me/submissions/4e747ed2-9b60-4976-aa57-4b6d3cc3546a

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

theorem bair_main {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) :
    blockAlgebraLeft U ∩ blockAlgebraRight U = blockAlgebraCenter U := by
  have key : ∀ Z : Matrix (BlockIndex N dr drb) (BlockIndex N dr drb) ℂ,
      U * (Uᴴ * Z * U) * Uᴴ = Z := fun Z => by
    rw [show U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) by simp only [Matrix.mul_assoc],
      hU.2, Matrix.one_mul, Matrix.mul_one]
  ext X
  simp only [Set.mem_inter_iff, blockAlgebraLeft, blockAlgebraRight, blockAlgebraCenter,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    have hLR : blockLeftOp (drb := drb) x = blockRightOp (dr := dr) y :=
      calc blockLeftOp (drb := drb) x = U * (Uᴴ * blockLeftOp (drb := drb) x * U) * Uᴴ :=
            (key _).symm
        _ = U * (Uᴴ * blockRightOp (dr := dr) y * U) * Uᴴ := by rw [hy]
        _ = _ := key _
    have hb' : ∀ a (i k : Fin (dr a)) (j l : Fin (drb a)),
        x a i k * (1 : Matrix (Fin (drb a)) (Fin (drb a)) ℂ) j l =
          (1 : Matrix (Fin (dr a)) (Fin (dr a)) ℂ) i k * y a j l := by
      intro a i k j l
      have := congrFun (congrFun hLR ⟨a, (i, j)⟩) ⟨a, (k, l)⟩
      simpa [blockLeftOp, blockRightOp, blockDiagonal'_apply_eq, kroneckerMap_apply] using this
    let c : Fin N → ℂ := fun a =>
      haveI := Classical.dec (Nonempty (Fin (dr a) × Fin (drb a)))
      if h : Nonempty (Fin (dr a) × Fin (drb a)) then x a h.some.1 h.some.1 else 0
    refine ⟨c, ?_⟩
    have hc : ∀ a (i k : Fin (dr a)) (j l : Fin (drb a)),
        x a i k * (1 : Matrix (Fin (drb a)) (Fin (drb a)) ℂ) j l =
          c a * (1 : Matrix (Fin (dr a) × Fin (drb a)) (Fin (dr a) × Fin (drb a)) ℂ)
            (i, j) (k, l) := by
      intro a i k j l
      have hn : Nonempty (Fin (dr a) × Fin (drb a)) := ⟨(i, j)⟩
      simp only [c, dif_pos hn]
      by_cases hjl : j = l
      · subst hjl
        by_cases hik : i = k
        · subst hik
          have h1 := hb' a i i j j
          have h2 := hb' a hn.some.1 hn.some.1 j j
          simp only [one_apply_eq, mul_one, one_mul] at h1 h2
          simp only [one_apply_eq, mul_one, h1, h2]
        · have h1 := hb' a i k j j
          simp only [one_apply_eq, mul_one, one_apply_ne hik, zero_mul] at h1
          simp [h1, hik]
      · simp [hjl]
    congr 2
    simp only [blockLeftOp, blockScalarOp]
    congr 1
    funext a
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
    exact hc a i k j l
  · rintro ⟨c, rfl⟩
    refine ⟨⟨fun a => c a • 1, ?_⟩, ⟨fun a => c a • 1, ?_⟩⟩ <;> congr 2 <;>
      simp only [blockLeftOp, blockRightOp, blockScalarOp, smul_kronecker, kronecker_smul,
        one_kronecker_one]

end HarlowTASI

open HarlowTASI in
theorem solution {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) :
    blockAlgebraLeft U ∩ blockAlgebraRight U = blockAlgebraCenter U :=
  bair_main U hU
