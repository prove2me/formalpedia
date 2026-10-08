-- Prove2me | solution 1 for GomoryGroup.Rel.group_problem_periodic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:19:45.215975+00:00
-- url     : https://prove2.me/submissions/1edb0b8c-dfbb-4a4e-ba1f-737618057cff

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting



namespace GomoryGroup.Rel

open Matrix

theorem ipfgf_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ),
      IsIPFeasible B N b xB xN → IsGroupFeasible B N b xN := by
  intro xB xN h
  refine ⟨fun i => (xB i : ℤ), ?_⟩
  unfold IsIPFeasible at h
  rw [← h]; abel

theorem periodic_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) :
    ∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b := by
  intro i
  have hcol : (fun r => B r i) = B *ᵥ (Pi.single i 1 : Fin m → ℤ) := by
    ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y := by
    intro y
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k - Pi.single i 1, ?_⟩
      rw [Matrix.mulVec_sub, ← hk, hcol]; abel
    · rintro ⟨k, hk⟩
      refine ⟨k + Pi.single i 1, ?_⟩
      rw [Matrix.mulVec_add, ← hk, hcol]; abel
  refine ⟨key, ?_⟩
  ext z
  simp only [groupValues, Set.mem_setOf_eq, key]

theorem fund_core {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0) :
    ∀ (xB : Fin m → ℝ) (xN : Fin n → ℝ),
      Br B *ᵥ xB + Nr N *ᵥ xN = (fun i => (b i : ℝ)) →
        cB ⬝ᵥ xB + cN ⬝ᵥ xN =
          cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + ∑ j, reducedCost B N cB cN j * xN j := by
  intro xB xN h
  have hdet : IsUnit (Br B).det := by
    have : (Br B).det = ((B.det : ℤ) : ℝ) := by
      unfold Br
      have := (Int.castRingHom ℝ).map_det B
      simpa using this.symm
    rw [this]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hB)
  have hx : xB = (Br B)⁻¹ *ᵥ ((fun i => (b i : ℝ)) - Nr N *ᵥ xN) := by
    rw [← h, add_sub_cancel_right, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  have hcol : ∀ j, ((cB ᵥ* (Br B)⁻¹) ᵥ* Nr N) j = cB ⬝ᵥ ((Br B)⁻¹ *ᵥ fun r => (N r j : ℝ)) := by
    intro j
    rw [dotProduct_mulVec]
    rfl
  have hsum : cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (Nr N *ᵥ xN)) =
      ∑ j, (cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun r => (N r j : ℝ)))) * xN j := by
    rw [dotProduct_mulVec, dotProduct_mulVec]
    conv_lhs => unfold dotProduct
    exact Finset.sum_congr rfl (fun j _ => by rw [hcol j])
  rw [hx, Matrix.mulVec_sub, dotProduct_sub, hsum]
  have : cN ⬝ᵥ xN = ∑ j, cN j * xN j := rfl
  rw [this]
  simp only [reducedCost, sub_mul, Finset.sum_sub_distrib]
  ring

end GomoryGroup.Rel

open GomoryGroup.Rel


theorem solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) :
    ∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b := by
  exact periodic_core B N cB cN b
