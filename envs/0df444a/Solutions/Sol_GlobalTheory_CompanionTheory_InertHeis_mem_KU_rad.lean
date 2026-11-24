-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertHeis.mem_KU_rad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:28:28.252379+00:00
-- url     : https://prove2.me/submissions/75e1fa7d-1a07-4c7c-9605-5a6da39d31e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_mid_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_mid_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_last_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_last_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rad_last_last
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rowOf_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_row_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_colOf_inv
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
end Entries
private theorem mat_apply_mem_intL_of_mem_radQ_of_blocks {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (hr : ∀ j, rowOf w j ∈ intL L) (hb : ∀ i, colOf w i ∈ intL L) (hc : cornerOf w ∈ intL L)
    (i j : Fin (N + 2)) : mat w i j ∈ intL L := by
  rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
  · rw [rad_zero_zero hw]; exact one_mem _
  · exact hr q
  · exact hc
  · rw [rad_mid_zero hw]; exact zero_mem _
  · rw [rad_mid_mid hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · exact hb p
  · rw [rad_last_zero hw]; exact zero_mem _
  · rw [rad_last_mid hw]; exact zero_mem _
  · rw [rad_last_last hw]; exact one_mem _
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {u : GU σ (N + 2)}
    (hu : u ∈ radQ σ N) :
    u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L := by
  have hσint : ∀ x, σ x ∈ intL L ↔ x ∈ intL L := fun x => by
    show σ x ∈ Valued.v.integer ↔ x ∈ Valued.v.integer
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hσ]
  simp only [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf, MonoidHom.mem_range]
  constructor
  · rintro ⟨-, h, hh⟩
    have e : ∀ i j, mat u i j = (((h : GL (Fin (N + 2)) (intL L)) : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L)) i j : L) := by
      intro i j
      show ((u : GL (Fin (N + 2)) L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j = _
      rw [← hh]
      rfl
    refine ⟨fun j => ?_, ?_⟩
    · show mat u 0 (mid j) ∈ intL L
      rw [e]
      exact Subtype.prop _
    · show mat u 0 (Fin.last (N + 1)) ∈ intL L
      rw [e]
      exact Subtype.prop _
  · rintro ⟨hr, hc⟩
    have hb : ∀ i, colOf u i ∈ intL L := by
      intro i
      have h1 := row_eq hu i.rev
      rw [Fin.rev_rev] at h1
      have h2 : σ (colOf u i) = -rowOf u i.rev := by rw [h1, neg_neg]
      have h3 : σ (colOf u i) ∈ intL L := by
        rw [h2]
        exact neg_mem (hr i.rev)
      exact (hσint _).1 h3
    have hu' := inv_mem hu
    have E1 := mat_apply_mem_intL_of_mem_radQ_of_blocks hu hr hb hc
    have E2 := mat_apply_mem_intL_of_mem_radQ_of_blocks hu'
      (fun j => by rw [rowOf_inv]; exact (hσint _).2 (hb _))
      (fun i => by rw [colOf_inv hu]; exact neg_mem (hb i))
      (by rw [cornerOf_inv]; exact (hσint _).2 hc)
    have inj : Function.Injective ((intL L).subtype.mapMatrix : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) → _) :=
      fun X Y hXY => by
        ext i j
        exact congrFun (congrFun hXY i) j
    have m1 : mat u * mat u⁻¹ = 1 := by
      show mat (u * u⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    have m2 : mat u⁻¹ * mat u = 1 := by
      show mat (u⁻¹ * u) = 1
      rw [inv_mul_cancel]
      rfl
    let A : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) := Matrix.of fun i j => ⟨mat u i j, E1 i j⟩
    let B : Matrix (Fin (N + 2)) (Fin (N + 2)) (intL L) := Matrix.of fun i j => ⟨mat u⁻¹ i j, E2 i j⟩
    have hA : (intL L).subtype.mapMatrix A = mat u := by
      ext i j
      rfl
    have hB : (intL L).subtype.mapMatrix B = mat u⁻¹ := by
      ext i j
      rfl
    have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, m1])
    have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, m2])
    refine ⟨u.2, ⟨⟨A, B, hAB, hBA⟩, ?_⟩⟩
    apply Units.ext
    exact hA
end GlobalTheory.CompanionTheory.InertHeis
