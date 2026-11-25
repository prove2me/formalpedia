-- Prove2me | solution 1 for GlobalTheory.UnitCase.ubUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:56.709835+00:00
-- url     : https://prove2.me/submissions/5a3b7071-875c-4fdf-b7f3-b6a8bd4dd6b5

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Theorems.Thm_GlobalTheory_UnitCase_mvExp_add
import Theorems.Thm_GlobalTheory_UnitCase_coeff_zero_mvExp
import Theorems.Thm_GlobalTheory_UnitCase_mem_mult
import Theorems.Thm_GlobalTheory_UnitCase_jet_sub_mem
import Theorems.Thm_GlobalTheory_UnitCase_row_det_pow
import Theorems.Thm_GlobalTheory_UnitCase_map_cayDet
import Theorems.Thm_GlobalTheory_UnitCase_detL_eq
import Theorems.Thm_GlobalTheory_UnitCase_detR_eq
import Theorems.Thm_GlobalTheory_UnitCase_inv_mem_intRing
import Theorems.Thm_GlobalTheory_UnitCase_val_prod_factorial
import Theorems.Thm_GlobalTheory_DetPowPairing_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.UnitCase
theorem _root_.solution : UBUnit := by
  intro C _ _ v l hl h5 hvl hp n n0 y hn hy h1 h10 hint
  classical
  set q := cayDet n0 ℤ ^ y with hq
  have hrB : ∀ B ∈ q.support, ∀ b, ∑ c, B (b, c) = y := fun B hB => row_det_pow n0 y B hB
  have hrA : ∀ A ∈ (q ^ l).support, ∀ b, ∑ c, A (b, c) = l * y := fun A hA => by
    rw [hq, ← pow_mul, mul_comm] at hA
    exact row_det_pow n0 _ A hA
  have key := jet_sub_mem hl (intRing v) (inv_mem_intRing hp) q
    (fun B hB j => by
      have h2 : B (j.1, j.2) ≤ ∑ c, B (j.1, c) :=
        Finset.single_le_sum (f := fun c => B (j.1, c)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j.2)
      rw [hrB B hB] at h2
      change B (j.1, j.2) < l
      omega)
    (fun A hA B hB => by
      simp only [Fintype.sum_prod_type, hrA A hA, hrB B hB, Finset.mul_sum])
    (mvExp h1) (coeff_zero_mvExp h1)
    (fun A hA B hB m hm => hint m
      (fun b => by
        rw [← hrA A hA b]
        exact Finset.sum_le_sum fun c _ => by simpa using hm (Sum.inl (b, c)))
      (fun b => by
        rw [← hrB B hB b]
        exact Finset.sum_le_sum fun c _ => by simpa using hm (Sum.inr (b, c))))
  have hmain : hP C l 1 n0 h1 = mainTerm l (-(l : C)⁻¹) + h1 := by
    simp [hP, mainTerm, expE, Fintype.sum_prod_type]
  have hL : LamP C l 1 n0 h1 y =
      jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) (q ^ l)) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q))
        (mvExp (mainTerm l (-(l : C)⁻¹)) * mvExp h1) := by
    rw [LamP, hmain, mvExp_add _ h10, detL_eq, detR_eq, hq, ← pow_mul, mul_comm y l, pow_one]
    · simp only [map_pow, map_cayDet]
    · simp [mainTerm]
  rw [← hL] at key
  obtain ⟨o, ho, he⟩ := mem_mult.1 key
  have hcap := GlobalTheory.DetPowPairing.main C n0 y
  have hsum : (∑ A ∈ (cayDet n0 C ^ y).support, MvPolynomial.coeff A (cayDet n0 C ^ y) *
      (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n0 C ^ y)) =
      ∑ B ∈ q.support, ((MvPolynomial.coeff B q : ℤ) : C) * mfact B *
        (MvPolynomial.coeff B q : ℤ) := by
    rw [← map_cayDet, ← map_pow, ← hq,
      MvPolynomial.support_map_of_injective _ (RingHom.injective_int _)]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp [MvPolynomial.coeff_map, mfact, Finsupp.prod]
  rw [hsum] at hcap
  have hv := congrArg v hcap
  rw [v.map_mul, val_prod_factorial hl hp _ (fun c => c) (fun c hc => by
      have := Finset.mem_range.1 hc
      omega),
    val_prod_factorial hl hp _ (fun c => y + c) (fun c hc => by
      have := Finset.mem_range.1 hc
      omega), zero_add] at hv
  rw [eq_add_of_sub_eq' he.symm, v.map_add_eq_of_lt_left, hv]
  rw [hv, v.map_mul, hvl]
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right ho)
end GlobalTheory.UnitCase
