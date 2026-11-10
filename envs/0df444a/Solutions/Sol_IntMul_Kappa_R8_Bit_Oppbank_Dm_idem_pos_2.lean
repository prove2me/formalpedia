-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.Dm_idem_pos
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T07:20:56.613181+00:00
-- url     : https://prove2.me/submissions/f0387823-e383-4619-a401-0d8174f09631

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The target is elaborated inside namespace `IntMul.Kappa.R8.Bit.Oppbank`; the empty block registers it for `open`.
namespace IntMul.Kappa.R8.Bit.Oppbank
end IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix
open IntMul IntMul.Kappa IntMul.Kappa.R8 IntMul.Kappa.R8.Bit IntMul.Kappa.R8.Bit.Oppbank in
theorem solution :
    ¬ (∀ (o c : ℕ) (ho : o < codeBound) (hc : c < codeBound) (hr : 0 < rkC o c), Dm o c * Dm o c = Dm o c) := by
  intro claimed
  have hsup0 : SupG.densSupG 0 = 1 := by decide
  have htri : triL 0 = 7 := by decide
  have htv_p (p : Fin 23) : tvQ 0 p = if (7 : ℕ).testBit p.val = true then 1 else 0 := by
    unfold tvQ
    rw [htri]
  have hsum_nat : (∑ p : Fin 23, if (7 : ℕ).testBit p.val = true then (1 : ℕ) else 0) = 3 := by
    decide
  have hsum : (∑ p : Fin 23, tvQ 0 p) = 3 := by
    have hcast : ∀ p : Fin 23, tvQ 0 p =
        ((if (7 : ℕ).testBit p.val = true then (1 : ℕ) else 0 : ℕ) : ℚ) := by
      intro p
      rw [htv_p p]
      split_ifs <;> simp
    simp_rw [hcast]
    exact_mod_cast hsum_nat
  have hC : HasCentre (SupG.densSupG 0) := by
    rw [hsup0]
    refine ⟨0, by decide, fun i hi => ?_⟩
    rcases i with _ | i
    · refine ⟨by decide, ?_, hsum⟩
      rw [htri]
      decide
    · exfalso
      have hpow : 1 < 2 ^ (i + 1) := Nat.one_lt_two_pow (by omega)
      have hlt : (1 : ℕ).testBit (i + 1) = false := Nat.testBit_lt_two_pow hpow
      rw [hlt] at hi
      cases hi
  have hmem : xv 0 ∈ spanS (SupG.densSupG 0) :=
    Submodule.subset_span ⟨0, by decide, rfl⟩
  have hPc1773 : Pc 1773 *ᵥ xv 0 = xv 0 := by
    have hnd : Pc 1773 = prjM (spanS (SupG.densSupG 0)) (compl_spanS hC) :=
      Pc_ND_ne_stub 0 (by decide) hC
    rw [hnd, prjM, LinearMap.toMatrix'_mulVec]
    exact Submodule.projection_apply_of_mem_left (compl_spanS hC) hmem
  have hsq (p : Fin 23) : tvQ 0 p * tvQ 0 p = tvQ 0 p := by
    unfold tvQ
    split_ifs <;> ring
  have hyv_xv : yv 0 ⬝ᵥ xv 0 = 1 := by
    have h1 : yv 0 ⬝ᵥ xv 0 = (∑ p : Fin 23, (tvQ 0 p - (3 : ℚ) / 9) / 2 * tvQ 0 p) := by
      simp only [yv, xv, dotProduct, hsum]
    have h2 : ∀ p : Fin 23, (tvQ 0 p - (3 : ℚ) / 9) / 2 * tvQ 0 p = (1 / 3 : ℚ) * tvQ 0 p := by
      intro p
      calc (tvQ 0 p - (3 : ℚ) / 9) / 2 * tvQ 0 p
          = (tvQ 0 p * tvQ 0 p - (1 / 3 : ℚ) * tvQ 0 p) / 2 := by ring
        _ = (tvQ 0 p - (1 / 3 : ℚ) * tvQ 0 p) / 2 := by rw [hsq p]
        _ = (1 / 3 : ℚ) * tvQ 0 p := by ring
    simp_rw [h1, h2, ← Finset.mul_sum, hsum]
    norm_num
  have hPl0 : Pl 0 *ᵥ xv 0 = xv 0 := by
    ext i
    simp only [Pl, vecMulVec_apply, mulVec, dotProduct, mul_assoc, ← Finset.mul_sum]
    have hdot : (∑ j : Fin 23, yv 0 j * xv 0 j) = yv 0 ⬝ᵥ xv 0 := rfl
    rw [hdot, hyv_xv, mul_one]
  have hPc2 : Pc 2 *ᵥ xv 0 = 0 := by
    have h2 : Pc 2 = 1 - Pl 0 := rfl
    rw [h2, Matrix.sub_mulVec, Matrix.one_mulVec, hPl0, sub_self]
  have hDm : Dm 2 1773 = Pc 2 - Pc 1773 := by
    unfold Dm
    have hcmp : ¬ (dimCF 2 ≤ dimCF 1773) := by decide
    simp [hcmp]
  have hDm_xv : Dm 2 1773 *ᵥ xv 0 = - xv 0 := by
    rw [hDm, Matrix.sub_mulVec, hPc2, hPc1773, zero_sub]
  have hDm2_xv : (Dm 2 1773 * Dm 2 1773) *ᵥ xv 0 = xv 0 := by
    rw [← Matrix.mulVec_mulVec, hDm_xv, Matrix.mulVec_neg, hDm_xv, neg_neg]
  have hidem := claimed 2 1773 (by decide) (by decide) (by decide)
  have heq : (Dm 2 1773 * Dm 2 1773) *ᵥ xv 0 = Dm 2 1773 *ᵥ xv 0 := by
    rw [hidem]
  rw [hDm2_xv, hDm_xv] at heq
  have h0 : xv 0 0 = (- xv 0) 0 := congrFun heq 0
  have hx0 : xv 0 0 = 1 := by
    change tvQ 0 0 = 1
    rw [htv_p 0]
    rfl
  rw [Pi.neg_apply, hx0] at h0
  norm_num at h0

#print axioms solution
