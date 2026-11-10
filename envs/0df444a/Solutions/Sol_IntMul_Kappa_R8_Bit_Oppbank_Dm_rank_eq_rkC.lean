-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.Dm_rank_eq_rkC
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T07:20:57.568193+00:00
-- url     : https://prove2.me/submissions/d1fddfe7-749e-438b-8368-99197eb4e7ca

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
open Matrix Module
open IntMul IntMul.Kappa IntMul.Kappa.R8 IntMul.Kappa.R8.Bit IntMul.Kappa.R8.Bit.Oppbank in
theorem solution :
    ¬ (∀ {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound) (hr : 0 < rkC o c), (Dm o c).rank = rkC o c) := by
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
  have hnd : Pc 1773 = prjM (spanS (SupG.densSupG 0)) (compl_spanS hC) :=
    Pc_ND_ne_stub 0 (by decide) hC
  have hPc1773_xv : Pc 1773 *ᵥ xv 0 = xv 0 := by
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
  have hPl_w (w : V23) : Pl 0 *ᵥ w = (yv 0 ⬝ᵥ w) • xv 0 := by
    ext i
    simp only [Pl, vecMulVec_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  have hbf (u : V23) : bfF (xv 0) u = 2 * (yv 0 ⬝ᵥ u) := by
    simp only [bfF, xv, yv, hsum, dotProduct, Finset.mul_sum, Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have horth (w : V23) : w - (yv 0 ⬝ᵥ w) • xv 0 ∈ Bf.orthogonal (spanS (SupG.densSupG 0)) := by
    rw [mem_orth]
    let H : Submodule ℚ V23 :=
      { carrier := {v | bfF v (w - (yv 0 ⬝ᵥ w) • xv 0) = 0}
        add_mem' := fun {a b} ha hb => by
          change bfF (a + b) _ = 0
          rw [← Bf_apply, map_add, LinearMap.add_apply, Bf_apply, Bf_apply, ha, hb, add_zero]
        zero_mem' := by
          change bfF 0 _ = 0
          rw [← Bf_apply, map_zero, LinearMap.zero_apply]
        smul_mem' := fun r a ha => by
          change bfF (r • a) _ = 0
          rw [← Bf_apply, map_smul, LinearMap.smul_apply, Bf_apply, ha, smul_zero] }
    have hle : spanS (SupG.densSupG 0) ≤ H := by
      rw [hsup0, spanS, Submodule.span_le]
      rintro v ⟨i, hi, rfl⟩
      rcases i with _ | i
      · change bfF (xv 0) (w - (yv 0 ⬝ᵥ w) • xv 0) = 0
        rw [hbf, dotProduct_sub, dotProduct_smul, hyv_xv, smul_eq_mul, mul_one, sub_self, mul_zero]
      · exfalso
        have hpow : 1 < 2 ^ (i + 1) := Nat.one_lt_two_pow (by omega)
        have hlt : (1 : ℕ).testBit (i + 1) = false := Nat.testBit_lt_two_pow hpow
        rw [hlt] at hi
        cases hi
    intro v hv
    exact hle hv
  have hPc1773_orth (u : V23) (hu : u ∈ Bf.orthogonal (spanS (SupG.densSupG 0))) :
      Pc 1773 *ᵥ u = 0 := by
    rw [hnd, prjM, LinearMap.toMatrix'_mulVec]
    set U := spanS (SupG.densSupG 0)
    set hc := compl_spanS hC
    have hp1 : U.projection (Bf.orthogonal U) hc u ∈ U :=
      Submodule.projection_apply_mem hc u
    have hadd := Submodule.projection_add_projection_eq_self hc u
    have hp2 : u - U.projection (Bf.orthogonal U) hc u ∈ Bf.orthogonal U := by
      have heq : u - U.projection (Bf.orthogonal U) hc u =
          (Bf.orthogonal U).projection U hc.symm u := (eq_sub_of_add_eq' hadd).symm
      rw [heq]
      exact Submodule.projection_apply_mem hc.symm u
    have hp3 : U.projection (Bf.orthogonal U) hc u ∈ Bf.orthogonal U := by
      have hsub := (Bf.orthogonal U).sub_mem hu hp2
      simpa using hsub
    have hbot : U.projection (Bf.orthogonal U) hc u ∈ U ⊓ Bf.orthogonal U := ⟨hp1, hp3⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hbot
    exact hbot
  have hPc1773_w (w : V23) : Pc 1773 *ᵥ w = (yv 0 ⬝ᵥ w) • xv 0 := by
    have hsplit : w = (yv 0 ⬝ᵥ w) • xv 0 + (w - (yv 0 ⬝ᵥ w) • xv 0) := by abel
    conv_lhs => rw [hsplit]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hPc1773_xv, hPc1773_orth _ (horth w), add_zero]
  have hPc2_w (w : V23) : Pc 2 *ᵥ w = w - (yv 0 ⬝ᵥ w) • xv 0 := by
    have h2 : Pc 2 = 1 - Pl 0 := rfl
    rw [h2, Matrix.sub_mulVec, Matrix.one_mulVec, hPl_w]
  have hDm : Dm 2 1773 = Pc 2 - Pc 1773 := by
    unfold Dm
    have hcmp : ¬ (dimCF 2 ≤ dimCF 1773) := by decide
    simp [hcmp]
  have hDm_w (w : V23) : Dm 2 1773 *ᵥ w = w - ((2 : ℚ) * (yv 0 ⬝ᵥ w)) • xv 0 := by
    rw [hDm, Matrix.sub_mulVec, hPc2_w, hPc1773_w, sub_sub, ← add_smul]
    ring_nf
  have hDm_xv : Dm 2 1773 *ᵥ xv 0 = - xv 0 := by
    rw [hDm_w, hyv_xv, mul_one, two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hinv (w : V23) : Dm 2 1773 *ᵥ (Dm 2 1773 *ᵥ w) = w := by
    conv_lhs => rw [hDm_w w, Matrix.mulVec_sub, Matrix.mulVec_smul, hDm_w w, hDm_xv]
    simp [smul_neg, sub_neg_eq_add]
  have htop : LinearMap.range (Dm 2 1773).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 fun w => ⟨Dm 2 1773 *ᵥ w, hinv w⟩
  have hrk : (Dm 2 1773).rank = 23 := by
    rw [Matrix.rank, htop, finrank_top, Module.finrank_pi, Fintype.card_fin]
  have hclaimed := claimed (o := 2) (c := 1773) (by decide) (by decide) (by decide)
  rw [hrk] at hclaimed
  revert hclaimed
  decide

#print axioms solution
