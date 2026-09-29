-- Prove2me | solution 1 for ModularCurve.exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d52e5d33-89dd-5abf-b35a-71e30235f21a

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient_toricSlotSet
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Theorems.Thm_WeierstrassCurve_map_veluQuotient_image
import Theorems.Thm_ModularCurve_tateUniv_equation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

namespace StepCurve

variable (K : Type u) [Field K]

theorem qExpand_comp_qExpand (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    (qExpand K a).comp (qExpand K b) = qExpand K (a * b) :=
  RingHom.ext fun f => qExpand_qExpand b a f

theorem qExpand_comp_qExpand_one (a : ℕ) [NeZero a] :
    (qExpand K a).comp (qExpand K 1) = qExpand K a :=
  RingHom.ext fun f => by rw [RingHom.comp_apply, qExpand_one_apply]

theorem map_qExpand_eq_self_of_const (a : ℕ) [NeZero a] (C : VariableChange (LaurentSeries K))
    (n : ℕ) (r s t : K) (hu : (C.u : LaurentSeries K) = (n : LaurentSeries K))
    (hr : C.r = HahnSeries.C r) (hs : C.s = HahnSeries.C s) (ht : C.t = HahnSeries.C t) :
    C.map (qExpand K a) = C := by
  ext
  · rw [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe, hu, map_natCast]
  · rw [VariableChange.map_r, hr, qExpand_C]
  · rw [VariableChange.map_s, hs, qExpand_C]
  · rw [VariableChange.map_t, ht, qExpand_C]

theorem image_toricPoint_one (a : ℕ) [NeZero a] (ℓ : ℕ) (ζ : K)
    [DecidableEq (LaurentSeries K × LaurentSeries K)] :
    (((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k)).image
        (Prod.map (qExpand K a) (qExpand K a))) =
      (Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K a (ζ ^ k) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  have h := toricPoint_level_mul K 1 a (ζ ^ k)
  rw [mul_one] at h
  rw [h]
  rfl

theorem card_image_prodMap_qExpand (a : ℕ) [NeZero a] (S : Finset (LaurentSeries K × LaurentSeries K))
    [DecidableEq (LaurentSeries K × LaurentSeries K)] :
    (S.image (Prod.map (qExpand K a) (qExpand K a))).card = S.card :=
  Finset.card_image_of_injective _ (Prod.map_injective.mpr ⟨qExpand_injective a, qExpand_injective a⟩)

end StepCurve

open StepCurve in
open scoped Classical in
theorem solution
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (ℓ : LaurentSeries K) ∧
        C.r = HahnSeries.C (((ℓ : K) ^ 2 - 1) / 12) ∧
          C.s = HahnSeries.C (((ℓ : K) - 1) / 2) ∧
            C.t = HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)) ∧
              C • ((tateLaurent K).map (qExpand K m)).veluQuotient
                  ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k)) =
                (tateLaurent K).map (qExpand K (m * ℓ)) := by
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓ.ne_zero
  set ζu : Kˣ := Units.mk0 ζ hζ0 with hζu
  have hζu' : IsPrimitiveRoot (ζu : K) ℓ := hζ
  obtain ⟨C, hu, hr, hs, ht, hC⟩ :=
    exists_variableChange_veluQuotient_toricSlotSet K ℓ hodd ζu hζu' tateUniv_equation
  refine ⟨C, hu, hr, hs, ht, ?_⟩
  have hCmap : ∀ (a : ℕ) [NeZero a], C.map (qExpand K a) = C := fun a _ =>
    map_qExpand_eq_self_of_const K a C ℓ _ _ _ hu hr hs ht

  set S1 : Finset (LaurentSeries K × LaurentSeries K) :=
    (Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k) with hS1
  have hpush : ∀ (a : ℕ) [NeZero a],
      (C • ((tateLaurent K).map (qExpand K 1)).veluQuotient S1).map (qExpand K a) =
        C • ((tateLaurent K).map (qExpand K a)).veluQuotient
          ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K a (ζ ^ k)) := by
    intro a _
    rw [← map_variableChange, ← map_veluQuotient_image _ _ _ (card_image_prodMap_qExpand K a S1),
      WeierstrassCurve.map_map, qExpand_comp_qExpand_one, hS1, image_toricPoint_one, hCmap]
  have hpushR : ∀ (a : ℕ) [NeZero a] [NeZero (a * ℓ)],
      ((tateLaurent K).map (qExpand K ℓ)).map (qExpand K a) = (tateLaurent K).map (qExpand K (a * ℓ)) := by
    intro a _ _
    rw [WeierstrassCurve.map_map, qExpand_comp_qExpand]

  haveI : NeZero (ℓ * ℓ) := ⟨Nat.mul_ne_zero hℓ.ne_zero hℓ.ne_zero⟩
  have hone : C • ((tateLaurent K).map (qExpand K 1)).veluQuotient S1 = (tateLaurent K).map (qExpand K ℓ) := by
    apply WeierstrassCurve.map_injective (qExpand_injective ℓ)
    dsimp only
    rw [hpush ℓ, hpushR ℓ]
    exact hC

  haveI : NeZero (m * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne m) hℓ.ne_zero⟩
  have h := congrArg (fun W : WeierstrassCurve (LaurentSeries K) => W.map (qExpand K m)) hone
  rw [hpush m, hpushR m] at h
  exact h

end S_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
end P2MW
export P2MW.S_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul (solution)
