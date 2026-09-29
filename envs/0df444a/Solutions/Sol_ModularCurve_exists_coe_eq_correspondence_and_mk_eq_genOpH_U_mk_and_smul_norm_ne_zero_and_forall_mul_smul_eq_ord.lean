-- Prove2me | solution 1 for ModularCurve.exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d2ecaba9-d763-51c3-8bd6-17a61e835666

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (hin : HeckeDiamondInputsHAll M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdivf : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (p : ℤ) * (wgen • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord f) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H p) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H p)
      (_ : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))))
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p))
      (_ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hfin)
      (D_U : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))),
      (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Divisor.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H p) (heckeAlphaHBar (AlgebraicClosure ℚ) M H p) hβ hα
            (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
      (Pic0.mk D_U : JH M H) = genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) (Pic0.mk D) ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
       wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H)) ≠ 0) ∧
      ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (p : ℤ) * (wgen • (D_U : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v =
          v.ord (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
                 wgen • (Algebra.norm ↥(xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(xHFunctionFieldBar M H))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hin.heckeInputsHAlong p Fact.out

  set α := heckeAlphaHBar (AlgebraicClosure ℚ) M H p with hαdef
  set β := heckeBetaHBar (AlgebraicClosure ℚ) M H p with hβdef
  letI instA : Algebra ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.algebraAlong α
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.isScalarTower_along α
  haveI : Algebra.IsIntegral ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.isIntegral_along α hα
  haveI instF : Module.Finite ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := hfin
  set g : ↥(xHFunctionFieldBar M H) := wgen⁻¹ • f with hg
  have hg0 : g ≠ 0 := by rw [hg, SemilinearAut.smul_def]; exact (map_ne_zero _).mpr hf
  have hβg0 : β g ≠ 0 := (map_ne_zero _).mpr hg0
  set N : ↥(xHFunctionFieldBar M H) := Algebra.norm ↥(xHFunctionFieldBar M H) (β g) with hNdef
  have hN0 : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβg0
  refine ⟨hα, hβ, hP, hfin, hN, Pic0.degZeroCorrespondence β α hβ hα hFI D,
    Pic0.coe_degZeroCorrespondence β α hβ hα hFI D, ?_, ?_, ?_⟩
  ·
    symm
    rw [genOpH_U, heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN]
    exact Pic0.correspondence_mk β α hβ hα hFI hfin hN D
  ·
    show wgen • N ≠ 0
    rw [SemilinearAut.smul_def]; exact (map_ne_zero _).mpr hN0
  ·
    intro v
    show (p : ℤ) * (wgen • (Pic0.degZeroCorrespondence β α hβ hα hFI D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) v = v.ord (wgen • N)

    have hpD : ∀ w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ((p : ℤ) • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) w = w.ord g := by
      intro w
      rw [Finsupp.smul_apply, smul_eq_mul, hg, ← SemilinearAut.ord_smul wgen w (wgen⁻¹ • f), smul_inv_smul,
        ← hdivf (wgen • w), SemilinearAut.divisor_smul_apply, inv_smul_smul]

    have hpull : ∀ w' : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))),
        Divisor.pullbackAlong β hβ ((p : ℤ) • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) w' = w'.ord (β g) := by
      intro w'
      letI : Algebra ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.algebraAlong β
      haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.isScalarTower_along β
      haveI : Algebra.IsIntegral ↥(xHFunctionFieldBar M H) ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * p))) := AlgebraicCurve.isIntegral_along β hβ
      exact Divisor.pullback_apply_eq_ord hpD w'

    have hpush : Divisor.pushforwardAlong α hα (Divisor.pullbackAlong β hβ ((p : ℤ) • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))) v = v.ord N :=
      hN (β g) hβg0 _ hpull v

    rw [SemilinearAut.divisor_smul_apply, Pic0.coe_degZeroCorrespondence]
    have hcorr : (p : ℤ) * Divisor.correspondence β α hβ hα (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (wgen⁻¹ • v) =
        Divisor.correspondence β α hβ hα ((p : ℤ) • (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (wgen⁻¹ • v) := by
      rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    rw [hcorr, Divisor.correspondence_apply]
    have := SemilinearAut.ord_smul wgen (wgen⁻¹ • v) N
    rw [smul_inv_smul] at this
    rw [this]
    exact hN (β g) hβg0 _ hpull (wgen⁻¹ • v)

end S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord
end P2MW
export P2MW.S_ModularCurve_exists_coe_eq_correspondence_and_mk_eq_genOpH_U_mk_and_smul_norm_ne_zero_and_forall_mul_smul_eq_ord (solution)
