-- Prove2me | solution 1 for ModularCurve.XOneP.eval_fibrePoly_apply_heckePin_jChartFin_eq_zero_of_modularPolynomialData_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/99465d07-4c13-520b-890a-0dd787761682

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_eval_fibrePoly_apply_heckePin_jChartFin_eq_zero_of_modularPolynomialData_twoChartModel_x1_mul

set_option autoImplicit false

open Polynomial

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
      ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (data : ModularCurve.ModularPolynomialData ℓ)
    (Ω : Type) [Field Ω]
    (φ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) →+* Ω) :
    (ModularCurve.fibrePoly data.Φ (φ (ια (ModularCurve.TwoChart.jChartFin A (↥K) j)))).eval
      (φ (ιβ (ModularCurve.TwoChart.jChartFin A (↥K) j))) = 0 := by
  classical

  have hext : ∀ {S : Type} [CommRing S] (f g : Polynomial ℤ →+* S), f Polynomial.X = g Polynomial.X → f = g :=
    fun f g h => Polynomial.ringHom_ext' (RingHom.ext_int _ _) h

  let Kℓ := ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))
  let Bℓ := ModularCurve.TwoChart.chartAlgFin A (↥Kℓ) jℓ
  let ĵ := ModularCurve.TwoChart.jChartFin A (↥K) j

  let c : ↥Bℓ →+* LaurentSeries L := (algebraMap (↥Kℓ) (LaurentSeries L)).comp (Bℓ.val : ↥Bℓ →ₐ[A] ↥Kℓ).toRingHom
  have hc : ∀ b : ↥Bℓ, c b = ((b : ↥Kℓ) : LaurentSeries L) := fun _ => rfl
  have hcinj : Function.Injective c := fun x y h => Subtype.ext (Subtype.ext (by rw [← hc, ← hc]; exact h))
  have hα : c (ια ĵ) = ModularCurve.coeffEmb L ModularCurve.jq := by
    rw [hc, hια, ModularCurve.TwoChart.coe_jChartFin, hj]
  have hβv : c (ιβ ĵ) = ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq) := by
    rw [hc, hιβ, ModularCurve.TwoChart.coe_jChartFin, hj]

  have key : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (ModularCurve.coeffEmb L ModularCurve.jq))
      (ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq)) = 0 := by
    have h0 := congrArg (ModularCurve.coeffEmb L) data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂] at h0
    have h1 : (ModularCurve.coeffEmb L).comp ModularCurve.evalAtJ =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (ModularCurve.coeffEmb L ModularCurve.jq) := by
      apply hext
      rw [RingHom.comp_apply, ModularCurve.evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    have h2 : ModularCurve.coeffEmb L (ModularCurve.jqN ℓ) = ModularCurve.qExpand L ℓ (ModularCurve.coeffEmb L ModularCurve.jq) := by
      show ModularCurve.coeffMap (algebraMap ℚ L) (ModularCurve.qExpand ℚ ℓ ModularCurve.jq) = _
      rw [ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
      rfl
    rw [h1, h2] at h0
    exact h0

  have keyB : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥Bℓ) (ια ĵ)) (ιβ ĵ) = 0 := by
    apply hcinj
    rw [map_zero, Polynomial.hom_eval₂, hβv]
    have h3 : c.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥Bℓ) (ια ĵ)) =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) (ModularCurve.coeffEmb L ModularCurve.jq) := by
      apply hext
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hα, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [h3]
    exact key

  have h4 := congrArg φ keyB
  rw [map_zero, Polynomial.hom_eval₂] at h4
  have h5 : φ.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥Bℓ) (ια ĵ)) =
      Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ (ια ĵ)) := by
    apply hext
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [h5] at h4
  rw [ModularCurve.fibrePoly, Polynomial.eval_map]
  exact h4

end S_ModularCurve_XOneP_eval_fibrePoly_apply_heckePin_jChartFin_eq_zero_of_modularPolynomialData_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_eval_fibrePoly_apply_heckePin_jChartFin_eq_zero_of_modularPolynomialData_twoChartModel_x1_mul (solution)
