-- Prove2me | solution 1 for ModularCurve.arithmeticRingAut_geomAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4b728424-5fa3-5b28-8104-ed30c82887f9

import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticRingAut_geomAut

open ModularCurve AlgebraicCurve
open scoped TensorProduct

theorem solution (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (τ : L ≃ₐ[ℚ] L) (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ τ (geomAut L F₀ σ x) = geomAut L F₀ σ (arithmeticRingAut F₀ τ x) := by
  have hgen : ∀ g : F₀, arithmeticRingAut F₀ τ ⟨coeffEmb L g, coeffEmb_mem_laurentBaseChange L g.2⟩ =
      ⟨coeffEmb L g, coeffEmb_mem_laurentBaseChange L g.2⟩ :=
    fun g => Subtype.ext (coeffMap_coeffEmb τ (g : LaurentSeries ℚ))
  let e : TensorProduct ℚ L F₀ →+* laurentBaseChange L F₀ := (baseChangeEquiv L F₀).toRingEquiv.toRingHom
  let gσ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀ := (geomAut L F₀ σ).toRingEquiv.toRingHom
  let aτ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀ := (arithmeticRingAut F₀ τ).toRingHom
  have key : ∀ y, aτ (gσ (e y)) = gσ (aτ (e y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c f =>
        change arithmeticRingAut F₀ τ (geomAut L F₀ σ (baseChangeEquiv L F₀ (c ⊗ₜ[ℚ] f))) =
          geomAut L F₀ σ (arithmeticRingAut F₀ τ (baseChangeEquiv L F₀ (c ⊗ₜ[ℚ] f)))
        rw [baseChangeEquiv_tmul, map_mul, map_mul, map_mul, map_mul, AlgEquiv.commutes,
          arithmeticRingAut_algebraMap, AlgEquiv.commutes, geomAut_coeffEmb, hgen, hgen, geomAut_coeffEmb]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨y, rfl⟩ := (baseChangeEquiv L F₀).surjective x
  exact key y

end S_ModularCurve_arithmeticRingAut_geomAut
end P2MW
export P2MW.S_ModularCurve_arithmeticRingAut_geomAut (solution)
