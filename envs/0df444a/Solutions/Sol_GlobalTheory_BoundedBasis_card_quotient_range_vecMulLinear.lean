-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.card_quotient_range_vecMulLinear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:21.071807+00:00
-- url     : https://prove2.me/submissions/7a8b4d39-89fe-4c0c-8fff-a42ac247173c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {r : ℕ} (N : Matrix (Fin r) (Fin r) (𝓞 E))
    (hN : N.det ≠ 0) :
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) =
      (Algebra.norm ℤ N.det).natAbs := by
  have hinj : Function.Injective N.vecMulLinear := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_vecMul_eq_zero hN hx
  let P : Submodule ℤ (Fin r → 𝓞 E) := (LinearMap.range N.vecMulLinear).restrictScalars ℤ
  let e : (Fin r → 𝓞 E) ≃+ P := (LinearEquiv.ofInjective _ hinj).toAddEquiv
  have key := Submodule.natAbs_det_equiv P e
  have hcomp : P.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin r → 𝓞 E) →+ P) =
      (Matrix.toLin' Nᵀ).restrictScalars ℤ :=
    LinearMap.ext fun x => by
      change x ᵥ* N = Nᵀ *ᵥ x
      rw [Matrix.mulVec_transpose]
  rw [hcomp, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose] at key
  rw [key]
  rfl
end GlobalTheory.BoundedBasis
