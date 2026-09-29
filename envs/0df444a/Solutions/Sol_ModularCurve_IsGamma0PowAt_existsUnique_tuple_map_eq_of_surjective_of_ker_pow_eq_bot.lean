-- Prove2me | solution 1 for ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e22585a4-d222-55ec-ab51-d7a480473339

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃"

set_option autoImplicit false

universe u

open Polynomial

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (M' : ℕ) (hM' : IsUnit ((M' : ℕ) : T))
    (hh' : ↥M'.primeFactors → T'[X])
    (H' : ∀ p : ↥M'.primeFactors,
      ModularCurve.IsGamma0PowAt (W.map π) (p : ℕ) (M'.factorization (p : ℕ)) (hh' p)) :
    ∃! hh : ↥M'.primeFactors → T[X],
      (fun p => (hh p).map π) = hh' ∧
      ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (hh p) := by
  classical
  have hp : ∀ p : ↥M'.primeFactors, IsUnit (((p : ℕ) : ℕ) : T) := fun p =>
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (Nat.dvd_of_mem_primeFactors p.2)) hM'
  haveI hprime : ∀ p : ↥M'.primeFactors, Fact (p : ℕ).Prime := fun p => ⟨Nat.prime_of_mem_primeFactors p.2⟩
  have H : ∀ p : ↥M'.primeFactors, ∃! h : T[X], h.map π = hh' p ∧
      ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) h := fun p =>
    ModularCurve.IsGamma0PowAt.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot π hπ hnil W hΔ (p : ℕ)
      (M'.factorization (p : ℕ)) (hp p) (hh' p) (H' p)
  refine ⟨fun p => (H p).choose, ⟨funext fun p => (H p).choose_spec.1.1, fun p => (H p).choose_spec.1.2⟩, ?_⟩
  rintro hh ⟨hmap, hlev⟩
  funext p
  exact (H p).unique ⟨congrFun hmap p, hlev p⟩ (H p).choose_spec.1

end S_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot (solution)
