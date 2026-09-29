-- Prove2me | solution 1 for ModularCurve.LevelP.isUnit_discriminant_quotientByLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/79761397-59f8-5781-a1fa-b37cd95e8ecc

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPQuotient
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
import Theorems.Thm_ModularCurve_LevelP_quotientByLine_eq_veluQuotient_oddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty"

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.quotientByLine LevelP.quotientByLine_map LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet"
namespace LevelP
p2m_export "ModularCurve.LevelP" "quotientByLine quotientByLine_map quotientByLine_eq_veluQuotient_oddOrderSummingSet"
namespace DiscUnit
p2m_open "ModularCurve.LevelP ModularCurve"

p2m_open "WeierstrassCurve Polynomial ModularCurve.LevelP P2MW.S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine.ModularCurve.LevelP"

variable {A : Type u} [CommRing A]

theorem isUnit_of_forall_maximal (d : A)
    (h : ∀ M : Ideal A, M.IsMaximal → d ∉ M) : IsUnit d := by
  by_contra hd
  have hne : Ideal.span ({d} : Set A) ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  exact h M hM (hle (Ideal.subset_span (Set.mem_singleton d)))

theorem isUnit_ΨSq_of_mem_Icc (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : IsUnit ((p : A) * W.Δ)) {x : A} (hx : (W.preΨ p).eval x = 0)
    (a : ℕ) (ha : a ∈ Finset.Icc 1 ((p - 1) / 2)) : IsUnit ((W.ΨSq a).eval x) := by
  have hp : p.Prime := Fact.out
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have hlt : a < p := by
    have := Nat.div_le_self (p - 1) 2; omega
  have hnd : ¬ (p : ℤ) ∣ (a : ℤ) := by
    intro hdvd
    have := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp hdvd)
    omega
  exact (WeierstrassCurve.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero W hp2 hW hx hnd).1

theorem quotientByLine_Δ_ne_zero {L : Type u} [Field L] [IsAlgClosed L] (W : WeierstrassCurve L)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hΔ : W.Δ ≠ 0) {x : L}
    (hx : (W.preΨ p).eval x = 0) : (quotientByLine W p x).Δ ≠ 0 := by
  classical
  have hp : p.Prime := Fact.out
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩

  let q : L[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hqdeg : q.degree = 2 := by
    simp only [q]
    compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; decide)
  have hEq : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have : y ^ 2 + (W.a₁ * x + W.a₃) * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
      simpa [q, Polynomial.IsRoot] using hy
    linear_combination this
  have hNS : W.toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEq

  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpQ : p • (WeierstrassCurve.Affine.Point.some x y hNS) = 0 := by
    rw [WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hNS,
      ← WeierstrassCurve.preΨ_ofNat]
    exact hx
  have hord : addOrderOf (WeierstrassCurve.Affine.Point.some x y hNS) = p :=
    addOrderOf_eq_prime hpQ (WeierstrassCurve.Affine.Point.some_ne_zero hNS)

  rw [ModularCurve.LevelP.quotientByLine_eq_veluQuotient_oddOrderSummingSet W hodd hNS hord]
  refine WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
    W ((p - 1) / 2) _ ?_
  rw [hord]
  obtain ⟨m, hm⟩ := hodd
  omega

end ModularCurve.LevelP.DiscUnit

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine.ModularCurve _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine.ModularCurve.LevelP WeierstrassCurve in

theorem solution
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : IsUnit ((p : A) * W.Δ)) {x : A} (hx : (W.preΨ p).eval x = 0) :
    IsUnit (ModularCurve.LevelP.quotientByLine W p x).Δ := by
  classical
  refine ModularCurve.LevelP.DiscUnit.isUnit_of_forall_maximal _ fun M hM hmem => ?_

  haveI : M.IsMaximal := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  let L := AlgebraicClosure (A ⧸ M)
  let f : A →+* L := (algebraMap (A ⧸ M) L).comp (Ideal.Quotient.mk M)
  have hf0 : f (LevelP.quotientByLine W p x).Δ = 0 := by
    simp only [f, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]

  have hunit : IsUnit (f ((p : A) * W.Δ)) := hW.map f
  rw [map_mul, map_natCast] at hunit
  have hΔ : (W.map f).Δ ≠ 0 := by rw [WeierstrassCurve.map_Δ]; exact (IsUnit.mul_iff.mp hunit).2.ne_zero
  have hx' : ((W.map f).preΨ p).eval (f x) = 0 := by
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx, map_zero]

  have hmap : (LevelP.quotientByLine W p x).map f = LevelP.quotientByLine (W.map f) p (f x) :=
    LevelP.quotientByLine_map W p x f
      (fun a ha => ModularCurve.LevelP.DiscUnit.isUnit_ΨSq_of_mem_Icc W hp2 hW hx a ha)
  have key := ModularCurve.LevelP.DiscUnit.quotientByLine_Δ_ne_zero (W.map f) hp2 hΔ hx'
  rw [← hmap, WeierstrassCurve.map_Δ] at key
  exact key hf0

end S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine
end P2MW
export P2MW.S_ModularCurve_LevelP_isUnit_discriminant_quotientByLine (solution)
