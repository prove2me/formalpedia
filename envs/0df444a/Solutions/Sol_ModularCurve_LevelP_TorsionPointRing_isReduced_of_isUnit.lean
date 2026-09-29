-- Prove2me | solution 1 for ModularCurve.LevelP.TorsionPointRing.isReduced_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a8d31d0a-4c7e-56b6-9d3a-a415c2cf9f65

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_Affine_Point_two_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false

open Polynomial WeierstrassCurve

noncomputable section

namespace KTRing
namespace TorsionPointReduced

theorem isReduced_adjoinRoot_of_monic_of_separable {R : Type*} [CommRing R] [IsReduced R]
    (g : R[X]) (hg : g.Monic) (hsep : g.Separable) : IsReduced (AdjoinRoot g) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton (AdjoinRoot g) := Module.subsingleton R _
    exact ⟨fun x _ => Subsingleton.elim _ _⟩
  refine ⟨fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective (g := g) x

  have hrep : AdjoinRoot.mk g (f %ₘ g) = AdjoinRoot.mk g f := by
    have h := AdjoinRoot.mk_leftInverse hg (AdjoinRoot.mk g f)
    rwa [AdjoinRoot.modByMonicHom_mk] at h
  rw [← hrep]
  suffices h0 : f %ₘ g = 0 by rw [h0, map_zero]
  obtain ⟨n, hn⟩ := hx
  have hdiv : g ∣ (f %ₘ g) ^ n := by
    rw [← AdjoinRoot.mk_eq_zero, map_pow, hrep, hn]
  ext i
  rw [coeff_zero]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  haveI := hJ
  let K := FractionRing (R ⧸ J)
  let φ : R →+* K := (algebraMap (R ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hker : ∀ a : R, φ a = 0 → a ∈ J := by
    intro a ha
    have h1 : (Ideal.Quotient.mk J a : R ⧸ J) = 0 :=
      (IsFractionRing.injective (R ⧸ J) K) (by rw [map_zero]; exact ha)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have hdivK : g.map φ ∣ ((f %ₘ g).map φ) ^ n := by
    rw [← Polynomial.map_pow]; exact Polynomial.map_dvd φ hdiv
  have hdvd : g.map φ ∣ (f %ₘ g).map φ := (hsep.map).squarefree.isRadical n _ hdivK
  have hdeg : ((f %ₘ g).map φ).degree < (g.map φ).degree := by
    rw [hg.degree_map]
    exact (degree_map_le).trans_lt (degree_modByMonic_lt f hg)
  have hzero : (f %ₘ g).map φ = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  apply hker
  rw [← coeff_map, hzero, coeff_zero]

theorem isReduced_adjoinRoot_of_isUnit_leadingCoeff_of_separable {R : Type*} [CommRing R] [IsReduced R]
    (f : R[X]) (hu : IsUnit f.leadingCoeff) (hsep : f.Separable) : IsReduced (AdjoinRoot f) := by
  obtain ⟨u, hu⟩ := hu
  set g : R[X] := C (↑u⁻¹ : R) * f with hg
  have hgm : g.Monic := by
    rw [hg]; exact monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul])
  have hfg : f = C (↑u : R) * g := by
    rw [hg, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  have hgs : g.Separable := hsep.of_dvd ⟨C (↑u : R), by rw [hfg, mul_comm]⟩
  have hredg : IsReduced (AdjoinRoot g) := isReduced_adjoinRoot_of_monic_of_separable g hgm hgs
  have hspan : (Ideal.span {g} : Ideal R[X]) = Ideal.span {f} := by
    rw [hg]; exact Ideal.span_singleton_mul_left_unit (isUnit_C.mpr (Units.isUnit u⁻¹)) f
  haveI : IsReduced (R[X] ⧸ (Ideal.span {g} : Ideal R[X])) := hredg
  show IsReduced (R[X] ⧸ (Ideal.span {f} : Ideal R[X]))
  exact isReduced_of_injective (Ideal.quotEquivOfEq hspan.symm) (Ideal.quotEquivOfEq hspan.symm).injective

theorem isUnit_eval_Ψ₂Sq_of_eval_preΨ'_eq_zero {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {p : ℕ} (hp : Odd p) (hp1 : p ≠ 1) (hpR : IsUnit (p : R)) (hΔ : IsUnit W.Δ)
    (x : R) (hx : (W.preΨ' p).eval x = 0) : IsUnit (W.Ψ₂Sq.eval x) := by
  classical
  by_contra hnu
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  set φ : R →+* AlgebraicClosure (R ⧸ 𝔪) :=
    (algebraMap (R ⧸ 𝔪) (AlgebraicClosure (R ⧸ 𝔪))).comp (Ideal.Quotient.mk 𝔪) with hφ
  have hφm : φ (W.Ψ₂Sq.eval x) = 0 := by
    rw [hφ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  set W' : WeierstrassCurve (AlgebraicClosure (R ⧸ 𝔪)) := W.map φ with hW'
  have hΔ' : IsUnit W'.Δ := by rw [hW', map_Δ]; exact hΔ.map φ
  haveI : W'.IsElliptic := ⟨hΔ'⟩
  set x₀ : AlgebraicClosure (R ⧸ 𝔪) := φ x with hx₀
  have hx' : (W'.preΨ' p).eval x₀ = 0 := by
    rw [hW', map_preΨ', hx₀, eval_map, eval₂_at_apply, hx, map_zero]
  have hΨ₂' : W'.Ψ₂Sq.eval x₀ = 0 := by
    rw [hW', map_Ψ₂Sq, hx₀, eval_map, eval₂_at_apply, hφm]

  set q : (AlgebraicClosure (R ⧸ 𝔪))[X] := C 1 * X ^ 2 + C (W'.a₁ * x₀ + W'.a₃) * X + C (-(x₀ ^ 3 + W'.a₂ * x₀ ^ 2 + W'.a₄ * x₀ + W'.a₆)) with hq
  have hqdeg : q.degree = 2 := by rw [hq]; exact degree_quadratic one_ne_zero
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root q (by rw [hqdeg]; decide)
  have heq : W'.toAffine.Equation x₀ y₀ := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have h := hy₀
    simp only [hq, IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at h
    linear_combination h
  have hns : W'.toAffine.Nonsingular x₀ y₀ := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq

  have hpP : p • WeierstrassCurve.Affine.Point.some x₀ y₀ hns = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W' hp hns).mpr hx'
  have h2P : 2 • WeierstrassCurve.Affine.Point.some x₀ y₀ hns = 0 :=
    (WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff W' hns).mpr hΨ₂'
  obtain ⟨k, hk⟩ := hp
  have hP : WeierstrassCurve.Affine.Point.some x₀ y₀ hns = 0 := by
    have h := hpP
    rw [hk, add_smul, one_smul, mul_comm, ← smul_smul, h2P, nsmul_zero, zero_add] at h
    exact h
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns hP

open ModularCurve ModularCurve.LevelP

end KTRing.TorsionPointReduced

open KTRing.TorsionPointReduced ModularCurve ModularCurve.LevelP in
theorem solution {B : Type} [CommRing B] [IsDomain B] (W : WeierstrassCurve B) {p : ℕ}
    (hp : Odd p) (hp1 : p ≠ 1) (hu : IsUnit ((p : B) * W.Δ)) :
    IsReduced (ModularCurve.LevelP.TorsionPointRing W p) := by
  classical
  have hpU : IsUnit (p : B) := isUnit_of_mul_isUnit_left hu
  have hΔ : IsUnit W.Δ := isUnit_of_mul_isUnit_right hu
  have hp0 : (p : B) ≠ 0 := hpU.ne_zero

  have hlead : (W.preΨ (p : ℕ)).leadingCoeff = (p : B) := by
    rw [preΨ_ofNat, leadingCoeff, natDegree_preΨ' _ hp0, coeff_preΨ', if_neg (Nat.not_even_iff_odd.mpr hp)]
  have hsep : (W.preΨ (p : ℕ)).Separable := by rw [preΨ_ofNat]; exact W.separable_prePsi_of_isUnit hp hu
  haveI hR : IsReduced (PsiRoot W p) := by
    show IsReduced (AdjoinRoot (W.preΨ (p : ℕ)))
    exact isReduced_adjoinRoot_of_isUnit_leadingCoeff_of_separable _ (by rw [hlead]; exact hpU) hsep

  set o := PsiRoot.ofBase W p with ho
  set xb := psiRootX W p with hxb
  set t : PsiRoot W p := -(o W.a₁ * xb + o W.a₃) with ht
  set n : PsiRoot W p := -(xb ^ 3 + o W.a₂ * xb ^ 2 + o W.a₄ * xb + o W.a₆) with hn
  have hq : torsionQuadratic W p = X ^ 2 - C t * X + C n := by
    rw [torsionQuadratic, ht, hn, ← ho, ← hxb, C_neg, C_neg]; ring
  have hdisc : t ^ 2 - 4 * n = (W.map o).Ψ₂Sq.eval xb := by
    simp only [ht, hn, Ψ₂Sq, b₂, b₄, b₆, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eval_add, eval_mul, eval_C,
      eval_pow, eval_X]
    ring
  have hx : ((W.map o).preΨ' p).eval xb = 0 := by
    rw [← preΨ_ofNat, map_preΨ, eval_map, hxb, ho]
    exact preΨ_eval₂_psiRootX W p
  have hunit : IsUnit (t ^ 2 - 4 * n) := by
    rw [hdisc]
    refine isUnit_eval_Ψ₂Sq_of_eval_preΨ'_eq_zero (W.map o) hp hp1 ?_ ?_ xb hx
    · have h := hpU.map o; rwa [map_natCast] at h
    · rw [map_Δ]; exact hΔ.map o
  have hred := AdjoinRoot.isReduced_of_isReduced_of_isUnit_sq_sub_four_mul t n hunit
  show IsReduced (AdjoinRoot (torsionQuadratic W p))
  rw [hq]
  exact hred

end

end S_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit
end P2MW
export P2MW.S_ModularCurve_LevelP_TorsionPointRing_isReduced_of_isUnit (solution)
