-- Prove2me | solution 1 for ModularCurve.IsGamma1Point.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/35a7f1fb-f119-595a-a41c-544242292d5f

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

noncomputable section

open Polynomial WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsGamma1Point LevelP.PsiRoot LevelP.TorsionPointRing LevelP.TwoPointRing LevelP.BasisRing LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq"
namespace LevelP
p2m_export "ModularCurve.LevelP" "PsiRoot PsiRoot.ofBase psiRootX preΨ_eval₂_psiRootX torsionQuadratic TorsionPointRing TorsionPointRing.ofBase TorsionPointRing.algebraMap_eq torsionPtX torsionPtY torsionPtCurve equation_torsionPt preΨ_torsionPt TwoPointRing BasisRing TorsionPointRing.ringHom_ext TorsionPointRing.exists_ringHom_apply_torsionPt_eq"
namespace G1LiftEtale
p2m_open "ModularCurve.LevelP ModularCurve"

section StandardEtale

variable {A : Type*} [CommRing A]

def pairOfCoprime (f : A[X]) (hf : f.Monic) (hsep : IsCoprime f (derivative f)) :
    StandardEtalePair A where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := hsep
    exact ⟨b, a, 0, by rw [pow_zero]; linear_combination hab⟩

theorem pairOfCoprime_f (f : A[X]) (hf : f.Monic) (hsep : IsCoprime f (derivative f)) :
    (pairOfCoprime f hf hsep).f = f := rfl

theorem pairOfCoprime_g (f : A[X]) (hf : f.Monic) (hsep : IsCoprime f (derivative f)) :
    (pairOfCoprime f hf hsep).g = 1 := rfl

def pairRingEquiv (f : A[X]) (hf : f.Monic) (hsep : IsCoprime f (derivative f)) :
    (pairOfCoprime f hf hsep).Ring ≃ₐ[A] AdjoinRoot f := by
  set P := pairOfCoprime f hf hsep with hP
  have hroot : P.HasMap (AdjoinRoot.root f) := by
    refine ⟨?_, ?_⟩
    · rw [pairOfCoprime_f, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    · rw [pairOfCoprime_g, map_one]; exact isUnit_one
  have hX : eval₂ (↑(Algebra.ofId A P.Ring)) P.X f = 0 := by
    have h := (StandardEtalePair.hasMap_X (P := P)).1
    rwa [pairOfCoprime_f, aeval_def] at h
  refine AlgEquiv.ofAlgHom (P.lift (AdjoinRoot.root f) hroot)
    (AdjoinRoot.liftAlgHom f (Algebra.ofId A P.Ring) P.X hX) ?_ ?_
  · refine AdjoinRoot.algHom_ext ?_
    rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, StandardEtalePair.lift_X, AlgHom.id_apply]
  · refine StandardEtalePair.hom_ext ?_
    rw [AlgHom.comp_apply, StandardEtalePair.lift_X, AdjoinRoot.liftAlgHom_root, AlgHom.id_apply]

theorem etale_adjoinRoot_of_monic_of_isCoprime (f : A[X]) (hf : f.Monic)
    (hsep : IsCoprime f (derivative f)) : Algebra.Etale A (AdjoinRoot f) := by
  haveI : Algebra.IsStandardEtale A (AdjoinRoot f) :=
    Algebra.IsStandardEtale.of_equiv (pairRingEquiv f hf hsep)
  infer_instance

def adjoinRootEquivOfUnit (f : A[X]) {c : A} (hc : IsUnit c) :
    AdjoinRoot (C c * f) ≃ₐ[A] AdjoinRoot f :=
  Ideal.quotientEquivAlgOfEq A (Ideal.span_singleton_mul_left_unit (Polynomial.isUnit_C.mpr hc) f)

theorem etale_adjoinRoot_of_isCoprime {f : A[X]} {d : ℕ} (hdeg : f.natDegree ≤ d)
    (hlead : IsUnit (f.coeff d)) (hsep : IsCoprime f (derivative f)) :
    Algebra.Etale A (AdjoinRoot f) := by
  obtain ⟨c, hc⟩ := hlead

  set g : A[X] := C ((c⁻¹ : Aˣ) : A) * f with hg
  have hgmonic : g.Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one d ((natDegree_C_mul_le _ _).trans hdeg) ?_
    rw [hg, coeff_C_mul, ← hc, Units.inv_mul]
  have hCunit : IsUnit (C ((c⁻¹ : Aˣ) : A)) := Polynomial.isUnit_C.mpr (Units.isUnit _)
  have hgsep : IsCoprime g (derivative g) := by
    rw [hg, derivative_C_mul, isCoprime_mul_unit_left hCunit]
    exact hsep
  haveI : Algebra.IsStandardEtale A (AdjoinRoot g) :=
    Algebra.IsStandardEtale.of_equiv (pairRingEquiv g hgmonic hgsep)
  haveI : Algebra.IsStandardEtale A (AdjoinRoot f) :=
    Algebra.IsStandardEtale.of_equiv (adjoinRootEquivOfUnit f (Units.isUnit c⁻¹))
  infer_instance

end StandardEtale

section PsiRoot

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {n : ℕ}

theorem etale_adjoinRoot_preΨ (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    Algebra.Etale B (AdjoinRoot (W.preΨ n)) := by
  rw [WeierstrassCurve.preΨ_ofNat]
  have hn' : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  have hnu : IsUnit (n : B) := isUnit_of_mul_isUnit_left hu
  refine etale_adjoinRoot_of_isCoprime (d := (n ^ 2 - if Even n then 4 else 1) / 2)
    (W.natDegree_preΨ'_le n) ?_ ?_
  · rw [W.coeff_preΨ' n, if_neg hn']
    exact hnu
  · exact WeierstrassCurve.separable_prePsi_of_isUnit W hn hu

theorem etale_psiRoot (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    Algebra.Etale B (PsiRoot W n) :=
  etale_adjoinRoot_preΨ W hn hu

end PsiRoot

section TwoTorsion

theorem sq_eq_eval_Ψ₂Sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    eval_add, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination (4 : R) * h

theorem eval_Ψ₂Sq_ne_zero_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) {n : ℕ} (hn : Odd n) (hΔ : (n : K) * W.Δ ≠ 0) {x : K}
    (hx : (W.preΨ' n).eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by
  classical
  intro hΨ
  haveI : W.IsElliptic := (WeierstrassCurve.isElliptic_iff W).mpr
    (isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hΔ))

  set q : K[X] := C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
    with hq
  have hqdeg : q.degree ≠ 0 := by
    rw [hq, degree_quadratic (one_ne_zero' K)]; decide
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hqdeg
  have heq : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have hy' := hy
    simp only [hq, IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at hy'
    linear_combination hy'
  have hns : W.toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns with hP

  have hnP : n • P = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hn hns).mpr hx

  have hlin : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    have h2 := sq_eq_eval_Ψ₂Sq W heq
    rw [hΨ] at h2
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
  have hneg : W.toAffine.negY x y = y := by
    rw [WeierstrassCurve.Affine.negY]; linear_combination -hlin
  have hnegP : -P = P := by
    rw [hP, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
  have h2P : (2 : ℕ) • P = 0 := by
    rw [two_nsmul]
    nth_rw 1 [← hnegP]
    exact neg_add_cancel P

  obtain ⟨k, rfl⟩ := hn
  have hP0 : P = 0 := by
    have h := hnP
    rwa [add_nsmul, one_nsmul, mul_comm, mul_nsmul', h2P, nsmul_zero, zero_add] at h
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns hP0

theorem eval_Ψ₂Sq_ne_zero_of_field {K : Type*} [Field K] (W : WeierstrassCurve K) {n : ℕ}
    (hn : Odd n) (hΔ : (n : K) * W.Δ ≠ 0) {x : K} (hx : (W.preΨ' n).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  intro hΨ
  set L := AlgebraicClosure K
  set ι : K →+* L := algebraMap K L
  have hΔ' : (n : L) * (W.map ι).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, ← map_natCast ι, ← map_mul]
    exact (map_ne_zero ι).mpr hΔ
  have hx' : ((W.map ι).preΨ' n).eval (ι x) = 0 := by
    rw [WeierstrassCurve.map_preΨ', eval_map, eval₂_at_apply, hx, map_zero]
  refine eval_Ψ₂Sq_ne_zero_of_isAlgClosed (W.map ι) hn hΔ' hx' ?_
  rw [WeierstrassCurve.map_Ψ₂Sq, eval_map, eval₂_at_apply, hΨ, map_zero]

theorem isUnit_eval_Ψ₂Sq {A : Type*} [CommRing A] (W : WeierstrassCurve A) {n : ℕ} (hn : Odd n)
    (hu : IsUnit ((n : A) * W.Δ)) {x : A} (hx : (W.preΨ' n).eval x = 0) :
    IsUnit (W.Ψ₂Sq.eval x) := by
  by_contra hnu
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hnu)
  set π : A →+* A ⧸ 𝔪 := Ideal.Quotient.mk 𝔪
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hΔ : (n : A ⧸ 𝔪) * (W.map π).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ, ← map_natCast π, ← map_mul]
    exact (hu.map π).ne_zero
  have hx' : ((W.map π).preΨ' n).eval (π x) = 0 := by
    rw [WeierstrassCurve.map_preΨ', eval_map, eval₂_at_apply, hx, map_zero]
  refine eval_Ψ₂Sq_ne_zero_of_field (W.map π) hn hΔ hx' ?_
  rw [WeierstrassCurve.map_Ψ₂Sq, eval_map, eval₂_at_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

end TwoTorsion

section Quadratic

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {n : ℕ}

theorem eval_preΨ'_psiRootX :
    ((W.map (PsiRoot.ofBase W n)).preΨ' n).eval (psiRootX W n) = 0 := by
  have h := preΨ_eval₂_psiRootX W n
  rwa [WeierstrassCurve.preΨ_ofNat, ← eval_map, ← WeierstrassCurve.map_preΨ'] at h

theorem torsionQuadratic_eq :
    torsionQuadratic W n = X ^ 2 +
      (C (PsiRoot.ofBase W n W.a₁ * psiRootX W n + PsiRoot.ofBase W n W.a₃) * X -
        C (psiRootX W n ^ 3 + PsiRoot.ofBase W n W.a₂ * psiRootX W n ^ 2 +
          PsiRoot.ofBase W n W.a₄ * psiRootX W n + PsiRoot.ofBase W n W.a₆)) := by
  rw [torsionQuadratic]; ring

theorem monic_torsionQuadratic : (torsionQuadratic W n).Monic := by
  rw [torsionQuadratic_eq]
  refine monic_X_pow_add ((degree_sub_le _ _).trans_lt (max_lt ?_ ?_))
  · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast one_lt_two)
  · exact (degree_C_le).trans_lt (by exact_mod_cast zero_lt_two)

theorem derivative_torsionQuadratic :
    derivative (torsionQuadratic W n) =
      2 * X + C (PsiRoot.ofBase W n W.a₁ * psiRootX W n + PsiRoot.ofBase W n W.a₃) := by
  rw [torsionQuadratic]
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, sub_zero, Nat.cast_ofNat, pow_one,
    Nat.add_one_sub_one, map_ofNat]

theorem discr_torsionQuadratic_eq :
    (PsiRoot.ofBase W n W.a₁ * psiRootX W n + PsiRoot.ofBase W n W.a₃) ^ 2 +
        4 * (psiRootX W n ^ 3 + PsiRoot.ofBase W n W.a₂ * psiRootX W n ^ 2 +
          PsiRoot.ofBase W n W.a₄ * psiRootX W n + PsiRoot.ofBase W n W.a₆) =
      ((W.map (PsiRoot.ofBase W n)).Ψ₂Sq).eval (psiRootX W n) := by
  simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem isCoprime_torsionQuadratic (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    IsCoprime (torsionQuadratic W n) (derivative (torsionQuadratic W n)) := by
  set b : PsiRoot W n := PsiRoot.ofBase W n W.a₁ * psiRootX W n + PsiRoot.ofBase W n W.a₃ with hb
  set c : PsiRoot W n := psiRootX W n ^ 3 + PsiRoot.ofBase W n W.a₂ * psiRootX W n ^ 2 +
    PsiRoot.ofBase W n W.a₄ * psiRootX W n + PsiRoot.ofBase W n W.a₆ with hc
  have hu' : IsUnit ((n : PsiRoot W n) * (W.map (PsiRoot.ofBase W n)).Δ) := by
    rw [WeierstrassCurve.map_Δ, ← map_natCast (PsiRoot.ofBase W n), ← map_mul]
    exact hu.map _
  have hd : IsUnit (b ^ 2 + 4 * c) := by
    rw [hb, hc, discr_torsionQuadratic_eq]
    exact isUnit_eval_Ψ₂Sq _ hn hu' (eval_preΨ'_psiRootX W)
  obtain ⟨v, hv⟩ := hd
  have hv1 : C ((v⁻¹ : (PsiRoot W n)ˣ) : PsiRoot W n) * (C b ^ 2 + 4 * C c) = (1 : (PsiRoot W n)[X]) := by
    rw [← map_pow, ← C_ofNat, ← map_mul, ← map_add, ← map_mul, ← hv, Units.inv_mul, map_one]
  refine ⟨C ((v⁻¹ : (PsiRoot W n)ˣ) : PsiRoot W n) * (-4),
    C ((v⁻¹ : (PsiRoot W n)ˣ) : PsiRoot W n) * (2 * X + C b), ?_⟩
  rw [derivative_torsionQuadratic, torsionQuadratic_eq, ← hb, ← hc]
  linear_combination hv1

theorem etale_torsionPointRing_psiRoot (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    Algebra.Etale (PsiRoot W n) (TorsionPointRing W n) :=
  etale_adjoinRoot_of_monic_of_isCoprime (torsionQuadratic W n) (monic_torsionQuadratic W)
    (isCoprime_torsionQuadratic W hn hu)

end Quadratic

section Assembly

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {n : ℕ}

theorem etale_torsionPointRing (hn : Odd n) (hu : IsUnit ((n : B) * W.Δ)) :
    Algebra.Etale B (TorsionPointRing W n) := by
  haveI := etale_psiRoot W hn hu
  haveI := etale_torsionPointRing_psiRoot W hn hu
  exact Algebra.Etale.comp B (PsiRoot W n) (TorsionPointRing W n)

end Assembly

end ModularCurve.LevelP.G1LiftEtale

end

p2m_open "ModularCurve P2MW.S_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.ModularCurve ModularCurve.LevelP P2MW.S_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot.ModularCurve.LevelP"

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓ : IsUnit ((ℓ : ℕ) : T))
    (D' : ModularCurve.LevelPData T') (hD' : ModularCurve.IsGamma1Point (W.map π) ℓ D') :
    ∃! D : ModularCurve.LevelPData T, D.map π = D' ∧ ModularCurve.IsGamma1Point W ℓ D := by
  classical
  have hodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  haveI : Algebra.Etale T (TorsionPointRing W ℓ) :=
    ModularCurve.LevelP.G1LiftEtale.etale_torsionPointRing W hodd (hℓ.mul hΔ)
  letI : Algebra T T' := π.toAlgebra
  have hker : IsNilpotent (RingHom.ker ((Algebra.ofId T T' : T →ₐ[T] T') : T →+* T')) := by
    obtain ⟨n, hn⟩ := hnil
    exact ⟨n, by simp [Ideal.zero_eq_bot] at hn ⊢; exact hn⟩
  have hsurj : Function.Surjective (Algebra.ofId T T') := hπ

  obtain ⟨ψ', hψ'b, hψ'x, hψ'y⟩ := ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq W ℓ π D'.xP D'.yP
    hD'.equation_P hD'.preΨ_P
  let ψ'ₐ : TorsionPointRing W ℓ →ₐ[T] T' :=
    { toRingHom := ψ'
      commutes' := fun t ↦ by
        change ψ' (algebraMap T (TorsionPointRing W ℓ) t) = π t
        rw [TorsionPointRing.algebraMap_eq, ← RingHom.comp_apply, hψ'b] }

  let ψ : TorsionPointRing W ℓ →ₐ[T] T := Algebra.FormallySmooth.liftOfSurjective ψ'ₐ (Algebra.ofId T T') hsurj hker
  have hψ : (Algebra.ofId T T').comp ψ = ψ'ₐ := Algebra.FormallySmooth.comp_liftOfSurjective _ _ hsurj hker
  have hψπ : π.comp (ψ : TorsionPointRing W ℓ →+* T) = ψ' := by
    ext b; exact AlgHom.congr_fun hψ b

  have hlev : ∀ (χ : TorsionPointRing W ℓ →ₐ[T] T),
      IsGamma1Point W ℓ ⟨χ (torsionPtX W ℓ), χ (torsionPtY W ℓ), χ (torsionPtX W ℓ), χ (torsionPtY W ℓ)⟩ := by
    intro χ
    have hc : (torsionPtCurve W ℓ).map (χ : TorsionPointRing W ℓ →+* T) = W := by
      rw [torsionPtCurve, WeierstrassCurve.map_map]
      have : (χ : TorsionPointRing W ℓ →+* T).comp (TorsionPointRing.ofBase W ℓ) = RingHom.id T := by
        ext t; change χ (algebraMap T (TorsionPointRing W ℓ) t) = t
        exact χ.commutes t
      rw [this, WeierstrassCurve.map_id]
    refine ⟨?_, ?_, rfl, rfl⟩
    · have h := (equation_torsionPt W ℓ).map (χ : TorsionPointRing W ℓ →+* T)
      change ((torsionPtCurve W ℓ).map (χ : TorsionPointRing W ℓ →+* T)).toAffine.Equation _ _ at h
      rw [hc] at h
      exact h
    · have h := preΨ_torsionPt W ℓ
      have := congrArg (χ : TorsionPointRing W ℓ →+* T) h
      rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← WeierstrassCurve.map_preΨ, hc] at this
      exact this
  refine ⟨⟨ψ (torsionPtX W ℓ), ψ (torsionPtY W ℓ), ψ (torsionPtX W ℓ), ψ (torsionPtY W ℓ)⟩, ⟨?_, hlev ψ⟩, ?_⟩
  · have ex : π (ψ (torsionPtX W ℓ)) = D'.xP := by rw [← hψ'x, ← hψπ]; rfl
    have ey : π (ψ (torsionPtY W ℓ)) = D'.yP := by rw [← hψ'y, ← hψπ]; rfl
    ext
    · exact ex
    · exact ey
    · rw [hD'.xQ_eq]; exact ex
    · rw [hD'.yQ_eq]; exact ey
  ·
    rintro D ⟨hDπ, hD⟩
    have hD0 : (W.map (RingHom.id T)).toAffine.Equation D.xP D.yP := by rw [WeierstrassCurve.map_id]; exact hD.equation_P
    have hD1 : ((W.map (RingHom.id T)).preΨ ℓ).eval D.xP = 0 := by rw [WeierstrassCurve.map_id]; exact hD.preΨ_P
    obtain ⟨χ, hχb, hχx, hχy⟩ := ModularCurve.LevelP.TorsionPointRing.exists_ringHom_apply_torsionPt_eq W ℓ (RingHom.id T)
      D.xP D.yP hD0 hD1
    let χₐ : TorsionPointRing W ℓ →ₐ[T] T :=
      { toRingHom := χ
        commutes' := fun t ↦ by
          change χ (algebraMap T (TorsionPointRing W ℓ) t) = t
          rw [TorsionPointRing.algebraMap_eq, ← RingHom.comp_apply, hχb]; rfl }
    have heq : χₐ = ψ := by
      apply Algebra.FormallyUnramified.lift_unique_of_ringHom π ?_ χₐ ψ
      · change π.comp χ = π.comp (ψ : TorsionPointRing W ℓ →+* T)
        rw [hψπ]
        apply TorsionPointRing.ringHom_ext
        · rw [RingHom.comp_assoc, hχb, hψ'b]; rfl
        · rw [RingHom.comp_apply, hχx, hψ'x, ← hDπ]; rfl
        · rw [RingHom.comp_apply, hχy, hψ'y, ← hDπ]; rfl
      · obtain ⟨n, hn⟩ := hnil
        exact ⟨n, by simpa [Ideal.zero_eq_bot] using hn⟩
    have eχ : ∀ z, χ z = ψ z := fun z => by rw [← heq]; rfl
    ext
    · rw [← hχx, eχ]
    · rw [← hχy, eχ]
    · rw [hD.xQ_eq, ← hχx, eχ]
    · rw [hD.yQ_eq, ← hχy, eχ]

end S_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot (solution)
