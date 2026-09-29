-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.eq_zero_of_forall_toFun_genericCurve_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b1e78509-a2e6-5351-bad6-3728ce2913cc

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_Generic
import Theorems.Thm_WeierstrassCurve_separable_prePsi_of_isUnit
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "indepElt indepElt_map LevelPData LevelPData.map_xP LevelPData.map_xQ LevelPData.map_map IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext KatzLevelPForm.zero_toFun LevelPData.mk LevelPData.mk.injEq"
namespace KatzLevelPForm
p2m_export "ModularCurve.KatzLevelPForm" "ext zero_toFun mul mk.injEq mk toFun map_toFun"
namespace GenericFibreProof
p2m_open "ModularCurve.KatzLevelPForm ModularCurve"

p2m_open "WeierstrassCurve ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve"

section quad

variable {A B : Type*} [CommRing A] [CommRing B]

noncomputable def quad (W : WeierstrassCurve A) (x : A) : A[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

theorem eval_quad (W : WeierstrassCurve A) (x y : A) :
    (quad W x).eval y =
      y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [quad, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  ring

theorem eval_quad_eq_zero_iff (W : WeierstrassCurve A) (x y : A) :
    (quad W x).eval y = 0 ↔ W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff, eval_quad, sub_eq_zero]

theorem quad_eq (W : WeierstrassCurve A) (x : A) :
    quad W x = X ^ 2 + (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
  rw [quad]; ring

theorem degree_quad_tail_lt (W : WeierstrassCurve A) (x : A) :
    (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).degree < 2 := by
  refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast Nat.lt_succ_self 1)
  · exact degree_C_le.trans_lt (by exact_mod_cast Nat.zero_lt_two)

theorem monic_quad (W : WeierstrassCurve A) (x : A) : (quad W x).Monic := by
  rw [quad_eq]
  exact monic_X_pow_add (by exact_mod_cast degree_quad_tail_lt W x)

theorem natDegree_quad [Nontrivial A] (W : WeierstrassCurve A) (x : A) :
    (quad W x).natDegree = 2 := by
  rw [quad_eq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_quad_tail_lt W x

theorem coeff_quad_one (W : WeierstrassCurve A) (x : A) : (quad W x).coeff 1 = W.a₁ * x + W.a₃ := by
  simp only [quad, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C_succ]
  norm_num

theorem quad_map (f : A →+* B) (W : WeierstrassCurve A) (x : A) :
    (quad W x).map f = quad (W.map f) (f x) := by
  simp [quad, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end quad

section Universal

variable (K : Type u) [Field K] (p : ℕ)

noncomputable def ψm : (MvPolynomial (Fin 5) K)[X] :=
  C (MvPolynomial.C ((p : K)⁻¹)) * (Generic.poly K).preΨ' p

abbrev R₁ : Type u := AdjoinRoot (ψm K p)

noncomputable def x₁ : R₁ K p := AdjoinRoot.root (ψm K p)

noncomputable def q₁ : (R₁ K p)[X] :=
  quad ((Generic.poly K).map (algebraMap (MvPolynomial (Fin 5) K) (R₁ K p))) (x₁ K p)

abbrev S : Type u := AdjoinRoot (q₁ K p)

noncomputable def xS : S K p := AdjoinRoot.of (q₁ K p) (x₁ K p)

noncomputable def yS : S K p := AdjoinRoot.root (q₁ K p)

abbrev T : Type u := TensorProduct (MvPolynomial (Fin 5) K) (S K p) (S K p)

example : Algebra (MvPolynomial (Fin 5) K) (T K p) := inferInstance
example : Algebra K (T K p) := inferInstance
example : IsScalarTower K (MvPolynomial (Fin 5) K) (T K p) := inferInstance
example : IsScalarTower K (MvPolynomial (Fin 5) K) (S K p) := inferInstance
example : IsScalarTower (MvPolynomial (Fin 5) K) (R₁ K p) (S K p) := inferInstance

noncomputable def WT : WeierstrassCurve (T K p) :=
  (Generic.poly K).map (algebraMap (MvPolynomial (Fin 5) K) (T K p))

noncomputable def DT : LevelPData (T K p) :=
  ⟨(xS K p) ⊗ₜ 1, (yS K p) ⊗ₜ 1, 1 ⊗ₜ (xS K p), 1 ⊗ₜ (yS K p)⟩

noncomputable def sT : T K p :=
  (WT K p).Δ * indepElt (WT K p) p (DT K p).xP (DT K p).xQ * indepElt (WT K p) p (DT K p).xQ (DT K p).xP

abbrev U : Type u := Localization.Away (sT K p)

example : Algebra (MvPolynomial (Fin 5) K) (U K p) := inferInstance
example : Algebra K (U K p) := inferInstance
example : IsScalarTower K (MvPolynomial (Fin 5) K) (U K p) := inferInstance
example : IsScalarTower (MvPolynomial (Fin 5) K) (T K p) (U K p) := inferInstance
example : IsScalarTower K (T K p) (U K p) := inferInstance

noncomputable def WU : WeierstrassCurve (U K p) :=
  (Generic.poly K).map (algebraMap (MvPolynomial (Fin 5) K) (U K p))

noncomputable def DU : LevelPData (U K p) :=
  (DT K p).map (algebraMap (T K p) (U K p))

end Universal

section Facts

variable {K : Type u} [Field K] {p : ℕ}

local notation "P5" => MvPolynomial (Fin 5) K

theorem algebraMap_R₁ : algebraMap P5 (R₁ K p) = AdjoinRoot.of (ψm K p) := rfl

theorem isUnit_C_inv (hp : (p : K) ≠ 0) : IsUnit (MvPolynomial.C (σ := Fin 5) ((p : K)⁻¹)) :=
  (IsUnit.mk0 _ (inv_ne_zero hp)).map MvPolynomial.C

theorem ψm_eq : ψm K p = C (MvPolynomial.C ((p : K)⁻¹)) * (Generic.poly K).preΨ' p := rfl

theorem natCast_P_ne_zero (hp : (p : K) ≠ 0) : (p : P5) ≠ 0 := by
  rw [← map_natCast (MvPolynomial.C (σ := Fin 5) (R := K)) p]
  exact (MvPolynomial.C_injective _ _).ne_iff' (map_zero _) |>.mpr hp

theorem monic_ψm (hp : (p : K) ≠ 0) (hp2 : ¬ Even p) : (ψm K p).Monic := by
  rw [Monic, ψm_eq, leadingCoeff_mul', leadingCoeff_C,
    WeierstrassCurve.leadingCoeff_preΨ' _ (natCast_P_ne_zero hp), if_neg hp2]
  · rw [← map_natCast (MvPolynomial.C (σ := Fin 5) (R := K)) p, ← map_mul, inv_mul_cancel₀ hp,
      map_one]
  · rw [leadingCoeff_C, WeierstrassCurve.leadingCoeff_preΨ' _ (natCast_P_ne_zero hp), if_neg hp2,
      ← map_natCast (MvPolynomial.C (σ := Fin 5) (R := K)) p, ← map_mul, inv_mul_cancel₀ hp,
      map_one]
    exact one_ne_zero

theorem natDegree_ψm (hp : (p : K) ≠ 0) (hp2 : ¬ Even p) :
    (ψm K p).natDegree = (p ^ 2 - 1) / 2 := by
  rw [ψm_eq, natDegree_C_mul_of_isUnit (isUnit_C_inv hp),
    WeierstrassCurve.natDegree_preΨ' _ (natCast_P_ne_zero hp), if_neg hp2]

theorem eval_preΨ'_x₁ (hp : (p : K) ≠ 0) :
    (((Generic.poly K).map (algebraMap P5 (R₁ K p))).preΨ' p).eval (x₁ K p) = 0 := by
  have h := AdjoinRoot.eval₂_root (ψm K p)
  rw [ψm_eq, eval₂_mul, eval₂_C, ((isUnit_C_inv hp).map _).mul_right_eq_zero] at h
  rwa [WeierstrassCurve.map_preΨ', eval_map, algebraMap_R₁]

theorem q₁_map_of :
    (q₁ K p).map (AdjoinRoot.of (q₁ K p)) =
      quad ((Generic.poly K).map (algebraMap P5 (S K p))) (xS K p) := by
  unfold q₁
  rw [quad_map, WeierstrassCurve.map_map]
  rfl

theorem equation_S :
    ((Generic.poly K).map (algebraMap P5 (S K p))).toAffine.Equation (xS K p) (yS K p) := by
  rw [← eval_quad_eq_zero_iff, ← q₁_map_of, eval_map]
  exact AdjoinRoot.eval₂_root (q₁ K p)

theorem eval_preΨ'_xS (hp : (p : K) ≠ 0) :
    (((Generic.poly K).map (algebraMap P5 (S K p))).preΨ' p).eval (xS K p) = 0 := by
  have h := congr_arg (AdjoinRoot.of (q₁ K p)) (eval_preΨ'_x₁ (K := K) (p := p) hp)
  rw [map_zero, ← Polynomial.eval₂_at_apply, ← eval_map, ← WeierstrassCurve.map_preΨ',
    WeierstrassCurve.map_map] at h
  exact h

theorem WT_eq_map_includeLeft :
    WT K p = ((Generic.poly K).map (algebraMap P5 (S K p))).map
      (Algebra.TensorProduct.includeLeft (S := P5) : S K p →ₐ[P5] T K p) := by
  rw [WT, WeierstrassCurve.map_map, AlgHom.comp_algebraMap]

theorem WT_eq_map_includeRight :
    WT K p = ((Generic.poly K).map (algebraMap P5 (S K p))).map
      (Algebra.TensorProduct.includeRight : S K p →ₐ[P5] T K p) := by
  rw [WT, WeierstrassCurve.map_map, AlgHom.comp_algebraMap]

theorem equation_T_P : (WT K p).toAffine.Equation (DT K p).xP (DT K p).yP := by
  have h := (equation_S (K := K) (p := p)).map
    ((Algebra.TensorProduct.includeLeft (S := P5) : S K p →ₐ[P5] T K p) : S K p →+* T K p)
  rw [WT_eq_map_includeLeft]
  exact h

theorem equation_T_Q : (WT K p).toAffine.Equation (DT K p).xQ (DT K p).yQ := by
  have h := (equation_S (K := K) (p := p)).map
    ((Algebra.TensorProduct.includeRight : S K p →ₐ[P5] T K p) : S K p →+* T K p)
  rw [WT_eq_map_includeRight]
  exact h

theorem DT_xP : (DT K p).xP =
    ((Algebra.TensorProduct.includeLeft (S := P5) : S K p →ₐ[P5] T K p) : S K p →+* T K p)
      (xS K p) := rfl

theorem DT_xQ : (DT K p).xQ =
    ((Algebra.TensorProduct.includeRight : S K p →ₐ[P5] T K p) : S K p →+* T K p) (xS K p) := rfl

theorem eval_preΨ'_T_P (hp : (p : K) ≠ 0) : ((WT K p).preΨ' p).eval (DT K p).xP = 0 := by
  rw [WT_eq_map_includeLeft, WeierstrassCurve.map_preΨ', eval_map, DT_xP, eval₂_at_apply,
    eval_preΨ'_xS hp, map_zero]

theorem eval_preΨ'_T_Q (hp : (p : K) ≠ 0) : ((WT K p).preΨ' p).eval (DT K p).xQ = 0 := by
  rw [WT_eq_map_includeRight, WeierstrassCurve.map_preΨ', eval_map, DT_xQ, eval₂_at_apply,
    eval_preΨ'_xS hp, map_zero]

theorem WU_eq : WU K p = (WT K p).map (algebraMap (T K p) (U K p)) := by
  rw [WU, WT, WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

theorem isUnit_algebraMap_sT : IsUnit (algebraMap (T K p) (U K p) (sT K p)) :=
  IsLocalization.Away.algebraMap_isUnit (sT K p)

theorem sT_eq : sT K p = (WT K p).Δ * indepElt (WT K p) p (DT K p).xP (DT K p).xQ *
    indepElt (WT K p) p (DT K p).xQ (DT K p).xP := rfl

theorem isUnit_algebraMap_factors :
    IsUnit (algebraMap (T K p) (U K p) (WT K p).Δ *
      algebraMap (T K p) (U K p) (indepElt (WT K p) p (DT K p).xP (DT K p).xQ) *
      algebraMap (T K p) (U K p) (indepElt (WT K p) p (DT K p).xQ (DT K p).xP)) := by
  have h := isUnit_algebraMap_sT (K := K) (p := p)
  have e := congr_arg (algebraMap (T K p) (U K p)) (sT_eq (K := K) (p := p))
  simp only [map_mul] at e
  exact e ▸ h

theorem isUnit_Δ_WU : IsUnit (WU K p).Δ := by
  have h := isUnit_algebraMap_factors (K := K) (p := p)
  rw [WU_eq, WeierstrassCurve.map_Δ]
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h)

theorem isLevelPStructure_DU (hp : (p : K) ≠ 0) : IsLevelPStructure (WU K p) p (DU K p) := by
  have hs := isUnit_algebraMap_factors (K := K) (p := p)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WU_eq]; exact (equation_T_P (K := K) (p := p)).map _
  · rw [WU_eq]; exact (equation_T_Q (K := K) (p := p)).map _
  · rw [WU_eq, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.map_preΨ', DU, LevelPData.map_xP,
      eval_map, Polynomial.eval₂_at_apply, eval_preΨ'_T_P hp, map_zero]
  · rw [WU_eq, WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.map_preΨ', DU, LevelPData.map_xQ,
      eval_map, Polynomial.eval₂_at_apply, eval_preΨ'_T_Q hp, map_zero]
  · rw [WU_eq, DU, LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs)
  · rw [WU_eq, DU, LevelPData.map_xP, LevelPData.map_xQ, indepElt_map]
    exact isUnit_of_mul_isUnit_right hs

end Facts

section Classify

variable {K : Type u} [Field K] {p : ℕ}
variable {A : Type u} [CommRing A] [Algebra (MvPolynomial (Fin 5) K) A]

local notation "P5" => MvPolynomial (Fin 5) K

noncomputable def WA (K : Type u) [Field K] (A : Type u) [CommRing A]
    [Algebra (MvPolynomial (Fin 5) K) A] : WeierstrassCurve A :=
  (Generic.poly K).map (algebraMap (MvPolynomial (Fin 5) K) A)

theorem eval₂_ψm_eq_zero {B : Type*} [CommRing B] (f : P5 →+* B) (x : B)
    (hx : (((Generic.poly K).map f).preΨ' p).eval x = 0) : (ψm K p).eval₂ f x = 0 := by
  rw [eval₂_eq_eval_map, ψm_eq, Polynomial.map_mul, map_C, eval_mul, eval_C,
    ← WeierstrassCurve.map_preΨ', hx, mul_zero]

noncomputable def lift₁ (x : A) (hx : ((WA K A).preΨ' p).eval x = 0) :
    R₁ K p →ₐ[P5] A :=
  AdjoinRoot.liftAlgHom (ψm K p) (Algebra.ofId P5 A) x (eval₂_ψm_eq_zero _ x hx)

@[scoped simp] theorem lift₁_x₁ (x : A) (hx : ((WA K A).preΨ' p).eval x = 0) :
    lift₁ x hx (x₁ K p) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem map_lift₁ (x : A) (hx : ((WA K A).preΨ' p).eval x = 0) :
    ((Generic.poly K).map (algebraMap P5 (R₁ K p))).map (lift₁ x hx : R₁ K p →+* A) = WA K A := by
  rw [WeierstrassCurve.map_map, AlgHom.comp_algebraMap]; rfl

noncomputable def liftS (x y : A) (hx : ((WA K A).preΨ' p).eval x = 0)
    (hxy : (WA K A).toAffine.Equation x y) : S K p →ₐ[P5] A :=
  AdjoinRoot.liftAlgHom (q₁ K p) (lift₁ x hx) y (by
    rw [eval₂_eq_eval_map]
    unfold q₁
    rw [quad_map, map_lift₁, AlgHom.coe_toRingHom, lift₁_x₁, eval_quad_eq_zero_iff]
    exact hxy)

@[scoped simp] theorem liftS_xS (x y : A) (hx : ((WA K A).preΨ' p).eval x = 0)
    (hxy : (WA K A).toAffine.Equation x y) : liftS x y hx hxy (xS K p) = x := by
  rw [xS, liftS, AdjoinRoot.liftAlgHom_of, lift₁_x₁]

@[scoped simp] theorem liftS_yS (x y : A) (hx : ((WA K A).preΨ' p).eval x = 0)
    (hxy : (WA K A).toAffine.Equation x y) : liftS x y hx hxy (yS K p) = y :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

structure PtPair (K : Type u) [Field K] (p : ℕ) (A : Type u) [CommRing A]
    [Algebra (MvPolynomial (Fin 5) K) A] where
  D : LevelPData A
  eqP : (WA K A).toAffine.Equation D.xP D.yP
  eqQ : (WA K A).toAffine.Equation D.xQ D.yQ
  ψP : ((WA K A).preΨ' p).eval D.xP = 0
  ψQ : ((WA K A).preΨ' p).eval D.xQ = 0

noncomputable def liftT (a : PtPair K p A) : T K p →ₐ[P5] A :=
  Algebra.TensorProduct.productMap (liftS a.D.xP a.D.yP a.ψP a.eqP)
    (liftS a.D.xQ a.D.yQ a.ψQ a.eqQ)

@[scoped simp] theorem liftT_xP (a : PtPair K p A) : liftT a (DT K p).xP = a.D.xP := by
  simp [liftT, DT, Algebra.TensorProduct.productMap_apply_tmul]

@[scoped simp] theorem liftT_yP (a : PtPair K p A) : liftT a (DT K p).yP = a.D.yP := by
  simp [liftT, DT, Algebra.TensorProduct.productMap_apply_tmul]

@[scoped simp] theorem liftT_xQ (a : PtPair K p A) : liftT a (DT K p).xQ = a.D.xQ := by
  simp [liftT, DT, Algebra.TensorProduct.productMap_apply_tmul]

@[scoped simp] theorem liftT_yQ (a : PtPair K p A) : liftT a (DT K p).yQ = a.D.yQ := by
  simp [liftT, DT, Algebra.TensorProduct.productMap_apply_tmul]

theorem WT_map_liftT (a : PtPair K p A) :
    (WT K p).map (liftT a : T K p →+* A) = WA K A := by
  rw [WT, WeierstrassCurve.map_map, AlgHom.comp_algebraMap]; rfl

theorem DT_map_liftT (a : PtPair K p A) :
    (DT K p).map (liftT a : T K p →+* A) = a.D := by
  ext <;> simp

theorem liftT_sT (a : PtPair K p A) :
    liftT a (sT K p) =
      (WA K A).Δ * indepElt (WA K A) p a.D.xP a.D.xQ * indepElt (WA K A) p a.D.xQ a.D.xP := by
  rw [sT, map_mul, map_mul, ← AlgHom.coe_toRingHom, ← WeierstrassCurve.map_Δ, ← liftT_xP a,
    ← liftT_xQ a, ← AlgHom.coe_toRingHom, ← indepElt_map, ← indepElt_map, WT_map_liftT]

noncomputable def liftU (a : PtPair K p A)
    (hs : IsUnit ((WA K A).Δ * indepElt (WA K A) p a.D.xP a.D.xQ * indepElt (WA K A) p a.D.xQ a.D.xP)) :
    U K p →ₐ[P5] A :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (sT K p)) (f := liftT a) (by
    rintro ⟨y, n, rfl⟩
    rw [map_pow, liftT_sT]
    exact hs.pow n)

theorem liftU_algebraMap (a : PtPair K p A) (hs) (t : T K p) :
    liftU a hs (algebraMap (T K p) (U K p) t) = liftT a t := by
  rw [liftU, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem WU_map_liftU (a : PtPair K p A) (hs) :
    (WU K p).map (liftU a hs : U K p →+* A) = WA K A := by
  rw [WU, WeierstrassCurve.map_map, AlgHom.comp_algebraMap]; rfl

theorem DU_map_liftU (a : PtPair K p A) (hs) :
    (DU K p).map (liftU a hs : U K p →+* A) = a.D := by
  rw [DU, LevelPData.map_map]
  have e : (liftU a hs : U K p →+* A).comp (algebraMap (T K p) (U K p)) =
      (liftT a : T K p →+* A) := RingHom.ext (liftU_algebraMap a hs)
  rw [e]
  exact DT_map_liftT a

def PtPair.ofLevel (D : LevelPData A) (hD : IsLevelPStructure (WA K A) p D) : PtPair K p A where
  D := D
  eqP := hD.equation_P
  eqQ := hD.equation_Q
  ψP := by rw [← WeierstrassCurve.preΨ_ofNat]; exact hD.preΨ_P
  ψQ := by rw [← WeierstrassCurve.preΨ_ofNat]; exact hD.preΨ_Q

theorem isUnit_of_isLevelPStructure {D : LevelPData A} (hD : IsLevelPStructure (WA K A) p D)
    (hΔ : IsUnit (WA K A).Δ) :
    IsUnit ((WA K A).Δ * indepElt (WA K A) p D.xP D.xQ * indepElt (WA K A) p D.xQ D.xP) :=
  (hΔ.mul hD.isUnit_indepElt_PQ).mul hD.isUnit_indepElt_QP

end Classify

section Reduce

variable {K : Type u} [Field K] {p : ℕ} {k : ℤ}

theorem toFun_congr {R : Type u} [CommRing R] (F : KatzLevelPForm R p k) {A : Type u} [CommRing A]
    [Algebra R A] {W W' : WeierstrassCurve A} (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ)
    {D D' : LevelPData A} (hD : IsLevelPStructure W p D) (hD' : IsLevelPStructure W' p D')
    (e : W = W') (e' : D = D') : F.toFun W hW D hD = F.toFun W' hW' D' hD' := by
  subst e e'
  rfl

theorem exists_toFun_eq (hp : (p : K) ≠ 0) (G : KatzLevelPForm K p k) {A : Type u} [CommRing A]
    [Algebra K A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (D : LevelPData A)
    (hD : IsLevelPStructure W p D) :
    ∃ f : U K p →ₐ[K] A, G.toFun W hW D hD =
      f (G.toFun (WU K p) isUnit_Δ_WU (DU K p) (isLevelPStructure_DU hp)) := by
  letI : Algebra (MvPolynomial (Fin 5) K) A := (Generic.classify K W).toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin 5) K) A :=
    IsScalarTower.of_algebraMap_eq fun c => ((Generic.classify K W).commutes c).symm
  have hWA : WA K A = W := Generic.poly_map_classify W
  have hD' : IsLevelPStructure (WA K A) p D := hWA ▸ hD
  have hΔ' : IsUnit (WA K A).Δ := hWA ▸ hW
  let a : PtPair K p A := PtPair.ofLevel D hD'
  let f : U K p →ₐ[MvPolynomial (Fin 5) K] A := liftU a (isUnit_of_isLevelPStructure hD' hΔ')
  refine ⟨f.restrictScalars K, ?_⟩
  have h1 := G.map_toFun (f.restrictScalars K) (WU K p) isUnit_Δ_WU
    (KatzModularForm.isUnit_Δ_map _ isUnit_Δ_WU) (DU K p) (isLevelPStructure_DU hp)
    ((isLevelPStructure_DU hp).map _)
  rw [← h1]
  have eW : (WU K p).map ((f.restrictScalars K : U K p →ₐ[K] A) : U K p →+* A) = W := by
    rw [← hWA]; exact WU_map_liftU a (isUnit_of_isLevelPStructure hD' hΔ')
  have eD : (DU K p).map ((f.restrictScalars K : U K p →ₐ[K] A) : U K p →+* A) = D :=
    DU_map_liftU a (isUnit_of_isLevelPStructure hD' hΔ')
  exact toFun_congr G _ _ _ _ eW.symm eD.symm

end Reduce

section Ranks

variable {K : Type u} [Field K] {p : ℕ}

local notation "P5" => MvPolynomial (Fin 5) K

theorem nontrivial_adjoinRoot_of_monic {R : Type*} [CommRing R] [Nontrivial R] {g : R[X]}
    (hg : g.Monic) (hdeg : g.natDegree ≠ 0) : Nontrivial (AdjoinRoot g) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  rw [hg.isUnit_iff] at hu
  rw [hu, natDegree_one] at hdeg
  exact hdeg rfl

theorem one_le_halfDegree (hodd : Odd p) (h1 : p ≠ 1) : 1 ≤ (p ^ 2 - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hodd
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd rfl h1
    · exact hm
  have : (2 * m + 1) ^ 2 - 1 = 2 * (2 * m * m + 2 * m) := by ring_nf; omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  nlinarith

theorem nontrivial_R₁ (hp : (p : K) ≠ 0) (hodd : Odd p) (h1 : p ≠ 1) : Nontrivial (R₁ K p) :=
  nontrivial_adjoinRoot_of_monic (monic_ψm hp (Nat.not_even_iff_odd.mpr hodd)) (by
    rw [natDegree_ψm hp (Nat.not_even_iff_odd.mpr hodd)]
    exact Nat.one_le_iff_ne_zero.mp (one_le_halfDegree hodd h1))

theorem monic_q₁ : (q₁ K p).Monic := monic_quad _ _

theorem free_finite_finrank_T (hp : (p : K) ≠ 0) (hodd : Odd p) (h1 : p ≠ 1) :
    Module.Free P5 (T K p) ∧ Module.Finite P5 (T K p) ∧
      Module.finrank P5 (T K p) = (2 * ((p ^ 2 - 1) / 2)) ^ 2 := by
  have hodd' := Nat.not_even_iff_odd.mpr hodd
  haveI : Nontrivial (R₁ K p) := nontrivial_R₁ hp hodd h1
  haveI hF₁ : Module.Free P5 (R₁ K p) := (monic_ψm hp hodd').free_adjoinRoot
  haveI hf₁ : Module.Finite P5 (R₁ K p) := (monic_ψm hp hodd').finite_adjoinRoot
  haveI hF₂ : Module.Free (R₁ K p) (S K p) := (monic_q₁ (K := K) (p := p)).free_adjoinRoot
  haveI hf₂ : Module.Finite (R₁ K p) (S K p) := (monic_q₁ (K := K) (p := p)).finite_adjoinRoot
  haveI hFS : Module.Free P5 (S K p) := Module.Free.trans (S := R₁ K p)
  haveI hfS : Module.Finite P5 (S K p) := Module.Finite.trans (R₁ K p) (S K p)
  have r₁ : Module.finrank P5 (R₁ K p) = (p ^ 2 - 1) / 2 := by
    rw [(AdjoinRoot.powerBasis' (monic_ψm hp hodd')).finrank, AdjoinRoot.powerBasis'_dim,
      natDegree_ψm hp hodd']
  have r₂ : Module.finrank (R₁ K p) (S K p) = 2 := by
    rw [(AdjoinRoot.powerBasis' (monic_q₁ (K := K) (p := p))).finrank, AdjoinRoot.powerBasis'_dim]
    exact natDegree_quad _ _
  have rS : Module.finrank P5 (S K p) = 2 * ((p ^ 2 - 1) / 2) := by
    rw [← Module.finrank_mul_finrank P5 (R₁ K p) (S K p), r₁, r₂, mul_comm]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [Module.finrank_tensorProduct, rS]
  ring

end Ranks

section Points

variable {K : Type u} [Field K] {p : ℕ}

local notation "P5" => MvPolynomial (Fin 5) K
local notation "Ω" => Generic.Closure K

theorem WA_closure : WA K (Generic.Closure K) = Generic.curve K := rfl

theorem natCast_closure_ne_zero (hp : (p : K) ≠ 0) : (p : Ω) ≠ 0 := by
  rw [← map_natCast (algebraMap K Ω)]
  exact (_root_.map_ne_zero _).mpr hp

theorem separable_ψ_curve (hp : (p : K) ≠ 0) (hodd : Odd p) :
    ((Generic.curve K).preΨ' p).Separable :=
  WeierstrassCurve.separable_prePsi_of_isUnit _ hodd
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (natCast_closure_ne_zero hp) (Generic.Δ_curve_ne_zero K)))

theorem card_rootSet_ψ_curve (hp : (p : K) ≠ 0) (hodd : Odd p) :
    Fintype.card (((Generic.curve K).preΨ' p).rootSet Ω) = (p ^ 2 - 1) / 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree (separable_ψ_curve hp hodd) (IsAlgClosed.splits _),
    WeierstrassCurve.natDegree_preΨ' _ (natCast_closure_ne_zero hp),
    if_neg (Nat.not_even_iff_odd.mpr hodd)]

theorem separable_quad_curve (hodd : Odd p) {x : Ω}
    (hx : (((Generic.curve K).preΨ' p)).eval x = 0) :
    (quad (Generic.curve K) x).Separable := by
  classical
  set E := Generic.curve K with hE
  have hmonic := monic_quad E x
  have hq0 : quad E x ≠ 0 := hmonic.ne_zero
  have hcard : (quad E x).roots.card = 2 := by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits _), natDegree_quad]
  obtain ⟨y₀, hy₀⟩ : ∃ y, y ∈ (quad E x).roots :=
    Multiset.card_pos_iff_exists_mem.mp (by omega)
  have hEq₀ : E.toAffine.Equation x y₀ :=
    (eval_quad_eq_zero_iff _ _ _).mp ((mem_roots hq0).mp hy₀)
  set y₁ := E.toAffine.negY x y₀ with hy₁def
  have hEq₁ : E.toAffine.Equation x y₁ := (WeierstrassCurve.Affine.equation_neg x y₀).mpr hEq₀
  have hy₁ : y₁ ∈ (quad E x).roots := (mem_roots hq0).mpr ((eval_quad_eq_zero_iff _ _ _).mpr hEq₁)

  have hne : y₀ ≠ y₁ := by
    intro he
    have hns : E.toAffine.Nonsingular x y₀ :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq₀
    set P₀ : E.toAffine.Point := WeierstrassCurve.Affine.Point.some x y₀ hns with hP₀
    have hsome : ∀ {y' : Ω} (h' : E.toAffine.Nonsingular x y'), y' = y₀ →
        WeierstrassCurve.Affine.Point.some x y' h' = P₀ := by
      rintro y' h' rfl; rfl
    have hneg : -P₀ = P₀ := by
      rw [hP₀, WeierstrassCurve.Affine.Point.neg_some]
      exact hsome _ he.symm
    have h2 : 2 • P₀ = 0 := by
      rw [two_nsmul]
      nth_rw 1 [← hneg]
      exact neg_add_cancel P₀
    have hpP : p • P₀ = 0 :=
      (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi E hodd hns).mpr hx
    obtain ⟨m, hm⟩ := hodd
    have hzero : P₀ = 0 := by
      have e1 : (2 * m + 1) • P₀ = 0 := hm ▸ hpP
      rwa [add_nsmul, one_nsmul, mul_nsmul, h2, nsmul_zero, zero_add] at e1
    exact WeierstrassCurve.Affine.Point.some_ne_zero hns hzero

  have hnd : ({y₀, y₁} : Multiset Ω).Nodup := by simp [hne]
  have hle : ({y₀, y₁} : Multiset Ω) ≤ (quad E x).roots := by
    refine (Multiset.le_iff_subset hnd).mpr fun y hy => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hy₀
    · exact hy₁
  have heq : ({y₀, y₁} : Multiset Ω) = (quad E x).roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcard]; simp)
  rw [← nodup_roots_iff_of_splits hq0 (IsAlgClosed.splits _), ← heq]
  exact hnd

theorem card_rootSet_quad_curve (hodd : Odd p) {x : Ω}
    (hx : (((Generic.curve K).preΨ' p)).eval x = 0) :
    Fintype.card ((quad (Generic.curve K) x).rootSet Ω) = 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree (separable_quad_curve hodd hx) (IsAlgClosed.splits _),
    natDegree_quad]

variable (K p) in

def Pt : Type u :=
  Σ x : (((Generic.curve K).preΨ' p).rootSet (Generic.Closure K)),
    ((quad (Generic.curve K) (x : Generic.Closure K)).rootSet (Generic.Closure K))

noncomputable scoped instance : Fintype (Pt K p) := by
  unfold Pt
  infer_instance

theorem card_Pt (hp : (p : K) ≠ 0) (hodd : Odd p) :
    Fintype.card (Pt K p) = 2 * ((p ^ 2 - 1) / 2) := by
  rw [show Fintype.card (Pt K p) =
      Fintype.card (Σ x : (((Generic.curve K).preΨ' p).rootSet (Generic.Closure K)),
        ((quad (Generic.curve K) (x : Generic.Closure K)).rootSet (Generic.Closure K))) from
      Fintype.card_congr (Equiv.refl _), Fintype.card_sigma]
  have h2 : ∀ x : (((Generic.curve K).preΨ' p).rootSet (Generic.Closure K)),
      Fintype.card ((quad (Generic.curve K) (x : Generic.Closure K)).rootSet (Generic.Closure K))
        = 2 := by
    intro x
    apply card_rootSet_quad_curve hodd
    have hx := (Polynomial.mem_rootSet.mp x.2).2
    rwa [Polynomial.coe_aeval_eq_eval] at hx
  simp_rw [h2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_rootSet_ψ_curve hp hodd, mul_comm]

namespace Pt

variable (a : Pt K p)

def x : Ω := (a.1 : Ω)

def y : Ω := (a.2 : Ω)

theorem eval_ψ_x : (((Generic.curve K).preΨ' p)).eval a.x = 0 := by
  have hx := (Polynomial.mem_rootSet.mp a.1.2).2
  rwa [Polynomial.coe_aeval_eq_eval] at hx

theorem equation : (Generic.curve K).toAffine.Equation a.x a.y := by
  have hy := (Polynomial.mem_rootSet.mp a.2.2).2
  rw [Polynomial.coe_aeval_eq_eval] at hy
  exact (eval_quad_eq_zero_iff _ _ _).mp hy

theorem ext' {a b : Pt K p} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  rcases a with ⟨⟨xa, hxa⟩, ⟨ya, hya⟩⟩
  rcases b with ⟨⟨xb, hxb⟩, ⟨yb, hyb⟩⟩
  change xa = xb at hx
  change ya = yb at hy
  subst hx
  subst hy
  rfl

end Pt

def pairData (i : Pt K p × Pt K p) : PtPair K p (Generic.Closure K) where
  D := ⟨i.1.x, i.1.y, i.2.x, i.2.y⟩
  eqP := i.1.equation
  eqQ := i.2.equation
  ψP := i.1.eval_ψ_x
  ψQ := i.2.eval_ψ_x

theorem pairData_D (i : Pt K p × Pt K p) : (pairData i).D = ⟨i.1.x, i.1.y, i.2.x, i.2.y⟩ := rfl

theorem pairData_injective : Function.Injective (pairData (K := K) (p := p)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have hD := congr_arg PtPair.D h
  rw [pairData_D, pairData_D, LevelPData.mk.injEq] at hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  dsimp only at h1 h2 h3 h4
  rw [Pt.ext' h1 h2, Pt.ext' h3 h4]

end Points

section Characters

variable {K : Type u} [Field K] {p : ℕ}

local notation "P5" => MvPolynomial (Fin 5) K
local notation "Ω" => Generic.Closure K

variable (K p) in

abbrev TΩ : Type u := TensorProduct (MvPolynomial (Fin 5) K) (Generic.Closure K) (T K p)

noncomputable def χΩ (a : PtPair K p (Generic.Closure K)) : TΩ K p →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) (liftT a) (fun _ _ => Commute.all _ _)

theorem χΩ_tmul (a : PtPair K p (Generic.Closure K)) (c : Ω) (t : T K p) :
    χΩ a (c ⊗ₜ t) = c * liftT a t :=
  Algebra.TensorProduct.lift_tmul _ _ _ c t

theorem χΩ_pairData_injective :
    Function.Injective (fun i : Pt K p × Pt K p => χΩ (pairData i)) := by
  intro i j h
  have key : ∀ t : T K p, liftT (pairData i) t = liftT (pairData j) t := by
    intro t
    have := congr_arg (fun χ : TΩ K p →ₐ[Ω] Ω => χ ((1 : Ω) ⊗ₜ t)) h
    simpa [χΩ_tmul] using this
  have h1 := key (DT K p).xP
  have h2 := key (DT K p).yP
  have h3 := key (DT K p).xQ
  have h4 := key (DT K p).yQ
  simp only [liftT_xP, liftT_yP, liftT_xQ, liftT_yQ, pairData_D] at h1 h2 h3 h4
  obtain ⟨a, b⟩ := i
  obtain ⟨a', b'⟩ := j
  simp only at h1 h2 h3 h4
  rw [Pt.ext' h1 h2, Pt.ext' h3 h4]

theorem eq_zero_of_forall_liftT [Module.Free P5 (T K p)]
    [Module.Finite P5 (T K p)]
    (hrank : Module.finrank P5 (T K p) = Fintype.card (Pt K p × Pt K p))
    (t : T K p) (ht : ∀ a : PtPair K p (Generic.Closure K), liftT a t = 0) : t = 0 := by

  set z : TΩ K p := (1 : Ω) ⊗ₜ t with hz
  have hχ : ∀ i : Pt K p × Pt K p, χΩ (pairData i) z = 0 := by
    intro i; rw [hz, χΩ_tmul, ht, mul_zero]

  let v : Pt K p × Pt K p → Module.Dual Ω (TΩ K p) := fun i => (χΩ (pairData i)).toLinearMap
  have hli : LinearIndependent Ω v :=
    (linearIndependent_algHom_toLinearMap Ω (TΩ K p) Ω).comp _ χΩ_pairData_injective
  haveI : Module.Free Ω (TΩ K p) := inferInstance
  haveI : Module.Finite Ω (TΩ K p) := inferInstance
  haveI : Module.Finite Ω (Module.Dual Ω (TΩ K p)) := Module.Finite.linearMap Ω Ω (TΩ K p) Ω
  have hcard : Fintype.card (Pt K p × Pt K p) = Module.finrank Ω (Module.Dual Ω (TΩ K p)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_baseChange, hrank]
  have hspan : Submodule.span Ω (Set.range v) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hcard

  have hz0 : z = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff Ω z).mp fun φ => ?_
    have hφ : φ ∈ Submodule.span Ω (Set.range v) := hspan ▸ Submodule.mem_top
    have hle : Submodule.span Ω (Set.range v) ≤ LinearMap.ker (Module.Dual.eval Ω (TΩ K p) z) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
      exact hχ i
    have := hle hφ
    rwa [LinearMap.mem_ker, Module.Dual.eval_apply] at this

  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : T K p →ₐ[P5] TΩ K p) :=
    Algebra.TensorProduct.includeRight_injective (Generic.algebraMap_closure_injective K)
  exact hinj (by rw [Algebra.TensorProduct.includeRight_apply, map_zero]; exact hz0)

end Characters

section Main

variable {K : Type u} [Field K] {p : ℕ} {k : ℤ}

local notation "P5" => MvPolynomial (Fin 5) K
local notation "Ω" => Generic.Closure K

theorem isLevelPStructure_of_ptPair (a : PtPair K p (Generic.Closure K))
    (hs : IsUnit ((WA K Ω).Δ * indepElt (WA K Ω) p a.D.xP a.D.xQ *
      indepElt (WA K Ω) p a.D.xQ a.D.xP)) :
    IsLevelPStructure (Generic.curve K) p a.D where
  equation_P := a.eqP
  equation_Q := a.eqQ
  preΨ_P := by rw [WeierstrassCurve.preΨ_ofNat]; exact a.ψP
  preΨ_Q := by rw [WeierstrassCurve.preΨ_ofNat]; exact a.ψQ
  isUnit_indepElt_PQ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hs)
  isUnit_indepElt_QP := isUnit_of_mul_isUnit_right hs

theorem universal_eq_zero [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (G : KatzLevelPForm K p k)
    (h : ∀ (D : LevelPData (Generic.Closure K))
      (hD : IsLevelPStructure (Generic.curve K) p D),
      G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD = 0) :
    G.toFun (WU K p) isUnit_Δ_WU (DU K p) (isLevelPStructure_DU hp) = 0 := by
  have hprime : p.Prime := Fact.out
  have hodd : Odd p := hprime.odd_of_ne_two hp2
  have h1 : p ≠ 1 := hprime.one_lt.ne'
  obtain ⟨hfree, hfin, hrank⟩ := free_finite_finrank_T hp hodd h1
  set g := G.toFun (WU K p) isUnit_Δ_WU (DU K p) (isLevelPStructure_DU hp) with hg

  obtain ⟨⟨t, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers (sT K p)) g
  simp only at e

  have hts : t * sT K p = 0 := by
    refine eq_zero_of_forall_liftT (by rw [hrank, Fintype.card_prod, card_Pt hp hodd, sq]) _ ?_
    intro a
    rw [map_mul, liftT_sT]
    by_cases hs : IsUnit ((WA K Ω).Δ * indepElt (WA K Ω) p a.D.xP a.D.xQ *
        indepElt (WA K Ω) p a.D.xQ a.D.xP)
    ·
      let f : U K p →ₐ[P5] Ω := liftU a hs
      have hDa : IsLevelPStructure (Generic.curve K) p a.D := isLevelPStructure_of_ptPair a hs
      have hval := h a.D hDa
      have hmap := G.map_toFun (f.restrictScalars K) (WU K p) isUnit_Δ_WU
        (KatzModularForm.isUnit_Δ_map _ isUnit_Δ_WU) (DU K p) (isLevelPStructure_DU hp)
        ((isLevelPStructure_DU hp).map _)
      have eW : (WU K p).map ((f.restrictScalars K : U K p →ₐ[K] Ω) : U K p →+* Ω) =
          Generic.curve K := WU_map_liftU a hs
      have eD : (DU K p).map ((f.restrictScalars K : U K p →ₐ[K] Ω) : U K p →+* Ω) = a.D :=
        DU_map_liftU a hs
      rw [toFun_congr G _ (Generic.isUnit_Δ_curve K) _ hDa eW eD, hval] at hmap

      have hfg : f g = 0 := hmap.symm
      have hft : liftT a t = 0 := by
        rw [← liftU_algebraMap a hs t, ← e, map_mul, hfg, zero_mul]
      rw [hft, zero_mul]
    · rw [isUnit_iff_ne_zero, not_not] at hs
      rw [hs, mul_zero]

  have hu : IsUnit (algebraMap (T K p) (U K p) (sT K p ^ (n + 1))) := by
    rw [map_pow]; exact isUnit_algebraMap_sT.pow _
  have : g * algebraMap (T K p) (U K p) (sT K p ^ (n + 1)) = 0 := by
    rw [pow_succ, map_mul, ← mul_assoc, e, ← map_mul, hts, map_zero]
  exact (hu.mul_left_eq_zero).mp this

theorem main [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) (G : KatzLevelPForm K p k)
    (h : ∀ (D : LevelPData (Generic.Closure K))
      (hD : IsLevelPStructure (Generic.curve K) p D),
      G.toFun (Generic.curve K) (Generic.isUnit_Δ_curve K) D hD = 0) :
    G = 0 := by
  refine KatzLevelPForm.ext fun A _ _ W hW D hD => ?_
  obtain ⟨f, hf⟩ := exists_toFun_eq hp G W hW D hD
  rw [hf, universal_eq_zero hp2 hp G h, map_zero, KatzLevelPForm.zero_toFun]

end Main

end ModularCurve.KatzLevelPForm.GenericFibreProof
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve.KatzLevelPForm P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve.KatzLevelPForm.GenericFibreProof"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve.KatzLevelPForm"
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve.KatzLevelPForm P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero.ModularCurve.KatzLevelPForm.GenericFibreProof"

theorem solution
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) {k : ℤ}
    (G : ModularCurve.KatzLevelPForm K p k)
    (h : ∀ (D : ModularCurve.LevelPData (WeierstrassCurve.Generic.Closure K))
      (hD : ModularCurve.IsLevelPStructure (WeierstrassCurve.Generic.curve K) p D),
      G.toFun (WeierstrassCurve.Generic.curve K) (WeierstrassCurve.Generic.isUnit_Δ_curve K) D hD = 0) :
    G = 0 :=
  ModularCurve.KatzLevelPForm.GenericFibreProof.main hp2 hp G h

end S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_eq_zero_of_forall_toFun_genericCurve_eq_zero (solution)
