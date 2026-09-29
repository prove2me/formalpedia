-- Prove2me | solution 1 for ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/74dfa137-782e-547f-9887-eeadb1e36ff8

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Theorems.Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq
import Theorems.Thm_ModularCurve_LevelP_TorsionPointRing_exists_ringHom_apply_torsionPt_eq
import Theorems.Thm_ModularCurve_LevelP_BasisRing_exists_ringHom_basisData_map_eq
import Theorems.Thm_ModularCurve_exists_torsionPt_indepElt_ne_zero
import Theorems.Thm_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field
import Theorems.Thm_ModularCurve_LevelP_BasisRing_faithfullyFlat
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

noncomputable section

open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "indepElt inLine_self indepElt_map LevelPData LevelPData.map LevelPData.variableChange IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext LevelP.BasisRing LevelP.BasisRing.ofBase LevelP.BasisRing.algebraMap_eq LevelP.basisCurve LevelP.isUnit_Δ_basisCurve LevelP.basisData LevelP.isLevelPStructure_basisData LevelP.BasisRing.exists_ringHom_basisData_map_eq exists_torsionPt_indepElt_ne_zero LevelP.BasisRing.faithfullyFlat LevelPData.map_variableChange LevelP.T3.isUnit_Δ_curve"
p2m_open "ModularCurve"

open scoped TensorProduct
open WeierstrassCurve Polynomial

namespace LevelP
p2m_export "ModularCurve.LevelP" "preΨ_eval_map TorsionPointRing TorsionPointRing.ofBase TorsionPointRing.algebraMap_eq torsionPtX torsionPtY torsionPtCurve equation_torsionPt preΨ_torsionPt BasisRing BasisRing.ofBase BasisRing.algebraMap_eq basisCurve isUnit_Δ_basisCurve basisData isLevelPStructure_basisData instAlgebraBasisRing TorsionPointRing.free_and_finrank_eq TorsionPointRing.exists_ringHom_apply_torsionPt_eq BasisRing.exists_ringHom_basisData_map_eq BasisRing.faithfullyFlat T3.isUnit_Δ_curve"
p2m_open "ModularCurve.LevelP"

private theorem _root_.ModularCurve.LevelPData.map_variableChange {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (C : VariableChange A) (D : LevelPData A) :
    (D.variableChange C).map φ = (D.map φ).variableChange (C.map φ) := by
  ext <;> simp [LevelPData.map, LevelPData.variableChange, VariableChange.map, Units.coe_map_inv,
    map_mul, map_sub, map_pow]

p2m_alias "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelPData.map_variableChange" "ModularCurve.LevelPData.map_variableChange"

section PointExt

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {p : ℕ}

namespace TorsionPointRing p2m_export "ModularCurve.LevelP.TorsionPointRing" "ofBase algebraMap_eq free_and_finrank_eq exists_ringHom_apply_torsionPt_eq" end TorsionPointRing
namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
private theorem _root_.ModularCurve.LevelP.TorsionPointRing.flat (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Flat B (TorsionPointRing W p) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · haveI : Module.Free B (TorsionPointRing W p) := Module.Free.of_subsingleton' B _
    infer_instance
  · haveI := (TorsionPointRing.free_and_finrank_eq W hp hp1 hpu).1
    infer_instance

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.flat"
end PointExt

section ThirdPoint

variable {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ)

abbrev T2 : Type u := BasisRing W p ⊗[A] BasisRing W p

def T2.curve : WeierstrassCurve (T2 W p) := W.map (algebraMap A (T2 W p))

def T2.data₁ : LevelPData (T2 W p) :=
  (basisData W p).map (Algebra.TensorProduct.includeLeftRingHom : BasisRing W p →+* T2 W p)

def T2.data₂ : LevelPData (T2 W p) :=
  (basisData W p).map
    ((Algebra.TensorProduct.includeRight : BasisRing W p →ₐ[A] T2 W p) : BasisRing W p →+* T2 W p)

theorem T2.includeLeft_comp_algebraMap :
    (Algebra.TensorProduct.includeLeftRingHom : BasisRing W p →+* T2 W p).comp
      (algebraMap A (BasisRing W p)) = algebraMap A (T2 W p) := by
  ext a
  simp [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.algebraMap_apply]

theorem T2.includeRight_comp_algebraMap :
    ((Algebra.TensorProduct.includeRight : BasisRing W p →ₐ[A] T2 W p) : BasisRing W p →+* T2 W p).comp
      (algebraMap A (BasisRing W p)) = algebraMap A (T2 W p) := by
  ext a
  exact (Algebra.TensorProduct.includeRight : BasisRing W p →ₐ[A] T2 W p).commutes a

theorem T2.curve_eq_map_left : T2.curve W p =
    (basisCurve W p).map (Algebra.TensorProduct.includeLeftRingHom : BasisRing W p →+* T2 W p) := by
  rw [basisCurve, WeierstrassCurve.map_map, ← BasisRing.algebraMap_eq, T2.includeLeft_comp_algebraMap,
    T2.curve]

theorem T2.curve_eq_map_right : T2.curve W p = (basisCurve W p).map
    ((Algebra.TensorProduct.includeRight : BasisRing W p →ₐ[A] T2 W p) : BasisRing W p →+* T2 W p) := by
  rw [basisCurve, WeierstrassCurve.map_map, ← BasisRing.algebraMap_eq, T2.includeRight_comp_algebraMap,
    T2.curve]

theorem T2.isLevelPStructure_data₁ : IsLevelPStructure (T2.curve W p) p (T2.data₁ W p) := by
  rw [T2.curve_eq_map_left]
  exact (isLevelPStructure_basisData W p).map _

theorem T2.isLevelPStructure_data₂ : IsLevelPStructure (T2.curve W p) p (T2.data₂ W p) := by
  rw [T2.curve_eq_map_right]
  exact (isLevelPStructure_basisData W p).map _

theorem T2.isUnit_Δ_curve (hW : IsUnit W.Δ) : IsUnit (T2.curve W p).Δ := by
  rw [T2.curve, WeierstrassCurve.map_Δ]; exact hW.map _

abbrev T3pre : Type u := TorsionPointRing (T2.curve W p) p

namespace T3 p2m_export "ModularCurve.LevelP.T3" "isUnit_Δ_curve" end T3

def T3.denom : T3pre W p :=
  indepElt (torsionPtCurve (T2.curve W p) p) p (torsionPtX (T2.curve W p) p)
      (TorsionPointRing.ofBase (T2.curve W p) p (T2.data₁ W p).xQ) *
    indepElt (torsionPtCurve (T2.curve W p) p)
      (p) (TorsionPointRing.ofBase (T2.curve W p) p (T2.data₁ W p).xQ) (torsionPtX (T2.curve W p) p) *
    (indepElt (torsionPtCurve (T2.curve W p) p) p (torsionPtX (T2.curve W p) p)
        (TorsionPointRing.ofBase (T2.curve W p) p (T2.data₂ W p).xQ) *
      indepElt (torsionPtCurve (T2.curve W p) p) p
        (TorsionPointRing.ofBase (T2.curve W p) p (T2.data₂ W p).xQ) (torsionPtX (T2.curve W p) p))

def T3 : Type u := Localization.Away (T3.denom W p)

scoped instance : CommRing (T3 W p) := inferInstanceAs (CommRing (Localization.Away (T3.denom W p)))
scoped instance : Algebra (T3pre W p) (T3 W p) :=
  inferInstanceAs (Algebra (T3pre W p) (Localization.Away (T3.denom W p)))
scoped instance : IsLocalization.Away (T3.denom W p) (T3 W p) :=
  inferInstanceAs (IsLocalization.Away (T3.denom W p) (Localization.Away (T3.denom W p)))

def T3.ofT2 : T2 W p →+* T3 W p :=
  (algebraMap (T3pre W p) (T3 W p)).comp (TorsionPointRing.ofBase (T2.curve W p) p)

scoped instance T3.algebraT2 : Algebra (T2 W p) (T3 W p) := (T3.ofT2 W p).toAlgebra

p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3"
theorem T3.algebraMap_eq : algebraMap (T2 W p) (T3 W p) = T3.ofT2 W p := rfl

scoped instance : IsScalarTower (T2 W p) (T3pre W p) (T3 W p) :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [T3.algebraMap_eq, T3.ofT2, TorsionPointRing.algebraMap_eq])

theorem T3.isUnit_denom : IsUnit (algebraMap (T3pre W p) (T3 W p) (T3.denom W p)) :=
  IsLocalization.Away.algebraMap_isUnit (S := T3 W p) (T3.denom W p)

theorem T3.flat (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : A)) : Module.Flat (T2 W p) (T3 W p) := by
  haveI : Module.Flat (T2 W p) (T3pre W p) :=
    TorsionPointRing.flat (T2.curve W p) hp hp1 (by simpa using hpu.map (algebraMap A (T2 W p)))
  haveI : Module.Flat (T3pre W p) (T3 W p) :=
    IsLocalization.flat (T3 W p) (Submonoid.powers (T3.denom W p))
  exact Module.Flat.trans (T2 W p) (T3pre W p) (T3 W p)

theorem T3.faithfullyFlat [Fact p.Prime] (hp2 : p ≠ 2) (hpu : IsUnit (p : A)) (hW : IsUnit W.Δ) :
    Module.FaithfullyFlat (T2 W p) (T3 W p) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  haveI := T3.flat W p hodd hp1 hpu
  refine Module.FaithfullyFlat.of_forall_isMaximal_exists_ringHom_field.{u, u, u} (fun m hm => ?_)
  haveI := hm.isPrime
  let K := AlgebraicClosure m.ResidueField
  let φ : T2 W p →+* K := (algebraMap m.ResidueField K).comp (algebraMap (T2 W p) m.ResidueField)
  have hφm : ∀ b ∈ m, φ b = 0 := fun b hb => by
    simp only [φ, RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero.mpr hb, map_zero]
  have hΔ : ((T2.curve W p).map φ).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]; exact ((T2.isUnit_Δ_curve W p hW).map φ).ne_zero
  have hpK : (p : K) ≠ 0 := by simpa using ((hpu.map (algebraMap A (T2 W p))).map φ).ne_zero
  have h₁ := (T2.isLevelPStructure_data₁ W p).map φ
  have h₂ := (T2.isLevelPStructure_data₂ W p).map φ
  obtain ⟨x, y, hxy, hx, i1, i2, i3, i4⟩ := exists_torsionPt_indepElt_ne_zero ((T2.curve W p).map φ)
    hp2 hpK hΔ _ _ _ _ h₁.equation_Q h₁.preΨ_Q h₂.equation_Q h₂.preΨ_Q
  obtain ⟨ψ₀, hψ₀, hψx, -⟩ :=
    TorsionPointRing.exists_ringHom_apply_torsionPt_eq (T2.curve W p) p φ x y hxy hx
  have hc : (torsionPtCurve (T2.curve W p) p).map ψ₀ = (T2.curve W p).map φ := by
    rw [torsionPtCurve, WeierstrassCurve.map_map, hψ₀]
  have hb : ∀ b, ψ₀ (TorsionPointRing.ofBase (T2.curve W p) p b) = φ b := fun b => by
    rw [← RingHom.comp_apply, hψ₀]
  have hunit : IsUnit (ψ₀ (T3.denom W p)) := by
    rw [T3.denom, map_mul, map_mul, map_mul, ← indepElt_map, ← indepElt_map, ← indepElt_map,
      ← indepElt_map, hc, hψx, hb, hb]
    exact ((isUnit_iff_ne_zero.mpr i1).mul (isUnit_iff_ne_zero.mpr i2)).mul
      ((isUnit_iff_ne_zero.mpr i3).mul (isUnit_iff_ne_zero.mpr i4))
  refine ⟨K, inferInstance, IsLocalization.Away.lift (T3.denom W p) hunit, fun b hb' => ?_⟩
  rw [RingHom.mem_ker, RingHom.comp_apply, T3.algebraMap_eq, T3.ofT2, RingHom.comp_apply,
    IsLocalization.Away.lift_eq, hb]
  exact hφm b hb'

theorem T3.ofT2_injective [Fact p.Prime] (hp2 : p ≠ 2) (hpu : IsUnit (p : A)) (hW : IsUnit W.Δ) :
    Function.Injective (T3.ofT2 W p) := by
  haveI := T3.faithfullyFlat W p hp2 hpu hW
  rw [← T3.algebraMap_eq]
  exact FaithfulSMul.algebraMap_injective (T2 W p) (T3 W p)

def T3.curve : WeierstrassCurve (T3 W p) := (T2.curve W p).map (T3.ofT2 W p)

theorem T3.curve_eq : T3.curve W p =
    (torsionPtCurve (T2.curve W p) p).map (algebraMap (T3pre W p) (T3 W p)) := by
  rw [T3.curve, T3.ofT2, torsionPtCurve, WeierstrassCurve.map_map]

def T3.xX : T3 W p := algebraMap (T3pre W p) (T3 W p) (torsionPtX (T2.curve W p) p)
def T3.yX : T3 W p := algebraMap (T3pre W p) (T3 W p) (torsionPtY (T2.curve W p) p)

def T3.XQ1 : LevelPData (T3 W p) :=
  ⟨T3.xX W p, T3.yX W p, T3.ofT2 W p (T2.data₁ W p).xQ, T3.ofT2 W p (T2.data₁ W p).yQ⟩

def T3.Q2X : LevelPData (T3 W p) :=
  ⟨T3.ofT2 W p (T2.data₂ W p).xQ, T3.ofT2 W p (T2.data₂ W p).yQ, T3.xX W p, T3.yX W p⟩

theorem T3.equation_X : (T3.curve W p).toAffine.Equation (T3.xX W p) (T3.yX W p) := by
  rw [T3.curve_eq]
  exact (equation_torsionPt (T2.curve W p) p).map _

theorem T3.preΨ_X : ((T3.curve W p).preΨ p).eval (T3.xX W p) = 0 := by
  rw [T3.curve_eq, T3.xX, preΨ_eval_map, preΨ_torsionPt, map_zero]

theorem T3.isLevelPStructure_XQ1 : IsLevelPStructure (T3.curve W p) p (T3.XQ1 W p) := by
  have h₁ := (T2.isLevelPStructure_data₁ W p).map (T3.ofT2 W p)
  have hu := T3.isUnit_denom W p
  rw [T3.denom, map_mul, map_mul, map_mul] at hu
  exact
  { equation_P := T3.equation_X W p
    equation_Q := h₁.equation_Q
    preΨ_P := T3.preΨ_X W p
    preΨ_Q := h₁.preΨ_Q
    isUnit_indepElt_PQ := by
      have h := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
      rw [← indepElt_map] at h
      rw [T3.curve_eq]
      exact h
    isUnit_indepElt_QP := by
      have h := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
      rw [← indepElt_map] at h
      rw [T3.curve_eq]
      exact h }

theorem T3.isLevelPStructure_Q2X : IsLevelPStructure (T3.curve W p) p (T3.Q2X W p) := by
  have h₂ := (T2.isLevelPStructure_data₂ W p).map (T3.ofT2 W p)
  have hu := T3.isUnit_denom W p
  rw [T3.denom, map_mul, map_mul, map_mul] at hu
  exact
  { equation_P := h₂.equation_Q
    equation_Q := T3.equation_X W p
    preΨ_P := h₂.preΨ_Q
    preΨ_Q := T3.preΨ_X W p
    isUnit_indepElt_PQ := by
      have h := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)
      rw [← indepElt_map] at h
      rw [T3.curve_eq]
      exact h
    isUnit_indepElt_QP := by
      have h := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu)
      rw [← indepElt_map] at h
      rw [T3.curve_eq]
      exact h }

end ThirdPoint
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3"

end LevelP
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "indepElt inLine_self indepElt_map LevelPData LevelPData.map LevelPData.variableChange IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext LevelP.BasisRing LevelP.BasisRing.ofBase LevelP.BasisRing.algebraMap_eq LevelP.basisCurve LevelP.isUnit_Δ_basisCurve LevelP.basisData LevelP.isLevelPStructure_basisData LevelP.BasisRing.exists_ringHom_basisData_map_eq exists_torsionPt_indepElt_ne_zero LevelP.BasisRing.faithfullyFlat LevelPData.map_variableChange LevelP.T3.isUnit_Δ_curve"
p2m_open "ModularCurve"

open scoped TensorProduct
open WeierstrassCurve Polynomial

namespace KatzLevelPForm
p2m_export "ModularCurve.KatzLevelPForm" "ext mul swap DependsOnlyOnSndLine SwapInvariant toFun map_toFun toFun_variableChange"
p2m_open "ModularCurve.KatzLevelPForm"

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_congr (F : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
    {W W' : WeierstrassCurve A} (hWW' : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ)
    {D D' : LevelPData A} (hDD' : D = D') (hD : IsLevelPStructure W p D)
    (hD' : IsLevelPStructure W' p D') : F.toFun W hW D hD = F.toFun W' hW' D' hD' := by
  subst hWW' hDD'; rfl

p2m_export "ModularCurve.KatzLevelPForm" "toFun_congr"

def algHomOfComp {A A' T T' : Type u} [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    [CommRing T] [CommRing T'] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    [Algebra A' T'] [Algebra R T'] [IsScalarTower R A' T'] (θ : T →+* T') (f : A →ₐ[R] A')
    (h : θ.comp (algebraMap A T) = (algebraMap A' T').comp (f : A →+* A')) : T →ₐ[R] T' :=
  { θ with
    commutes' := fun r => by
      have := congrArg (fun g : A →+* T' => g (algebraMap R A r)) h
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.commutes] at this
      rw [IsScalarTower.algebraMap_apply R A T, IsScalarTower.algebraMap_apply R A' T']
      exact this }

@[scoped simp] theorem algHomOfComp_coe {A A' T T' : Type u} [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] [CommRing T] [CommRing T'] [Algebra A T] [Algebra R T] [IsScalarTower R A T]
    [Algebra A' T'] [Algebra R T'] [IsScalarTower R A' T'] (θ : T →+* T') (f : A →ₐ[R] A') (h) :
    ((algHomOfComp θ f h : T →ₐ[R] T') : T →+* T') = θ :=
  RingHom.ext fun _ => rfl

section testObject

variable (F : KatzLevelPForm R p k) {A : Type u} [CommRing A] [Algebra R A]
  (W : WeierstrassCurve A) (hW : IsUnit W.Δ)

scoped instance instAlgebraBasisRing : Algebra R (LevelP.BasisRing W p) :=
  ((algebraMap A (LevelP.BasisRing W p)).comp (algebraMap R A)).toAlgebra

scoped instance instIsScalarTowerBasisRing : IsScalarTower R A (LevelP.BasisRing W p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private def _root_.ModularCurve.KatzLevelPForm.tauto : LevelP.BasisRing W p :=
  F.toFun (LevelP.basisCurve W p) (LevelP.isUnit_Δ_basisCurve W p hW) (LevelP.basisData W p)
    (LevelP.isLevelPStructure_basisData W p)

p2m_export "ModularCurve.KatzLevelPForm" "tauto"

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_eq_of_classifying {A' : Type u} [CommRing A'] [Algebra R A'] (f : A →ₐ[R] A')
    (hW' : IsUnit (W.map (f : A →+* A')).Δ) (D : LevelPData A')
    (hD : IsLevelPStructure (W.map (f : A →+* A')) p D)
    (ψ : LevelP.BasisRing W p →+* A')
    (hψ : ψ.comp (LevelP.BasisRing.ofBase W p) = (f : A →+* A'))
    (hψD : (LevelP.basisData W p).map ψ = D) :
    F.toFun (W.map (f : A →+* A')) hW' D hD = ψ (F.tauto W hW) := by
  letI : Algebra A' A' := Algebra.id A'
  have hψ' : ψ.comp (algebraMap A (LevelP.BasisRing W p)) = (algebraMap A' A').comp (f : A →+* A') := by
    rw [LevelP.BasisRing.algebraMap_eq, hψ, Algebra.algebraMap_self, RingHom.id_comp]
  let ψₐ : LevelP.BasisRing W p →ₐ[R] A' := algHomOfComp ψ f hψ'
  have hcurve : (LevelP.basisCurve W p).map (ψₐ : LevelP.BasisRing W p →+* A') = W.map (f : A →+* A') := by
    rw [algHomOfComp_coe, LevelP.basisCurve, WeierstrassCurve.map_map, hψ]
  have hdata : (LevelP.basisData W p).map (ψₐ : LevelP.BasisRing W p →+* A') = D := by
    rw [algHomOfComp_coe, hψD]
  have h := F.map_toFun ψₐ (LevelP.basisCurve W p) (LevelP.isUnit_Δ_basisCurve W p hW)
    (hcurve ▸ hW') (LevelP.basisData W p) (LevelP.isLevelPStructure_basisData W p)
    (by rw [hcurve, hdata]; exact hD)
  rw [F.toFun_congr hcurve.symm hW' (hcurve ▸ hW') hdata.symm hD (by rw [hcurve, hdata]; exact hD)]
  exact h

p2m_export "ModularCurve.KatzLevelPForm" "toFun_eq_of_classifying"

section walk

variable [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
include hp2 hp

open _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP in

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_data₁_eq_toFun_data₂_T3 (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant)
    [Algebra R (T3 W p)] (hW3 : IsUnit (T3.curve W p).Δ) :
    F.toFun (T3.curve W p) hW3 ((T2.data₁ W p).map (T3.ofT2 W p))
        ((T2.isLevelPStructure_data₁ W p).map (T3.ofT2 W p)) =
      F.toFun (T3.curve W p) hW3 ((T2.data₂ W p).map (T3.ofT2 W p))
        ((T2.isLevelPStructure_data₂ W p).map (T3.ofT2 W p)) := by
  have hp3 : 1 ≤ (p - 1) / 2 := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hXQ1 := T3.isLevelPStructure_XQ1 W p
  have hQ2X := T3.isLevelPStructure_Q2X W p
  have hL1 := (T2.isLevelPStructure_data₁ W p).map (T3.ofT2 W p)
  have hL2 := (T2.isLevelPStructure_data₂ W p).map (T3.ofT2 W p)

  have e1 := h1 (T3.curve W p) hW3 ((T2.data₁ W p).map (T3.ofT2 W p)) (T3.XQ1 W p) hL1 hXQ1
    (inLine_self (T3.curve W p) hp3 _)

  have e2 : F.toFun (T3.curve W p) hW3 (T3.XQ1 W p) hXQ1 =
      F.toFun (T3.curve W p) hW3 (T3.XQ1 W p).swap hXQ1.swap :=
    (h2 (T3.curve W p) hW3 (T3.XQ1 W p).swap hXQ1.swap)

  have e3 := h1 (T3.curve W p) hW3 (T3.XQ1 W p).swap (T3.Q2X W p) hXQ1.swap hQ2X
    (inLine_self (T3.curve W p) hp3 _)

  have e4 := h2 (T3.curve W p) hW3 (T3.Q2X W p) hQ2X

  have e5 := h1 (T3.curve W p) hW3 ((T2.data₂ W p).map (T3.ofT2 W p)) (T3.Q2X W p).swap hL2
    hQ2X.swap (inLine_self (T3.curve W p) hp3 _)
  rw [← e1, e2, ← e3, ← e4, e5]

p2m_export "ModularCurve.KatzLevelPForm" "toFun_data₁_eq_toFun_data₂_T3"
omit hp2 hp in
theorem _root_.P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3.isUnit_Δ_curve (hW : IsUnit W.Δ) : IsUnit (LevelP.T3.curve W p).Δ := by
  rw [LevelP.T3.curve, WeierstrassCurve.map_Δ]; exact (LevelP.T2.isUnit_Δ_curve W p hW).map _

scoped instance instAlgebraT3 : Algebra R (LevelP.T3 W p) :=
  ((algebraMap (LevelP.T2 W p) (LevelP.T3 W p)).comp (algebraMap R (LevelP.T2 W p))).toAlgebra

def T3ι : LevelP.T2 W p →ₐ[R] LevelP.T3 W p :=
  { LevelP.T3.ofT2 W p with commutes' := fun _ => rfl }

open _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP in

private theorem _root_.ModularCurve.KatzLevelPForm.toFun_data₁_eq_toFun_data₂ (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    F.toFun (T2.curve W p) (T2.isUnit_Δ_curve W p hW) (T2.data₁ W p) (T2.isLevelPStructure_data₁ W p) =
      F.toFun (T2.curve W p) (T2.isUnit_Δ_curve W p hW) (T2.data₂ W p)
        (T2.isLevelPStructure_data₂ W p) := by
  have hpA : IsUnit (p : A) := by simpa using hp.map (algebraMap R A)
  apply T3.ofT2_injective W p hp2 hpA hW
  let ι : T2 W p →ₐ[R] T3 W p := T3ι (R := R) W (p := p)
  have hι : (ι : T2 W p →+* T3 W p) = T3.ofT2 W p := RingHom.ext fun _ => rfl
  have hW3 := T3.isUnit_Δ_curve W (p := p) hW
  have h₁ := F.map_toFun ι (T2.curve W p) (T2.isUnit_Δ_curve W p hW) hW3 (T2.data₁ W p)
    (T2.isLevelPStructure_data₁ W p) ((T2.isLevelPStructure_data₁ W p).map (T3.ofT2 W p))
  have h₂ := F.map_toFun ι (T2.curve W p) (T2.isUnit_Δ_curve W p hW) hW3 (T2.data₂ W p)
    (T2.isLevelPStructure_data₂ W p) ((T2.isLevelPStructure_data₂ W p).map (T3.ofT2 W p))
  rw [← hι]
  change ι _ = ι _
  rw [← h₁, ← h₂]
  exact F.toFun_data₁_eq_toFun_data₂_T3 W hp2 hp h1 h2 hW3

p2m_export "ModularCurve.KatzLevelPForm" "toFun_data₁_eq_toFun_data₂"

def includeRightR : LevelP.BasisRing W p →ₐ[R] LevelP.T2 W p :=
  (Algebra.TensorProduct.includeRight : LevelP.BasisRing W p →ₐ[A] LevelP.T2 W p).restrictScalars R

open _root_.ModularCurve.LevelP _root_.P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP in

private theorem _root_.ModularCurve.KatzLevelPForm.tauto_tmul_one_eq_one_tmul_tauto (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    F.tauto W hW ⊗ₜ[A] (1 : BasisRing W p) = (1 : BasisRing W p) ⊗ₜ[A] F.tauto W hW := by
  let iL : BasisRing W p →ₐ[R] T2 W p := Algebra.TensorProduct.includeLeft
  let iR : BasisRing W p →ₐ[R] T2 W p := includeRightR (R := R) W (p := p)
  have hiL : (iL : BasisRing W p →+* T2 W p) = Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun _ => rfl
  have hiR : (iR : BasisRing W p →+* T2 W p) =
      ((Algebra.TensorProduct.includeRight : BasisRing W p →ₐ[A] T2 W p) : BasisRing W p →+* T2 W p) :=
    RingHom.ext fun _ => rfl
  have hcL : (basisCurve W p).map (iL : BasisRing W p →+* T2 W p) = T2.curve W p := by
    rw [hiL, ← T2.curve_eq_map_left]
  have hcR : (basisCurve W p).map (iR : BasisRing W p →+* T2 W p) = T2.curve W p := by
    rw [hiR, ← T2.curve_eq_map_right]
  have hL := F.map_toFun iL (basisCurve W p) (isUnit_Δ_basisCurve W p hW) (hcL ▸ T2.isUnit_Δ_curve W p hW)
    (basisData W p) (isLevelPStructure_basisData W p) ((isLevelPStructure_basisData W p).map _)
  have hR := F.map_toFun iR (basisCurve W p) (isUnit_Δ_basisCurve W p hW) (hcR ▸ T2.isUnit_Δ_curve W p hW)
    (basisData W p) (isLevelPStructure_basisData W p) ((isLevelPStructure_basisData W p).map _)
  have key := F.toFun_data₁_eq_toFun_data₂ W hW hp2 hp h1 h2
  rw [F.toFun_congr (hcL.symm) (T2.isUnit_Δ_curve W p hW) (hcL ▸ T2.isUnit_Δ_curve W p hW)
      (show T2.data₁ W p = (basisData W p).map (iL : BasisRing W p →+* T2 W p) by rw [hiL]; rfl)
      (T2.isLevelPStructure_data₁ W p) ((isLevelPStructure_basisData W p).map _),
    F.toFun_congr (hcR.symm) (T2.isUnit_Δ_curve W p hW) (hcR ▸ T2.isUnit_Δ_curve W p hW)
      (show T2.data₂ W p = (basisData W p).map (iR : BasisRing W p →+* T2 W p) by rw [hiR]; rfl)
      (T2.isLevelPStructure_data₂ W p) ((isLevelPStructure_basisData W p).map _), hL, hR] at key

  exact key

p2m_export "ModularCurve.KatzLevelPForm" "tauto_tmul_one_eq_one_tmul_tauto"

private theorem _root_.ModularCurve.KatzLevelPForm.existsUnique_algebraMap_eq_tauto (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    ∃! a : A, algebraMap A (LevelP.BasisRing W p) a = F.tauto W hW := by
  have hpA : IsUnit (p : A) := by simpa using hp.map (algebraMap R A)
  haveI := LevelP.BasisRing.faithfullyFlat W p hp2 hpA hW
  obtain ⟨a, ha⟩ := Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    (F.tauto_tmul_one_eq_one_tmul_tauto W hW hp2 hp h1 h2)
  exact ⟨a, ha, fun b hb => FaithfulSMul.algebraMap_injective A (LevelP.BasisRing W p) (hb.trans ha.symm)⟩

p2m_export "ModularCurve.KatzLevelPForm" "existsUnique_algebraMap_eq_tauto"
end walk
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve"

end testObject
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve"

end KatzLevelPForm
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

namespace ModularCurve
p2m_export "ModularCurve" "indepElt inLine_self indepElt_map LevelPData LevelPData.map LevelPData.variableChange IsLevelPStructure KatzLevelPForm KatzLevelPForm.ext LevelP.BasisRing LevelP.BasisRing.ofBase LevelP.BasisRing.algebraMap_eq LevelP.basisCurve LevelP.isUnit_Δ_basisCurve LevelP.basisData LevelP.isLevelPStructure_basisData LevelP.BasisRing.exists_ringHom_basisData_map_eq exists_torsionPt_indepElt_ne_zero LevelP.BasisRing.faithfullyFlat LevelPData.map_variableChange LevelP.T3.isUnit_Δ_curve"
p2m_open "ModularCurve"

open scoped TensorProduct
open WeierstrassCurve Polynomial

namespace KatzLevelPForm
p2m_export "ModularCurve.KatzLevelPForm" "ext mul swap DependsOnlyOnSndLine SwapInvariant toFun map_toFun toFun_variableChange"
p2m_open "ModularCurve.KatzLevelPForm"

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))

section descent

variable (F : KatzLevelPForm R p k) (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant)
include hp2 hp h1 h2

private noncomputable def _root_.ModularCurve.KatzLevelPForm.descendFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : A :=
  (F.existsUnique_algebraMap_eq_tauto W hW hp2 hp h1 h2).exists.choose

p2m_export "ModularCurve.KatzLevelPForm" "descendFun"
private theorem _root_.ModularCurve.KatzLevelPForm.algebraMap_descendFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) :
    algebraMap A (LevelP.BasisRing W p) (F.descendFun hp2 hp h1 h2 W hW) = F.tauto W hW :=
  (F.existsUnique_algebraMap_eq_tauto W hW hp2 hp h1 h2).exists.choose_spec

p2m_export "ModularCurve.KatzLevelPForm" "algebraMap_descendFun"
private theorem _root_.ModularCurve.KatzLevelPForm.eq_descendFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) {a : A} (ha : algebraMap A (LevelP.BasisRing W p) a = F.tauto W hW) :
    a = F.descendFun hp2 hp h1 h2 W hW :=
  (F.existsUnique_algebraMap_eq_tauto W hW hp2 hp h1 h2).unique ha (F.algebraMap_descendFun hp2 hp h1 h2 W hW)

p2m_export "ModularCurve.KatzLevelPForm" "eq_descendFun"
omit h1 h2 in
private theorem _root_.ModularCurve.KatzLevelPForm.algebraMap_injective {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : Function.Injective (algebraMap A (LevelP.BasisRing W p)) := by
  have hpA : IsUnit (p : A) := by simpa using hp.map (algebraMap R A)
  haveI := LevelP.BasisRing.faithfullyFlat W p hp2 hpA hW
  exact FaithfulSMul.algebraMap_injective A (LevelP.BasisRing W p)

p2m_export "ModularCurve.KatzLevelPForm" "algebraMap_injective"

private theorem _root_.ModularCurve.KatzLevelPForm.descendFun_map {A A' : Type u} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
    (f : A →ₐ[R] A') (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW' : IsUnit (W.map (f : A →+* A')).Δ) :
    F.descendFun hp2 hp h1 h2 (W.map (f : A →+* A')) hW' = f (F.descendFun hp2 hp h1 h2 W hW) := by
  symm
  apply F.eq_descendFun hp2 hp h1 h2

  set T' := LevelP.BasisRing (W.map (f : A →+* A')) p
  let f' : A →ₐ[R] T' := (IsScalarTower.toAlgHom R A' T').comp f
  have hf' : (f' : A →+* T') = (algebraMap A' T').comp (f : A →+* A') := rfl
  have hcurve : LevelP.basisCurve (W.map (f : A →+* A')) p = W.map (f' : A →+* T') := by
    rw [hf', LevelP.basisCurve, WeierstrassCurve.map_map, LevelP.BasisRing.algebraMap_eq]
  have hD : IsLevelPStructure (W.map (f' : A →+* T')) p (LevelP.basisData (W.map (f : A →+* A')) p) := by
    rw [← hcurve]; exact LevelP.isLevelPStructure_basisData _ p
  obtain ⟨θ, hθ, hθD⟩ := LevelP.BasisRing.exists_ringHom_basisData_map_eq W p (f' : A →+* T')
    (LevelP.basisData (W.map (f : A →+* A')) p) hD
  have hWf' : IsUnit (W.map (f' : A →+* T')).Δ := by
    rw [← hcurve]; exact LevelP.isUnit_Δ_basisCurve _ p hW'
  have key := F.toFun_eq_of_classifying W hW f' hWf' _ hD θ hθ hθD

  rw [F.toFun_congr hcurve.symm hWf' (LevelP.isUnit_Δ_basisCurve _ p hW') rfl hD
    (LevelP.isLevelPStructure_basisData _ p)] at key
  change F.tauto (W.map (f : A →+* A')) hW' = θ (F.tauto W hW) at key
  rw [key, ← F.algebraMap_descendFun hp2 hp h1 h2 W hW]
  change algebraMap A' T' (f _) = θ (LevelP.BasisRing.ofBase W p _)
  rw [← RingHom.comp_apply θ, hθ, hf', RingHom.comp_apply]
  rfl

p2m_export "ModularCurve.KatzLevelPForm" "descendFun_map"

omit hp2 hp h1 h2 in
private theorem _root_.WeierstrassCurve.VariableChange.coe_map_u_inv_zpow {A B : Type*} [CommRing A]
    [CommRing B] (φ : A →+* B) (C : VariableChange A) (k : ℤ) :
    (((C.map φ).u⁻¹ ^ k : Bˣ) : B) = φ ((C.u⁻¹ ^ k : Aˣ) : A) := by
  have : ((C.map φ).u⁻¹ ^ k : Bˣ) = Units.map (φ : A →* B) (C.u⁻¹ ^ k) := by
    rw [map_zpow, map_inv]; rfl
  rw [this, Units.coe_map, MonoidHom.coe_coe]

p2m_alias "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.WeierstrassCurve.VariableChange.coe_map_u_inv_zpow" "WeierstrassCurve.VariableChange.coe_map_u_inv_zpow"
private theorem _root_.ModularCurve.KatzLevelPForm.descendFun_variableChange {A : Type u} [CommRing A] [Algebra R A] (C : VariableChange A)
    (W : WeierstrassCurve A) (hW : IsUnit W.Δ) (hW₁ : IsUnit (C • W).Δ) :
    F.descendFun hp2 hp h1 h2 (C • W) hW₁ = ((C.u⁻¹ ^ k : Aˣ) : A) * F.descendFun hp2 hp h1 h2 W hW := by
  set T := LevelP.BasisRing W p
  let φ : A →+* T := algebraMap A T
  let CT : VariableChange T := C.map φ

  let D₁ : LevelPData T := (LevelP.basisData W p).variableChange CT
  have hD₁ : IsLevelPStructure (CT • LevelP.basisCurve W p) p D₁ :=
    (LevelP.isLevelPStructure_basisData W p).variableChange CT
  have hcurve : CT • LevelP.basisCurve W p = (C • W).map φ := by
    rw [LevelP.basisCurve, ← LevelP.BasisRing.algebraMap_eq]
    exact WeierstrassCurve.map_variableChange W C φ
  have hD₁' : IsLevelPStructure ((C • W).map φ) p D₁ := hcurve ▸ hD₁
  obtain ⟨θ, hθ, hθD⟩ := LevelP.BasisRing.exists_ringHom_basisData_map_eq (C • W) p φ D₁ hD₁'

  let fφ : A →ₐ[R] T := IsScalarTower.toAlgHom R A T
  have hfφ : (fφ : A →+* T) = φ := rfl
  have hWφ : IsUnit ((C • W).map (fφ : A →+* T)).Δ := by
    rw [hfφ, WeierstrassCurve.map_Δ]; exact hW₁.map _
  have key := F.toFun_eq_of_classifying (C • W) hW₁ fφ hWφ D₁ (hfφ ▸ hD₁') θ hθ hθD

  have hCTW : IsUnit (CT • LevelP.basisCurve W p).Δ := by rw [hcurve, WeierstrassCurve.map_Δ]; exact hW₁.map _
  rw [F.toFun_congr (show (C • W).map (fφ : A →+* T) = CT • LevelP.basisCurve W p by rw [hfφ, hcurve])
    hWφ hCTW rfl (hfφ ▸ hD₁') hD₁] at key
  rw [F.toFun_variableChange CT (LevelP.basisCurve W p) (LevelP.isUnit_Δ_basisCurve W p hW) hCTW
    (LevelP.basisData W p) (LevelP.isLevelPStructure_basisData W p) hD₁] at key

  apply algebraMap_injective hp2 hp W hW
  rw [map_mul, F.algebraMap_descendFun hp2 hp h1 h2 W hW,
    ← WeierstrassCurve.VariableChange.coe_map_u_inv_zpow φ C k]
  change ((CT.u⁻¹ ^ k : Tˣ) : T) * F.tauto W hW = θ (F.tauto (C • W) hW₁) at key
  change _ = ((CT.u⁻¹ ^ k : Tˣ) : T) * F.tauto W hW
  rw [key, ← F.algebraMap_descendFun hp2 hp h1 h2 (C • W) hW₁]
  change _ = θ (LevelP.BasisRing.ofBase (C • W) p _)
  rw [← RingHom.comp_apply θ, hθ]

p2m_export "ModularCurve.KatzLevelPForm" "descendFun_variableChange"

private noncomputable def _root_.ModularCurve.KatzLevelPForm.descend : KatzModularForm R k where
  toFun A _ _ W hW := F.descendFun hp2 hp h1 h2 W hW
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    exact F.descendFun_map hp2 hp h1 h2 f W hW hW'
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    exact F.descendFun_variableChange hp2 hp h1 h2 C W hW hW'

p2m_export "ModularCurve.KatzLevelPForm" "descend"
@[scoped simp] theorem descend_toFun {A : Type u} [CommRing A] [Algebra R A] (W : WeierstrassCurve A)
    (hW : IsUnit W.Δ) : (F.descend hp2 hp h1 h2).toFun W hW = F.descendFun hp2 hp h1 h2 W hW := rfl

private theorem _root_.ModularCurve.KatzLevelPForm.pullbackLevelP_descend : (F.descend hp2 hp h1 h2).pullbackLevelP p = F := by
  refine KatzLevelPForm.ext fun A _ _ W hW D hD => ?_
  rw [KatzModularForm.pullbackLevelP_toFun, descend_toFun]
  symm

  have hD' : IsLevelPStructure (W.map ((AlgHom.id R A : A →ₐ[R] A) : A →+* A)) p D := by
    rw [show ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = RingHom.id A from rfl, WeierstrassCurve.map_id]
    exact hD
  obtain ⟨ψ, hψ, hψD⟩ := LevelP.BasisRing.exists_ringHom_basisData_map_eq W p
    ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) D hD'
  have hWid : IsUnit (W.map ((AlgHom.id R A : A →ₐ[R] A) : A →+* A)).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact hW.map _
  have key := F.toFun_eq_of_classifying W hW (AlgHom.id R A) hWid D hD' ψ hψ hψD
  rw [F.toFun_congr (show W.map ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = W by
      rw [show ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = RingHom.id A from rfl, WeierstrassCurve.map_id])
    hWid hW rfl hD' hD] at key
  rw [key, ← F.algebraMap_descendFun hp2 hp h1 h2 W hW]
  change ψ (LevelP.BasisRing.ofBase W p _) = _
  rw [← RingHom.comp_apply ψ, hψ]
  rfl

p2m_export "ModularCurve.KatzLevelPForm" "pullbackLevelP_descend"
end descent
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

section uniqueness

include hp2 hp

omit [Fact p.Prime] hp2 hp in
private theorem _root_.KatzModularForm.toFun_congr' (g : KatzModularForm R k) {A : Type u} [CommRing A]
    [Algebra R A] {W W' : WeierstrassCurve A} (h : W = W') (hW : IsUnit W.Δ) (hW' : IsUnit W'.Δ) :
    g.toFun W hW = g.toFun W' hW' := by
  subst h; rfl

p2m_alias "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.KatzModularForm.toFun_congr'" "KatzModularForm.toFun_congr'"
theorem pullbackLevelP_injective :
    Function.Injective (fun g : KatzModularForm R k => g.pullbackLevelP p) := by
  intro g g' hgg'
  refine KatzModularForm.ext fun A _ _ W hW => ?_
  apply algebraMap_injective hp2 hp W hW
  set T := LevelP.BasisRing W p
  let f : A →ₐ[R] T := IsScalarTower.toAlgHom R A T
  have hcurve : W.map (f : A →+* T) = LevelP.basisCurve W p := by
    rw [LevelP.basisCurve, ← LevelP.BasisRing.algebraMap_eq]; rfl
  have hWT : IsUnit (W.map (f : A →+* T)).Δ := by rw [hcurve]; exact LevelP.isUnit_Δ_basisCurve W p hW
  have e := congrArg (fun G : KatzLevelPForm R p k => G.toFun (LevelP.basisCurve W p)
    (LevelP.isUnit_Δ_basisCurve W p hW) (LevelP.basisData W p) (LevelP.isLevelPStructure_basisData W p)) hgg'
  simp only [KatzModularForm.pullbackLevelP_toFun] at e
  have hg := g.map_toFun f W hW hWT
  have hg' := g'.map_toFun f W hW hWT
  rw [g.toFun_congr' hcurve hWT (LevelP.isUnit_Δ_basisCurve W p hW)] at hg
  rw [g'.toFun_congr' hcurve hWT (LevelP.isUnit_Δ_basisCurve W p hW)] at hg'
  change algebraMap A T (g.toFun W hW) = algebraMap A T (g'.toFun W hW)
  have hf : ∀ a, (f : A →+* T) a = algebraMap A T a := fun _ => rfl
  rw [← hf, ← hf]
  change f _ = f _
  rw [← hg, ← hg', e]

end uniqueness
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

include hp2 hp in

theorem existsUnique_pullbackLevelP_eq_of_swapInvariant' (F : KatzLevelPForm R p k)
    (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    ∃! g : KatzModularForm R k, g.pullbackLevelP p = F :=
  ⟨F.descend hp2 hp h1 h2, F.pullbackLevelP_descend hp2 hp h1 h2, fun g hg =>
    pullbackLevelP_injective (k := k) hp2 hp (hg.trans (F.pullbackLevelP_descend hp2 hp h1 h2).symm)⟩

end KatzLevelPForm
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

end
p2m_reactivate "P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP.T3 P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.LevelP P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant.ModularCurve.KatzLevelPForm"

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R)) {k : ℤ}
    (F : ModularCurve.KatzLevelPForm R p k) (h1 : F.DependsOnlyOnSndLine) (h2 : F.SwapInvariant) :
    ∃! g : KatzModularForm R k, g.pullbackLevelP p = F :=
  ModularCurve.KatzLevelPForm.existsUnique_pullbackLevelP_eq_of_swapInvariant' hp2 hp F h1 h2

end S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant
end P2MW
export P2MW.S_ModularCurve_KatzLevelPForm_existsUnique_pullbackLevelP_eq_of_swapInvariant (solution)
