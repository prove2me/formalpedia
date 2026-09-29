-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.exists_natural_relabel_levelPData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/14a1c5aa-a217-5ff8-a623-a6b8965bbefb

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_ModularCurve_KatzLevelPClassifyingMaps
import Theorems.Thm_ModularCurve_LevelP_isReduced_univBasisRing
import Theorems.Thm_ModularCurve_LevelP_exists_levelPData_map_eq_relabel_univData
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_variableChange
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq
import Theorems.Thm_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace KatzRelabelAssembly

open ModularCurve ModularCurve.LevelP ModularCurve.LevelRelabelling WeierstrassCurve

section RingLemmas

variable {T : Type} [CommRing T]

theorem eq_of_forall_field [IsReduced T] {a b : T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), φ a = φ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsReduced.eq_zero
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro P hP
  haveI : P.IsPrime := hP
  have h1 := h (FractionRing (T ⧸ P)) ((algebraMap (T ⧸ P) (FractionRing (T ⧸ P))).comp (Ideal.Quotient.mk P))
  simp only [RingHom.comp_apply] at h1
  have h2 := IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P)) h1
  rw [Ideal.Quotient.eq] at h2
  exact h2

theorem isUnit_of_forall_field {a : T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), φ a ≠ 0) : IsUnit a := by
  by_contra ha
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (Ideal.span_singleton_ne_top ha)
  letI := Ideal.Quotient.field M
  exact h (T ⧸ M) (Ideal.Quotient.mk M) (Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.subset_span rfl)))

theorem levelPData_eq_of_forall_field [IsReduced T] {D D' : LevelPData T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), D.map φ = D'.map φ) : D = D' := by
  refine LevelPData.ext ?_ ?_ ?_ ?_
  · exact eq_of_forall_field fun F _ φ => congrArg LevelPData.xP (h F φ)
  · exact eq_of_forall_field fun F _ φ => congrArg LevelPData.yP (h F φ)
  · exact eq_of_forall_field fun F _ φ => congrArg LevelPData.xQ (h F φ)
  · exact eq_of_forall_field fun F _ φ => congrArg LevelPData.yQ (h F φ)

theorem equation_of_forall_field [IsReduced T] (W : WeierstrassCurve T) {x y : T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), (W.map φ).toAffine.Equation (φ x) (φ y)) :
    W.toAffine.Equation x y := by
  change W.toAffine.polynomial.evalEval x y = 0
  refine eq_of_forall_field fun F _ φ => ?_
  have := h F φ
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.map_polynomial,
    Polynomial.map_mapRingHom_evalEval] at this
  rw [this, map_zero]

theorem preΨ_of_forall_field [IsReduced T] (W : WeierstrassCurve T) (n : ℕ) {x : T}
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), ((W.map φ).preΨ n).eval (φ x) = 0) :
    (W.preΨ n).eval x = 0 := by
  refine eq_of_forall_field fun F _ φ => ?_
  have := h F φ
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at this
  rw [this, map_zero]

theorem isLevelPStructure_of_forall_field [IsReduced T] (W : WeierstrassCurve T) (n : ℕ) (D : LevelPData T)
    (h : ∀ (F : Type) [Field F] (φ : T →+* F), IsLevelPStructure (W.map φ) n (D.map φ)) :
    IsLevelPStructure W n D where
  equation_P := equation_of_forall_field W fun F _ φ => (h F φ).equation_P
  equation_Q := equation_of_forall_field W fun F _ φ => (h F φ).equation_Q
  preΨ_P := preΨ_of_forall_field W n fun F _ φ => (h F φ).preΨ_P
  preΨ_Q := preΨ_of_forall_field W n fun F _ φ => (h F φ).preΨ_Q
  isUnit_indepElt_PQ := isUnit_of_forall_field fun F _ φ => by
    rw [← indepElt_map]; exact (h F φ).isUnit_indepElt_PQ.ne_zero
  isUnit_indepElt_QP := isUnit_of_forall_field fun F _ φ => by
    rw [← indepElt_map]; exact (h F φ).isUnit_indepElt_QP.ne_zero

end RingLemmas

private theorem _root_.KatzRelabelAssembly.map_variableChange {T T' : Type*} [CommRing T] [CommRing T'] (f : T →+* T')
    (C : VariableChange T) (D : LevelPData T) :
    (D.variableChange C).map f = (D.map f).variableChange (C.map f) := by
  refine LevelPData.ext ?_ ?_ ?_ ?_ <;>
    simp [LevelPData.variableChange, LevelPData.map, VariableChange.map, Units.coe_map_inv]

p2m_export "KatzRelabelAssembly" "map_variableChange"

section Univ

set_option linter.unusedSectionVars false

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)

def γOf (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) := g.map (Int.castRingHom (ZMod ℓ))

def liftMat (γ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) ℤ := γ.map fun z => (z.val : ℤ)

theorem γOf_liftMat (γ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : γOf ℓ (liftMat ℓ γ) = γ := by
  ext i j
  simp [γOf, liftMat, Matrix.map_apply]

theorem γOf_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) : γOf ℓ (g * h) = γOf ℓ g * γOf ℓ h := by
  unfold γOf; exact Matrix.map_mul

theorem γOf_one : γOf ℓ 1 = 1 := by
  simp [γOf]

include hℓ3 in
theorem hℓ2 : ℓ ≠ 2 := by omega

theorem isUnit_ℓΔ_univ : IsUnit (((ℓ : ℕ) : UnivBasisRing ℓ) * (univCurveT ℓ).Δ) :=
  (isUnit_natCast_univBasisRing ℓ).mul (isUnit_Δ_univCurveT ℓ)

scoped instance isReduced_univ [h3 : Fact (3 ≤ ℓ)] : IsReduced (UnivBasisRing ℓ) :=
  ModularCurve.LevelP.isReduced_univBasisRing ℓ (hℓ2 ℓ h3.out)

scoped instance isReduced_vcRing [Fact (3 ≤ ℓ)] : IsReduced (VCRing ℓ) :=
  (inferInstance : IsReduced (Localization.Away (MvPolynomial.X 0 : VCPoly ℓ)))

def R (γ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) : LevelPData (UnivBasisRing ℓ) :=
  if hγ : IsUnit γ.det then
    Classical.choose (ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData.{0} ℓ hℓ3 (liftMat ℓ γ)
      (by rw [← γOf, γOf_liftMat]; exact hγ))
  else univData ℓ

theorem field_data {F : Type} [Field F] (φ : UnivBasisRing ℓ →+* F) :
    (ℓ : F) ≠ 0 ∧ IsUnit ((univCurveT ℓ).map φ).Δ ∧
      IsLevelPStructure ((univCurveT ℓ).map φ) ℓ ((univData ℓ).map φ) := by
  refine ⟨?_, ?_, (isLevelPStructure_univData ℓ).map φ⟩
  · have := (isUnit_natCast_univBasisRing ℓ).map φ
    rw [map_natCast] at this
    exact this.ne_zero
  · rw [WeierstrassCurve.map_Δ]; exact (isUnit_Δ_univCurveT ℓ).map φ

include hℓ3 in

theorem R_map_field {γ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : γOf ℓ g = γ)
    (hγ : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    {F : Type} [Field F] (φ : UnivBasisRing ℓ →+* F) :
    (R ℓ hℓ3 γ).map φ = LevelPData.relabel ((univCurveT ℓ).map φ) g ((univData ℓ).map φ) := by
  have hγ' : IsUnit γ.det := by rw [← hg]; exact hγ
  rw [R, dif_pos hγ']
  have hspec := Classical.choose_spec
    (ModularCurve.LevelP.exists_levelPData_map_eq_relabel_univData.{0} ℓ hℓ3 (liftMat ℓ γ)
      (by rw [← γOf, γOf_liftMat]; exact hγ')) F φ
  rw [hspec]
  obtain ⟨-, hΔ, hD⟩ := field_data ℓ φ
  refine (ModularCurve.IsLevelPStructure.relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq ℓ hℓ3
    _ hΔ _ hD).2.2 (liftMat ℓ γ) g ?_
  change γOf ℓ (liftMat ℓ γ) = γOf ℓ g
  rw [γOf_liftMat, hg]

include hℓ3 in

theorem isLevelPStructure_R [Fact (3 ≤ ℓ)] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) :
    IsLevelPStructure (univCurveT ℓ) ℓ (R ℓ hℓ3 (γOf ℓ g)) := by
  refine isLevelPStructure_of_forall_field _ _ _ fun F _ φ => ?_
  rw [R_map_field ℓ hℓ3 g rfl hg φ]
  obtain ⟨hℓF, hΔ, hD⟩ := field_data ℓ φ
  have hg' : IsUnit ((g.det : ℤ) : ZMod ℓ) := by
    have := hg
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast] at this
  exact ModularCurve.IsLevelPStructure.relabel_of_isUnit_det ℓ hℓ3 hℓF _ hΔ _ hD g hg'

include hℓ3 in

theorem R_one [Fact (3 ≤ ℓ)] : R ℓ hℓ3 1 = univData ℓ := by
  refine levelPData_eq_of_forall_field fun F _ φ => ?_
  have h1 : IsUnit ((1 : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod ℓ))).det := by
    rw [← γOf, γOf_one, Matrix.det_one]; exact isUnit_one
  rw [R_map_field ℓ hℓ3 1 (γOf_one ℓ) h1 φ]
  obtain ⟨-, hΔ, hD⟩ := field_data ℓ φ
  exact (ModularCurve.IsLevelPStructure.relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq ℓ hℓ3
    _ hΔ _ hD).2.1

include hℓ3 in

theorem R_map_classify_R [Fact (3 ≤ ℓ)] (g h : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (hh : IsUnit (h.map (Int.castRingHom (ZMod ℓ))).det) :
    (R ℓ hℓ3 (γOf ℓ h)).map
        (UnivBasisRing.classify ℓ (univCurveT ℓ) (isUnit_ℓΔ_univ ℓ) (R ℓ hℓ3 (γOf ℓ g))
          (isLevelPStructure_R ℓ hℓ3 g hg)) =
      R ℓ hℓ3 (γOf ℓ (g * h)) := by
  have hgh : IsUnit ((g * h).map (Int.castRingHom (ZMod ℓ))).det := by
    rw [Matrix.map_mul, Matrix.det_mul]; exact hg.mul hh
  refine levelPData_eq_of_forall_field fun F _ φ => ?_
  rw [LevelPData.map_map, R_map_field ℓ hℓ3 h rfl hh, ← WeierstrassCurve.map_map, univCurveT_map_classify,
    ← LevelPData.map_map, univData_map_classify, R_map_field ℓ hℓ3 g rfl hg φ,
    R_map_field ℓ hℓ3 (g * h) rfl hgh φ]
  obtain ⟨-, hΔ, hD⟩ := field_data ℓ φ
  exact (ModularCurve.IsLevelPStructure.relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq ℓ hℓ3
    _ hΔ _ hD).1 g h hg

theorem isUnit_ℓΔ_vc : IsUnit (((ℓ : ℕ) : VCRing ℓ) * (univVC ℓ • vcCurve ℓ).Δ) := by
  rw [WeierstrassCurve.variableChange_Δ, mul_left_comm]
  exact (((univVC ℓ).u⁻¹).isUnit.pow 12).mul ((isUnit_natCast_vcRing ℓ).mul (isUnit_Δ_vcCurve ℓ))

theorem isLevelPStructure_vc :
    IsLevelPStructure (univVC ℓ • vcCurve ℓ) ℓ ((vcData ℓ).variableChange (univVC ℓ)) :=
  ModularCurve.IsLevelPStructure.variableChange (isLevelPStructure_vcData ℓ) (univVC ℓ)

include hℓ3 in

theorem R_map_classify_vc [Fact (3 ≤ ℓ)] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) :
    (R ℓ hℓ3 (γOf ℓ g)).map
        (UnivBasisRing.classify ℓ (univVC ℓ • vcCurve ℓ) (isUnit_ℓΔ_vc ℓ)
          ((vcData ℓ).variableChange (univVC ℓ)) (isLevelPStructure_vc ℓ)) =
      ((R ℓ hℓ3 (γOf ℓ g)).map (VCRing.ofUniv ℓ)).variableChange (univVC ℓ) := by
  refine levelPData_eq_of_forall_field fun F _ φ => ?_
  rw [LevelPData.map_map, R_map_field ℓ hℓ3 g rfl hg, ← WeierstrassCurve.map_map, univCurveT_map_classify,
    ← LevelPData.map_map, univData_map_classify, ← WeierstrassCurve.map_variableChange, map_variableChange,
    map_variableChange, LevelPData.map_map, R_map_field ℓ hℓ3 g rfl hg]

  have hΔ : IsUnit ((vcCurve ℓ).map φ).Δ := by
    rw [WeierstrassCurve.map_Δ]; exact (isUnit_Δ_vcCurve ℓ).map φ
  have hD : IsLevelPStructure ((vcCurve ℓ).map φ) ℓ ((vcData ℓ).map φ) := (isLevelPStructure_vcData ℓ).map φ
  have e1 : (univCurveT ℓ).map (φ.comp (VCRing.ofUniv ℓ)) = (vcCurve ℓ).map φ := by
    rw [← WeierstrassCurve.map_map]; rfl
  have e2 : (univData ℓ).map (φ.comp (VCRing.ofUniv ℓ)) = (vcData ℓ).map φ := by
    rw [← LevelPData.map_map]; rfl
  rw [e1, e2]
  exact ModularCurve.IsLevelPStructure.relabel_variableChange ℓ hℓ3 _ hΔ _ hD g hg _

end Univ

section Relab

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)

def relab (T : Type) [CommRing T] (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : LevelPData T) :
    LevelPData T :=
  if h : IsUnit (((ℓ : ℕ) : T) * W.Δ) ∧ IsLevelPStructure W ℓ D then
    (R ℓ hℓ3 (γOf ℓ g)).map (UnivBasisRing.classify ℓ W h.1 D h.2)
  else D

variable {T : Type} [CommRing T]

theorem relab_of (W : WeierstrassCurve T) (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ)) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 T W g D = (R ℓ hℓ3 (γOf ℓ g)).map (UnivBasisRing.classify ℓ W hW D hD) := by
  rw [relab, dif_pos ⟨hW, hD⟩]

include hℓ3 in

theorem relab_field {F : Type} [Field F] (W : WeierstrassCurve F) (hW : IsUnit (((ℓ : ℕ) : F) * W.Δ))
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (D : LevelPData F) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 F W g D = LevelPData.relabel W g D := by
  rw [relab_of ℓ hℓ3 W hW g D hD, R_map_field ℓ hℓ3 g rfl hg, univCurveT_map_classify, univData_map_classify]

include hℓ3 in

theorem isLevelPStructure_relab [Fact (3 ≤ ℓ)] (W : WeierstrassCurve T) (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ))
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    IsLevelPStructure W ℓ (relab ℓ hℓ3 T W g D) := by
  rw [relab_of ℓ hℓ3 W hW g D hD]
  have := (isLevelPStructure_R ℓ hℓ3 g hg).map (UnivBasisRing.classify ℓ W hW D hD)
  rwa [univCurveT_map_classify] at this

theorem relab_map {T' : Type} [CommRing T'] (f : T →+* T') (W : WeierstrassCurve T)
    (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ)) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 T' (W.map f) g (D.map f) = (relab ℓ hℓ3 T W g D).map f := by
  have hW' : IsUnit (((ℓ : ℕ) : T') * (W.map f).Δ) := by
    rw [WeierstrassCurve.map_Δ, ← map_natCast f, ← map_mul]; exact hW.map f
  rw [relab_of ℓ hℓ3 W hW g D hD, relab_of ℓ hℓ3 (W.map f) hW' g (D.map f) (hD.map f), LevelPData.map_map,
    UnivBasisRing.comp_classify]

theorem relab_congr (W : WeierstrassCurve T) (g g' : Matrix (Fin 2) (Fin 2) ℤ)
    (hgg' : g.map (Int.castRingHom (ZMod ℓ)) = g'.map (Int.castRingHom (ZMod ℓ))) (D : LevelPData T) :
    relab ℓ hℓ3 T W g D = relab ℓ hℓ3 T W g' D := by
  simp only [relab, γOf, hgg']

include hℓ3 in

theorem relab_one [Fact (3 ≤ ℓ)] (W : WeierstrassCurve T) (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ))
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 T W 1 D = D := by
  rw [relab_of ℓ hℓ3 W hW 1 D hD, γOf_one, R_one, univData_map_classify]

include hℓ3 in

theorem relab_relab [Fact (3 ≤ ℓ)] (W : WeierstrassCurve T) (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ))
    (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (hh : IsUnit (h.map (Int.castRingHom (ZMod ℓ))).det)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 T W h (relab ℓ hℓ3 T W g D) = relab ℓ hℓ3 T W (g * h) D := by
  have hD₁ := isLevelPStructure_relab ℓ hℓ3 W hW g hg D hD
  rw [relab_of ℓ hℓ3 W hW h _ hD₁]
  set cl := UnivBasisRing.classify ℓ W hW D hD with hcl

  have hfac : UnivBasisRing.classify ℓ W hW (relab ℓ hℓ3 T W g D) hD₁ =
      cl.comp (UnivBasisRing.classify ℓ (univCurveT ℓ) (isUnit_ℓΔ_univ ℓ) (R ℓ hℓ3 (γOf ℓ g))
        (isLevelPStructure_R ℓ hℓ3 g hg)) := by
    refine (UnivBasisRing.eq_classify ℓ _ _ _ _ ?_ ?_).symm
    · rw [← WeierstrassCurve.map_map, univCurveT_map_classify, univCurveT_map_classify]
    · rw [← LevelPData.map_map, univData_map_classify, relab_of ℓ hℓ3 W hW g D hD]
  rw [hfac, ← LevelPData.map_map, R_map_classify_R ℓ hℓ3 g h hg hh, relab_of ℓ hℓ3 W hW (g * h) D hD]

include hℓ3 in

theorem relab_variableChange [Fact (3 ≤ ℓ)] (W : WeierstrassCurve T) (hW : IsUnit (((ℓ : ℕ) : T) * W.Δ))
    (C : VariableChange T) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D) :
    relab ℓ hℓ3 T (C • W) g (D.variableChange C) = (relab ℓ hℓ3 T W g D).variableChange C := by
  have hW' : IsUnit (((ℓ : ℕ) : T) * (C • W).Δ) := by
    rw [WeierstrassCurve.variableChange_Δ, mul_left_comm]
    exact ((C.u⁻¹).isUnit.pow 12).mul hW
  have hD' : IsLevelPStructure (C • W) ℓ (D.variableChange C) := ModularCurve.IsLevelPStructure.variableChange hD C
  rw [relab_of ℓ hℓ3 (C • W) hW' g _ hD', relab_of ℓ hℓ3 W hW g D hD]
  set cl := UnivBasisRing.classify ℓ W hW D hD with hcl
  set lam := VCRing.lift ℓ cl C with hlam

  have hfac : UnivBasisRing.classify ℓ (C • W) hW' (D.variableChange C) hD' =
      lam.comp (UnivBasisRing.classify ℓ (univVC ℓ • vcCurve ℓ) (isUnit_ℓΔ_vc ℓ)
        ((vcData ℓ).variableChange (univVC ℓ)) (isLevelPStructure_vc ℓ)) := by
    refine (UnivBasisRing.eq_classify ℓ _ _ _ _ ?_ ?_).symm
    · rw [← WeierstrassCurve.map_map, univCurveT_map_classify, ← WeierstrassCurve.map_variableChange,
        univVC_map_lift, vcCurve_map_lift, univCurveT_map_classify]
    · rw [← LevelPData.map_map, univData_map_classify, map_variableChange, univVC_map_lift, vcData_map_lift,
        univData_map_classify]
  have eRHS : (((R ℓ hℓ3 (γOf ℓ g)).map (VCRing.ofUniv ℓ)).variableChange (univVC ℓ)).map lam =
      ((R ℓ hℓ3 (γOf ℓ g)).map cl).variableChange C := by
    rw [map_variableChange, LevelPData.map_map, VCRing.lift_comp_ofUniv, univVC_map_lift]
  rw [hfac, ← LevelPData.map_map, R_map_classify_vc ℓ hℓ3 g hg, eRHS]

end Relab

theorem main (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) :
    ∃ relab : ∀ (T : Type) [CommRing T] [Algebra A T],
        WeierstrassCurve T → Matrix (Fin 2) (Fin 2) ℤ → ModularCurve.LevelPData T → ModularCurve.LevelPData T,
      (∀ (T : Type) [Field T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W g D = ModularCurve.LevelRelabelling.LevelPData.relabel W g D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          ModularCurve.IsLevelPStructure W ℓ (relab T W g D)) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
          (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T' (W.map f.toRingHom) g (D.map f.toRingHom) = (relab T W g D).map f.toRingHom) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (C : WeierstrassCurve.VariableChange T) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T (C • W) g (D.variableChange C) = (relab T W g D).variableChange C) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g g' : Matrix (Fin 2) (Fin 2) ℤ)
          (hgg' : g.map (Int.castRingHom (ZMod ℓ)) = g'.map (Int.castRingHom (ZMod ℓ)))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W g D = relab T W g' D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D), relab T W 1 D = D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g h : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (hh : IsUnit (h.map (Int.castRingHom (ZMod ℓ))).det)
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W h (relab T W g D) = relab T W (g * h) D) := by
  haveI : Fact (3 ≤ ℓ) := ⟨hℓ3⟩

  have hU : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T), IsUnit W.Δ →
      IsUnit (((ℓ : ℕ) : T) * W.Δ) := fun T _ _ W hΔ => by
    have h := hℓA.map (algebraMap A T)
    rw [map_natCast] at h
    exact h.mul hΔ
  refine ⟨fun T _ _ W g D => relab ℓ hℓ3 T W g D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ _ W hΔ g hg D hD
    exact relab_field ℓ hℓ3 W (hU T W hΔ) g hg D hD
  · intro T _ _ W hΔ g hg D hD
    exact isLevelPStructure_relab ℓ hℓ3 W (hU T W hΔ) g hg D hD
  · intro T T' _ _ _ _ f W hΔ g hg D hD
    exact relab_map ℓ hℓ3 f.toRingHom W (hU T W hΔ) g D hD
  · intro T _ _ W hΔ C g hg D hD
    exact relab_variableChange ℓ hℓ3 W (hU T W hΔ) C g hg D hD
  · intro T _ _ W hΔ g g' hgg' D hD
    exact relab_congr ℓ hℓ3 W g g' hgg' D
  · intro T _ _ W hΔ D hD
    exact relab_one ℓ hℓ3 W (hU T W hΔ) D hD
  · intro T _ _ W hΔ g h hg hh D hD
    exact relab_relab ℓ hℓ3 W (hU T W hΔ) g h hg hh D hD

end KatzRelabelAssembly
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData.KatzRelabelAssembly"

end
p2m_reactivate "P2MW.S_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData.KatzRelabelAssembly"

theorem solution
    (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) :
    ∃ relab : ∀ (T : Type) [CommRing T] [Algebra A T],
        WeierstrassCurve T → Matrix (Fin 2) (Fin 2) ℤ → ModularCurve.LevelPData T → ModularCurve.LevelPData T,

      (∀ (T : Type) [Field T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W g D = ModularCurve.LevelRelabelling.LevelPData.relabel W g D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          ModularCurve.IsLevelPStructure W ℓ (relab T W g D)) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
          (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T' (W.map f.toRingHom) g (D.map f.toRingHom) = (relab T W g D).map f.toRingHom) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
          (C : WeierstrassCurve.VariableChange T) (g : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T (C • W) g (D.variableChange C) = (relab T W g D).variableChange C) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g g' : Matrix (Fin 2) (Fin 2) ℤ)
          (hgg' : g.map (Int.castRingHom (ZMod ℓ)) = g'.map (Int.castRingHom (ZMod ℓ)))
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W g D = relab T W g' D) ∧

      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData T)
          (hD : ModularCurve.IsLevelPStructure W ℓ D), relab T W 1 D = D) ∧
      (∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (g h : Matrix (Fin 2) (Fin 2) ℤ)
          (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det) (hh : IsUnit (h.map (Int.castRingHom (ZMod ℓ))).det)
          (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D),
          relab T W h (relab T W g D) = relab T W (g * h) D) :=
  KatzRelabelAssembly.main A ℓ hℓ3 hℓA

end S_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData (solution)
