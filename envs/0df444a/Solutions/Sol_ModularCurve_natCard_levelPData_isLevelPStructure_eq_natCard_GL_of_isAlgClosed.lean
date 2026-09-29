-- Prove2me | solution 1 for ModularCurve.natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e7518511-88e8-55aa-b034-ac867669be46

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace KatzCountAux

theorem exists_eq_some {F : Type*} [CommRing F] {W : WeierstrassCurve F} (P : W.toAffine.Point) (hP : P ≠ 0) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y), P = .some x y h := by
  rcases P with _ | @⟨x, y, h⟩
  · exact absurd rfl hP
  · exact ⟨_, _, h, rfl⟩

end KatzCountAux

theorem solution
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓΩ : ((ℓ : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) :
    Nat.card {D : ModularCurve.LevelPData Ω // ModularCurve.IsLevelPStructure W₀ ℓ D} =
      Nat.card (GL (Fin 2) (ZMod ℓ)) := by
  classical
  haveI hE : W₀.IsElliptic := ⟨hΔ⟩
  have hℓp : ℓ.Prime := Fact.out
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hℓp.odd_of_ne_two hℓ2
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) W₀ (n := ℓ) hℓΩ
  have hbc : WeierstrassCurve.Affine.baseChange W₀ Ω = W₀ := by
    rw [WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hbc] at e

  set T := Submodule.torsionBy ℤ W₀.toAffine.Point (ℓ : ℤ) with hT
  have hns : ∀ {x y : Ω}, W₀.toAffine.Equation x y → W₀.toAffine.Nonsingular x y := fun h =>
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp h
  have hmem : ∀ {x y : Ω} (h : W₀.toAffine.Nonsingular x y), (W₀.preΨ ℓ).eval x = 0 →
      WeierstrassCurve.Affine.Point.some x y h ∈ T := by
    intro x y h hx
    rw [hT, Submodule.mem_torsionBy_iff, natCast_zsmul]
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W₀ hodd h).mpr hx
  have hTℓ : ∀ P : T, ℓ • (P : W₀.toAffine.Point) = 0 := by
    intro P
    have := (Submodule.mem_torsionBy_iff _ _).mp P.2
    rwa [natCast_zsmul] at this

  have hsmul : ∀ (a : ZMod ℓ) (v : ZMod ℓ × ZMod ℓ), ((e (a • v) : T) : W₀.toAffine.Point) = a.val • ((e v : T) : W₀.toAffine.Point) := by
    intro a v
    conv_lhs => rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, map_nsmul]
    rfl
  have hzsmul : ∀ (k : ℤ) (t : T), e.symm (k • t) = (k : ZMod ℓ) • e.symm t := by
    intro k t
    rw [map_zsmul, Int.cast_smul_eq_zsmul]

  let vec : {D : ModularCurve.LevelPData Ω // ModularCurve.IsLevelPStructure W₀ ℓ D} → (Fin 2 → ZMod ℓ × ZMod ℓ) :=
    fun D => ![e.symm ⟨_, hmem (hns D.2.equation_P) D.2.preΨ_P⟩, e.symm ⟨_, hmem (hns D.2.equation_Q) D.2.preΨ_Q⟩]

  have hdict : ∀ {x₀ y₀ x y : Ω} (h₀ : W₀.toAffine.Nonsingular x₀ y₀) (h : W₀.toAffine.Nonsingular x y)
      (m₀ : WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ ∈ T) (m : WeierstrassCurve.Affine.Point.some x y h ∈ T),
      ModularCurve.indepElt W₀ ℓ x₀ x = 0 ↔ ∃ a : ZMod ℓ, a • e.symm ⟨_, m₀⟩ = e.symm ⟨_, m⟩ := by
    intro x₀ y₀ x y h₀ h m₀ m
    rw [ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 h₀ h (hTℓ ⟨_, m₀⟩), AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨(k : ZMod ℓ), ?_⟩
      rw [← hzsmul]
      congr 1
      exact Subtype.ext (by simpa using hk)
    · rintro ⟨a, ha⟩
      refine ⟨(a.val : ℤ), ?_⟩
      have := congrArg (fun z => ((e z : T) : W₀.toAffine.Point)) ha
      simp only [hsmul, AddEquiv.apply_symm_apply] at this
      rw [natCast_zsmul]
      exact this
  have hvec_indep : ∀ D, LinearIndependent (ZMod ℓ) (vec D) := by
    intro D
    rw [linearIndependent_fin2]
    simp only [vec, Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · intro h0
      have : (⟨_, hmem (hns D.2.equation_Q) D.2.preΨ_Q⟩ : T) = 0 := e.symm.injective (by rw [h0, map_zero])
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ (congrArg Subtype.val this)
    · intro a ha
      have h0 : ModularCurve.indepElt W₀ ℓ D.1.xQ D.1.xP = 0 :=
        (hdict (hns D.2.equation_Q) (hns D.2.equation_P) _ _).mpr ⟨a, ha⟩
      exact D.2.isUnit_indepElt_QP.ne_zero h0
  have hinj : Function.Injective vec := by
    intro D D' hDD
    have h0 := congrFun hDD 0
    have h1 := congrFun hDD 1
    simp only [vec, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have h0' := congrArg Subtype.val (e.symm.injective h0)
    have h1' := congrArg Subtype.val (e.symm.injective h1)
    simp only at h0' h1'
    injection h0' with hxP hyP
    injection h1' with hxQ hyQ
    exact Subtype.ext (ModularCurve.LevelPData.ext hxP hyP hxQ hyQ)
  have hsurj : ∀ w : Fin 2 → ZMod ℓ × ZMod ℓ, LinearIndependent (ZMod ℓ) w → ∃ D, vec D = w := by
    intro w hw
    have hne : ∀ i, ((e (w i) : T) : W₀.toAffine.Point) ≠ 0 := by
      intro i h0
      apply hw.ne_zero i
      have : (e (w i) : T) = 0 := Subtype.ext h0
      simpa using this
    obtain ⟨xP, yP, hP, hPe⟩ := KatzCountAux.exists_eq_some _ (hne 0)
    obtain ⟨xQ, yQ, hQ, hQe⟩ := KatzCountAux.exists_eq_some _ (hne 1)
    have mP : WeierstrassCurve.Affine.Point.some xP yP hP ∈ T := hPe ▸ (e (w 0)).2
    have mQ : WeierstrassCurve.Affine.Point.some xQ yQ hQ ∈ T := hQe ▸ (e (w 1)).2
    have heP : e.symm ⟨_, mP⟩ = w 0 := by
      rw [AddEquiv.symm_apply_eq]; exact Subtype.ext hPe.symm
    have heQ : e.symm ⟨_, mQ⟩ = w 1 := by
      rw [AddEquiv.symm_apply_eq]; exact Subtype.ext hQe.symm
    have hψP : (W₀.preΨ ℓ).eval xP = 0 := by
      rw [WeierstrassCurve.preΨ_ofNat, ← WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W₀ hodd hP]
      exact hTℓ ⟨_, mP⟩
    have hψQ : (W₀.preΨ ℓ).eval xQ = 0 := by
      rw [WeierstrassCurve.preΨ_ofNat, ← WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W₀ hodd hQ]
      exact hTℓ ⟨_, mQ⟩
    have hw' := LinearIndependent.pair_iff.mp (by
      have : w = ![w 0, w 1] := by funext i; fin_cases i <;> rfl
      rw [← this]; exact hw)
    have hPQ : ModularCurve.indepElt W₀ ℓ xP xQ ≠ 0 := by
      intro h0
      obtain ⟨a, ha⟩ := (hdict hP hQ mP mQ).mp h0
      rw [heP, heQ] at ha
      have := (hw' a (-1) (by rw [ha, neg_one_smul, add_neg_cancel])).2
      exact one_ne_zero (neg_eq_zero.mp this)
    have hQP : ModularCurve.indepElt W₀ ℓ xQ xP ≠ 0 := by
      intro h0
      obtain ⟨a, ha⟩ := (hdict hQ hP mQ mP).mp h0
      rw [heP, heQ] at ha
      have := (hw' (-1) a (by rw [ha, neg_one_smul, neg_add_cancel])).1
      exact one_ne_zero (neg_eq_zero.mp this)
    refine ⟨⟨⟨xP, yP, xQ, yQ⟩, ⟨hP.left, hQ.left, hψP, hψQ, isUnit_iff_ne_zero.mpr hPQ, isUnit_iff_ne_zero.mpr hQP⟩⟩, ?_⟩
    funext i
    fin_cases i
    · simp only [vec, Matrix.cons_val_zero]; exact heP
    · simp only [vec, Matrix.cons_val_one]; exact heQ

  let Φ : {D : ModularCurve.LevelPData Ω // ModularCurve.IsLevelPStructure W₀ ℓ D} →
      {w : Fin 2 → ZMod ℓ × ZMod ℓ // LinearIndependent (ZMod ℓ) w} := fun D => ⟨vec D, hvec_indep D⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun D D' h => hinj (congrArg Subtype.val h), fun w => ?_⟩
    obtain ⟨D, hD⟩ := hsurj w.1 w.2
    exact ⟨D, Subtype.ext hD⟩
  rw [Nat.card_eq_of_bijective Φ hΦ, card_linearIndependent (by simp), Matrix.card_GL_field]
  simp [ZMod.card]

end S_ModularCurve_natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed (solution)
