-- Prove2me | solution 1 for ModularCurve.eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8fc4fe74-da6c-5de1-8553-5fa17b2ec01e

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_map_eq_map_relabel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false

open ModularCurve ModularCurve.LevelRelabelling
open scoped Classical

namespace TateSideH1

theorem toPoint_of_nonsingular {T : Type} [Field T] (W : WeierstrassCurve T) (x y : T) (h : W.toAffine.Nonsingular x y) :
    toPoint W x y = WeierstrassCurve.Affine.Point.some x y h := dif_pos h

theorem relabel_xP_yP {T : Type} [Field T] (W : WeierstrassCurve T) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (D : ModularCurve.LevelPData T) (x y : T) (hxy : W.toAffine.Nonsingular x y)
    (h : g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ = WeierstrassCurve.Affine.Point.some x y hxy) :
    (LevelPData.relabel W g D).xP = x ∧ (LevelPData.relabel W g D).yP = y := by
  have e : ofPoint W (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ) = (x, y) := by rw [h]; rfl
  refine ⟨?_, ?_⟩ <;> simp only [LevelPData.relabel, e]

theorem variableChange_inv_variableChange {T : Type} [CommRing T] (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T) : (D.variableChange C⁻¹).variableChange C = D := by
  rw [← ModularCurve.LevelPData.variableChange_mul, mul_inv_cancel, ModularCurve.LevelPData.variableChange_one]

theorem variableChange_variableChange_inv {T : Type} [CommRing T] (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T) : (D.variableChange C).variableChange C⁻¹ = D := by
  rw [← ModularCurve.LevelPData.variableChange_mul, inv_mul_cancel, ModularCurve.LevelPData.variableChange_one]

theorem map_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (ModularCurve.LevelPData.map f) := by
  intro D D' h
  have h1 := congrArg ModularCurve.LevelPData.xP h
  have h2 := congrArg ModularCurve.LevelPData.yP h
  have h3 := congrArg ModularCurve.LevelPData.xQ h
  have h4 := congrArg ModularCurve.LevelPData.yQ h
  simp only [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP, ModularCurve.LevelPData.map_xQ,
    ModularCurve.LevelPData.map_yQ] at h1 h2 h3 h4
  ext <;> first | exact hf h1 | exact hf h2 | exact hf h3 | exact hf h4

theorem map_qExpand_variableChange_inv_relabel_eq_cuspData
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ]
    (U : (L)ˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (D : ModularCurve.LevelPData (LaurentSeries L)) (v w : Fin 2 → ZMod (ℓ * q)) (hv : v ≠ 0) (hw : w ≠ 0)
    (hD : haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
      D.map (ModularCurve.qExpand L ℓ) = ModularCurve.cuspData L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit v w)
    (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hv' : (g 0 0 : ℤ) • v + (g 1 0 : ℤ) • w ≠ 0) (hw' : (g 0 1 : ℤ) • v + (g 1 1 : ℤ) • w ≠ 0)
    (hP : W₂.toAffine.Nonsingular (D.variableChange Cy).xP (D.variableChange Cy).yP)
    (hQ : W₂.toAffine.Nonsingular (D.variableChange Cy).xQ (D.variableChange Cy).yQ)
    (h₁ : g 0 0 • toPoint W₂ (D.variableChange Cy).xP (D.variableChange Cy).yP +
        g 1 0 • toPoint W₂ (D.variableChange Cy).xQ (D.variableChange Cy).yQ ≠ 0)
    (h₂ : g 0 1 • toPoint W₂ (D.variableChange Cy).xP (D.variableChange Cy).yP +
        g 1 1 • toPoint W₂ (D.variableChange Cy).xQ (D.variableChange Cy).yQ ≠ 0) :
    haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
    ((LevelPData.relabel W₂ g (D.variableChange Cy)).variableChange Cy⁻¹).map (ModularCurve.qExpand L ℓ) =
      ModularCurve.cuspData L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit
        ((g 0 0 : ℤ) • v + (g 1 0 : ℤ) • w) ((g 0 1 : ℤ) • v + (g 1 1 : ℤ) • w) := by
  haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩

  have key := ModularCurve.LevelRelabelling.relabel_smul_variableChange W₂ Cy⁻¹ g (D.variableChange Cy) hP.left hQ.left h₁ h₂
  have hW : Cy⁻¹ • W₂ = ModularCurve.tateBase L q := by rw [hW₂, inv_smul_smul]
  rw [hW, variableChange_variableChange_inv] at key

  rw [← key]

  obtain ⟨hTate, -, -⟩ := ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq L q ℓ
      |> fun h => (⟨h.1, h.2.1, h.2.2⟩ : _ ∧ _ ∧ _)
  rw [← ModularCurve.LevelRelabelling.relabel_map_eq_map_relabel (ModularCurve.qExpand L ℓ) (ModularCurve.tateBase L q) g D, hD,
    ← hTate]
  exact ModularCurve.LevelRelabelling.relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul L (ℓ * q) (U : L) hU v w g hv hw hv' hw'

end TateSideH1

namespace TateSideH1

theorem toric_pt (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ]
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q)) (a : ℕ) (ha : a < ℓ * q) :
    haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
    ModularCurve.cuspPoint L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit ![(a : ZMod (ℓ * q)), 0] =
      ((ModularCurve.qExpand L ℓ (ModularCurve.tateToricPoint L q (U ^ a)).1),
       (ModularCurve.qExpand L ℓ (ModularCurve.tateToricPoint L q (U ^ a)).2)) := by
  haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
  have hUu : (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit = U := Units.ext (IsUnit.unit_spec _)
  rw [ModularCurve.cuspPoint_of_eq_zero _ (by simp), hUu]
  have hval : ((a : ZMod (ℓ * q))).val = a := ZMod.val_natCast_of_lt ha
  simp only [Matrix.cons_val_zero, hval]
  obtain ⟨-, htor, -⟩ := ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq L q ℓ
  obtain ⟨h1, h2⟩ := htor (U ^ a)
  exact Prod.ext h1 h2

theorem nonToric_pt (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ]
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q)) (a j : ℕ) (ha : a < ℓ * q) (hj : 0 < j) (hjq : j < q) :
    haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
    ModularCurve.cuspPoint L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit
        ![(a : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))] =
      ((ModularCurve.qExpand L ℓ (ModularCurve.nonToricPoint L q (U ^ a) j).1),
       (ModularCurve.qExpand L ℓ (ModularCurve.nonToricPoint L q (U ^ a) j).2)) := by
  haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
  have hUu : (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit = U := Units.ext (IsUnit.unit_spec _)
  have hlt : ℓ * j < ℓ * q := Nat.mul_lt_mul_of_pos_left hjq (Nat.pos_of_ne_zero (NeZero.ne ℓ))
  have hne : (((ℓ * j : ℕ) : ZMod (ℓ * q))) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne ℓ)) hj) h0
    omega
  rw [ModularCurve.cuspPoint_of_ne_zero _ (by simpa using hne), hUu]
  have hval : ((a : ZMod (ℓ * q))).val = a := ZMod.val_natCast_of_lt ha
  have hval' : (((ℓ * j : ℕ) : ZMod (ℓ * q))).val = ℓ * j := ZMod.val_natCast_of_lt hlt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hval, hval']
  obtain ⟨-, -, hnt⟩ := ModularCurve.tateBase_mul_eq_map_qExpand_and_tateToricPoint_eq_and_nonToricPoint_eq L q ℓ
  obtain ⟨h1, h2⟩ := hnt (U ^ a) j hj hjq
  exact Prod.ext h1 h2

theorem read_first
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ]
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (D D' : ModularCurve.LevelPData (LaurentSeries L)) (v w : Fin 2 → ZMod (ℓ * q)) (hv : v ≠ 0) (hw : w ≠ 0)
    (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hv' : (g 0 0 : ℤ) • v + (g 1 0 : ℤ) • w ≠ 0) (hw' : (g 0 1 : ℤ) • v + (g 1 1 : ℤ) • w ≠ 0)
    (hD : haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
      D.map (ModularCurve.qExpand L ℓ) = ModularCurve.cuspData L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit v w)
    (hD' : haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
      D'.map (ModularCurve.qExpand L ℓ) = ModularCurve.cuspData L (ℓ * q) (hU.isUnit (Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q))).unit
        ((g 0 0 : ℤ) • v + (g 1 0 : ℤ) • w) ((g 0 1 : ℤ) • v + (g 1 1 : ℤ) • w))
    (hP : W₂.toAffine.Nonsingular (D.variableChange Cy).xP (D.variableChange Cy).yP)
    (hQ : W₂.toAffine.Nonsingular (D.variableChange Cy).xQ (D.variableChange Cy).yQ)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : g 0 0 • toPoint W₂ (D.variableChange Cy).xP (D.variableChange Cy).yP +
        g 1 0 • toPoint W₂ (D.variableChange Cy).xQ (D.variableChange Cy).yQ = WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY)
    (h₂ : g 0 1 • toPoint W₂ (D.variableChange Cy).xP (D.variableChange Cy).yP +
        g 1 1 • toPoint W₂ (D.variableChange Cy).xQ (D.variableChange Cy).yQ ≠ 0) :
    X₂ = (D'.variableChange Cy).xP ∧ Y₂ = (D'.variableChange Cy).yP := by
  haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
  have h₁ : g 0 0 • toPoint W₂ (D.variableChange Cy).xP (D.variableChange Cy).yP +
      g 1 0 • toPoint W₂ (D.variableChange Cy).xQ (D.variableChange Cy).yQ ≠ 0 := by
    rw [h]; exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have key := map_qExpand_variableChange_inv_relabel_eq_cuspData L q ℓ U hU Cy W₂ hW₂ D v w hv hw hD g hv' hw' hP hQ h₁ h₂
  rw [← hD'] at key
  have key' := map_injective _ (ModularCurve.qExpand_injective (R := L) ℓ) key
  have key'' := congrArg (fun E => E.variableChange Cy) key'
  simp only [variableChange_inv_variableChange] at key''
  obtain ⟨hx, hy⟩ := relabel_xP_yP W₂ g (D.variableChange Cy) X₂ Y₂ hXY h
  rw [key''] at hx hy
  exact ⟨hx.symm, hy.symm⟩

theorem vec_ne_zero_of_lt {n : ℕ} [NeZero n] (a : ℕ) (ha : 0 < a) (han : a < n) :
    (![(a : ZMod n), 0] : Fin 2 → ZMod n) ≠ 0 := by
  intro h0
  have h1 : (a : ZMod n) = 0 := by simpa using congrFun h0 0
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd ha h1
  omega

theorem vec_ne_zero_of_snd {n : ℕ} [NeZero n] (a b : ZMod n) (hb : b ≠ 0) :
    (![a, b] : Fin 2 → ZMod n) ≠ 0 := by
  intro h0
  exact hb (by simpa using congrFun h0 1)

end TateSideH1

open TateSideH1 in

theorem solution
    (L : Type) [Field L] [CharZero L] (q ℓ : ℕ) [NeZero q] [NeZero ℓ] (h2q : 2 ≤ q) (h2ℓ : 2 ≤ ℓ) (j : ℕ) (hj : 0 < j) (hjq : j < q)
    (U : Lˣ) (hU : IsPrimitiveRoot (U : L) (ℓ * q))
    (Cy : WeierstrassCurve.VariableChange (LaurentSeries L))
    (W₂ : WeierstrassCurve (LaurentSeries L)) [W₂.IsElliptic] (hW₂ : W₂ = Cy • ModularCurve.tateBase L q)
    (E₂ : ModularCurve.LevelPData (LaurentSeries L))
    (hE₂ : E₂ = (⟨(ModularCurve.tateToricPoint L q (U ^ q)).1, (ModularCurve.tateToricPoint L q (U ^ q)).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy)
    (hP : W₂.toAffine.Nonsingular E₂.xP E₂.yP) (hQ : W₂.toAffine.Nonsingular E₂.xQ E₂.yQ)
    (X₂ Y₂ : LaurentSeries L) (hXY : W₂.toAffine.Nonsingular X₂ Y₂)
    (h : ModularCurve.LevelRelabelling.toPoint W₂ E₂.xP E₂.yP + ModularCurve.LevelRelabelling.toPoint W₂ E₂.xQ E₂.yQ =
      WeierstrassCurve.Affine.Point.some X₂ Y₂ hXY) :
    X₂ = ((⟨(ModularCurve.nonToricPoint L q (U ^ q) j).1, (ModularCurve.nonToricPoint L q (U ^ q) j).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).xP ∧
    Y₂ = ((⟨(ModularCurve.nonToricPoint L q (U ^ q) j).1, (ModularCurve.nonToricPoint L q (U ^ q) j).2,
        (ModularCurve.nonToricPoint L q 1 j).1, (ModularCurve.nonToricPoint L q 1 j).2⟩ :
          ModularCurve.LevelPData (LaurentSeries L)).variableChange Cy).yP := by
  haveI : NeZero (ℓ * q) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne q)⟩
  have hq : q < ℓ * q := by nlinarith
  have h0 : 0 < ℓ * q := by positivity
  have hlt : ℓ * j < ℓ * q := Nat.mul_lt_mul_of_pos_left hjq (by omega)
  have hne : (((ℓ * j : ℕ) : ZMod (ℓ * q))) ≠ 0 := by
    intro hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have := Nat.le_of_dvd (Nat.mul_pos (by omega) hj) hz
    omega
  subst hE₂
  set D : ModularCurve.LevelPData (LaurentSeries L) := ⟨(ModularCurve.tateToricPoint L q (U ^ q)).1,
    (ModularCurve.tateToricPoint L q (U ^ q)).2, (ModularCurve.nonToricPoint L q 1 j).1,
    (ModularCurve.nonToricPoint L q 1 j).2⟩ with hDdef
  have e1 : ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) • (![(q : ZMod (ℓ * q)), 0] : Fin 2 → ZMod (ℓ * q)) +
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) • ![(0 : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))] =
      ![(q : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))] := by
    ext i; fin_cases i <;> simp
  have e2 : ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) • (![(q : ZMod (ℓ * q)), 0] : Fin 2 → ZMod (ℓ * q)) +
      ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) • ![(0 : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))] =
      ![(0 : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))] := by
    ext i; fin_cases i <;> simp
  refine read_first L q ℓ U hU Cy W₂ hW₂ D _ ![(q : ZMod (ℓ * q)), 0] ![(0 : ZMod (ℓ * q)), ((ℓ * j : ℕ) : ZMod (ℓ * q))]
    (vec_ne_zero_of_lt q (by omega) hq) (vec_ne_zero_of_snd _ _ hne) !![1, 0; 1, 1] ?_ ?_ ?_ ?_ hP hQ X₂ Y₂ hXY ?_ ?_
  · rw [e1]; exact vec_ne_zero_of_snd _ _ hne
  · rw [e2]; exact vec_ne_zero_of_snd _ _ hne
  · have h1 := toric_pt L q ℓ U hU q hq
    have h2 := nonToric_pt L q ℓ U hU 0 j h0 hj hjq
    rw [pow_zero, Nat.cast_zero] at h2
    unfold ModularCurve.cuspData
    rw [h1, h2]
    rfl
  · rw [e1, e2]
    have h1 := nonToric_pt L q ℓ U hU q j hq hj hjq
    have h2 := nonToric_pt L q ℓ U hU 0 j h0 hj hjq
    rw [pow_zero, Nat.cast_zero] at h2
    unfold ModularCurve.cuspData
    rw [h1, h2]
    rfl
  · simpa using h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_smul, one_smul, zero_add]
    rw [toPoint_of_nonsingular W₂ _ _ hQ]; exact WeierstrassCurve.Affine.Point.some_ne_zero _

end S_ModularCurve_eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some
end P2MW
export P2MW.S_ModularCurve_eq_variableChange_nonToricPoint_pow_of_toPoint_add_toPoint_nonToricPoint_one_eq_some (solution)
