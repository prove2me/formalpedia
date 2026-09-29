-- Prove2me | solution 1 for ModularCurve.FullLevel.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f0bdc678-4227-5c09-a518-a328d4e6e3a4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange
import Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Theorems.Thm_ModularCurve_coeff_zero_cuspPoint_fst_add_inv_twelve_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false

open scoped MatrixGroups
open scoped Classical
open ModularCurve ModularCurve.LevelRelabelling

namespace H34A

noncomputable def pmap {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) :
    W.toAffine.Point →+ (W.map (algebraMap K F)).toAffine.Point :=
  WeierstrassCurve.Affine.Point.baseChange (W' := W) K F

theorem pmap_zero {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) :
    pmap (F := F) W 0 = 0 := map_zero _

theorem pmap_some {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    pmap (F := F) W (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (algebraMap K F x) (algebraMap K F y)
        ((WeierstrassCurve.Affine.map_nonsingular W (algebraMap K F).injective x y).mpr h) := rfl

theorem pmap_injective {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) :
    Function.Injective (pmap (F := F) W) :=
  WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId K F)

theorem toPoint_baseChange {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) (x y : K) :
    toPoint (W.map (algebraMap K F)) (algebraMap K F x) (algebraMap K F y) = pmap W (toPoint W x y) := by
  by_cases h : W.toAffine.Nonsingular x y
  · have h' : (W.map (algebraMap K F)).toAffine.Nonsingular (algebraMap K F x) (algebraMap K F y) :=
      (WeierstrassCurve.Affine.map_nonsingular W (algebraMap K F).injective x y).mpr h
    have e1 : toPoint W x y = WeierstrassCurve.Affine.Point.some x y h := dif_pos h
    have e2 : toPoint (W.map (algebraMap K F)) (algebraMap K F x) (algebraMap K F y) =
        WeierstrassCurve.Affine.Point.some _ _ h' := dif_pos h'
    rw [e1, e2]
    rfl
  · have h' : ¬ (W.map (algebraMap K F)).toAffine.Nonsingular (algebraMap K F x) (algebraMap K F y) :=
      fun h' => h ((WeierstrassCurve.Affine.map_nonsingular W (algebraMap K F).injective x y).mp h')
    have e1 : toPoint W x y = 0 := dif_neg h
    have e2 : toPoint (W.map (algebraMap K F)) (algebraMap K F x) (algebraMap K F y) = 0 := dif_neg h'
    rw [e1, e2, pmap_zero]

theorem ofPoint_baseChange {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K) (P : W.toAffine.Point) :
    ofPoint (W.map (algebraMap K F)) (pmap W P) = (algebraMap K F (ofPoint W P).1, algebraMap K F (ofPoint W P).2) := by
  rcases P with _ | ⟨x, y, h⟩
  · show ofPoint (W.map (algebraMap K F)) (pmap W 0) = (algebraMap K F 0, algebraMap K F 0)
    rw [pmap_zero, map_zero]; rfl
  · rfl

theorem relabel_map_eq {K F : Type} [Field K] [Field F] [Algebra K F] (W : WeierstrassCurve K)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (D : LevelPData K) :
    (LevelPData.relabel W g D).map (algebraMap K F) =
      LevelPData.relabel (W.map (algebraMap K F)) g (D.map (algebraMap K F)) := by
  have key : ∀ (a b : ℤ),
      (algebraMap K F (ofPoint W (a • toPoint W D.xP D.yP + b • toPoint W D.xQ D.yQ)).1,
        algebraMap K F (ofPoint W (a • toPoint W D.xP D.yP + b • toPoint W D.xQ D.yQ)).2) =
      ofPoint (W.map (algebraMap K F))
        (a • toPoint (W.map (algebraMap K F)) (algebraMap K F D.xP) (algebraMap K F D.yP) +
          b • toPoint (W.map (algebraMap K F)) (algebraMap K F D.xQ) (algebraMap K F D.yQ)) := by
    intro a b
    rw [toPoint_baseChange, toPoint_baseChange, ← map_zsmul (pmap (F := F) W), ← map_zsmul (pmap (F := F) W),
      ← map_add (pmap (F := F) W),
      ofPoint_baseChange]
  unfold LevelPData.relabel
  refine LevelPData.ext ?_ ?_ ?_ ?_
  · exact congrArg Prod.fst (key (g 0 0) (g 1 0))
  · exact congrArg Prod.snd (key (g 0 0) (g 1 0))
  · exact congrArg Prod.fst (key (g 0 1) (g 1 1))
  · exact congrArg Prod.snd (key (g 0 1) (g 1 1))

end H34A

namespace H34A

theorem finish {K : Type} [Field K] (W : WeierstrassCurve K) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : LevelPData K)
    (hx1 : (LevelPData.relabel W g D).xP ≠ 0) (hx2 : (LevelPData.relabel W g D).xQ ≠ 0) :
    (W.toAffine.Nonsingular (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP ∧
      W.toAffine.Nonsingular (LevelPData.relabel W g D).xQ (LevelPData.relabel W g D).yQ) ∧
    g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ =
      toPoint W (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP ∧
    g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ =
      toPoint W (LevelPData.relabel W g D).xQ (LevelPData.relabel W g D).yQ := by
  have key1 : ∀ (R : W.toAffine.Point), (ofPoint W R).1 ≠ 0 →
      ∃ h : W.toAffine.Nonsingular (ofPoint W R).1 (ofPoint W R).2, R = toPoint W (ofPoint W R).1 (ofPoint W R).2 := by
    rintro (_ | ⟨x, y, h⟩) hR
    · exact absurd rfl hR
    · exact ⟨h, (dif_pos h).symm⟩
  have hDr : LevelPData.relabel W g D =
      ⟨(ofPoint W (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ)).1,
       (ofPoint W (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ)).2,
       (ofPoint W (g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ)).1,
       (ofPoint W (g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ)).2⟩ := rfl
  rw [hDr] at hx1 hx2 ⊢
  obtain ⟨h1, e1⟩ := key1 _ hx1
  obtain ⟨h2, e2⟩ := key1 _ hx2
  exact ⟨⟨h1, h2⟩, e1, e2⟩

end H34A

namespace H1Curve

theorem sq_add_ten_mul_add_one_ne_zero {L : Type} [Field L] (ι : L →+* ℂ) {c : L} {N : ℕ} (hN : N ≠ 0)
    (hc : c ^ N = 1) : c ^ 2 + 10 * c + 1 ≠ 0 := by
  intro h
  have hz : (ι c) ^ N = 1 := by rw [← map_pow, hc, map_one]
  have hn : ‖ι c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz hN
  have h' : (10 : ℂ) * ι c = -((ι c) ^ 2 + 1) := by
    have := congrArg ι h
    simp only [map_add, map_mul, map_pow, map_one, map_zero, map_ofNat] at this
    linear_combination this
  have h1 : ‖(10 : ℂ) * ι c‖ = 10 := by rw [norm_mul, hn, mul_one]; simp
  have h2 : ‖-((ι c) ^ 2 + 1)‖ ≤ 2 := by
    rw [norm_neg]
    calc ‖(ι c) ^ 2 + 1‖ ≤ ‖(ι c) ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, hn, one_pow, norm_one]; norm_num
  rw [h'] at h1
  linarith

theorem pow_val_ne_one {L : Type} [Field L] {N : ℕ} [NeZero N] {ξ : L} (hξ : IsPrimitiveRoot ξ N)
    {a : ZMod N} (ha : a ≠ 0) : ξ ^ a.val ≠ 1 := by
  rw [Ne, hξ.pow_eq_one_iff_dvd]
  intro hd
  apply ha
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a)

theorem fst_ne_zero_of_snd_eq_zero {N : ℕ} {v : Fin 2 → ZMod N} (hv : v ≠ 0) (hv1 : v 1 = 0) : v 0 ≠ 0 := by
  intro h0; apply hv; funext i; fin_cases i <;> simp [h0, hv1]

theorem X_ne_zero (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) (N : ℕ) [NeZero N]
    (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹) ≠ 0 := by
  intro h0
  have hc := ModularCurve.coeff_zero_cuspPoint_fst_add_inv_twelve_sq L N ξ hξ v hv
  rw [h0, zero_pow two_ne_zero] at hc
  simp only [HahnSeries.coeff_zero] at hc
  by_cases hv1 : v 1 = 0
  · rw [if_pos hv1, Units.val_pow_eq_pow_val] at hc
    have hv0 := fst_ne_zero_of_snd_eq_zero hv hv1
    have hc1 : (1 : L) - (ξ : L) ^ (v 0).val ≠ 0 := sub_ne_zero.mpr (pow_val_ne_one hξ hv0).symm
    have key : (ξ : L) ^ (v 0).val * ((1 - (ξ : L) ^ (v 0).val)⁻¹) ^ 2 + 12⁻¹ = 0 :=
      (pow_eq_zero_iff two_ne_zero).mp hc.symm
    have hN : ((ξ : L) ^ (v 0).val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
    apply sq_add_ten_mul_add_one_ne_zero ι (NeZero.ne N) hN
    field_simp at key
    linear_combination key
  · rw [if_neg hv1] at hc
    exact pow_ne_zero 2 (inv_ne_zero (by norm_num)) hc.symm

end H1Curve

p2m_open "ModularCurve WeierstrassCurve~cusp WeierstrassCurve.Affine ModularCurve.LevelRelabelling"
open scoped Classical MatrixGroups

noncomputable section

namespace H34S1
namespace TateAdd

variable (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N]

def PP (c : Lˣ) (j : ℕ) : (tateBase L N).toAffine.Point :=
  if j = 0 then (if (c : L) = 1 then 0 else toPoint (tateBase L N) (toricPoint L N (c : L)).1 (toricPoint L N (c : L)).2)
  else toPoint (tateBase L N) (nonToricPoint L N c j).1 (nonToricPoint L N c j).2

variable {L N}

theorem toPoint_of_nonsingular {x y : LaurentSeries L} (h : (tateBase L N).toAffine.Nonsingular x y) :
    toPoint (tateBase L N) x y = Point.some x y h := dif_pos h

theorem PP_one_zero (c : Lˣ) (hc : (c : L) = 1) : PP L N c 0 = 0 := by
  rw [PP, if_pos rfl, if_pos hc]

theorem nonsingular_toric (c : Lˣ) (hc : (c : L) ≠ 1) :
    (tateBase L N).toAffine.Nonsingular (toricPoint L N (c : L)).1 (toricPoint L N (c : L)).2 := by
  obtain ⟨h, -, -⟩ := toricPoint_add_toricPoint_tateBase_of_charZero L N (c : L) (c : L) c.ne_zero c.ne_zero hc hc
  exact h

theorem nonsingular_slot (c : Lˣ) {j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (tateBase L N).toAffine.Nonsingular (nonToricPoint L N c j).1 (nonToricPoint L N c j).2 := by
  obtain ⟨h, -, -⟩ := (toricPoint_add_nonToricPoint_of_charZero L N).2.2 c j hj0 hjN
  exact h

theorem PP_toric (c : Lˣ) (hc : (c : L) ≠ 1) :
    PP L N c 0 = Point.some _ _ (nonsingular_toric c hc) := by
  rw [PP, if_pos rfl, if_neg hc, toPoint_of_nonsingular]

theorem PP_slot (c : Lˣ) {j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    PP L N c j = Point.some _ _ (nonsingular_slot c hj0 hjN) := by
  rw [PP, if_neg (Nat.pos_iff_ne_zero.mp hj0), toPoint_of_nonsingular]

theorem PP_toric_add_toric (c d : Lˣ) : PP L N c 0 + PP L N d 0 = PP L N (c * d) 0 := by
  by_cases hc : (c : L) = 1
  · have hc' : c = 1 := Units.ext hc
    rw [PP_one_zero c hc, zero_add, hc', one_mul]
  by_cases hd : (d : L) = 1
  · have hd' : d = 1 := Units.ext hd
    rw [PP_one_zero d hd, add_zero, hd', mul_one]
  obtain ⟨hcn, hdn, h1, h2⟩ :=
    toricPoint_add_toricPoint_tateBase_of_charZero L N (c : L) (d : L) c.ne_zero d.ne_zero hc hd
  rw [PP_toric c hc, PP_toric d hd]
  by_cases hcd : (c : L) * (d : L) = 1
  · have hcd' : ((c * d : Lˣ) : L) = 1 := by rw [Units.val_mul]; exact hcd
    rw [PP_one_zero _ hcd']
    exact h1 hcd
  · have hcd' : ((c * d : Lˣ) : L) ≠ 1 := by rw [Units.val_mul]; exact hcd
    obtain ⟨hcdn, h⟩ := h2 hcd
    rw [PP_toric _ hcd', h]
    congr 1

theorem PP_toric_add_slot (c d : Lˣ) {j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    PP L N c 0 + PP L N d j = PP L N (c * d) j := by
  by_cases hc : (c : L) = 1
  · have hc' : c = 1 := Units.ext hc
    rw [PP_one_zero c hc, zero_add, hc', one_mul]
  obtain ⟨hcn, hdn, hcdn, h⟩ := (toricPoint_add_nonToricPoint_of_charZero L N).1 c d j hc hj0 hjN
  rw [PP_toric c hc, PP_slot d hj0 hjN, PP_slot (c * d) hj0 hjN]
  exact h

theorem PP_slot_add_slot_of_lt (c d : Lˣ) {i j : ℕ} (hi0 : 0 < i) (hj0 : 0 < j) (hij : i + j < N) :
    PP L N c i + PP L N d j = PP L N (c * d) (i + j) := by
  obtain ⟨hcn, hdn, hcdn, h⟩ := (toricPoint_add_nonToricPoint_of_charZero L N).2.1 c d i j hi0 hj0 hij
  rw [PP_slot c hi0 (by omega), PP_slot d hj0 (by omega), PP_slot (c * d) (by omega) hij]
  exact h

theorem PP_slot_add_opposite (c : Lˣ) {j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    PP L N c j + PP L N c⁻¹ (N - j) = 0 := by
  obtain ⟨hcn, hcn', h⟩ := (toricPoint_add_nonToricPoint_of_charZero L N).2.2 c j hj0 hjN
  rw [PP_slot c hj0 hjN, PP_slot c⁻¹ (by omega) (by omega)]
  exact h

theorem PP_slot_add_slot_of_eq (c d : Lˣ) {i j : ℕ} (hi0 : 0 < i) (hj0 : 0 < j) (hij : i + j = N) :
    PP L N c i + PP L N d j = PP L N (c * d) 0 := by
  have hjN : j < N := by omega
  have hiN : i < N := by omega
  have hj : j = N - i := by omega

  have h1 : PP L N (c * d) 0 + PP L N c⁻¹ j = PP L N d j := by
    rw [PP_toric_add_slot (c * d) c⁻¹ hj0 hjN, mul_inv_cancel_comm]
  have h2 : PP L N c i + PP L N c⁻¹ j = 0 := by rw [hj]; exact PP_slot_add_opposite c hi0 hiN
  rw [← h1, add_comm (PP L N (c * d) 0), ← add_assoc, h2, zero_add]

theorem PP_slot_add_slot_of_gt (c d : Lˣ) {i j : ℕ} (hiN : i < N) (hjN : j < N) (hij : N < i + j) :
    PP L N c i + PP L N d j = PP L N (c * d) (i + j - N) := by
  have hi0 : 0 < i := by omega
  have hj0 : 0 < j := by omega
  set r := i + j - N with hr
  have hr0 : 0 < r := by omega
  have hrN : r < N := by omega

  have h1 : PP L N 1 (N - i) + PP L N d r = PP L N d j := by
    rw [PP_slot_add_slot_of_lt 1 d (by omega) hr0 (by omega), one_mul]
    congr 1; omega

  have h2 : PP L N c i + PP L N 1 (N - i) = PP L N c 0 := by
    rw [PP_slot_add_slot_of_eq c 1 hi0 (by omega) (by omega), mul_one]
  rw [← h1, ← add_assoc, h2, PP_toric_add_slot c d hr0 hrN]

theorem PP_add (c d : Lˣ) {i j : ℕ} (hiN : i < N) (hjN : j < N) :
    PP L N c i + PP L N d j = PP L N (c * d) ((i + j) % N) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.zero_add, Nat.zero_mod]; exact PP_toric_add_toric c d
    · rw [Nat.zero_add, Nat.mod_eq_of_lt hjN]; exact PP_toric_add_slot c d hj0 hjN
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Nat.add_zero, Nat.mod_eq_of_lt hiN, add_comm, mul_comm]; exact PP_toric_add_slot d c hi0 hiN
  rcases lt_trichotomy (i + j) N with hlt | heq | hgt
  · rw [Nat.mod_eq_of_lt hlt]; exact PP_slot_add_slot_of_lt c d hi0 hj0 hlt
  · rw [heq, Nat.mod_self]; exact PP_slot_add_slot_of_eq c d hi0 hj0 heq
  · rw [Nat.mod_eq_sub_mod (le_of_lt hgt), Nat.mod_eq_of_lt (by omega)]
    exact PP_slot_add_slot_of_gt c d hiN hjN hgt

variable (L N) in

def Φ (ζ : Lˣ) (v : Fin 2 → ZMod N) : (tateBase L N).toAffine.Point := PP L N (ζ ^ (v 0).val) (v 1).val

theorem pow_val_add (ζ : Lˣ) (hζ : ζ ^ N = 1) (a b : ZMod N) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) N, pow_add, pow_mul, hζ, one_pow, one_mul]

theorem Φ_add (ζ : Lˣ) (hζ : ζ ^ N = 1) (v w : Fin 2 → ZMod N) : Φ L N ζ (v + w) = Φ L N ζ v + Φ L N ζ w := by
  show PP L N (ζ ^ ((v + w) 0).val) ((v + w) 1).val = PP L N (ζ ^ (v 0).val) (v 1).val + PP L N (ζ ^ (w 0).val) (w 1).val
  rw [PP_add _ _ (ZMod.val_lt _) (ZMod.val_lt _), Pi.add_apply, Pi.add_apply, pow_val_add ζ hζ, ZMod.val_add]

variable (L N) in

def Φhom (ζ : Lˣ) (hζ : ζ ^ N = 1) : (Fin 2 → ZMod N) →+ (tateBase L N).toAffine.Point :=
  AddMonoidHom.mk' (Φ L N ζ) (Φ_add ζ hζ)

theorem Φ_eq_toPoint_cuspPoint (ξ : L) (hξ : IsPrimitiveRoot ξ N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    Φ L N (hξ.isUnit (NeZero.ne N)).unit v =
      toPoint (tateBase L N) (cuspPoint L N (hξ.isUnit (NeZero.ne N)).unit v).1
        (cuspPoint L N (hξ.isUnit (NeZero.ne N)).unit v).2 := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    have hne : (((hξ.isUnit (NeZero.ne N)).unit ^ (v 0).val : Lˣ) : L) ≠ 1 := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact hξ.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero _).mpr h0) (ZMod.val_lt _)
    rw [cuspPoint_of_eq_zero _ h1, tateToricPoint_eq_toricPoint, Φ, h1, ZMod.val_zero, PP, if_pos rfl, if_neg hne]
  · rw [cuspPoint_of_ne_zero _ h1, Φ, PP, if_neg ((ZMod.val_ne_zero _).mpr h1)]

theorem nonsingular_cuspPoint (ξ : L) (hξ : IsPrimitiveRoot ξ N) (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (tateBase L N).toAffine.Nonsingular (cuspPoint L N (hξ.isUnit (NeZero.ne N)).unit v).1
      (cuspPoint L N (hξ.isUnit (NeZero.ne N)).unit v).2 := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    have hne : (((hξ.isUnit (NeZero.ne N)).unit ^ (v 0).val : Lˣ) : L) ≠ 1 := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      exact hξ.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero _).mpr h0) (ZMod.val_lt _)
    rw [cuspPoint_of_eq_zero _ h1, tateToricPoint_eq_toricPoint]
    exact nonsingular_toric _ hne
  · rw [cuspPoint_of_ne_zero _ h1]
    exact nonsingular_slot _ (ZMod.val_pos.mpr h1) (ZMod.val_lt _)

end H34S1.TateAdd

open H34S1.TateAdd in
theorem H34S1.relabel_smul_tate_cuspData
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : L) (hξ : IsPrimitiveRoot ξ N)
    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L)) (γ : SL(2, ℤ)) (n : ZMod N) (hn : n ≠ 0) :
    (![((γ 0 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1)] : Fin 2 → ZMod N) ≠ 0 ∧
    (![((γ 0 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1)] : Fin 2 → ZMod N) ≠ 0 ∧
    ModularCurve.LevelRelabelling.LevelPData.relabel (C₀ • ModularCurve.tateBase L N) ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        ((ModularCurve.cuspData L N (hξ.isUnit (NeZero.ne N)).unit ![n, 0] ![0, -n]).variableChange C₀) =
      (ModularCurve.cuspData L N (hξ.isUnit (NeZero.ne N)).unit
          ![((γ 0 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1)]
          ![((γ 0 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1)]).variableChange C₀ := by
  classical
  set ζ : Lˣ := (hξ.isUnit (NeZero.ne N)).unit with hζ
  have hζN : ζ ^ N = 1 := by
    apply Units.ext; rw [Units.val_pow_eq_pow_val, hζ, IsUnit.unit_spec, Units.val_one]; exact hξ.pow_eq_one
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact h
  have hdetZ : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) - ((γ 0 1 : ℤ) : ZMod N) * ((γ 1 0 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    push_cast at this
    exact this

  have ev' : (![((γ 0 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![n, 0] : Fin 2 → ZMod N) 1)] : Fin 2 → ZMod N) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) • (![n, 0] : Fin 2 → ZMod N) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) • (![0, -n] : Fin 2 → ZMod N) := by
    funext i; fin_cases i <;> simp [zsmul_eq_mul]
  have ew' : (![((γ 0 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0) - ((γ 0 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1),
        -(((γ 1 0 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 0)) + ((γ 1 1 : ℤ) : ZMod N) * ((![0, -n] : Fin 2 → ZMod N) 1)] : Fin 2 → ZMod N) =
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) • (![n, 0] : Fin 2 → ZMod N) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) • (![0, -n] : Fin 2 → ZMod N) := by
    funext i; fin_cases i <;> simp [zsmul_eq_mul]
  have hv : (![n, 0] : Fin 2 → ZMod N) ≠ 0 := by
    intro h; apply hn; have := congrFun h 0; simpa using this
  have hw : (![0, -n] : Fin 2 → ZMod N) ≠ 0 := by
    intro h; apply hn; have := congrFun h 1; simpa using this
  have hv' : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) • (![n, 0] : Fin 2 → ZMod N) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) • (![0, -n] : Fin 2 → ZMod N) ≠ 0 := by
    rw [← ev']
    intro h
    have e0 : ((γ 0 0 : ℤ) : ZMod N) * n = 0 := by have := congrFun h 0; simpa using this
    have e1 : ((γ 1 0 : ℤ) : ZMod N) * n = 0 := by have := congrFun h 1; simpa using this
    apply hn
    linear_combination ((γ 1 1 : ℤ) : ZMod N) * e0 - ((γ 0 1 : ℤ) : ZMod N) * e1 - n * hdetZ
  have hw' : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) • (![n, 0] : Fin 2 → ZMod N) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) • (![0, -n] : Fin 2 → ZMod N) ≠ 0 := by
    rw [← ew']
    intro h
    have e0 : ((γ 0 1 : ℤ) : ZMod N) * n = 0 := by have := congrFun h 0; simpa using this
    have e1 : ((γ 1 1 : ℤ) : ZMod N) * n = 0 := by have := congrFun h 1; simpa using this
    apply hn
    linear_combination ((γ 0 0 : ℤ) : ZMod N) * e1 - ((γ 1 0 : ℤ) : ZMod N) * e0 - n * hdetZ

  have key : ∀ (a b : ℤ) (hab : a • (![n, 0] : Fin 2 → ZMod N) + b • (![0, -n] : Fin 2 → ZMod N) ≠ 0),
      a • toPoint (tateBase L N) (cuspPoint L N ζ ![n, 0]).1 (cuspPoint L N ζ ![n, 0]).2 +
        b • toPoint (tateBase L N) (cuspPoint L N ζ ![0, -n]).1 (cuspPoint L N ζ ![0, -n]).2 ≠ 0 := by
    intro a b hab
    rw [← Φ_eq_toPoint_cuspPoint ξ hξ _ hv, ← Φ_eq_toPoint_cuspPoint ξ hξ _ hw]
    have h := (Φhom L N ζ hζN).map_add (a • (![n, 0] : Fin 2 → ZMod N)) (b • (![0, -n] : Fin 2 → ZMod N))
    rw [map_zsmul, map_zsmul] at h
    change Φ L N ζ (a • (![n, 0] : Fin 2 → ZMod N) + b • (![0, -n] : Fin 2 → ZMod N)) = a • Φ L N ζ ![n, 0] + b • Φ L N ζ ![0, -n] at h
    rw [← h, Φ_eq_toPoint_cuspPoint ξ hξ _ hab, toPoint_of_nonsingular (nonsingular_cuspPoint ξ hξ _ hab)]
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have eqP := (nonsingular_cuspPoint (L := L) (N := N) ξ hξ _ hv).left
  have eqQ := (nonsingular_cuspPoint (L := L) (N := N) ξ hξ _ hw).left
  refine ⟨ev' ▸ hv', ew' ▸ hw', ?_⟩
  rw [ev', ew',
    ModularCurve.LevelRelabelling.relabel_smul_variableChange (ModularCurve.tateBase L N) C₀
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (ModularCurve.cuspData L N ζ ![n, 0] ![0, -n]) eqP eqQ
      (key _ _ hv') (key _ _ hw'),
    ModularCurve.LevelRelabelling.relabel_tateBase_cuspData_eq_cuspData_zsmul_add_zsmul L N ξ hξ _ _
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) hv hw hv' hw']

end

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hC₀ : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)))

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))

    (W : WeierstrassCurve ↥K)
    (hW : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      W.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L (q * ℓ))
    (n : ZMod (q * ℓ)) (hn : n ≠ 0)
    (D : ModularCurve.LevelPData ↥K)
    (hD : D.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![(n : ZMod (q * ℓ)), 0] ![0, -(n : ZMod (q * ℓ))]).variableChange C₀) :

    haveI : DecidableEq ↥K := fun a b => Classical.propDecidable (a = b)
    (W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
      W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xQ) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yQ)) ∧
    (γ 0 0 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (γ 1 0 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ =
      ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
    (γ 0 1 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (γ 1 1 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ =
      ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xQ) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yQ) := by

  haveI hN0 : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hN1 : 1 < q * ℓ := by nlinarith [hq, hℓ3]

  obtain ⟨ι, hι'⟩ := id hιξ

  have hv : (![n, 0] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h => hn (by simpa using congrFun h 0)
  have hw : (![0, -n] : Fin 2 → ZMod (q * ℓ)) ≠ 0 := fun h => hn (by simpa using congrFun h 1)

  obtain ⟨hv', hw', S1⟩ := H34S1.relabel_smul_tate_cuspData L (q * ℓ) ξ hξ C₀ γ n hn

  have S2 := H34A.relabel_map_eq (F := LaurentSeries L) W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D
  rw [hW, hD, S1] at S2

  have hX := congrArg ModularCurve.LevelPData.xP hD
  have hY := congrArg ModularCurve.LevelPData.yP hD
  have hXq := congrArg ModularCurve.LevelPData.xQ hD
  have hYq := congrArg ModularCurve.LevelPData.yQ hD
  have hX' := congrArg ModularCurve.LevelPData.xP S2
  have hY' := congrArg ModularCurve.LevelPData.yP S2
  have hXq' := congrArg ModularCurve.LevelPData.xQ S2
  have hYq' := congrArg ModularCurve.LevelPData.yQ S2
  simp only [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP, ModularCurve.LevelPData.map_xQ,
    ModularCurve.LevelPData.map_yQ, ModularCurve.LevelPData.variableChange, ModularCurve.cuspData_xP,
    ModularCurve.cuspData_yP, ModularCurve.cuspData_xQ, ModularCurve.cuspData_yQ] at hX hY hXq hYq hX' hY' hXq' hYq'

  obtain ⟨eX1, eY1⟩ := ModularCurve.FullLevel.AuxLevel.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι' K hK γ hγ τ hτ C₀ hC₀ μ hμ ![n, 0] hv D.xP D.yP
    (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).xP
    (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).yP hX hY hX' hY'
  obtain ⟨eX2, eY2⟩ := ModularCurve.FullLevel.AuxLevel.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ ι hι' K hK γ hγ τ hτ C₀ hC₀ μ hμ ![0, -n] hw D.xQ D.yQ
    (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).xQ
    (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).yQ hXq hYq hXq' hYq'

  have invmul : ∀ (k : ℕ) (a : ↥K), ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ k * ((((μ : (↥K)ˣ) : ↥K) ^ k) * a) = a := by
    intro k a
    rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have c1x : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP = (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).xP := by
    rw [eX1, invmul]
  have c1y : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP = (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).yP := by
    rw [eY1, invmul]
  have c2x : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xQ = (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).xQ := by
    rw [eX2, invmul]
  have c2y : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yQ = (LevelPData.relabel W ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) D).yQ := by
    rw [eY2, invmul]

  have hread : ∀ (Z : ↥K) (ζu : Lˣ) (hζu : IsPrimitiveRoot (ζu : L) (q * ℓ)) (u' : Fin 2 → ZMod (q * ℓ)), u' ≠ 0 →
      (algebraMap ↥K (LaurentSeries L)) Z =
        ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L (q * ℓ) ζu u').1 - C₀.r) →
      Z ≠ 0 := by
    intro Z ζu hζu u' hu' hZ h0
    rw [h0, map_zero] at hZ
    have hu : ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have h2 := (mul_eq_zero.mp hZ.symm).resolve_left hu
    rw [hC₀.2.1, map_neg, sub_neg_eq_add] at h2
    exact H1Curve.X_ne_zero L ι (q * ℓ) ζu hζu u' hu' h2
  have hξu : IsPrimitiveRoot (((hξ.isUnit (NeZero.ne (q * ℓ))).unit : Lˣ) : L) (q * ℓ) := by
    rw [IsUnit.unit_spec]; exact hξ
  have hx1 := hread _ _ hξu _ hv' hX'
  have hx2 := hread _ _ hξu _ hw' hXq'

  rw [c1x, c1y, c2x, c2y]
  exact H34A.finish W _ D hx1 hx2

end S_ModularCurve_FullLevel_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom
end P2MW
export P2MW.S_ModularCurve_FullLevel_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom (solution)
