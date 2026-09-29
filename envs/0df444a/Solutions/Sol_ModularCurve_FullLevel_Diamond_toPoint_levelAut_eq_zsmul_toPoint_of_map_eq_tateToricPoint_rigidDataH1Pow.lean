-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/d6b709b4-1a14-50b8-8a5b-d2facc8dfef7

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
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
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_FullLevel_Diamond_levelAut_apply_eq_unit_pow_mul_of_coe_eq_tateToricPoint_variableChange
import Theorems.Thm_ModularCurve_LevelRelabelling_relabel_smul_variableChange
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
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

end H1Curve

namespace H1Tor

theorem fst_coeff_zero (L : Type) [Field L] (q : ℕ) (c : Lˣ) :
    (ModularCurve.tateToricPoint L q c).1.coeff 0 = (c : L) / (1 - (c : L)) ^ 2 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.toricPoint_fst,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]

theorem snd_coeff_zero (L : Type) [Field L] (q : ℕ) (c : Lˣ) :
    (ModularCurve.tateToricPoint L q c).2.coeff 0 = (c : L) ^ 2 / (1 - (c : L)) ^ 3 := by
  rw [ModularCurve.tateToricPoint_eq_toricPoint, ModularCurve.toricPoint_snd,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]

theorem R_ne_zero (L : Type) [Field L] [CharZero L] (q : ℕ) (ℓ : ℕ) (hℓ : Odd ℓ)
    (c : Lˣ) (hc : c ^ ℓ = 1) (hc1 : c ≠ 1) :
    2 * (ModularCurve.tateToricPoint L q c).2 + (ModularCurve.tateToricPoint L q c).1 ≠ 0 := by
  intro h0
  have h := congrArg (fun s : LaurentSeries L => s.coeff 0) h0
  simp only [HahnSeries.coeff_zero] at h
  rw [HahnSeries.coeff_add, show (2 : LaurentSeries L) = HahnSeries.C (2 : L) from (map_ofNat HahnSeries.C 2).symm,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, snd_coeff_zero, fst_coeff_zero, smul_eq_mul] at h
  have hc1' : (1 : L) - (c : L) ≠ 0 := by
    rw [sub_ne_zero]; intro e; apply hc1; ext; rw [Units.val_one]; exact e.symm
  have hc0 : (c : L) ≠ 0 := c.ne_zero
  have hcm1 : (c : L) ≠ -1 := by
    intro e
    have : ((c : L)) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    rw [e, hℓ.neg_one_pow] at this
    norm_num at this
  field_simp at h
  have : (c : L) * ((c : L) + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with e | e
  · exact hc0 e
  · exact hcm1 (by linear_combination e)

theorem X_ne_zero (L : Type) [Field L] [CharZero L] (ι : L →+* ℂ) (q : ℕ) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (c : Lˣ) (hc : c ^ ℓ = 1) (hc1 : c ≠ 1) :
    (ModularCurve.tateToricPoint L q c).1 + HahnSeries.C ((12 : L)⁻¹) ≠ 0 := by
  intro h0
  have h := congrArg (fun s : LaurentSeries L => s.coeff 0) h0
  simp only [HahnSeries.coeff_zero] at h
  rw [HahnSeries.coeff_add, fst_coeff_zero, HahnSeries.C_apply, HahnSeries.coeff_single_same] at h
  have hc1' : (1 : L) - (c : L) ≠ 0 := by
    rw [sub_ne_zero]; intro e; apply hc1; ext; rw [Units.val_one]; exact e.symm
  have hN : ((c : L)) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  apply H1Curve.sq_add_ten_mul_add_one_ne_zero ι hℓ hN
  field_simp at h
  linear_combination h

end H1Tor

namespace TPAux
open ModularCurve WeierstrassCurve
open scoped Classical

section Core

variable (F : Type) [Field F] [CharZero F] (q : ℕ) [NeZero q]

theorem toric_nonsingular (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (tateBase F q).toAffine.Nonsingular (toricPoint F q c).1 (toricPoint F q c).2 := by
  obtain ⟨h, -, -⟩ := ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero F q c c hc0 hc0 hc1 hc1
  exact h

theorem toric_nsmul (N : ℕ) (hN : 2 ≤ N) (ζ : F) (hζ : IsPrimitiveRoot ζ N) (m : ℕ) :
    (N ∣ m → m • (Affine.Point.some _ _ (toric_nonsingular F q ζ (hζ.ne_zero (by omega)) (hζ.ne_one (by omega))) :
        (tateBase F q).toAffine.Point) = 0) ∧
    (∀ hm : ¬ N ∣ m, m • (Affine.Point.some _ _ (toric_nonsingular F q ζ (hζ.ne_zero (by omega)) (hζ.ne_one (by omega))) :
        (tateBase F q).toAffine.Point) =
      Affine.Point.some _ _ (toric_nonsingular F q (ζ ^ m) (pow_ne_zero _ (hζ.ne_zero (by omega)))
        (by rwa [Ne, hζ.pow_eq_one_iff_dvd]))) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  induction m with
  | zero => exact ⟨fun _ => by rw [zero_nsmul], fun h => absurd (dvd_zero N) h⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    by_cases hm : N ∣ m
    ·
      have hm1 : ¬ N ∣ m + 1 := fun h => by
        have := (Nat.dvd_add_right hm).mp h
        exact absurd (Nat.le_of_dvd one_pos this) (by omega)
      refine ⟨fun h => absurd h hm1, fun _ => ?_⟩
      rw [succ_nsmul, ih1 hm, zero_add]
      have hpow : ζ ^ (m + 1) = ζ := by
        rw [pow_succ, (hζ.pow_eq_one_iff_dvd m).mpr hm, one_mul]
      congr 1 <;> simp [hpow]
    · have hmne : ζ ^ m ≠ 1 := by rwa [Ne, hζ.pow_eq_one_iff_dvd]
      have hm0 : ζ ^ m ≠ 0 := pow_ne_zero _ hζ0
      obtain ⟨hc, hd, hsum1, hsum2⟩ :=
        ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero F q (ζ ^ m) ζ hm0 hζ0 hmne hζ1
      rw [succ_nsmul, ih2 hm]
      by_cases hm1 : N ∣ m + 1
      · refine ⟨fun _ => ?_, fun h => absurd hm1 h⟩
        have h1 : ζ ^ m * ζ = 1 := by rw [← pow_succ]; exact (hζ.pow_eq_one_iff_dvd _).mpr hm1
        exact hsum1 h1
      · refine ⟨fun h => absurd h hm1, fun _ => ?_⟩
        have h1 : ζ ^ m * ζ ≠ 1 := by rw [← pow_succ]; rwa [Ne, hζ.pow_eq_one_iff_dvd]
        obtain ⟨hcd, hsum⟩ := hsum2 h1
        rw [hsum]
        congr 1 <;> simp [pow_succ]

end Core
end TPAux

namespace TPAux
open ModularCurve WeierstrassCurve

theorem toric_zsmul (F : Type) [Field F] [CharZero F] (q : ℕ) [NeZero q] (N : ℕ) (hN : 2 ≤ N) (c : Fˣ)
    (hc : IsPrimitiveRoot c N) (a : ℤ) (ha : ¬ (N : ℤ) ∣ a)
    (h0 : (tateBase F q).toAffine.Nonsingular (tateToricPoint F q c).1 (tateToricPoint F q c).2)
    (h1 : (tateBase F q).toAffine.Nonsingular (tateToricPoint F q (c ^ a)).1 (tateToricPoint F q (c ^ a)).2) :
    a • (Affine.Point.some _ _ h0 : (tateBase F q).toAffine.Point) = Affine.Point.some _ _ h1 := by
  have hc' : IsPrimitiveRoot (c : F) N := IsPrimitiveRoot.coe_units_iff.mpr hc
  have hcN : c ^ N = 1 := hc.pow_eq_one

  set m : ℕ := (a % (N : ℤ)).toNat with hm
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (m : ℤ) = a % (N : ℤ) := by rw [hm, Int.toNat_of_nonneg (Int.emod_nonneg a (by omega))]
  have ha' : a = (m : ℤ) + (N : ℤ) * (a / (N : ℤ)) := by rw [hm0, Int.emod_add_mul_ediv]
  have hmN : ¬ N ∣ m := by
    intro h
    apply ha
    have : ((N : ℤ)) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr h
    rw [ha']; exact dvd_add this (dvd_mul_right _ _)

  obtain ⟨hkill, hmul⟩ := toric_nsmul F q N hN (c : F) hc' m
  obtain ⟨hkillN, -⟩ := toric_nsmul F q N hN (c : F) hc' N
  have eP : (Affine.Point.some _ _ h0 : (tateBase F q).toAffine.Point) =
      Affine.Point.some _ _ (toric_nonsingular F q (c : F) (hc'.ne_zero (by omega)) (hc'.ne_one (by omega))) := by
    congr 1 <;> rw [tateToricPoint_eq_toricPoint]
  have ecm : ((c ^ a : Fˣ) : F) = (c : F) ^ m := by
    rw [zpow_eq_zpow_emod' a hcN, ← hm0, zpow_natCast, Units.val_pow_eq_pow_val]
  have eQ : (Affine.Point.some _ _ h1 : (tateBase F q).toAffine.Point) =
      Affine.Point.some _ _ (toric_nonsingular F q ((c : F) ^ m) (pow_ne_zero _ (hc'.ne_zero (by omega)))
        (by rwa [Ne, hc'.pow_eq_one_iff_dvd])) := by
    congr 1 <;> rw [tateToricPoint_eq_toricPoint, ecm]
  rw [eP, eQ, ← hmul hmN, ha', add_zsmul, natCast_zsmul, mul_comm, ← smul_smul, natCast_zsmul, hkillN (dvd_refl N),
    zsmul_zero, add_zero]

end TPAux

set_option maxHeartbeats 4000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [DecidableEq ↥K]
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)

    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hC₀ : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)))

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).2 + (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1) * (2 * ((ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1) * (2 * ((ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1 + HahnSeries.C ((12 : L)⁻¹))))

    (W : WeierstrassCurve ↥K)
    (hW : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      W.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q)
    (D : ModularCurve.LevelPData ↥K)
    (hD : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      D.map (algebraMap ↥K (LaurentSeries L)) =
        ((⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀)) :
    W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
    ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP := by

  have hinst : (‹DecidableEq ↥K›) = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst hinst
  letI instK : DecidableEq ↥K := fun a b => Classical.propDecidable (a = b)
  haveI hN0 : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hNqℓ : q * ℓg ≠ 0 := Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero
  obtain ⟨ι, hι'⟩ := id hιξ
  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit with hξu

  have hξu' : IsPrimitiveRoot ((ξu : Lˣ) : L) (q * ℓg) := by rw [hξu, IsUnit.unit_spec]; exact hξ
  have hcq : IsPrimitiveRoot (ξu ^ q) ℓg := by
    have h := hξu'.pow (Nat.pos_of_ne_zero hNqℓ) (rfl : q * ℓg = q * ℓg)
    rw [← Units.val_pow_eq_pow_val] at h
    exact IsPrimitiveRoot.coe_units_iff.mp h
  have hcqL : IsPrimitiveRoot (((ξu ^ q : Lˣ)) : L) ℓg := IsPrimitiveRoot.coe_units_iff.mpr hcq
  have hc0ℓ : (ξu ^ q) ^ ℓg = 1 := hcq.pow_eq_one
  have hc0ne : ξu ^ q ≠ 1 := hcq.ne_one (by omega)
  have hγ10 : (ℓg : ℤ) ∣ (γ 1 0 : ℤ) := by
    have h1 : ((γ 1 0 : ℤ) : ZMod M') = 0 := by
      have := hγ; rw [CongruenceSubgroup.Gamma0_mem] at this; exact_mod_cast this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact (Int.natCast_dvd_natCast.mpr hℓgM').trans h1
  have hγ00 : ¬ (ℓg : ℤ) ∣ (γ 0 0 : ℤ) := by
    intro h
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have h1 : (ℓg : ℤ) ∣ 1 := by
      rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hγ10 _)
    have := Int.eq_one_of_dvd_one (by positivity) h1
    omega
  have hcwℓ : ((ξu ^ q) ^ ((γ 0 0 : ℤ))) ^ ℓg = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc0ℓ, one_zpow]
  have hcwne : (ξu ^ q) ^ ((γ 0 0 : ℤ)) ≠ 1 := by
    rw [Ne, hcq.zpow_eq_one_iff_dvd]; exact hγ00
  haveI : (ModularCurve.tateBase L q).IsElliptic := ⟨ModularCurve.isUnit_Δ_tateBase L q⟩

  have n0 : (ModularCurve.tateBase L q).toAffine.Nonsingular (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 := by
    rw [ModularCurve.tateToricPoint_eq_toricPoint]
    exact TPAux.toric_nonsingular L q _ (Units.ne_zero _) (fun h => hc0ne (Units.ext h))
  have nw : (ModularCurve.tateBase L q).toAffine.Nonsingular (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).1 (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).2 := by
    rw [ModularCurve.tateToricPoint_eq_toricPoint]
    exact TPAux.toric_nonsingular L q _ (Units.ne_zero _) (fun h => hcwne (Units.ext h))
  have htP0 : toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 = WeierstrassCurve.Affine.Point.some _ _ n0 := dif_pos n0
  have hmulw : ((γ 0 0 : ℤ)) • (WeierstrassCurve.Affine.Point.some _ _ n0 : (ModularCurve.tateBase L q).toAffine.Point) =
      WeierstrassCurve.Affine.Point.some _ _ nw :=
    TPAux.toric_zsmul L q ℓg (by omega) (ξu ^ q) hcq ((γ 0 0 : ℤ)) hγ00 n0 nw

  set g : Matrix (Fin 2) (Fin 2) ℤ := !![((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0, 0; 0, 1] with hg
  have hg00 : g 0 0 = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by rw [hg]; rfl
  have hg10 : g 1 0 = 0 := by rw [hg]; rfl
  have hg01 : g 0 1 = 0 := by rw [hg]; rfl
  have hg11 : g 1 1 = 1 := by rw [hg]; rfl

  have hPsum : g 0 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
      g 1 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 = WeierstrassCurve.Affine.Point.some _ _ nw := by
    rw [hg00, hg10, zero_zsmul, add_zero, htP0]
    exact hmulw
  have hQsum : g 0 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
      g 1 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 = WeierstrassCurve.Affine.Point.some _ _ n0 := by
    rw [hg01, hg11, zero_zsmul, zero_add, one_zsmul, htP0]
  have S1 : LevelPData.relabel (C₀ • ModularCurve.tateBase L q) g
      ((⟨(ModularCurve.tateToricPoint L q (ξu ^ q)).1, (ModularCurve.tateToricPoint L q (ξu ^ q)).2, (ModularCurve.tateToricPoint L q (ξu ^ q)).1, (ModularCurve.tateToricPoint L q (ξu ^ q)).2⟩ : ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀) =
      ((⟨(ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).1, (ModularCurve.tateToricPoint L q ((ξu ^ q) ^ ((γ 0 0 : ℤ)))).2, (ModularCurve.tateToricPoint L q (ξu ^ q)).1, (ModularCurve.tateToricPoint L q (ξu ^ q)).2⟩ : ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀) := by
    rw [ModularCurve.LevelRelabelling.relabel_smul_variableChange (ModularCurve.tateBase L q) C₀ g _ n0.left n0.left
      (by rw [hPsum]; exact WeierstrassCurve.Affine.Point.some_ne_zero _)
      (by rw [hQsum]; exact WeierstrassCurve.Affine.Point.some_ne_zero _)]
    congr 1
    show (⟨(ofPoint _ (g 0 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
        g 1 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2)).1, (ofPoint _ (g 0 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
        g 1 0 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2)).2, (ofPoint _ (g 0 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
        g 1 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2)).1, (ofPoint _ (g 0 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2 +
        g 1 1 • toPoint (ModularCurve.tateBase L q) (ModularCurve.tateToricPoint L q (ξu ^ q)).1 (ModularCurve.tateToricPoint L q (ξu ^ q)).2)).2⟩ : ModularCurve.LevelPData (LaurentSeries L)) = _
    rw [hPsum, hQsum]
    rfl

  have S2 := H34A.relabel_map_eq (F := LaurentSeries L) W g D
  rw [hW, hD, S1] at S2
  have hX := congrArg ModularCurve.LevelPData.xP hD
  have hY := congrArg ModularCurve.LevelPData.yP hD
  have hXq := congrArg ModularCurve.LevelPData.xQ hD
  have hX' := congrArg ModularCurve.LevelPData.xP S2
  have hY' := congrArg ModularCurve.LevelPData.yP S2
  have hXq' := congrArg ModularCurve.LevelPData.xQ S2
  simp only [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.map_yP, ModularCurve.LevelPData.map_xQ,
    ModularCurve.LevelPData.variableChange] at hX hY hXq hX' hY' hXq'
  obtain ⟨eX1, eY1⟩ := ModularCurve.FullLevel.Diamond.levelAut_apply_eq_unit_pow_mul_of_coe_eq_tateToricPoint_variableChange
    q M' hqM' ℓg hℓg hℓg12 hℓgM' L ξ hξ ι hι' H₁ hH₁ K hK γ hγ τ hτ C₀ hC₀ μ hμ (ξu ^ q) hc0ℓ hc0ne D.xP D.yP
    (LevelPData.relabel W g D).xP (LevelPData.relabel W g D).yP hX hY hX' hY'
  have invmul : ∀ (k : ℕ) (a : ↥K), ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ k * ((((μ : (↥K)ˣ) : ↥K) ^ k) * a) = a := by
    intro k a
    rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have c1x : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP = (LevelPData.relabel W g D).xP := by rw [eX1, invmul]
  have c1y : ((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP = (LevelPData.relabel W g D).yP := by rw [eY1, invmul]

  have hread : ∀ (Z : ↥K) (c : Lˣ), c ^ ℓg = 1 → c ≠ 1 →
      (algebraMap ↥K (LaurentSeries L)) Z =
        ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.tateToricPoint L q c).1 - C₀.r) → Z ≠ 0 := by
    intro Z c hc hc1 hZ h0
    rw [h0, map_zero] at hZ
    have hu : ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have h2 := (mul_eq_zero.mp hZ.symm).resolve_left hu
    rw [hC₀.2.1, map_neg, sub_neg_eq_add] at h2
    exact H1Tor.X_ne_zero L ι q ℓg hℓg.ne_zero c hc hc1 h2
  have hx1 := hread _ _ hcwℓ hcwne hX'
  have hx2 := hread _ _ hc0ℓ hc0ne hXq'
  obtain ⟨⟨h1, -⟩, e1, -⟩ := H34A.finish W g D hx1 hx2
  rw [c1x, c1y]
  refine ⟨h1, ?_⟩
  rw [← e1, hg00, hg10, zero_zsmul, add_zero]

end S_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow (solution)
