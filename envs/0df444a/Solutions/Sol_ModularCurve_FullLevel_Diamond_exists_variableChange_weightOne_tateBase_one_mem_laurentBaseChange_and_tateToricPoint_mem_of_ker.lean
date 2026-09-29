-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/19ecb04a-a039-5066-ab4b-56bcd8cc60cf

import Mathlib
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
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint
import Theorems.Thm_ModularCurve_exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "UpperHalfPlane~I"
open ModularCurve HahnSeries CongruenceSubgroup WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups ModularForm

namespace R4TateModelKHb

section Groups

variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ)

abbrev Γsl : Subgroup SL(2, ℤ) := CohCarrier.GammaH N₀ H

abbrev Γgl : Subgroup (GL (Fin 2) ℝ) := (Γsl N₀ H : Subgroup (GL (Fin 2) ℝ))

scoped instance : (Γsl N₀ H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N₀ H)

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γgl N₀ H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH N₀ H)]
  exact AddSubgroup.mem_zmultiples _

end Groups

section GroupsHb

variable (M' ℓg : ℕ) [NeZero M'] [NeZero ℓg] (hℓgM' : ℓg ∣ M')

abbrev Hb : Subgroup (ZMod M')ˣ := (ZMod.unitsMap hℓgM').ker

theorem entries_of_mem_Hb {γ : SL(2, ℤ)} (hγ : γ ∈ Γsl M' (Hb M' ℓg hℓgM')) :
    ((γ 1 0 : ℤ) : ZMod M') = 0 ∧ ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by
  obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  refine ⟨Gamma0_mem.mp h0, ?_⟩
  rw [MonoidHom.mem_ker] at hH
  have h := congrArg (fun u : (ZMod ℓg)ˣ => (u : ZMod ℓg)) hH
  simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
    Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one] at h
  rwa [ZMod.castHom_apply, ZMod.cast_intCast hℓgM'] at h

theorem Γsl_le_levelGroup_Hb :
    Γsl M' (Hb M' ℓg hℓgM') ≤ Gamma1 ℓg ⊓ Gamma0 (1 * ℓg) := by
  intro γ hγ
  obtain ⟨hc, hd⟩ := entries_of_mem_Hb M' ℓg hℓgM' hγ
  have hcZ : ((M' : ℕ) : ℤ) ∣ (γ 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have hℓZ : ((ℓg : ℕ) : ℤ) ∣ ((M' : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hℓgM'
  have hcℓ : ((γ 1 0 : ℤ) : ZMod ℓg) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hℓZ.trans hcZ)
  have hc1ℓ : ((γ 1 0 : ℤ) : ZMod (1 * ℓg)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by rw [one_mul]; exact hℓZ.trans hcZ)
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ; rwa [Matrix.det_fin_two] at this
  have ha : ((γ 0 0 : ℤ) : ZMod ℓg) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod ℓg)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hcℓ, hd, mul_one, mul_zero, sub_zero] at h
    exact h
  refine Subgroup.mem_inf.mpr ⟨?_, Gamma0_mem.mpr hc1ℓ⟩
  exact (Gamma1_mem ℓg γ).mpr ⟨ha, hd, hcℓ⟩

theorem Γsl_le_Gamma0_one : Γsl M' (Hb M' ℓg hℓgM') ≤ Gamma0 1 := by
  intro γ hγ
  obtain ⟨hc, -⟩ := entries_of_mem_Hb M' ℓg hℓgM' hγ
  refine Gamma0_mem.mpr ?_
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
  exact (Int.natCast_dvd_natCast.mpr (one_dvd M')).trans hc

theorem Γgl_le_levelGroup_Hb :
    Γgl M' (Hb M' ℓg hℓgM') ≤
      ((Gamma1 ℓg ⊓ Gamma0 (1 * ℓg) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Γsl_le_levelGroup_Hb M' ℓg hℓgM')

theorem Γgl_le_Gamma0_one :
    Γgl M' (Hb M' ℓg hℓgM') ≤ ((Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Γsl_le_Gamma0_one M' ℓg hℓgM')

end GroupsHb

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ofPowerSeries_coeff_natCast (P : PowerSeries R) (n : ℕ) :
    (ofPowerSeries ℤ R P).coeff (n : ℤ) = PowerSeries.coeff n P :=
  ofPowerSeries_apply_coeff P n

theorem ofPowerSeries_coeff_of_neg (P : PowerSeries R) {m : ℤ} (hm : m < 0) :
    (ofPowerSeries ℤ R P).coeff m = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  rintro ⟨n, hn⟩
  first | omega | (simp at hn; done) | (simp at hn; omega)

theorem coeffMap_ofPowerSeries (f : R →+* S) (P : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R P) = ofPowerSeries ℤ S (P.map f) := by
  ext m
  rw [coeffMap_coeff]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ofPowerSeries_coeff_of_neg P hm, ofPowerSeries_coeff_of_neg _ hm, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [ofPowerSeries_coeff_natCast, ofPowerSeries_coeff_natCast, PowerSeries.coeff_map]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext m
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

def expandZ (N : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => if N ∣ m then PowerSeries.coeff (m / N) p else 0

theorem coeff_expandZ (N : ℕ) (p : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.coeff m (expandZ N p) = if N ∣ m then PowerSeries.coeff (m / N) p else 0 :=
  PowerSeries.coeff_mk _ _

theorem ofPowerSeries_map_expandZ (N : ℕ) [NeZero N] (p : PowerSeries ℤ) :
    ofPowerSeries ℤ R ((expandZ N p).map (Int.castRingHom R)) =
      qExpand R N (ofPowerSeries ℤ R (p.map (Int.castRingHom R))) := by
  ext m
  rcases lt_or_ge m 0 with hm | hm
  · rw [ofPowerSeries_coeff_of_neg _ hm]
    by_cases hdvd : (N : ℤ) ∣ m
    · obtain ⟨k, rfl⟩ := hdvd
      rw [qExpand_coeff_mul, ofPowerSeries_coeff_of_neg]
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      by_contra hk
      exact absurd hm (not_lt.mpr (mul_nonneg hN.le (not_lt.mp hk)))
    · rw [qExpand_coeff_of_not_dvd N _ hdvd]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [ofPowerSeries_coeff_natCast, PowerSeries.coeff_map, coeff_expandZ]
    by_cases hdvd : N ∣ n
    · obtain ⟨k, rfl⟩ := hdvd
      rw [if_pos (Dvd.intro k rfl), Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero (NeZero.ne N)),
        Nat.cast_mul, qExpand_coeff_mul, ofPowerSeries_coeff_natCast, PowerSeries.coeff_map]
    · rw [if_neg hdvd, map_zero, qExpand_coeff_of_not_dvd]
      exact fun h => hdvd (Int.natCast_dvd_natCast.mp h)

end Laurent

section Modular

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ)

def IsModular (k : ℤ) (z : LaurentSeries L) : Prop :=
  ∃ (f : ModularForm (Γgl N₀ H) k) (P : PowerSeries L),
    z = ofPowerSeries ℤ L P ∧ qExpansion 1 (⇑f) = P.map ι

variable {ι N₀ H}

theorem IsModular.of_form {k : ℤ} (f : ModularForm (Γgl N₀ H) k) (P : PowerSeries L)
    (h : qExpansion 1 (⇑f) = P.map ι) : IsModular ι N₀ H k (ofPowerSeries ℤ L P) :=
  ⟨f, P, rfl, h⟩

theorem IsModular.add {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N₀ H k z)
    (hw : IsModular ι N₀ H k w) : IsModular ι N₀ H k (z + w) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  obtain ⟨g, Q, rfl, hg⟩ := hw
  refine ⟨f + g, P + Q, by rw [map_add], ?_⟩
  rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N₀ H) f g, hf, hg, map_add]

theorem IsModular.smul {k : ℤ} {z : LaurentSeries L} (a : L) (hz : IsModular ι N₀ H k z) :
    IsModular ι N₀ H k (HahnSeries.C a * z) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  refine ⟨(ι a) • f, PowerSeries.C a * P, by rw [map_mul, ofPowerSeries_C], ?_⟩
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N₀ H) (ι a) f,
    hf, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]

theorem IsModular.neg {k : ℤ} {z : LaurentSeries L} (hz : IsModular ι N₀ H k z) :
    IsModular ι N₀ H k (-z) := by
  have h := hz.smul (-1)
  rwa [map_neg, map_one, neg_one_mul] at h

theorem IsModular.sub {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N₀ H k z)
    (hw : IsModular ι N₀ H k w) : IsModular ι N₀ H k (z - w) := by
  rw [sub_eq_add_neg]; exact hz.add hw.neg

theorem IsModular.mul {k k' : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N₀ H k z)
    (hw : IsModular ι N₀ H k' w) : IsModular ι N₀ H (k + k') (z * w) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  obtain ⟨g, Q, rfl, hg⟩ := hw
  refine ⟨f.mul g, P * Q, by rw [map_mul], ?_⟩
  rw [ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods N₀ H) f g, hf, hg, map_mul]

theorem IsModular.cast {k k' : ℤ} (h : k = k') {z : LaurentSeries L} (hz : IsModular ι N₀ H k z) :
    IsModular ι N₀ H k' z := by
  subst h; exact hz

theorem IsModular.const (a : L) : IsModular ι N₀ H 0 (HahnSeries.C a) := by
  have h1 : IsModular ι N₀ H 0 (1 : LaurentSeries L) := by
    refine ⟨1, 1, by rw [map_one], ?_⟩
    rw [map_one]
    exact ModularForm.qExpansion_one
  simpa using h1.smul a

theorem IsModular.natCast (n : ℕ) : IsModular ι N₀ H 0 (n : LaurentSeries L) := by
  simpa using IsModular.const (ι := ι) (N₀ := N₀) (H := H) (n : L)

theorem IsModular.pow {k : ℤ} {z : LaurentSeries L} (hz : IsModular ι N₀ H k z) (n : ℕ) :
    IsModular ι N₀ H (n * k) (z ^ n) := by
  induction n with
  | zero => simpa using IsModular.const (ι := ι) (N₀ := N₀) (H := H) (1 : L)
  | succ n ih =>
    rw [pow_succ]
    exact (ih.mul hz).cast (by push_cast; ring)

theorem ofNat_eq_C (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : LaurentSeries L) = HahnSeries.C (OfNat.ofNat n : L) := (map_ofNat _ n).symm

theorem IsModular.ofNat_mul {k : ℤ} {z : LaurentSeries L} (n : ℕ) [n.AtLeastTwo]
    (hz : IsModular ι N₀ H k z) : IsModular ι N₀ H k ((OfNat.ofNat n : LaurentSeries L) * z) := by
  rw [ofNat_eq_C]; exact hz.smul _

theorem IsModular.of_form_le {Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γgl N₀ H ≤ Γ') {k : ℤ}
    (F : ModularForm Γ' k) (P : PowerSeries L) (h : qExpansion 1 (⇑F) = P.map ι) :
    IsModular ι N₀ H k (ofPowerSeries ℤ L P) :=
  ⟨restrictForm hle F, P, rfl, by rw [coe_restrictForm]; exact h⟩

theorem IsModular.div_mem {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N₀ H k z)
    (hw : IsModular ι N₀ H k w) (hw0 : w ≠ 0) :
    z / w ∈ laurentBaseChange L (xHFunctionField N₀ H) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  obtain ⟨g, Q, rfl, hg⟩ := hw
  have hQ : Q ≠ 0 := by rintro rfl; exact hw0 (map_zero _)
  have hg0 : g ≠ 0 := by
    intro h0
    apply hQ
    have h1 : qExpansion 1 (⇑g) = 0 := by rw [h0, ModularForm.coe_zero, qExpansion_zero]
    rw [hg] at h1
    exact (PowerSeries.map_injective ι ι.injective) (by rw [h1, map_zero])
  have hcoeff : ∀ (R : PowerSeries L) (n : ℕ), (R.map ι).coeff n ∈ Set.range ι := fun R n =>
    ⟨PowerSeries.coeff n R, by rw [PowerSeries.coeff_map]⟩
  obtain ⟨x, hxK, hx⟩ :=
    ModularCurve.exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
      N₀ H f g hg0 L ι
      (fun n => by rw [hf]; exact hcoeff P n) (fun n => by rw [hg]; exact hcoeff Q n)
  rw [hf, hg, ← coeffMap_ofPowerSeries, ← coeffMap_ofPowerSeries, ← map_mul] at hx
  have hx' := coeffMap_injective ι.injective hx
  have hwne : ofPowerSeries ℤ L Q ≠ 0 := hw0
  rw [← hx', mul_div_cancel_right₀ _ hwne]
  exact hxK

end Modular

section Series

variable {R S : Type*} [CommRing R] [CommRing S]

scoped instance instCharZeroLaurent (L : Type*) [Field L] [CharZero L] : CharZero (LaurentSeries L) :=
  charZero_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective

theorem C_inv_natCast (L : Type*) [Field L] (n : ℕ) :
    HahnSeries.C ((n : L)⁻¹) = ((n : LaurentSeries L))⁻¹ := by
  rw [map_inv₀, map_natCast]

variable (R) in

def toricX (p : ℕ) (c : Rˣ) : PowerSeries R :=
  PowerSeries.mk fun m =>
    if m = 0 then (c : R) * Ring.inverse (1 - (c : R)) ^ 2
    else (∑ d ∈ m.divisors, if p ∣ d then
            ((m / d : ℕ) : R) * ((c : R) ^ (m / d) + ((c⁻¹ : Rˣ) : R) ^ (m / d)) else 0)
      - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)

variable (R) in

def toricY (p : ℕ) (c : Rˣ) : PowerSeries R :=
  PowerSeries.mk fun m =>
    if m = 0 then (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3
    else (∑ d ∈ m.divisors, if p ∣ d then
            ((m / d).choose 2 : R) * (c : R) ^ (m / d)
              - ((m / d + 1).choose 2 : R) * ((c⁻¹ : Rˣ) : R) ^ (m / d) else 0)
      + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : R) else 0)

theorem tateToricPoint_fst' (p : ℕ) (c : Rˣ) :
    (tateToricPoint R p c).1 = ofPowerSeries ℤ R (toricX R p c) := rfl

theorem tateToricPoint_snd' (p : ℕ) (c : Rˣ) :
    (tateToricPoint R p c).2 = ofPowerSeries ℤ R (toricY R p c) := rfl

theorem toricX_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (p : ℕ) (c : Fˣ) :
    (toricX F p c).map f = toricX K p (Units.map (f : F →* K) c) := by
  ext m
  simp only [toricX, PowerSeries.coeff_map, PowerSeries.coeff_mk, Units.coe_map, MonoidHom.coe_coe,
    Units.coe_map_inv]
  by_cases hm : m = 0
  · simp only [hm, ↓reduceIte, Ring.inverse_eq_inv', map_mul, map_pow, map_inv₀, map_sub, map_one]
  · simp only [hm, ↓reduceIte, map_sub, map_sum, map_mul, map_natCast, map_add, map_pow, map_ofNat,
      apply_ite f, map_zero]

theorem slotSubst_tateUnivX_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (p : ℕ) (c : Fˣ)
    (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (slotSubst F p c j tateUnivX).map f = slotSubst K p (Units.map (f : F →* K) c) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_map, ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp n,
    ModularCurve.coeff_slotSubst_tateUnivX p _ j hj hjp n]
  simp only [map_add, map_sum, map_mul, map_natCast, map_pow, map_sub, apply_ite f, map_zero, map_ofNat,
    Units.coe_map, MonoidHom.coe_coe, Units.coe_map_inv]

end Series

section Abscissa

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ) (p n : ℕ) [NeZero p] [NeZero n] (hpn : p ∣ n)
variable (hle : Γgl N₀ H ≤ ((Gamma1 n ⊓ Gamma0 (p * n) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))

def Xc (x : LaurentSeries L) : LaurentSeries L := x + HahnSeries.C ((12 : L)⁻¹)

def Yc (x y : LaurentSeries L) : LaurentSeries L := 2 * y + x

theorem Xc_def (x : LaurentSeries L) : Xc x = x + HahnSeries.C ((12 : L)⁻¹) := rfl
theorem Yc_def (x y : LaurentSeries L) : Yc x y = 2 * y + x := rfl

theorem coeff_C_ι (a : L) (m : ℕ) :
    ι (PowerSeries.coeff m (PowerSeries.C a)) = if m = 0 then ι a else 0 := by
  rw [PowerSeries.coeff_C]; split_ifs <;> simp

variable {p n}

theorem units_map_ne_one {c : Lˣ} (hc1 : (c : L) ≠ 1) : Units.map (ι : L →* ℂ) c ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h'
  exact hc1 (ι.injective (by rw [h', map_one]))

theorem units_map_pow_eq_one {c : Lˣ} (hc : c ^ n = 1) : (Units.map (ι : L →* ℂ) c) ^ n = 1 := by
  rw [← map_pow, hc, map_one]

include hpn hle in

theorem isModular_XT (c : Lˣ) (hc : c ^ n = 1) (hc1 : (c : L) ≠ 1) :
    IsModular ι N₀ H 2 (Xc (toricPoint L p (c : L)).1) := by
  have h12 : ι (12 : L)⁻¹ = 1 / 12 := by rw [map_inv₀, map_ofNat, one_div]
  set cC : ℂˣ := Units.map (ι : L →* ℂ) c with hcC
  have hcn : cC ^ n = 1 := units_map_pow_eq_one ι hc
  have hc1' : cC ≠ 1 := units_map_ne_one ι hc1
  obtain ⟨F, hF⟩ :=
    ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_tateToricPoint p n hpn cC hcn hc1'
  rw [Xc_def, ← tateToricPoint_eq_toricPoint, tateToricPoint_fst', ← ofPowerSeries_C, ← map_add]
  refine IsModular.of_form_le hle F _ ?_
  ext m
  rw [hF m, map_add, map_add, toricX_map, ← hcC, tateToricPoint_fst', ofPowerSeries_coeff_natCast,
    PowerSeries.coeff_map, coeff_C_ι, h12, add_comm]

include hpn hle in

theorem isModular_XN (c : Lˣ) (hc : c ^ n = 1) (b : ℕ) (hb0 : 0 < b) (hbp : b < p) :
    IsModular ι N₀ H 2 (Xc (nonToricPoint L p c b).1) := by
  have h12 : ι (12 : L)⁻¹ = 1 / 12 := by rw [map_inv₀, map_ofNat, one_div]
  set cC : ℂˣ := Units.map (ι : L →* ℂ) c with hcC
  have hcn : cC ^ n = 1 := units_map_pow_eq_one ι hc
  obtain ⟨F, hF⟩ :=
    ModularCurve.exists_modularForm_gamma1_inf_gamma0_mul_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
      p n hpn cC hcn b hb0 hbp
  rw [Xc_def, nonToricPoint_fst, ← ofPowerSeries_C, ← map_add]
  refine IsModular.of_form_le hle F _ ?_
  ext m
  rw [hF m, map_add, map_add, slotSubst_tateUnivX_map ι p c b hb0 hbp, ← hcC,
    PowerSeries.coeff_map, coeff_C_ι, h12, add_comm]

end Abscissa

section Eisenstein

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ) (p : ℕ) [NeZero p]
variable (hle0 : Γgl N₀ H ≤ ((Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))

theorem eisenstein4_eq : eisenstein4 = 1 - 48 * tateA4 := by
  ext n
  have h48 : (48 : PowerSeries ℤ) = PowerSeries.C 48 := by rw [map_ofNat]
  rw [map_sub, h48, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, coeff_tateA4]
  simp only [eisenstein4, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ↓reduceIte, mul_neg, zero_sub, neg_neg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

theorem eisenstein6_eq : eisenstein6 = 1 - 72 * tateA4 + 864 * tateA6 := by
  ext n
  have h72 : (72 : PowerSeries ℤ) = PowerSeries.C 72 := by rw [map_ofNat]
  have h864 : (864 : PowerSeries ℤ) = PowerSeries.C 864 := by rw [map_ofNat]
  rw [map_add, map_sub, h72, h864, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_one,
    coeff_tateA4, coeff_tateA6]
  simp only [eisenstein6, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ↓reduceIte, mul_neg, zero_sub, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    linear_combination (72 : ℤ) * twelve_mul_tateB d

theorem gamma0_one_le_SL : ((Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

theorem intCast_comp (f : L →+* ℂ) : f.comp (Int.castRingHom L) = Int.castRingHom ℂ :=
  RingHom.ext_int _ _

include hle0 in

theorem isModular_qExpand_of_levelOne {k : ℤ} (E : ModularForm 𝒮ℒ k) (r : PowerSeries ℤ)
    (hE : qExpansion 1 (⇑E) = r.map (Int.castRingHom ℂ)) :
    IsModular ι N₀ H k (qExpand L p (laurentOfInt L r)) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0 (k := k) (M := 1) (N := p) (d := p)
    (by rw [mul_one]) (restrictForm gamma0_one_le_SL E)
  have hq : qExpansion 1 (⇑G) = ((expandZ p r).map (Int.castRingHom L)).map ι := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [← RingHom.comp_apply (PowerSeries.map ι) (PowerSeries.map (Int.castRingHom L)),
      ← PowerSeries.map_comp, intCast_comp, ofPowerSeries_map_expandZ, ← hE, hG]
    exact ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne p E
  have h := IsModular.of_form_le (ι := ι) hle0 G _ hq
  rwa [ofPowerSeries_map_expandZ] at h

theorem tateBase_a₁ : (tateBase L p).a₁ = 1 := by simp [tateBase, tateLaurent]
theorem tateBase_a₂ : (tateBase L p).a₂ = 0 := by simp [tateBase, tateLaurent]
theorem tateBase_a₃ : (tateBase L p).a₃ = 0 := by simp [tateBase, tateLaurent]
theorem tateBase_a₄ : (tateBase L p).a₄ = qExpand L p (laurentOfInt L tateA4) := by simp [tateBase]
theorem tateBase_a₆ : (tateBase L p).a₆ = qExpand L p (laurentOfInt L tateA6) := by simp [tateBase]

include hle0 in

theorem isModular_c4 : IsModular ι N₀ H 4 (1 - 48 * (tateBase L p).a₄) := by
  have h := isModular_qExpand_of_levelOne ι N₀ H p hle0 ModularForm.E₄ eisenstein4
    ModularCurve.qExpansion_E4_eq_map_eisenstein4
  rwa [eisenstein4_eq, map_sub, map_mul, map_one, map_sub, map_mul, map_one, map_ofNat, map_ofNat,
    ← tateBase_a₄] at h

include hle0 in

theorem isModular_c6 : IsModular ι N₀ H 6 (1 - 72 * (tateBase L p).a₄ + 864 * (tateBase L p).a₆) := by
  have h := isModular_qExpand_of_levelOne ι N₀ H p hle0 ModularForm.E₆ eisenstein6
    ModularCurve.qExpansion_E6_eq_map_mk
  rwa [eisenstein6_eq, map_add, map_sub, map_mul, map_mul, map_one, map_add, map_sub, map_mul, map_mul,
    map_one, map_ofNat, map_ofNat, map_ofNat, map_ofNat, ← tateBase_a₄, ← tateBase_a₆] at h

end Eisenstein

section Points

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N₀ : ℕ) [NeZero N₀] (H : Subgroup (ZMod N₀)ˣ) (p : ℕ) [NeZero p]
variable (hle0 : Γgl N₀ H ≤ ((Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))

open scoped Classical

theorem point_some_congr {T : Type*} [CommRing T] {V : WeierstrassCurve T} {x x' y y' : T}
    (hx : x = x') (hy : y = y') (h : V.toAffine.Nonsingular x y) (h' : V.toAffine.Nonsingular x' y') :
    (Point.some x y h : V.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem C_inv_ofNat (m : ℕ) [m.AtLeastTwo] :
    HahnSeries.C ((OfNat.ofNat m : L)⁻¹) = (OfNat.ofNat m : LaurentSeries L)⁻¹ := by
  rw [map_inv₀, map_ofNat]

variable {p} in

theorem equation_short {x y : LaurentSeries L} (h : (tateBase L p).toAffine.Equation x y) :
    y ^ 2 + x * y = x ^ 3 + (tateBase L p).a₄ * x + (tateBase L p).a₆ := by
  rw [Affine.equation_iff, tateBase_a₁, tateBase_a₂, tateBase_a₃] at h
  linear_combination h

variable {p} in

theorem Yc_sq {x y : LaurentSeries L} (h : (tateBase L p).toAffine.Equation x y) :
    Yc x y ^ 2 = 4 * Xc x ^ 3
      - HahnSeries.C ((12 : L)⁻¹) * (1 - 48 * (tateBase L p).a₄) * Xc x
      + HahnSeries.C ((216 : L)⁻¹) * (1 - 72 * (tateBase L p).a₄ + 864 * (tateBase L p).a₆) := by
  have h' := equation_short h
  rw [Yc_def, Xc_def, C_inv_ofNat, C_inv_ofNat]
  field_simp
  linear_combination (1492992 : LaurentSeries L) * h'

include hle0 in
variable {p} in
theorem isModular_Yc_sq {x y : LaurentSeries L} (h : (tateBase L p).toAffine.Equation x y)
    (hX : IsModular ι N₀ H 2 (Xc x)) : IsModular ι N₀ H 6 (Yc x y ^ 2) := by
  rw [Yc_sq h]
  refine ((((hX.pow 3).cast (by norm_num)).ofNat_mul 4).sub ?_).add ?_
  · rw [mul_assoc]
    exact (((isModular_c4 ι N₀ H p hle0).mul hX).cast (by norm_num)).smul _
  · exact (isModular_c6 ι N₀ H p hle0).smul _

theorem chord_identity {A : Type*} [Field A] {x₁ y₁ x₂ y₂ x₃ : A} (hx : x₁ ≠ x₂)
    (h₃ : x₃ = ((y₁ - y₂) / (x₁ - x₂)) ^ 2 + (y₁ - y₂) / (x₁ - x₂) - x₁ - x₂) :
    2 * ((2 * y₁ + x₁) * (2 * y₂ + x₂)) =
      (2 * y₁ + x₁) ^ 2 + (2 * y₂ + x₂) ^ 2 - (4 * (x₃ + x₁ + x₂) + 1) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have h3' : x₃ * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + (y₁ - y₂) * (x₁ - x₂) - (x₁ + x₂) * (x₁ - x₂) ^ 2 := by
    rw [h₃]; field_simp; ring
  linear_combination 4 * h3'

include hle0 in
variable {p} in

theorem isModular_Yc_mul {x₁ y₁ x₂ y₂ : LaurentSeries L}
    (h₁ : (tateBase L p).toAffine.Nonsingular x₁ y₁) (h₂ : (tateBase L p).toAffine.Nonsingular x₂ y₂)
    (hX₁ : IsModular ι N₀ H 2 (Xc x₁)) (hX₂ : IsModular ι N₀ H 2 (Xc x₂))
    (hsum : x₁ ≠ x₂ → ∃ (x₃ y₃ : LaurentSeries L) (h₃ : (tateBase L p).toAffine.Nonsingular x₃ y₃),
        (Point.some x₁ y₁ h₁ : (tateBase L p).toAffine.Point) + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
          IsModular ι N₀ H 2 (Xc x₃)) :
    IsModular ι N₀ H 6 (Yc x₁ y₁ * Yc x₂ y₂) := by
  by_cases hx : x₁ = x₂
  ·
    have hXe : Xc x₁ = Xc x₂ := by rw [Xc_def, Xc_def, hx]
    have hsq : Yc x₁ y₁ ^ 2 = Yc x₂ y₂ ^ 2 := by rw [Yc_sq h₁.1, Yc_sq h₂.1, hXe]
    have hY2 := isModular_Yc_sq ι N₀ H hle0 h₂.1 hX₂
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · rw [h, ← pow_two]; exact hY2
    · rw [h, neg_mul, ← pow_two]; exact hY2.neg
  ·
    obtain ⟨x₃, y₃, h₃, hsum, hX₃⟩ := hsum hx
    rw [Point.add_of_X_ne hx] at hsum
    obtain ⟨hx3, -⟩ := Point.some.inj hsum
    rw [Affine.slope_of_X_ne hx] at hx3
    simp only [Affine.addX, tateBase_a₁, tateBase_a₂, one_mul, sub_zero] at hx3
    have hch := chord_identity hx hx3.symm
    have key : Yc x₁ y₁ * Yc x₂ y₂ = HahnSeries.C ((2 : L)⁻¹) *
        (Yc x₁ y₁ ^ 2 + Yc x₂ y₂ ^ 2
          - 4 * (Xc x₃ + Xc x₁ + Xc x₂) * (Xc x₁ - Xc x₂) ^ 2) := by
      rw [Yc_def, Yc_def, Xc_def, Xc_def, Xc_def, C_inv_ofNat, C_inv_ofNat]
      field_simp
      linear_combination 1728 * hch
    rw [key]
    refine IsModular.smul _ ((((isModular_Yc_sq ι N₀ H hle0 h₁.1 hX₁).add
      (isModular_Yc_sq ι N₀ H hle0 h₂.1 hX₂)).sub ?_))
    rw [mul_assoc]
    exact ((((hX₃.add hX₁).add hX₂).mul ((hX₁.sub hX₂).pow 2)).cast (by norm_num)).ofNat_mul 4

end Points

section Nonvanishing

variable {L : Type} [Field L] [CharZero L]
variable (p : ℕ) [NeZero p]

theorem sum_divisors_ite_dvd_eq (f : ℕ → L) :
    (∑ d ∈ p.divisors, if p ∣ d then f d else 0) = f p := by
  have hN0 : p ≠ 0 := NeZero.ne p
  rw [Finset.sum_eq_single_of_mem p (Nat.mem_divisors_self p hN0)]
  · rw [if_pos dvd_rfl]
  · intro d hd hdN
    rw [if_neg]
    exact fun hNd => hdN (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) hNd)

theorem coeff_toricX_self (c : Lˣ) :
    PowerSeries.coeff p (toricX L p c) = (c : L) + ((c⁻¹ : Lˣ) : L) - 2 := by
  have hN0 : p ≠ 0 := NeZero.ne p
  simp only [toricX, PowerSeries.coeff_mk, hN0, ↓reduceIte, dvd_rfl, sum_divisors_ite_dvd_eq,
    Nat.div_self (Nat.pos_of_ne_zero hN0), Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, pow_one,
    one_mul, mul_one]

theorem coeff_toricY_self (c : Lˣ) :
    PowerSeries.coeff p (toricY L p c) = 1 - ((c⁻¹ : Lˣ) : L) := by
  have hN0 : p ≠ 0 := NeZero.ne p
  simp only [toricY, PowerSeries.coeff_mk, hN0, ↓reduceIte, dvd_rfl, sum_divisors_ite_dvd_eq,
    Nat.div_self (Nat.pos_of_ne_zero hN0), Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, pow_one,
    Nat.choose_succ_self, Nat.choose_self, Nat.cast_zero, zero_mul, one_mul, zero_sub]
  ring

theorem coeff_C_natCast_of_ne_zero (a : L) : (HahnSeries.C a : LaurentSeries L).coeff (p : ℤ) = 0 := by
  rw [HahnSeries.C_apply, coeff_single_of_ne]
  exact_mod_cast NeZero.ne p

theorem coeff_ofNat_mul (m : ℕ) [m.AtLeastTwo] (z : LaurentSeries L) (k : ℤ) :
    ((OfNat.ofNat m : LaurentSeries L) * z).coeff k = (OfNat.ofNat m : L) * z.coeff k := by
  rw [ofNat_eq_C, C_mul_eq_smul, coeff_smul, smul_eq_mul]

theorem D_ne_zero (c : Lˣ) (hc1 : (c : L) ≠ 1) :
    2 * (tateToricPoint L p c).1 + HahnSeries.C ((6 : L)⁻¹) ≠ 0 := by
  intro h
  rw [tateToricPoint_fst'] at h
  have hc := congrArg (fun z : LaurentSeries L => z.coeff (p : ℤ)) h
  rw [coeff_add, coeff_ofNat_mul, ofPowerSeries_coeff_natCast, coeff_toricX_self, coeff_C_natCast_of_ne_zero,
    coeff_zero, add_zero, Units.val_inv_eq_inv_val] at hc
  have hξ0 : (c : L) ≠ 0 := c.ne_zero
  have h2 : ((c : L) - 1) ^ 2 = 0 := by
    field_simp at hc
    linear_combination (1 / 2 : L) * hc
  exact hc1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))

theorem Y_ne_zero (c : Lˣ) (hc2 : (c : L) ^ 2 ≠ 1) :
    2 * (tateToricPoint L p c).2 + (tateToricPoint L p c).1 ≠ 0 := by
  intro h
  rw [tateToricPoint_fst', tateToricPoint_snd'] at h
  have hc := congrArg (fun z : LaurentSeries L => z.coeff (p : ℤ)) h
  rw [coeff_add, coeff_ofNat_mul, ofPowerSeries_coeff_natCast, ofPowerSeries_coeff_natCast, coeff_toricX_self,
    coeff_toricY_self, coeff_zero, Units.val_inv_eq_inv_val] at hc
  have hξ0 : (c : L) ≠ 0 := c.ne_zero
  have h2 : (c : L) ^ 2 = 1 := by
    field_simp at hc
    linear_combination hc
  exact hc2 h2

end Nonvanishing

section Main

open scoped Classical

theorem mem_range_of_mem {L : Type} [Field L] {F : IntermediateField L (LaurentSeries L)}
    {z : LaurentSeries L} (h : z ∈ F) : z ∈ Set.range ((↑) : ↥F → LaurentSeries L) :=
  ⟨⟨z, h⟩, rfl⟩

theorem main
    (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓg)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓg))
    (K'' : IntermediateField L (LaurentSeries L))
    (hK'' : K'' = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker)) :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 + HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2 + (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L 1).a₁ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₂ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₃ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₄ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₆ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧

      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).yP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L)) := by
  haveI hℓ0 : NeZero ℓg := ⟨hℓg.ne_zero⟩
  have hℓg11 : 11 ≤ ℓg := by omega

  set ζu : Lˣ := (hζ.isUnit hℓg.ne_zero).unit with hζu_def
  have hζu : IsPrimitiveRoot ((ζu : Lˣ) : L) ℓg := by rwa [hζu_def, IsUnit.unit_spec]
  have hζun : ζu ^ ℓg = 1 := by
    ext; rw [Units.val_pow_eq_pow_val, hζu.pow_eq_one, Units.val_one]
  obtain ⟨ι, -⟩ := hιζ
  subst hK''

  have hle := Γgl_le_levelGroup_Hb M' ℓg hℓgM'
  have hle0 := Γgl_le_Gamma0_one M' ℓg hℓgM'
  have h1n : 1 ∣ ℓg := one_dvd ℓg

  have hc₀1 : (ζu : L) ≠ 1 := hζu.ne_one (by omega)
  have hc₀2 : (ζu : L) ^ 2 ≠ 1 := hζu.pow_ne_one_of_pos_of_lt two_ne_zero (by omega)

  set A₀ := ModularCurve.tateBase L 1 with hA₀
  have hTP : ∀ c : Lˣ, tateToricPoint L 1 c = toricPoint L 1 (c : L) := fun c => tateToricPoint_eq_toricPoint L 1 c
  set x₀ : LaurentSeries L := (tateToricPoint L 1 ζu).1 with hx₀
  set y₀ : LaurentSeries L := (tateToricPoint L 1 ζu).2 with hy₀
  set D₀ : LaurentSeries L := 2 * x₀ + HahnSeries.C ((6 : L)⁻¹) with hD₀
  set Y₀ : LaurentSeries L := 2 * y₀ + x₀ with hY₀
  have hY₀' : Y₀ = Yc x₀ y₀ := rfl
  have hD : D₀ ≠ 0 := D_ne_zero 1 ζu hc₀1
  have hY : Y₀ ≠ 0 := Y_ne_zero 1 ζu hc₀2
  set u : LaurentSeries L := Y₀ / D₀ with hu_def
  have hu : u ≠ 0 := div_ne_zero hY hD
  have hui : (((Units.mk0 u hu)⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) = D₀ / Y₀ := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, hu_def, inv_div]
  have hx₀' : x₀ = (toricPoint L 1 (ζu : L)).1 := by rw [hx₀, hTP]
  have hy₀' : y₀ = (toricPoint L 1 (ζu : L)).2 := by rw [hy₀, hTP]
  have hD0X : D₀ = 2 * Xc x₀ := by
    rw [Xc_def, hD₀, mul_add, C_inv_ofNat, C_inv_ofNat]
    norm_num

  obtain ⟨h₀ns', -, -⟩ :=
    ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero L 1 (ζu : L) (ζu : L) ζu.ne_zero ζu.ne_zero hc₀1 hc₀1
  have h₀ns : A₀.toAffine.Nonsingular x₀ y₀ := by rw [hx₀', hy₀']; exact h₀ns'

  have hX0 : IsModular ι M' (Hb M' ℓg hℓgM') 2 (Xc x₀) := by
    rw [hx₀']; exact isModular_XT ι _ _ h1n hle ζu hζun hc₀1
  have hDm : IsModular ι M' (Hb M' ℓg hℓgM') 2 D₀ := by rw [hD0X]; exact hX0.ofNat_mul 2
  have hYsq : IsModular ι M' (Hb M' ℓg hℓgM') 6 (Y₀ ^ 2) := by
    rw [hY₀']; exact isModular_Yc_sq ι _ _ hle0 h₀ns.1 hX0
  have hc4 := isModular_c4 ι M' (Hb M' ℓg hℓgM') 1 hle0 (L := L)
  have hc6 := isModular_c6 ι M' (Hb M' ℓg hℓgM') 1 hle0 (L := L)
  have hY2 : Y₀ ^ 2 ≠ 0 := pow_ne_zero _ hY

  have hT : ∀ c : Lˣ, c ^ ℓg = 1 → (c : L) ≠ 1 →
      ∃ hns : A₀.toAffine.Nonsingular (toricPoint L 1 (c : L)).1 (toricPoint L 1 (c : L)).2,
        IsModular ι M' (Hb M' ℓg hℓgM') 2 (Xc (toricPoint L 1 (c : L)).1) ∧
        IsModular ι M' (Hb M' ℓg hℓgM') 6
          (Yc (toricPoint L 1 (c : L)).1 (toricPoint L 1 (c : L)).2 * Y₀) := by
    intro c hcn hc1
    obtain ⟨hcns, hdns, hinv, hmul⟩ :=
      ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero L 1 (c : L) (ζu : L) c.ne_zero ζu.ne_zero hc1 hc₀1
    have hXc := isModular_XT ι _ _ h1n hle c hcn hc1
    refine ⟨hcns, hXc, ?_⟩
    rw [hY₀']
    have h₀e : Point.some x₀ y₀ h₀ns = Point.some _ _ hdns := point_some_congr hx₀' hy₀' _ _
    refine isModular_Yc_mul ι _ _ hle0 hcns h₀ns hXc hX0 fun hx => ?_
    by_cases h1 : (c : L) * ζu = 1
    · exfalso
      have h0 := hinv h1
      rw [← h₀e, add_eq_zero_iff_eq_neg, Point.neg_some] at h0
      obtain ⟨hxx, -⟩ := Point.some.inj h0
      exact hx hxx
    · obtain ⟨hcdns, hsum⟩ := hmul h1
      have hXcd := isModular_XT ι _ _ h1n hle (c * ζu) (by rw [mul_pow, hcn, hζun, one_mul])
        (by rwa [Units.val_mul])
      rw [Units.val_mul] at hXcd
      exact ⟨_, _, hcdns, by rw [h₀e]; exact hsum, hXcd⟩

  set Cᵥ : WeierstrassCurve.VariableChange (LaurentSeries L) :=
    ⟨Units.mk0 u hu, HahnSeries.C (-(12 : L)⁻¹), HahnSeries.C (-(2 : L)⁻¹), HahnSeries.C ((24 : L)⁻¹)⟩ with hCᵥ
  have transport : ∀ D : ModularCurve.LevelPData (LaurentSeries L),
      IsModular ι M' (Hb M' ℓg hℓgM') 2 (Xc D.xP) →
      IsModular ι M' (Hb M' ℓg hℓgM') 6 (Yc D.xP D.yP * Y₀) →
      (D.variableChange Cᵥ).xP ∈ Set.range ((↑) : ↥(ModularCurve.laurentBaseChange L
          (ModularCurve.xHFunctionField M' (Hb M' ℓg hℓgM'))) → LaurentSeries L) ∧
      (D.variableChange Cᵥ).yP ∈ Set.range ((↑) : ↥(ModularCurve.laurentBaseChange L
          (ModularCurve.xHFunctionField M' (Hb M' ℓg hℓgM'))) → LaurentSeries L) := by
    intro D hXv hYv
    rw [hCᵥ]
    simp only [LevelPData.variableChange_xP, LevelPData.variableChange_yP, hui]
    refine ⟨mem_range_of_mem ?_, mem_range_of_mem ?_⟩
    · rw [map_neg, sub_neg_eq_add, ← Xc_def, div_pow, div_mul_eq_mul_div]
      exact IsModular.div_mem (k := 6) (((hDm.pow 2).mul hXv).cast (by norm_num)) hYsq hY2
    · have e : D.yP - HahnSeries.C (-(2 : L)⁻¹) * (D.xP - HahnSeries.C (-(12 : L)⁻¹))
          - HahnSeries.C ((24 : L)⁻¹) = HahnSeries.C ((2 : L)⁻¹) * Yc D.xP D.yP := by
        rw [Yc_def]
        simp only [map_neg, map_inv₀, map_ofNat]
        field_simp; ring
      have e' : (D₀ / Y₀) ^ 3 * (HahnSeries.C ((2 : L)⁻¹) * Yc D.xP D.yP) =
          D₀ ^ 3 * (HahnSeries.C ((2 : L)⁻¹) * (Yc D.xP D.yP * Y₀)) / (Y₀ ^ 2) ^ 2 := by
        rw [div_pow]; field_simp
      rw [e, e']
      exact IsModular.div_mem (k := 12) (((hDm.pow 3).mul (hYv.smul _)).cast (by norm_num))
        ((hYsq.pow 2).cast (by norm_num)) (pow_ne_zero _ hY2)
  refine ⟨Cᵥ, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show u * D₀ = Y₀
    rw [hu_def, div_mul_cancel₀ _ hD]
  ·
    refine mem_range_of_mem ?_
    rw [hCᵥ, variableChange_a₁, tateBase_a₁]
    have e : (1 : LaurentSeries L) + 2 * HahnSeries.C (-(2 : L)⁻¹) = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [hCᵥ, variableChange_a₂, tateBase_a₁, tateBase_a₂]
    have e : (0 : LaurentSeries L) - HahnSeries.C (-(2 : L)⁻¹) * 1 + 3 * HahnSeries.C (-(12 : L)⁻¹)
        - HahnSeries.C (-(2 : L)⁻¹) ^ 2 = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [hCᵥ, variableChange_a₃, tateBase_a₁, tateBase_a₃]
    have e : (0 : LaurentSeries L) + HahnSeries.C (-(12 : L)⁻¹) * 1 + 2 * HahnSeries.C ((24 : L)⁻¹) = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [hCᵥ, variableChange_a₄, tateBase_a₁, tateBase_a₂, tateBase_a₃, hui]
    have e : A₀.a₄ - HahnSeries.C (-(2 : L)⁻¹) * 0 + 2 * HahnSeries.C (-(12 : L)⁻¹) * 0
        - (HahnSeries.C ((24 : L)⁻¹) + HahnSeries.C (-(12 : L)⁻¹) * HahnSeries.C (-(2 : L)⁻¹)) * 1
        + 3 * HahnSeries.C (-(12 : L)⁻¹) ^ 2 - 2 * HahnSeries.C (-(2 : L)⁻¹) * HahnSeries.C ((24 : L)⁻¹)
        = HahnSeries.C (-(48 : L)⁻¹) * (1 - 48 * A₀.a₄) := by
      simp only [map_neg, map_inv₀, map_ofNat]
      field_simp; ring
    rw [e, div_pow, div_mul_eq_mul_div, show Y₀ ^ 4 = (Y₀ ^ 2) ^ 2 by ring]
    exact IsModular.div_mem (k := 12) (((hDm.pow 4).mul (hc4.smul _)).cast (by norm_num))
      ((hYsq.pow 2).cast (by norm_num)) (pow_ne_zero _ hY2)
  ·
    refine mem_range_of_mem ?_
    rw [hCᵥ, variableChange_a₆, tateBase_a₁, tateBase_a₂, tateBase_a₃, hui]
    have e : A₀.a₆ + HahnSeries.C (-(12 : L)⁻¹) * A₀.a₄ + HahnSeries.C (-(12 : L)⁻¹) ^ 2 * 0
        + HahnSeries.C (-(12 : L)⁻¹) ^ 3 - HahnSeries.C ((24 : L)⁻¹) * 0 - HahnSeries.C ((24 : L)⁻¹) ^ 2
        - HahnSeries.C (-(12 : L)⁻¹) * HahnSeries.C ((24 : L)⁻¹) * 1
        = HahnSeries.C ((864 : L)⁻¹) * (1 - 72 * A₀.a₄ + 864 * A₀.a₆) := by
      simp only [map_neg, map_inv₀, map_ofNat]
      field_simp; ring
    rw [e, div_pow, div_mul_eq_mul_div, show Y₀ ^ 6 = (Y₀ ^ 2) ^ 3 by ring]
    exact IsModular.div_mem (k := 18) (((hDm.pow 6).mul (hc6.smul _)).cast (by norm_num))
      ((hYsq.pow 3).cast (by norm_num)) (pow_ne_zero _ hY2)
  ·
    intro c hcℓ hc1
    have hc1' : (c : L) ≠ 1 := fun h => hc1 (Units.val_eq_one.mp h)
    obtain ⟨hns, hXv, hYv⟩ := hT c hcℓ hc1'
    have := transport ⟨(tateToricPoint L 1 c).1, (tateToricPoint L 1 c).2,
      (tateToricPoint L 1 c).1, (tateToricPoint L 1 c).2⟩ (by rw [hTP]; exact hXv) (by rw [hTP]; exact hYv)
    exact this

end Main

end R4TateModelKHb
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb"

open ModularCurve in
theorem solution
    (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓg)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓg))
    (K'' : IntermediateField L (LaurentSeries L))
    (hK'' : K'' = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker)) :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 + HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2 + (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L 1).a₁ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₂ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₃ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₄ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L 1).a₆ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧

      (∀ c : Lˣ, c ^ ℓg = 1 → c ≠ 1 →
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L) ∧
        ((⟨(ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2, (ModularCurve.tateToricPoint L 1 c).1, (ModularCurve.tateToricPoint L 1 c).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).yP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L)) :=
  R4TateModelKHb.main M' ℓg hℓg hℓg12 hℓgM' L ζ hζ hιζ K'' hK''

end S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker (solution)
