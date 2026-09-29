-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5fe36c41-184a-551c-a508-76e1f817a905

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_mem_laurentBaseChange_coeffMap_mul_qExpansion_eq_of_forall_coeff_mem_range
import Theorems.Thm_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Theorems.Thm_ModularCurve_qExpansion_E6_eq_map_mk
import Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane~I"
open ModularCurve HahnSeries CongruenceSubgroup WeierstrassCurve WeierstrassCurve.Affine
open scoped MatrixGroups ModularForm

namespace R4TateModelK

section Groups

variable (N M' : ℕ) [NeZero N] [NeZero M']

abbrev Γsl : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M')

abbrev Γgl : Subgroup (GL (Fin 2) ℝ) := (Γsl N M' : Subgroup (GL (Fin 2) ℝ))

scoped instance : NeZero (N ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (NeZero.ne N)) (NeZero.ne M')⟩

scoped instance : (Γsl N M').FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M'))

theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γgl N M').strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem
    (translation_mem_GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M'))]
  exact AddSubgroup.mem_zmultiples _

theorem entries_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Γsl N M') :
    ((γ 1 0 : ℤ) : ZMod (N ^ 2 * M')) = 0 ∧ ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  refine ⟨Gamma0_mem.mp h0, ?_⟩
  rw [ModularCurve.FullLevel.mem_levelH_iff] at hH
  have h := congrArg (fun u : (ZMod N)ˣ => (u : ZMod N)) hH
  simp only [ZMod.unitsMap, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units,
    Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one] at h
  rwa [ZMod.castHom_apply, ZMod.cast_intCast (ModularCurve.FullLevel.dvd_sq_mul N M')] at h

theorem Γsl_le_levelGroup : Γsl N M' ≤ Gamma1 N ⊓ Gamma0 (N ^ 2) := by
  intro γ hγ
  obtain ⟨hc, hd⟩ := entries_of_mem N M' hγ
  have hcN2 : ((γ 1 0 : ℤ) : ZMod (N ^ 2)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
    exact (Int.natCast_dvd_natCast.mpr (Dvd.intro _ rfl)).trans hc
  have hcN : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc ⊢
    exact (Int.natCast_dvd_natCast.mpr
      ((dvd_pow_self N two_ne_zero).trans (Dvd.intro _ rfl))).trans hc
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ; rwa [Matrix.det_fin_two] at this
  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod N)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hcN, hd, mul_one, mul_zero, sub_zero] at h
    exact h
  refine Subgroup.mem_inf.mpr ⟨?_, Gamma0_mem.mpr hcN2⟩
  exact (Gamma1_mem N γ).mpr ⟨ha, hd, hcN⟩

theorem Γsl_le_Gamma0 : Γsl N M' ≤ Gamma0 N := fun γ hγ =>
  Gamma0_mem.mpr ((Gamma1_mem N γ).mp (Γsl_le_levelGroup N M' hγ).1).2.2

theorem Γgl_le_levelGroup :
    Γgl N M' ≤ ((Gamma1 N ⊓ Gamma0 (N ^ 2) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Γsl_le_levelGroup N M')

theorem Γgl_le_Gamma0 : Γgl N M' ≤ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Γsl_le_Gamma0 N M')

end Groups

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ofPowerSeries_coeff_natCast (P : PowerSeries R) (n : ℕ) :
    (ofPowerSeries ℤ R P).coeff (n : ℤ) = PowerSeries.coeff n P :=
  ofPowerSeries_apply_coeff P n

theorem ofPowerSeries_coeff_of_neg (P : PowerSeries R) {m : ℤ} (hm : m < 0) :
    (ofPowerSeries ℤ R P).coeff m = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  rintro ⟨n, hn⟩
  first
    | (simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hn; omega)
    | (simp at hn; omega)
    | omega

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
variable (N M' : ℕ) [NeZero N] [NeZero M']

def IsModular (k : ℤ) (z : LaurentSeries L) : Prop :=
  ∃ (f : ModularForm (Γgl N M') k) (P : PowerSeries L),
    z = ofPowerSeries ℤ L P ∧ qExpansion 1 (⇑f) = P.map ι

variable {ι N M'}

theorem IsModular.of_form {k : ℤ} (f : ModularForm (Γgl N M') k) (P : PowerSeries L)
    (h : qExpansion 1 (⇑f) = P.map ι) : IsModular ι N M' k (ofPowerSeries ℤ L P) :=
  ⟨f, P, rfl, h⟩

theorem IsModular.add {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N M' k z)
    (hw : IsModular ι N M' k w) : IsModular ι N M' k (z + w) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  obtain ⟨g, Q, rfl, hg⟩ := hw
  refine ⟨f + g, P + Q, by rw [map_add], ?_⟩
  rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N M') f g, hf, hg, map_add]

theorem IsModular.smul {k : ℤ} {z : LaurentSeries L} (a : L) (hz : IsModular ι N M' k z) :
    IsModular ι N M' k (HahnSeries.C a * z) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  refine ⟨(ι a) • f, PowerSeries.C a * P, by rw [map_mul, ofPowerSeries_C], ?_⟩
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N M') (ι a) f,
    hf, map_mul, PowerSeries.map_C, PowerSeries.smul_eq_C_mul]

theorem IsModular.neg {k : ℤ} {z : LaurentSeries L} (hz : IsModular ι N M' k z) :
    IsModular ι N M' k (-z) := by
  have h := hz.smul (-1)
  rwa [map_neg, map_one, neg_one_mul] at h

theorem IsModular.sub {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N M' k z)
    (hw : IsModular ι N M' k w) : IsModular ι N M' k (z - w) := by
  rw [sub_eq_add_neg]; exact hz.add hw.neg

theorem IsModular.mul {k k' : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N M' k z)
    (hw : IsModular ι N M' k' w) : IsModular ι N M' (k + k') (z * w) := by
  obtain ⟨f, P, rfl, hf⟩ := hz
  obtain ⟨g, Q, rfl, hg⟩ := hw
  refine ⟨f.mul g, P * Q, by rw [map_mul], ?_⟩
  rw [ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods N M') f g, hf, hg, map_mul]

theorem IsModular.cast {k k' : ℤ} (h : k = k') {z : LaurentSeries L} (hz : IsModular ι N M' k z) :
    IsModular ι N M' k' z := by
  subst h; exact hz

theorem IsModular.const (a : L) : IsModular ι N M' 0 (HahnSeries.C a) := by
  have h1 : IsModular ι N M' 0 (1 : LaurentSeries L) := by
    refine ⟨1, 1, by rw [map_one], ?_⟩
    rw [map_one]
    exact ModularForm.qExpansion_one
  simpa using h1.smul a

theorem IsModular.natCast (n : ℕ) : IsModular ι N M' 0 (n : LaurentSeries L) := by
  simpa using IsModular.const (ι := ι) (N := N) (M' := M') (n : L)

theorem IsModular.pow {k : ℤ} {z : LaurentSeries L} (hz : IsModular ι N M' k z) (n : ℕ) :
    IsModular ι N M' (n * k) (z ^ n) := by
  induction n with
  | zero => simpa using IsModular.const (ι := ι) (N := N) (M' := M') (1 : L)
  | succ n ih =>
    rw [pow_succ]
    exact (ih.mul hz).cast (by push_cast; ring)

theorem ofNat_eq_C (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : LaurentSeries L) = HahnSeries.C (OfNat.ofNat n : L) := (map_ofNat _ n).symm

theorem IsModular.ofNat_mul {k : ℤ} {z : LaurentSeries L} (n : ℕ) [n.AtLeastTwo]
    (hz : IsModular ι N M' k z) : IsModular ι N M' k ((OfNat.ofNat n : LaurentSeries L) * z) := by
  rw [ofNat_eq_C]; exact hz.smul _

theorem IsModular.of_form_le {Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γgl N M' ≤ Γ') {k : ℤ}
    (F : ModularForm Γ' k) (P : PowerSeries L) (h : qExpansion 1 (⇑F) = P.map ι) :
    IsModular ι N M' k (ofPowerSeries ℤ L P) :=
  ⟨restrictForm hle F, P, rfl, by rw [coe_restrictForm]; exact h⟩

theorem IsModular.div_mem {k : ℤ} {z w : LaurentSeries L} (hz : IsModular ι N M' k z)
    (hw : IsModular ι N M' k w) (hw0 : w ≠ 0) :
    z / w ∈ laurentBaseChange L (xHFunctionField (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M')) := by
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
      (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M') f g hg0 L ι
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
variable (N M' : ℕ) [NeZero N] [NeZero M'] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)

def Xf (v : Fin 2 → ZMod N) : LaurentSeries L :=
  (cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)

def Yf (v : Fin 2 → ZMod N) : LaurentSeries L :=
  2 * (cuspPoint L N ξ v).2 + (cuspPoint L N ξ v).1

theorem Xf_def (v : Fin 2 → ZMod N) : Xf N ξ v = (cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹) := rfl
theorem Yf_def (v : Fin 2 → ZMod N) : Yf N ξ v = 2 * (cuspPoint L N ξ v).2 + (cuspPoint L N ξ v).1 := rfl

variable {N ξ}

include hξ in
theorem units_pow_N : ξ ^ N = 1 := by
  ext; rw [Units.val_pow_eq_pow_val, hξ.pow_eq_one, Units.val_one]

include hξ in
theorem map_pow_N (a : ℕ) : (Units.map (ι : L →* ℂ) (ξ ^ a)) ^ N = 1 := by
  rw [← map_pow, ← pow_mul, mul_comm, pow_mul, units_pow_N hξ, one_pow, map_one]

include hξ in
theorem val_pow_ne_one {a : ZMod N} (ha : a ≠ 0) : ((ξ ^ a.val : Lˣ) : L) ≠ 1 := by
  rw [Units.val_pow_eq_pow_val]
  exact hξ.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero a).mpr ha) (ZMod.val_lt a)

theorem ne_zero_of_apply_ne {v : Fin 2 → ZMod N} {i : Fin 2} (h : v i ≠ 0) : v ≠ 0 := by
  rintro rfl; exact h rfl

theorem fst_ne_zero_of_snd_eq_zero {v : Fin 2 → ZMod N} (hv : v ≠ 0) (h1 : v 1 = 0) : v 0 ≠ 0 := by
  intro h0; apply hv; funext i; fin_cases i <;> assumption

theorem coeff_C_ι (a : L) (n : ℕ) :
    ι (PowerSeries.coeff n (PowerSeries.C a)) = if n = 0 then ι a else 0 := by
  rw [PowerSeries.coeff_C]; split_ifs <;> simp

include hξ in

theorem isModular_Xf (v : Fin 2 → ZMod N) (hv : v ≠ 0) : IsModular ι N M' 2 (Xf N ξ v) := by
  have h12 : ι (12 : L)⁻¹ = 1 / 12 := by rw [map_inv₀, map_ofNat, one_div]
  by_cases h1 : v 1 = 0
  ·
    have ha : v 0 ≠ 0 := fst_ne_zero_of_snd_eq_zero hv h1
    set c : Lˣ := ξ ^ (v 0).val with hc
    set cC : ℂˣ := Units.map (ι : L →* ℂ) c with hcC
    have hcN : cC ^ N = 1 := map_pow_N ι hξ _
    have hc1 : cC ≠ 1 := by
      intro h
      have h' := congrArg (fun u : ℂˣ => (u : ℂ)) h
      simp only [hcC, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h'
      exact val_pow_ne_one hξ ha (ι.injective (by rw [h', map_one]))
    obtain ⟨F, hF⟩ := ModularCurve.exists_modularForm_qExpansion_coeff_eq_coeff_tateToricPoint N cC hcN hc1
    rw [Xf_def, cuspPoint_of_eq_zero _ h1, tateToricPoint_fst', ← hc, ← ofPowerSeries_C, ← map_add]
    refine IsModular.of_form_le (Γgl_le_levelGroup N M') F _ ?_
    ext n
    rw [hF n, map_add, map_add, toricX_map, ← hcC, tateToricPoint_fst', ofPowerSeries_coeff_natCast,
      PowerSeries.coeff_map, coeff_C_ι, h12, add_comm]
  ·
    set b : ℕ := (v 1).val with hb
    have hb0 : 0 < b := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr h1)
    have hbN : b < N := ZMod.val_lt _
    set c : Lˣ := ξ ^ (v 0).val with hc
    set cC : ℂˣ := Units.map (ι : L →* ℂ) c with hcC
    have hcN : cC ^ N = 1 := map_pow_N ι hξ _
    obtain ⟨F, hF⟩ :=
      ModularCurve.exists_modularForm_qExpansion_coeff_eq_coeff_slotSubst_tateUnivX N cC hcN b hb0 hbN
    rw [Xf_def, cuspPoint_of_ne_zero _ h1, nonToricPoint_fst, ← hc, ← hb, ← ofPowerSeries_C, ← map_add]
    refine IsModular.of_form_le (Γgl_le_levelGroup N M') F _ ?_
    ext n
    rw [hF n, map_add, map_add, slotSubst_tateUnivX_map ι N c b hb0 hbN, ← hcC,
      PowerSeries.coeff_map, coeff_C_ι, h12, add_comm]

end Abscissa

section Eisenstein

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N M' : ℕ) [NeZero N] [NeZero M']

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

theorem isModular_qExpand_of_levelOne {k : ℤ} (E : ModularForm 𝒮ℒ k) (p : PowerSeries ℤ)
    (hE : qExpansion 1 (⇑E) = p.map (Int.castRingHom ℂ)) :
    IsModular ι N M' k (qExpand L N (laurentOfInt L p)) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0 (k := k) (M := 1) (N := N) (d := N)
    (by rw [mul_one]) (restrictForm gamma0_one_le_SL E)
  have hq : qExpansion 1 (⇑G) = ((expandZ N p).map (Int.castRingHom L)).map ι := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [← RingHom.comp_apply (PowerSeries.map ι) (PowerSeries.map (Int.castRingHom L)),
      ← PowerSeries.map_comp, intCast_comp, ofPowerSeries_map_expandZ, ← hE, hG]
    exact ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne N E
  have h := IsModular.of_form_le (ι := ι) (Γgl_le_Gamma0 N M') G _ hq
  rwa [ofPowerSeries_map_expandZ] at h

theorem tateBase_a₁ : (tateBase L N).a₁ = 1 := by simp [tateBase, tateLaurent]
theorem tateBase_a₂ : (tateBase L N).a₂ = 0 := by simp [tateBase, tateLaurent]
theorem tateBase_a₃ : (tateBase L N).a₃ = 0 := by simp [tateBase, tateLaurent]
theorem tateBase_a₄ : (tateBase L N).a₄ = qExpand L N (laurentOfInt L tateA4) := by simp [tateBase]
theorem tateBase_a₆ : (tateBase L N).a₆ = qExpand L N (laurentOfInt L tateA6) := by simp [tateBase]

theorem isModular_c4 : IsModular ι N M' 4 (1 - 48 * (tateBase L N).a₄) := by
  have h := isModular_qExpand_of_levelOne ι N M' ModularForm.E₄ eisenstein4
    ModularCurve.qExpansion_E4_eq_map_eisenstein4
  rwa [eisenstein4_eq, map_sub, map_mul, map_one, map_sub, map_mul, map_one, map_ofNat, map_ofNat,
    ← tateBase_a₄] at h

theorem isModular_c6 : IsModular ι N M' 6 (1 - 72 * (tateBase L N).a₄ + 864 * (tateBase L N).a₆) := by
  have h := isModular_qExpand_of_levelOne ι N M' ModularForm.E₆ eisenstein6
    ModularCurve.qExpansion_E6_eq_map_mk
  rwa [eisenstein6_eq, map_add, map_sub, map_mul, map_mul, map_one, map_add, map_sub, map_mul, map_mul,
    map_one, map_ofNat, map_ofNat, map_ofNat, map_ofNat, ← tateBase_a₄, ← tateBase_a₆] at h

end Eisenstein

section Points

variable {L : Type} [Field L] [CharZero L] (ι : L →+* ℂ)
variable (N M' : ℕ) [NeZero N] [NeZero M'] [Fact (1 < N)] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)

open scoped Classical

abbrev w₀ : Fin 2 → ZMod N := ![1, 0]

theorem w₀_ne_zero : (w₀ N) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem w₀_zero_val : ((w₀ N) 0).val = 1 := by
  show (1 : ZMod N).val = 1
  exact ZMod.val_one N

theorem cuspPoint_toric (v : Fin 2 → ZMod N) (h1 : v 1 = 0) :
    cuspPoint L N ξ v = toricPoint L N ((ξ : L) ^ (v 0).val) := by
  rw [cuspPoint_of_eq_zero _ h1, tateToricPoint_eq_toricPoint, Units.val_pow_eq_pow_val]

theorem cuspPoint_w₀ : cuspPoint L N ξ (w₀ N) = toricPoint L N (ξ : L) := by
  rw [cuspPoint_toric N ξ _ (by rfl), w₀_zero_val, pow_one]

theorem cuspPoint_w₀' : cuspPoint L N ξ (w₀ N) = tateToricPoint L N ξ := by
  rw [cuspPoint_of_eq_zero _ (by rfl : (w₀ N) 1 = 0), w₀_zero_val, pow_one]

variable {N ξ}

include hξ in
theorem xi_ne_one : (ξ : L) ≠ 1 := hξ.ne_one Fact.out

include hξ in
theorem pow_mod_N (m : ℕ) : ξ ^ (m % N) = ξ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N, _root_.pow_add, _root_.pow_mul, units_pow_N hξ, one_pow, mul_one]

include hξ in
theorem pow_val_add_one (a : ZMod N) : ξ ^ (a + 1).val = ξ ^ a.val * ξ := by
  rw [ZMod.val_add, ZMod.val_one, pow_mod_N hξ, pow_succ]

include hξ in

theorem nonsingular_cusp (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (tateBase L N).toAffine.Nonsingular (cuspPoint L N ξ v).1 (cuspPoint L N ξ v).2 := by
  by_cases h1 : v 1 = 0
  · have ha : v 0 ≠ 0 := fst_ne_zero_of_snd_eq_zero hv h1
    have hc1 : ((ξ : L) ^ (v 0).val) ≠ 1 := by
      have := val_pow_ne_one hξ ha; rwa [Units.val_pow_eq_pow_val] at this
    have hc0 : ((ξ : L) ^ (v 0).val) ≠ 0 := pow_ne_zero _ ξ.ne_zero
    obtain ⟨hc, -, -⟩ :=
      ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero L N _ _ hc0 hc0 hc1 hc1
    rw [cuspPoint_toric N ξ v h1]
    exact hc
  · have hb0 : 0 < (v 1).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr h1)
    obtain ⟨-, hd, -, -⟩ := (ModularCurve.toricPoint_add_nonToricPoint_of_charZero L N).1 ξ
      (ξ ^ (v 0).val) (v 1).val (xi_ne_one hξ) hb0 (ZMod.val_lt _)
    rw [cuspPoint_of_ne_zero _ h1]
    exact hd

def Pt (v : Fin 2 → ZMod N) (hv : v ≠ 0) : (tateBase L N).toAffine.Point :=
  .some _ _ (nonsingular_cusp hξ v hv)

theorem point_some_congr {T : Type*} [CommRing T] {V : WeierstrassCurve T} {x x' y y' : T}
    (hx : x = x') (hy : y = y') (h : V.toAffine.Nonsingular x y) (h' : V.toAffine.Nonsingular x' y') :
    (Point.some x y h : V.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem Pt_eq_of_eq {v : Fin 2 → ZMod N} (hv : v ≠ 0) {P : LaurentSeries L × LaurentSeries L}
    (hP : cuspPoint L N ξ v = P) (h' : (tateBase L N).toAffine.Nonsingular P.1 P.2) :
    Pt hξ v hv = .some P.1 P.2 h' :=
  point_some_congr (by rw [hP]) (by rw [hP]) _ _

include hξ in

theorem exists_add_eq (v : Fin 2 → ZMod N) (hv : v ≠ 0)
    (hx : (cuspPoint L N ξ v).1 ≠ (cuspPoint L N ξ (w₀ N)).1) :
    ∃ (w : Fin 2 → ZMod N) (hw : w ≠ 0), Pt hξ v hv + Pt hξ (w₀ N) (w₀_ne_zero N) = Pt hξ w hw := by
  have hξ1 := xi_ne_one hξ
  have hξ0 : (ξ : L) ≠ 0 := ξ.ne_zero
  by_cases h1 : v 1 = 0
  ·
    have ha : v 0 ≠ 0 := fst_ne_zero_of_snd_eq_zero hv h1
    set c : L := (ξ : L) ^ (v 0).val with hc
    have hc1 : c ≠ 1 := by have := val_pow_ne_one hξ ha; rwa [Units.val_pow_eq_pow_val] at this
    have hc0 : c ≠ 0 := pow_ne_zero _ hξ0
    obtain ⟨hcns, hdns, hinv, hmul⟩ :=
      ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero L N c ξ hc0 hξ0 hc1 hξ1
    have hPv : Pt hξ v hv = .some _ _ hcns := Pt_eq_of_eq hξ hv (cuspPoint_toric N ξ v h1) hcns
    have hP0 : Pt hξ (w₀ N) (w₀_ne_zero N) = .some _ _ hdns := Pt_eq_of_eq hξ _ (cuspPoint_w₀ N ξ) hdns
    have hcd : c * ξ = (ξ : L) ^ (v 0 + 1).val := by
      rw [hc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_val_add_one hξ, Units.val_pow_eq_pow_val]
    by_cases hsum : v 0 + 1 = 0
    · exfalso
      have h1' : c * ξ = 1 := by rw [hcd, hsum, ZMod.val_zero, pow_zero]
      have h0 := hinv h1'
      rw [← hPv, ← hP0, add_eq_zero_iff_eq_neg, hP0, Point.neg_some] at h0
      simp only [Pt] at h0
      obtain ⟨hxx, -⟩ := Point.some.inj h0
      exact hx (hxx.trans (by rw [cuspPoint_w₀]))
    · have h1' : c * ξ ≠ 1 := by
        rw [hcd]
        intro h
        apply hsum
        have hdvd := (hξ.pow_eq_one_iff_dvd _).mp h
        rw [← ZMod.natCast_zmod_val (v 0 + 1), (ZMod.natCast_eq_zero_iff _ _).mpr hdvd]
      obtain ⟨hcdns, hsum'⟩ := hmul h1'
      refine ⟨![v 0 + 1, 0], ne_zero_of_apply_ne (i := 0) (by simpa using hsum), ?_⟩
      rw [hPv, hP0, hsum']
      symm
      refine Pt_eq_of_eq hξ _ ?_ hcdns
      rw [cuspPoint_toric N ξ _ (by rfl), hcd]
      rfl
  ·
    have hb0 : 0 < (v 1).val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr h1)
    obtain ⟨hcns, hdns, hcdns, hsum⟩ := (ModularCurve.toricPoint_add_nonToricPoint_of_charZero L N).1 ξ
      (ξ ^ (v 0).val) (v 1).val hξ1 hb0 (ZMod.val_lt _)
    have hPv : Pt hξ v hv = .some _ _ hdns := Pt_eq_of_eq hξ hv (cuspPoint_of_ne_zero _ h1) hdns
    have hP0 : Pt hξ (w₀ N) (w₀_ne_zero N) = .some _ _ hcns := Pt_eq_of_eq hξ _ (cuspPoint_w₀ N ξ) hcns
    refine ⟨![v 0 + 1, v 1], ne_zero_of_apply_ne (i := 1) (by simpa using h1), ?_⟩
    rw [hPv, hP0, add_comm, hsum]
    symm
    refine Pt_eq_of_eq hξ _ ?_ hcdns
    rw [cuspPoint_of_ne_zero _ (by simpa using h1)]
    show nonToricPoint L N (ξ ^ (v 0 + 1).val) (v 1).val = _
    rw [pow_val_add_one hξ, mul_comm]

include hξ in

theorem equation_cusp (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (cuspPoint L N ξ v).2 ^ 2 + (cuspPoint L N ξ v).1 * (cuspPoint L N ξ v).2 =
      (cuspPoint L N ξ v).1 ^ 3 + (tateBase L N).a₄ * (cuspPoint L N ξ v).1 + (tateBase L N).a₆ := by
  have h := (nonsingular_cusp hξ v hv).1
  rw [Affine.equation_iff, tateBase_a₁, tateBase_a₂, tateBase_a₃] at h
  linear_combination h

theorem C_inv_ofNat (n : ℕ) [n.AtLeastTwo] :
    HahnSeries.C ((OfNat.ofNat n : L)⁻¹) = (OfNat.ofNat n : LaurentSeries L)⁻¹ := by
  rw [map_inv₀, map_ofNat]

include hξ in

theorem Yf_sq (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    Yf N ξ v ^ 2 = 4 * Xf N ξ v ^ 3
      - HahnSeries.C ((12 : L)⁻¹) * (1 - 48 * (tateBase L N).a₄) * Xf N ξ v
      + HahnSeries.C ((216 : L)⁻¹) * (1 - 72 * (tateBase L N).a₄ + 864 * (tateBase L N).a₆) := by
  have h := equation_cusp hξ v hv
  rw [Yf_def, Xf_def, C_inv_ofNat, C_inv_ofNat]
  field_simp
  linear_combination (1492992 : LaurentSeries L) * h

include hξ in
theorem isModular_Yf_sq (v : Fin 2 → ZMod N) (hv : v ≠ 0) : IsModular ι N M' 6 (Yf N ξ v ^ 2) := by
  rw [Yf_sq hξ v hv]
  have hX := isModular_Xf ι M' hξ v hv
  refine ((((hX.pow 3).cast (by norm_num)).ofNat_mul 4).sub ?_).add ?_
  · rw [mul_assoc]
    exact (((isModular_c4 ι N M').mul hX).cast (by norm_num)).smul _
  · exact (isModular_c6 ι N M').smul _

theorem chord_identity {A : Type*} [Field A] {x₁ y₁ x₂ y₂ x₃ : A} (hx : x₁ ≠ x₂)
    (h₃ : x₃ = ((y₁ - y₂) / (x₁ - x₂)) ^ 2 + (y₁ - y₂) / (x₁ - x₂) - x₁ - x₂) :
    2 * ((2 * y₁ + x₁) * (2 * y₂ + x₂)) =
      (2 * y₁ + x₁) ^ 2 + (2 * y₂ + x₂) ^ 2 - (4 * (x₃ + x₁ + x₂) + 1) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have h3' : x₃ * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + (y₁ - y₂) * (x₁ - x₂) - (x₁ + x₂) * (x₁ - x₂) ^ 2 := by
    rw [h₃]; field_simp; ring
  linear_combination 4 * h3'

include hξ in

theorem isModular_Yf_mul (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    IsModular ι N M' 6 (Yf N ξ v * Yf N ξ (w₀ N)) := by
  have h0 := w₀_ne_zero N
  by_cases hx : (cuspPoint L N ξ v).1 = (cuspPoint L N ξ (w₀ N)).1
  ·
    have hX : Xf N ξ v = Xf N ξ (w₀ N) := by rw [Xf_def, Xf_def, hx]
    have hsq : Yf N ξ v ^ 2 = Yf N ξ (w₀ N) ^ 2 := by rw [Yf_sq hξ v hv, Yf_sq hξ _ h0, hX]
    have hY0 := isModular_Yf_sq ι M' hξ (w₀ N) h0
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
    · rw [h, ← pow_two]; exact hY0
    · rw [h, neg_mul, ← pow_two]; exact hY0.neg
  ·
    obtain ⟨w, hw, hsum⟩ := exists_add_eq hξ v hv hx
    rw [Pt, Pt, Pt, Point.add_of_X_ne hx] at hsum
    obtain ⟨hx3, -⟩ := Point.some.inj hsum
    rw [Affine.slope_of_X_ne hx] at hx3
    simp only [Affine.addX, tateBase_a₁, tateBase_a₂, one_mul, sub_zero] at hx3
    have hch := chord_identity hx hx3.symm

    have key : Yf N ξ v * Yf N ξ (w₀ N) = HahnSeries.C ((2 : L)⁻¹) *
        (Yf N ξ v ^ 2 + Yf N ξ (w₀ N) ^ 2
          - 4 * (Xf N ξ w + Xf N ξ v + Xf N ξ (w₀ N)) * (Xf N ξ v - Xf N ξ (w₀ N)) ^ 2) := by
      rw [Yf_def, Yf_def, Xf_def, Xf_def, Xf_def, C_inv_ofNat, C_inv_ofNat]
      field_simp
      linear_combination 1728 * hch
    rw [key]
    refine IsModular.smul _ ((((isModular_Yf_sq ι M' hξ v hv).add (isModular_Yf_sq ι M' hξ _ h0)).sub ?_))
    have hX := isModular_Xf ι M' hξ v hv
    have hX0 := isModular_Xf ι M' hξ _ h0
    have hXw := isModular_Xf ι M' hξ w hw
    rw [mul_assoc]
    exact ((((hXw.add hX).add hX0).mul ((hX.sub hX0).pow 2)).cast (by norm_num)).ofNat_mul 4

end Points

section Nonvanishing

variable {L : Type} [Field L] [CharZero L]
variable (N : ℕ) [NeZero N] [Fact (1 < N)] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)

theorem sum_divisors_ite_dvd_eq (f : ℕ → L) :
    (∑ d ∈ N.divisors, if N ∣ d then f d else 0) = f N := by
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [Finset.sum_eq_single_of_mem N (Nat.mem_divisors_self N hN0)]
  · rw [if_pos dvd_rfl]
  · intro d hd hdN
    rw [if_neg]
    exact fun hNd => hdN (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) hNd)

theorem coeff_toricX_self (c : Lˣ) :
    PowerSeries.coeff N (toricX L N c) = (c : L) + ((c⁻¹ : Lˣ) : L) - 2 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  simp only [toricX, PowerSeries.coeff_mk, hN0, ↓reduceIte, dvd_rfl, sum_divisors_ite_dvd_eq,
    Nat.div_self (Nat.pos_of_ne_zero hN0), Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, pow_one,
    one_mul, mul_one]

theorem coeff_toricY_self (c : Lˣ) :
    PowerSeries.coeff N (toricY L N c) = 1 - ((c⁻¹ : Lˣ) : L) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  simp only [toricY, PowerSeries.coeff_mk, hN0, ↓reduceIte, dvd_rfl, sum_divisors_ite_dvd_eq,
    Nat.div_self (Nat.pos_of_ne_zero hN0), Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, pow_one,
    Nat.choose_succ_self, Nat.choose_self, Nat.cast_zero, zero_mul, one_mul, zero_sub]
  ring

theorem coeff_C_natCast_of_ne_zero (a : L) : (HahnSeries.C a : LaurentSeries L).coeff (N : ℤ) = 0 := by
  rw [HahnSeries.C_apply, coeff_single_of_ne]
  exact_mod_cast NeZero.ne N

theorem coeff_ofNat_mul (n : ℕ) [n.AtLeastTwo] (z : LaurentSeries L) (m : ℤ) :
    ((OfNat.ofNat n : LaurentSeries L) * z).coeff m = (OfNat.ofNat n : L) * z.coeff m := by
  rw [ofNat_eq_C, C_mul_eq_smul, coeff_smul, smul_eq_mul]

include hξ in

theorem D₀_ne_zero : 2 * (cuspPoint L N ξ (w₀ N)).1 + HahnSeries.C ((6 : L)⁻¹) ≠ 0 := by
  intro h
  rw [cuspPoint_w₀', tateToricPoint_fst'] at h
  have hc := congrArg (fun z : LaurentSeries L => z.coeff (N : ℤ)) h
  beta_reduce at hc
  rw [coeff_add, coeff_ofNat_mul, ofPowerSeries_coeff_natCast, coeff_toricX_self, coeff_C_natCast_of_ne_zero,
    coeff_zero, add_zero, Units.val_inv_eq_inv_val] at hc
  have hξ0 : (ξ : L) ≠ 0 := ξ.ne_zero
  have h2 : ((ξ : L) - 1) ^ 2 = 0 := by
    field_simp at hc
    linear_combination (1 / 2 : L) * hc
  exact xi_ne_one hξ (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2))

include hξ in

theorem Y₀_ne_zero (hN2 : 2 < N) : Yf N ξ (w₀ N) ≠ 0 := by
  intro h
  rw [Yf_def, cuspPoint_w₀', tateToricPoint_fst', tateToricPoint_snd'] at h
  have hc := congrArg (fun z : LaurentSeries L => z.coeff (N : ℤ)) h
  beta_reduce at hc
  rw [coeff_add, coeff_ofNat_mul, ofPowerSeries_coeff_natCast, ofPowerSeries_coeff_natCast, coeff_toricX_self,
    coeff_toricY_self, coeff_zero, Units.val_inv_eq_inv_val] at hc
  have hξ0 : (ξ : L) ≠ 0 := ξ.ne_zero
  have h2 : (ξ : L) ^ 2 = 1 := by
    field_simp at hc
    linear_combination hc
  exact hξ.pow_ne_one_of_pos_of_lt two_ne_zero hN2 h2

end Nonvanishing

section Main

open scoped Classical

theorem mem_range_of_mem {L : Type} [Field L] {F : IntermediateField L (LaurentSeries L)}
    {z : LaurentSeries L} (h : z ∈ F) : z ∈ Set.range ((↑) : ↥F → LaurentSeries L) :=
  ⟨⟨z, h⟩, rfl⟩

theorem main
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),
      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 +
            HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 +
          (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod (q * ℓ), v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) := by
  haveI hN0 : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hN2 : 2 < q * ℓ := by nlinarith
  haveI : Fact (1 < q * ℓ) := ⟨by omega⟩

  set ξu : Lˣ := (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit
    with hξu_def
  have hξu : IsPrimitiveRoot ((ξu : Lˣ) : L) (q * ℓ) := by rwa [hξu_def, IsUnit.unit_spec]
  obtain ⟨ι, -⟩ := hιξ
  subst hK

  set A₀ := ModularCurve.tateBase L (q * ℓ) with hA₀
  set x₀ : LaurentSeries L := (cuspPoint L (q * ℓ) ξu ![1, 0]).1 with hx₀
  set y₀ : LaurentSeries L := (cuspPoint L (q * ℓ) ξu ![1, 0]).2 with hy₀
  set D₀ : LaurentSeries L := 2 * x₀ + HahnSeries.C ((6 : L)⁻¹) with hD₀
  set Y₀ : LaurentSeries L := 2 * y₀ + x₀ with hY₀
  have hY₀' : Y₀ = Yf (q * ℓ) ξu (w₀ (q * ℓ)) := rfl
  have hD : D₀ ≠ 0 := D₀_ne_zero (q * ℓ) ξu hξu
  have hY : Y₀ ≠ 0 := by rw [hY₀']; exact Y₀_ne_zero (q * ℓ) ξu hξu hN2
  set u : LaurentSeries L := Y₀ / D₀ with hu_def
  have hu : u ≠ 0 := div_ne_zero hY hD
  have hui : (((Units.mk0 u hu)⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) = D₀ / Y₀ := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, hu_def, inv_div]
  have hD0X : D₀ = 2 * Xf (q * ℓ) ξu (w₀ (q * ℓ)) := by
    rw [Xf_def, hD₀, hx₀, mul_add, C_inv_ofNat, C_inv_ofNat]
    norm_num

  have h0 := w₀_ne_zero (q * ℓ)
  have hX0 : IsModular ι (q * ℓ) M' 2 (Xf (q * ℓ) ξu (w₀ (q * ℓ))) := isModular_Xf ι M' hξu _ h0
  have hDm : IsModular ι (q * ℓ) M' 2 D₀ := by rw [hD0X]; exact hX0.ofNat_mul 2
  have hYsq : IsModular ι (q * ℓ) M' 6 (Y₀ ^ 2) := by rw [hY₀']; exact isModular_Yf_sq ι M' hξu _ h0
  have hc4 := isModular_c4 ι (q * ℓ) M' (L := L)
  have hc6 := isModular_c6 ι (q * ℓ) M' (L := L)
  have hY2 : Y₀ ^ 2 ≠ 0 := pow_ne_zero _ hY
  refine ⟨⟨Units.mk0 u hu, HahnSeries.C (-(12 : L)⁻¹), HahnSeries.C (-(2 : L)⁻¹), HahnSeries.C ((24 : L)⁻¹)⟩,
    ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show u * D₀ = Y₀
    rw [hu_def, div_mul_cancel₀ _ hD]
  ·
    refine mem_range_of_mem ?_
    rw [variableChange_a₁, tateBase_a₁]
    have e : (1 : LaurentSeries L) + 2 * HahnSeries.C (-(2 : L)⁻¹) = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [variableChange_a₂, tateBase_a₁, tateBase_a₂]
    have e : (0 : LaurentSeries L) - HahnSeries.C (-(2 : L)⁻¹) * 1 + 3 * HahnSeries.C (-(12 : L)⁻¹)
        - HahnSeries.C (-(2 : L)⁻¹) ^ 2 = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [variableChange_a₃, tateBase_a₁, tateBase_a₃]
    have e : (0 : LaurentSeries L) + HahnSeries.C (-(12 : L)⁻¹) * 1 + 2 * HahnSeries.C ((24 : L)⁻¹) = 0 := by
      simp only [map_neg, map_inv₀, map_ofNat]; norm_num
    rw [e, mul_zero]
    exact zero_mem _
  ·
    refine mem_range_of_mem ?_
    rw [variableChange_a₄, tateBase_a₁, tateBase_a₂, tateBase_a₃, hui]
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
    rw [variableChange_a₆, tateBase_a₁, tateBase_a₂, tateBase_a₃, hui]
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
    intro v w hv hw
    have hXv : IsModular ι (q * ℓ) M' 2 (Xf (q * ℓ) ξu v) := isModular_Xf ι M' hξu v hv
    have hYv : IsModular ι (q * ℓ) M' 6 (Yf (q * ℓ) ξu v * Y₀) := by
      rw [hY₀']; exact isModular_Yf_mul ι M' hξu v hv
    simp only [LevelPData.variableChange_xP, LevelPData.variableChange_yP, cuspData_xP, cuspData_yP, hui]
    refine ⟨mem_range_of_mem ?_, mem_range_of_mem ?_⟩
    · rw [map_neg, sub_neg_eq_add, ← Xf_def, div_pow, div_mul_eq_mul_div]
      exact IsModular.div_mem (k := 6) (((hDm.pow 2).mul hXv).cast (by norm_num)) hYsq hY2
    · have e : (cuspPoint L (q * ℓ) ξu v).2
          - HahnSeries.C (-(2 : L)⁻¹) * ((cuspPoint L (q * ℓ) ξu v).1 - HahnSeries.C (-(12 : L)⁻¹))
          - HahnSeries.C ((24 : L)⁻¹) = HahnSeries.C ((2 : L)⁻¹) * Yf (q * ℓ) ξu v := by
        rw [Yf_def]
        simp only [map_neg, map_inv₀, map_ofNat]
        field_simp; ring
      have e' : (D₀ / Y₀) ^ 3 * (HahnSeries.C ((2 : L)⁻¹) * Yf (q * ℓ) ξu v) =
          D₀ ^ 3 * (HahnSeries.C ((2 : L)⁻¹) * (Yf (q * ℓ) ξu v * Y₀)) / (Y₀ ^ 2) ^ 2 := by
        rw [div_pow]; field_simp
      rw [e, e']
      exact IsModular.div_mem (k := 12) (((hDm.pow 3).mul (hYv.smul _)).cast (by norm_num))
        ((hYsq.pow 2).cast (by norm_num)) (pow_ne_zero _ hY2)

end Main

end R4TateModelK
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom.R4TateModelK"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom.R4TateModelK"

open ModularCurve in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),

      ((C.u : (LaurentSeries L)ˣ) : LaurentSeries L) *
          (2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 +
            HahnSeries.C ((6 : L)⁻¹)) =
        2 * (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 +
          (ModularCurve.cuspPoint L (q * ℓ)
            (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
      C.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C.t = HahnSeries.C ((24 : L)⁻¹) ∧

      (C • ModularCurve.tateBase L (q * ℓ)).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod (q * ℓ), v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) :=
  R4TateModelK.main q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hιξ K hK

end S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem_of_exists_ringHom (solution)
