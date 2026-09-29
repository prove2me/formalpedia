-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2649fdaa-71c0-5c39-9262-3c7b7cc86c0b

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_XHDRLevel_algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

noncomputable section

namespace PoleUnitA

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_neg_of_ord_sub_neg (v : Place K F) {f g : F} (hg : g ∈ v.toValuationSubring)
    (h : v.ord (f - g) < 0) : v.ord f < 0 := by
  rw [← Place.not_adicValuation_le_one_iff] at h ⊢
  intro hf
  apply h
  calc v.adicValuation (f - g) ≤ max (v.adicValuation f) (v.adicValuation g) := Valuation.map_sub _ _ _
    _ ≤ 1 := max_le hf (v.adicValuation_le_one_of_mem hg)

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (Place.hasValue_algebraMap v c).ord_eq_zero hc

theorem ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have h := v.ord_zpow f n
  rwa [zpow_natCast] at h

theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · simpa using Place.hasValue_algebraMap v (0 : K)
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

theorem hvAdd {v : Place K F} {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have e : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [e, map_add, hfr, hgr, map_add]

theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {c : K} (h : v.HasValue g c)
    (hne : g ≠ algebraMap K F c) : 0 < v.ord (g - algebraMap K F c) := by
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem h.mem (v.algebraMap_mem' c)
  have hne0 : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hne
  have h0 : 0 ≤ v.ord (g - algebraMap K F c) := ord_nonneg_of_mem v hne0 hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne0 heq.symm
    have e : (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring c := Subtype.ext rfl
    have hres : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hm⟩ = 0 := by
      rw [e, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

theorem exists_hasValue_of_deg_eq_one (v : Place K F) (hdeg : v.deg = 1) {g : F}
    (hg : g ∈ v.toValuationSubring) : ∃ a : K, v.HasValue g a := by
  have h1 : (1 : v.ResidueField) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective (algebraMap K v.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) h1).mp hdeg x
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hsurj hg
  exact ⟨a, ha⟩

theorem inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S)
    (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have hinv : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  exact hinv ▸ SetLike.coe_mem _

theorem eq_of_ord_sub_one_pos (W : Place K F) (g : F) {c c' : K}
    (hc : 0 < W.ord (algebraMap K F c * g - 1)) (hc' : 0 < W.ord (algebraMap K F c' * g - 1)) : c = c' := by
  have hval : ∀ a : K, 0 < W.ord (algebraMap K F a * g - 1) → W.HasValue g a⁻¹ := by
    intro a ha
    have h0 : W.HasValue (algebraMap K F a * g - 1) 0 := hasValue_zero_of_ord_pos W (Or.inr ha)
    have h1 : W.HasValue (algebraMap K F a * g - 1 + 1) (0 + 1) := hvAdd h0 (Place.hasValue_one W)
    rw [sub_add_cancel, zero_add] at h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at h1
      exact zero_ne_one ((hasValue_zero_of_ord_pos W (Or.inl rfl)).unique h1)
    have h2 : W.HasValue (algebraMap K F a⁻¹ * (algebraMap K F a * g)) (a⁻¹ * 1) :=
      (Place.hasValue_algebraMap W a⁻¹).mul h1
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_mul, mul_one] at h2
  exact inv_injective ((hval c hc).unique (hval c' hc'))

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

end Generic

section Level

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem coe_algebraMap (c : (AlgebraicClosure ℚ)) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.single 0 c := by
  rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c from rfl,
    algebraMap_laurentSeries_eq_single]

theorem galois_smul_algebraMap (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (c : (AlgebraicClosure ℚ)) :
    arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (σ c) :=
  (SemilinearAut.smul_algebraMap _ c).trans rfl

theorem galois_smul_eq_of_coe (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (g : ↥(xHFunctionFieldBar M H))
    (h : coeffMap (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) (g : LaurentSeries (AlgebraicClosure ℚ)) = (g : LaurentSeries (AlgebraicClosure ℚ))) :
    arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • g = g := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul]
  exact h

theorem degOne (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : w.deg = 1 := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  exact IsCurveOver.deg_eq_one_of_isAlgClosed w

theorem jqModC_mem_xHFunctionField (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) : jqModC ℚ ∈ xHFunctionField N H' :=
  ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)

theorem coeffEmb_jqModC : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  exact coeffMap_jqModC _

end Level

section Carriers

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    {α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    {pb : (ZMod (M / p))ˣ} (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    {x : ↥(xHFunctionFieldBar M H)} (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

variable (p M H hpM) in

def xlow : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqModC_mem_xHFunctionField (M / p) (infSubgroup p M H hpM))⟩

variable (p M H hpM) in
omit [Fact p.Prime] [NeZero M] in
theorem coe_xlow : ((xlow p M H hpM : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := coeffEmb_jqModC

include hα_coe hx in
omit [Fact p.Prime] in
theorem alpha_xlow : α (xlow p M H hpM) = x :=
  Subtype.ext (by rw [hα_coe, coe_xlow, hx])

include hα_coe hβ_coe hx in

theorem coe_theta_x : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((θ x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
  rw [← alpha_xlow hα_coe hx]
  exact (hβ_coe (xlow p M H hpM)).trans (by rw [coe_xlow])

include hα_coe hβ_coe in

theorem theta_law : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
  intro f u h
  have : f = α u := Subtype.ext (h.trans (hα_coe u).symm)
  rw [this]
  exact hβ_coe u

include hpM2 hHp hα_coe hβ_coe hpb hx in

theorem theta_theta_x : θ (θ x) = x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨σ, hσ1, hσ2⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  have h10 := ModularCurve.XHDRLevel.algEquiv_coeffEmb_eq_coeffEmb_ratAlgEquiv_of_atkinLehner_generic p M H hpM hpM2 hHp θ
    (theta_law hα_coe hβ_coe) σ hσ1

  let j₁ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := ⟨jqModC ℚ, jqModC_mem_xHFunctionField M H⟩
  let jlow : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))) :=
    ⟨jqModC ℚ, jqModC_mem_xHFunctionField (M / p) (infSubgroup p M H hpM)⟩
  have hσj : ((σ j₁ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) :=
    hσ1 j₁ jlow rfl

  have hx₁ : x = ⟨coeffEmb (AlgebraicClosure ℚ) (j₁ : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j₁.2⟩ :=
    Subtype.ext (by rw [hx]; exact coeffEmb_jqModC.symm)
  have hθx : θ x = ⟨coeffEmb (AlgebraicClosure ℚ) ((σ j₁ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (σ j₁).2⟩ :=
    Subtype.ext (by rw [hx₁]; exact h10 j₁)
  apply Subtype.ext
  rw [hθx, h10 (σ j₁), hσ2 pb hpb (σ j₁) jlow hσj,
    ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) pb _ (jqModC ℚ)
      (ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)) rfl,
    hx]
  exact coeffEmb_jqModC

include hpM2 hHp hα_coe hβ_coe hpb hx in
theorem theta_symm_x : θ.symm x = θ x :=
  θ.injective (by rw [AlgEquiv.apply_symm_apply, theta_theta_x hpM2 hHp hα_coe hβ_coe hpb hx])

end Carriers

section Units

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    {α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    {pb : (ZMod (M / p))ˣ} (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    {Psp : JHPlaceSpecialization p M H hpM A} (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    {x : ↥(xHFunctionFieldBar M H)} (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

section Carrier
include hx
omit [Fact p.Prime]

theorem x_ne_algebraMap (c : (AlgebraicClosure ℚ)) : x ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c := by
  intro h
  have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
  simp only [hx, coe_algebraMap] at h1
  rw [HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide), coeff_jqModC_neg_one] at h1
  exact one_ne_zero h1

theorem x_ne_zero : x ≠ 0 := by simpa using x_ne_algebraMap hx 0

theorem galois_smul_x (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • x = x :=
  galois_smul_eq_of_coe σ x (by rw [hx, coeffMap_jqModC])

theorem coe_uJ (b : ↥A) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * x - 1 : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (HahnSeries.C b * jqModC ↥A - 1) := by
  rw [map_sub, map_mul, map_one, coeffMap_C, coeffMap_jqModC]
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, hx, coe_algebraMap, HahnSeries.C_apply]
  rfl

end Carrier

include hα_coe hβ_coe hx in
theorem thetax_ne_algebraMap (c : (AlgebraicClosure ℚ)) : θ x ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro h
  have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff ((p : ℤ) * (-1))) h
  simp only [coe_theta_x hα_coe hβ_coe hx, coe_algebraMap] at h1
  rw [qExpand_coeff_mul, HahnSeries.coeff_single_of_ne, coeff_jqModC_neg_one] at h1
  · exact one_ne_zero h1
  · have : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    omega

include hα_coe hβ_coe hx in
theorem thetax_ne_zero : θ x ≠ 0 := by
  simpa using thetax_ne_algebraMap hα_coe hβ_coe hx 0

include hα_coe hβ_coe hx in
theorem galois_smul_thetax (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • θ x = θ x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact galois_smul_eq_of_coe σ _ (by rw [coe_theta_x hα_coe hβ_coe hx, coeffMap_qExpand, coeffMap_jqModC])

include hα_coe hβ_coe hx in

theorem coe_uJq (b : ↥A) : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * θ x - 1 : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype (HahnSeries.C b * qExpand ↥A p (jqModC ↥A) - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [map_sub, map_mul, map_one, coeffMap_C, coeffMap_qExpand, coeffMap_jqModC]
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, coe_theta_x hα_coe hβ_coe hx, coe_algebraMap,
    HahnSeries.C_apply]
  rfl

omit [Fact p.Prime] [NeZero M] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem coeffMap_residue_yJ (b : ↥A) (hb : b ∈ maximalIdeal ↥A) :
    coeffMap (IsLocalRing.residue ↥A) (HahnSeries.C b * jqModC ↥A - 1) = -1 := by
  rw [map_sub, map_mul, map_one, coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb, map_zero, zero_mul, zero_sub]

omit [NeZero M] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem coeffMap_residue_yJq (b : ↥A) (hb : b ∈ maximalIdeal ↥A) : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    coeffMap (IsLocalRing.residue ↥A) (HahnSeries.C b * qExpand ↥A p (jqModC ↥A) - 1) = -1 := by
  rw [map_sub, map_mul, map_one, coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb, map_zero, zero_mul, zero_sub]

theorem mem₁_of_coe_eq (g : ↥(xHFunctionFieldBar M H)) (y : LaurentSeries ↥A) (hy : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y)
    (hres : coeffMap (IsLocalRing.residue ↥A) y = -1) :
    ∃ h : g ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g, h⟩ = -1 := by
  have hy' : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by rw [← hy]; exact g.2
  obtain ⟨h, hr⟩ := Rpd.residue₁_coeffMap y hy'
  have e : (⟨coeffMap A.subtype y, hy'⟩ : ↥(xHFunctionFieldBar M H)) = g := Subtype.ext hy.symm
  have h' : g ∈ Rpd.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨g, h'⟩ : ↥Rpd.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hr, hres, NegMemClass.coe_neg, OneMemClass.coe_one]

include hx in
theorem uJ_mem₁ (b : ↥A) (hb : b ∈ maximalIdeal ↥A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * x - 1 ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨_, h⟩ = -1 :=
  mem₁_of_coe_eq Rpd _ _ (coe_uJ hx b) (coeffMap_residue_yJ b hb)

include hα_coe hβ_coe hx in
theorem uJq_mem₁ (b : ↥A) (hb : b ∈ maximalIdeal ↥A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * θ x - 1 ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨_, h⟩ = -1 :=
  mem₁_of_coe_eq Rpd _ _ (coe_uJq hα_coe hβ_coe hx b) (coeffMap_residue_yJq b hb)

omit [NeZero (M / p)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem theta_uJ (b : ↥A) : θ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * x - 1) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * θ x - 1 := by
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes]

include hpM2 hHp hα_coe hβ_coe hpb hx in
theorem theta_uJq (b : ↥A) : θ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * θ x - 1) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * x - 1 := by
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, theta_theta_x hpM2 hHp hα_coe hβ_coe hpb hx]

theorem mem₂_of_theta (g g' : ↥(xHFunctionFieldBar M H)) (hθg : θ g = g') (h1 : ∃ h : g' ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨g', h⟩ = -1) :
    ∃ h : g ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨g, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := h1
  have h1' : θ g ∈ Rpd.R₁.integers := by rw [hθg]; exact h1
  have h2 : g ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [Rpd.residue₂_eq]
  have e : (⟨θ g, (Rpd.mem_integers₂_iff _).mp h2⟩ : ↥Rpd.R₁.integers) = ⟨g', h1⟩ := Subtype.ext hθg
  rw [e, hres]

include hα_coe hβ_coe hx in
theorem uJ_mem₂ (b : ↥A) (hb : b ∈ maximalIdeal ↥A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * x - 1 ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h⟩ = -1 :=
  mem₂_of_theta Rpd _ _ (theta_uJ b) (uJq_mem₁ hα_coe hβ_coe Rpd hx b hb)

include hpM2 hHp hα_coe hβ_coe hpb hx in
theorem uJq_mem₂ (b : ↥A) (hb : b ∈ maximalIdeal ↥A) :
    ∃ h : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : (AlgebraicClosure ℚ)) * θ x - 1 ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h⟩ = -1 :=
  mem₂_of_theta Rpd _ _ (theta_uJq hpM2 hHp hα_coe hβ_coe hpb hx b) (uJ_mem₁ Rpd hx b hb)

omit [Fact p.Prime] [NeZero M] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem isUnit_jqModC : IsUnit (jqModC ↥A) := by
  unfold jqModC
  refine IsUnit.mul ?_ ?_
  · refine IsUnit.of_mul_eq_one (HahnSeries.single (1 : ℤ) (1 : ↥A)) ?_
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one]
    rfl
  · exact (PowerSeries.isUnit_iff_constantCoeff.mpr (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_jNum, map_one]
      exact isUnit_one)).map _

omit [Fact p.Prime] [NeZero M] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem jqModC_residueField_ne_zero : jqModC (ResidueField ↥A) ≠ 0 := fun h => by
  have h1 := coeff_jqModC_neg_one (ResidueField ↥A)
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem isUnit₁_of_coe_eq (g : ↥(xHFunctionFieldBar M H)) (y : LaurentSeries ↥A) (hy : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y)
    (hres : coeffMap (IsLocalRing.residue ↥A) y ≠ 0) :
    ∃ h : g ∈ Rpd.R₁.integers, IsUnit (⟨g, h⟩ : ↥Rpd.R₁.integers) := by
  have hy' : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := by rw [← hy]; exact g.2
  obtain ⟨h, hr⟩ := Rpd.residue₁_coeffMap y hy'
  have e : (⟨coeffMap A.subtype y, hy'⟩ : ↥(xHFunctionFieldBar M H)) = g := Subtype.ext hy.symm
  have h' : g ∈ Rpd.R₁.integers := by rw [← e]; exact h
  refine ⟨h', Rpd.R₁.isUnit_of_residue_ne_zero ?_⟩
  have e2 : (⟨g, h'⟩ : ↥Rpd.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  intro h0
  apply hres
  rw [← hr, h0]
  rfl

theorem isUnit₂_of_theta (g : ↥(xHFunctionFieldBar M H)) (h1 : ∃ h : θ g ∈ Rpd.R₁.integers, IsUnit (⟨θ g, h⟩ : ↥Rpd.R₁.integers)) :
    ∃ h : g ∈ Rpd.R₂.integers, IsUnit (⟨g, h⟩ : ↥Rpd.R₂.integers) := by
  obtain ⟨h1, hu⟩ := h1
  have h2 : g ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr h1
  refine ⟨h2, Rpd.R₂.isUnit_of_residue_ne_zero ?_⟩
  rw [Rpd.residue₂_eq]
  exact Rpd.R₁.residue_ne_zero_of_isUnit hu

include hx in
omit [Fact p.Prime] in
theorem coe_xinv : ((x⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (↑((isUnit_jqModC (A := A)).unit⁻¹) : LaurentSeries ↥A) := by
  rw [map_units_inv, IsUnit.unit_spec, coeffMap_jqModC, IntermediateField.coe_inv, hx]

omit [Fact p.Prime] [NeZero M] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem coeffMap_residue_xinv :
    coeffMap (IsLocalRing.residue ↥A) (↑((isUnit_jqModC (A := A)).unit⁻¹) : LaurentSeries ↥A) = (jqModC (ResidueField ↥A))⁻¹ := by
  rw [map_units_inv, IsUnit.unit_spec, coeffMap_jqModC]

include hx in
theorem xinv_mem₁ : ∃ h : x⁻¹ ∈ Rpd.R₁.integers, IsUnit (⟨x⁻¹, h⟩ : ↥Rpd.R₁.integers) :=
  isUnit₁_of_coe_eq Rpd _ _ (coe_xinv hx)
    (by rw [coeffMap_residue_xinv]; exact inv_ne_zero jqModC_residueField_ne_zero)

include hα_coe hβ_coe hx in
theorem coe_theta_xinv : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((θ x⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand ↥A p (↑((isUnit_jqModC (A := A)).unit⁻¹) : LaurentSeries ↥A)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [coeffMap_qExpand, map_units_inv, IsUnit.unit_spec, coeffMap_jqModC, map_inv₀, map_inv₀, IntermediateField.coe_inv,
    coe_theta_x hα_coe hβ_coe hx]

include hα_coe hβ_coe hx in
theorem xinv_mem₂ : ∃ h : x⁻¹ ∈ Rpd.R₂.integers, IsUnit (⟨x⁻¹, h⟩ : ↥Rpd.R₂.integers) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine isUnit₂_of_theta Rpd _ (isUnit₁_of_coe_eq Rpd _ _ (coe_theta_xinv hα_coe hβ_coe hx) ?_)
  rw [coeffMap_qExpand, coeffMap_residue_xinv]
  exact (map_ne_zero_iff _ (qExpand_injective p)).mpr (inv_ne_zero jqModC_residueField_ne_zero)

include hx in
omit [Fact p.Prime] in
theorem galois_smul_xinv (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • x⁻¹ = x⁻¹ := by
  rw [SemilinearAut.smul_def, map_inv₀, ← SemilinearAut.smul_def, galois_smul_x hx σ]

end Units

section ModEq

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def eval22 {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (r₁ r₂ : R) : R :=
  (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) r₁)).eval r₂

theorem eval22_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (Φ : Polynomial (Polynomial ℤ)) (r₁ r₂ : R) :
    φ (eval22 Φ r₁ r₂) = eval22 Φ (φ r₁) (φ r₂) := by
  unfold eval22
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext (fun a => by simp) ?_
  simp

theorem mem_of_eval22 {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (W : Place K F) {x y : F}
    (hx : x ∈ W.toValuationSubring) (hxy : eval22 Φ x y = 0) : y ∈ W.toValuationSubring := by
  set P : Polynomial W.toValuationSubring :=
    Φ.map (Polynomial.eval₂RingHom (Int.castRingHom W.toValuationSubring) ⟨x, hx⟩) with hP
  have hmonic : P.Monic := hΦ.map _
  have hmap : P.map (algebraMap W.toValuationSubring F) = Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) x) := by
    rw [hP, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hint : IsIntegral W.toValuationSubring y := by
    refine ⟨P, hmonic, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hmap]
    exact hxy
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hz ▸ z.2

theorem exists_int_value {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (A : ValuationSubring K) (W : Place K F) (hdeg : W.deg = 1)
    {u v : F} (huv : eval22 Φ u v = 0) (hv_ne : ∀ c : K, v ≠ algebraMap K F c)
    (a : ↥A) (ha : W.HasValue u (a : K)) : ∃ a' : ↥A, 0 < W.ord (v - algebraMap K F (a' : K)) := by
  have hum : u ∈ W.toValuationSubring := ha.mem
  have hvm : v ∈ W.toValuationSubring := mem_of_eval22 hΦ W hum huv
  obtain ⟨c, hc⟩ := exists_hasValue_of_deg_eq_one W hdeg hvm

  have h1 : eval22 Φ (⟨u, hum⟩ : W.toValuationSubring) ⟨v, hvm⟩ = 0 := by
    apply Subtype.val_injective
    rw [show ((eval22 Φ (⟨u, hum⟩ : W.toValuationSubring) ⟨v, hvm⟩ : W.toValuationSubring) : F) =
        W.toValuationSubring.subtype (eval22 Φ (⟨u, hum⟩ : W.toValuationSubring) ⟨v, hvm⟩) from rfl, eval22_map]
    exact huv
  have h2 := congrArg (IsLocalRing.residue W.toValuationSubring) h1
  rw [eval22_map, map_zero, ha.residue_eq, hc.residue_eq, ← eval22_map, map_eq_zero] at h2

  have hint : IsIntegral ↥A c := by
    refine ⟨Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥A) a), hΦ.map _, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_map]
    have : (algebraMap ↥A K).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥A) a) = Polynomial.eval₂RingHom (Int.castRingHom K) (a : K) := by
      refine Polynomial.ringHom_ext (fun n => by simp) ?_
      simp
    rw [this]
    exact h2
  obtain ⟨a', ha'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a', ord_sub_pos_of_hasValue W ?_ (hv_ne _)⟩
  rw [show ((a' : ↥A) : K) = algebraMap ↥A K a' from rfl, ha']
  exact hc

theorem hasValue_of_ord_sub_pos (W : Place K F) {u : F} {a : K} (h : 0 < W.ord (u - algebraMap K F a)) : W.HasValue u a := by
  have h0 := hasValue_zero_of_ord_pos W (Or.inr h)
  have h1 := hvAdd h0 (Place.hasValue_algebraMap W a)
  rwa [sub_add_cancel, zero_add] at h1

theorem ord_neg_of_ord_cmul_sub_one_neg (W : Place K F) {g : F} (hg : g ≠ 0) (b : K)
    (h : W.ord (algebraMap K F b * g - 1) < 0) : W.ord g < 0 := by
  have h1 : W.ord (algebraMap K F b * g) < 0 := ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : b ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) hg, ord_algebraMap, zero_add] at h1
  exact h1

theorem cmul_sub_one_ne_zero {g : F} (hg : ∀ c : K, g ≠ algebraMap K F c) (b : K) : algebraMap K F b * g - 1 ≠ 0 := by
  intro h
  have h' : algebraMap K F b * g = 1 := sub_eq_zero.mp h
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · apply hg b⁻¹
    rw [← mul_right_inj' ((map_ne_zero (algebraMap K F)).mpr hb), h', ← map_mul, mul_inv_cancel₀ hb, map_one]

theorem exists_tate (A : ValuationSubring K) (W : Place K F) (hdeg : W.deg = 1) {g : F} (hg : ∀ c : K, g ≠ algebraMap K F c)
    (hW : ¬ W.ord g < 0) (hcusp : ∀ a : ↥A, W.ord (g - algebraMap K F (a : K)) ≤ 0) :
    ∃ b : ↥A, b ∈ maximalIdeal ↥A ∧ 0 < W.ord (algebraMap K F (b : K) * g - 1) := by
  have hg0 : g ≠ 0 := by simpa using hg 0
  have hj0 : 0 ≤ W.ord g := not_lt.mp hW
  have hmem : g ∈ W.toValuationSubring := mem_of_ord_nonneg W hg0 hj0
  obtain ⟨c, hc⟩ := exists_hasValue_of_deg_eq_one W hdeg hmem
  have hpos : 0 < W.ord (g - algebraMap _ _ c) := ord_sub_pos_of_hasValue W hc (hg c)
  have hcA : c ∉ A := fun hcA => absurd (hcusp ⟨c, hcA⟩) (not_le.mpr hpos)
  have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
  have hbA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  refine ⟨⟨c⁻¹, hbA⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hcA
    have h2 := inv_mem_of_isUnit hbA hu
    rwa [inv_inv] at h2
  · have e : algebraMap K F ((⟨c⁻¹, hbA⟩ : ↥A) : K) * g - 1 = algebraMap _ _ (c⁻¹ : K) * (g - algebraMap _ _ c) := by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [e, W.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hc0)) (sub_ne_zero.mpr (hg c)), ord_algebraMap, zero_add]
    exact hpos

end ModEq

section ModEqLevel

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    {α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)}
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    {pb : (ZMod (M / p))ˣ} (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    {x : ↥(xHFunctionFieldBar M H)} (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

include hα_coe hβ_coe hx in
theorem eval22_x_thetax (data : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularPolynomialData p) :
    eval22 data.Φ x (θ x) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  apply Subtype.val_injective
  have key := eval_int_eq_zero_geom (AlgebraicClosure ℚ) data
  rw [show ((eval22 data.Φ x (θ x) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (xHFunctionFieldBar M H).toSubalgebra.val.toRingHom (eval22 data.Φ x (θ x)) from rfl,
    eval22_map, ZeroMemClass.coe_zero]
  unfold eval22
  rw [Polynomial.eval_map]
  convert key using 2 <;> try rfl
  · refine Polynomial.ringHom_ext (fun a => by simp [evalAtJGeom]) ?_
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJGeom_X]
    exact hx
  · exact coe_theta_x hα_coe hβ_coe hx

include hpM2 hHp hα_coe hβ_coe hpb hx in
theorem eval22_thetax_x (data : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ModularPolynomialData p) :
    eval22 data.Φ (θ x) x = 0 := by
  have h := congrArg θ (eval22_x_thetax hα_coe hβ_coe hx data)
  rw [map_zero, show (θ : ↥(xHFunctionFieldBar M H) → ↥(xHFunctionFieldBar M H)) = (θ : ↥(xHFunctionFieldBar M H) →+* ↥(xHFunctionFieldBar M H)) from rfl, eval22_map] at h
  simpa [theta_theta_x hpM2 hHp hα_coe hβ_coe hpb hx] using h

end ModEqLevel

end PoleUnitA

end

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace PoleUnitB

universe u v w

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

theorem ord_nonneg_of_mem (W : Place L F) {f : F} (hf : f ≠ 0) (h : f ∈ W.toValuationSubring) : 0 ≤ W.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := (⟨f, h⟩ : W.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf) hπ
  have hcoe : f = ((u : W.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h' := congrArg Subtype.val hu
    push_cast at h'
    rw [zpow_natCast]
    exact h'
  rw [hcoe, W.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (W : Place L F) {f : F} (hf : f ≠ 0) (h : 0 ≤ W.ord f) : f ∈ W.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  obtain ⟨u, hu⟩ := W.exists_unit_mul_zpow hf hπ
  rw [hu, show W.ord f = (((W.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : W.toValuationSubring).2 (pow_mem (π : W.toValuationSubring).2 _)

theorem ord_pow (W : Place L F) (f : F) (n : ℕ) : W.ord (f ^ n) = n * W.ord f := by
  rw [← zpow_natCast, W.ord_zpow]

theorem ord_prod {ι : Type*} (W : Place L F) (s : Finset ι) (g : ι → F) (hg0 : ∀ i ∈ s, g i ≠ 0) :
    W.ord (∏ i ∈ s, g i) = ∑ i ∈ s, W.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      W.ord_mul (hg0 a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr fun i hi => hg0 i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))]

theorem ord_le_ord_affine (W : Place L F) (b : L) (y : F) (hy : W.ord y < 0) (h0 : algebraMap L F b * y - 1 ≠ 0) :
    W.ord y ≤ W.ord (algebraMap L F b * y - 1) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp [Place.ord_zero] at hy
  have e : (algebraMap L F b * y - 1) * y⁻¹ = algebraMap L F b - y⁻¹ := by
    rw [sub_mul, mul_assoc, mul_inv_cancel₀ hy0, mul_one, one_mul]
  have hmem : (algebraMap L F b * y - 1) * y⁻¹ ∈ W.toValuationSubring := by
    rw [e]
    exact sub_mem (W.algebraMap_mem' _) (mem_of_ord_nonneg W (inv_ne_zero hy0) (by rw [W.ord_inv]; omega))
  have h := ord_nonneg_of_mem W (mul_ne_zero h0 (inv_ne_zero hy0)) hmem
  rw [W.ord_mul h0 (inv_ne_zero hy0), W.ord_inv] at h
  omega

theorem isUnit_product {Fb : Type w} [Field Fb] {A : ValuationSubring L} [Algebra (ResidueField A) Fb]
    (R : RegularProlongation A F Fb) {ι : Type*} (T : Finset ι) (n m : ℕ)
    (x0 x0' : F) (u1 u2 : ι → F)
    (hx0 : ∃ h : x0 ∈ R.integers, IsUnit (⟨x0, h⟩ : R.integers))
    (hx0' : ∃ h : x0' ∈ R.integers, IsUnit (⟨x0', h⟩ : R.integers))
    (h1 : ∀ i, ∃ h : u1 i ∈ R.integers, R.residue ⟨u1 i, h⟩ = -1)
    (h2 : ∀ i, ∃ h : u2 i ∈ R.integers, R.residue ⟨u2 i, h⟩ = -1) :
    ∃ h : (x0 ^ n * x0' ^ n) * ((∏ i ∈ T, u1 i ^ m) * ∏ i ∈ T, u2 i ^ m) ∈ R.integers,
      IsUnit (⟨(x0 ^ n * x0' ^ n) * ((∏ i ∈ T, u1 i ^ m) * ∏ i ∈ T, u2 i ^ m), h⟩ : R.integers) := by
  classical
  obtain ⟨hm0, hu0⟩ := hx0
  obtain ⟨hm0', hu0'⟩ := hx0'
  set y0 : R.integers := ⟨x0, hm0⟩ with hy0
  set y0' : R.integers := ⟨x0', hm0'⟩ with hy0'
  set y1 : ι → R.integers := fun i => ⟨u1 i, (h1 i).1⟩ with hy1
  set y2 : ι → R.integers := fun i => ⟨u2 i, (h2 i).1⟩ with hy2
  set y : R.integers := (y0 ^ n * y0' ^ n) * ((∏ i ∈ T, y1 i ^ m) * ∏ i ∈ T, y2 i ^ m) with hy
  have e1 : ((∏ i ∈ T, y1 i ^ m : R.integers) : F) = ∏ i ∈ T, ((y1 i ^ m : R.integers) : F) := SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ i ∈ T, y2 i ^ m : R.integers) : F) = ∏ i ∈ T, ((y2 i ^ m : R.integers) : F) := SubmonoidClass.coe_finsetProd _ _
  have hyU : (y : F) = (x0 ^ n * x0' ^ n) * ((∏ i ∈ T, u1 i ^ m) * ∏ i ∈ T, u2 i ^ m) := by
    rw [hy, MulMemClass.coe_mul, MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, e1, e2]
    simp only [SubmonoidClass.coe_pow, hy0, hy0', hy1, hy2]
  have hmem : (x0 ^ n * x0' ^ n) * ((∏ i ∈ T, u1 i ^ m) * ∏ i ∈ T, u2 i ^ m) ∈ R.integers := hyU ▸ y.2
  refine ⟨hmem, ?_⟩
  have : (⟨_, hmem⟩ : R.integers) = y := Subtype.ext hyU.symm
  rw [this, hy]
  refine ((hu0.pow n).mul (hu0'.pow n)).mul (IsUnit.mul ?_ ?_)
  · apply R.isUnit_of_residue_ne_zero
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow, (h1 i).2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · apply R.isUnit_of_residue_ne_zero
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [map_pow, (h2 i).2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

set_option maxHeartbeats 6400000 in

theorem exists_bigU {Fb₁ : Type w} {Fb₂ : Type*} [Field Fb₁] [Field Fb₂] {A : ValuationSubring L}
    [Algebra (ResidueField A) Fb₁] [Algebra (ResidueField A) Fb₂]
    (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
    {G : Type*} (gal : G → SemilinearAut L F)
    (x xq : F)
    (hx0 : ∀ c : L, x ≠ algebraMap L F c) (hxq0 : ∀ c : L, xq ≠ algebraMap L F c)
    (hgalx : ∀ σ, gal σ • x = x) (hgalxq : ∀ σ, gal σ • xq = xq)
    (ρ : G → L → L) (hgalc : ∀ σ (c : L), gal σ • algebraMap L F c = algebraMap L F (ρ σ c))
    (huJ₁ : ∀ b : A, b ∈ maximalIdeal A → ∃ h : algebraMap L F (b : L) * x - 1 ∈ R₁.integers, R₁.residue ⟨_, h⟩ = -1)
    (huJ₂ : ∀ b : A, b ∈ maximalIdeal A → ∃ h : algebraMap L F (b : L) * x - 1 ∈ R₂.integers, R₂.residue ⟨_, h⟩ = -1)
    (huJq₁ : ∀ b : A, b ∈ maximalIdeal A → ∃ h : algebraMap L F (b : L) * xq - 1 ∈ R₁.integers, R₁.residue ⟨_, h⟩ = -1)
    (huJq₂ : ∀ b : A, b ∈ maximalIdeal A → ∃ h : algebraMap L F (b : L) * xq - 1 ∈ R₂.integers, R₂.residue ⟨_, h⟩ = -1)
    (hcusp_iff : ∀ W : Place L F, W.ord xq < 0 ↔ W.ord x < 0)
    (huJ_pole : ∀ (b : A) (W : Place L F), W.ord (algebraMap L F (b : L) * x - 1) < 0 → W.ord x < 0)
    (huJq_pole : ∀ (b : A) (W : Place L F), W.ord (algebraMap L F (b : L) * xq - 1) < 0 → W.ord x < 0)
    (huJ0 : ∀ b : A, algebraMap L F (b : L) * x - 1 ≠ 0) (huJq0 : ∀ b : A, algebraMap L F (b : L) * xq - 1 ≠ 0)
    (htateJ : ∀ W : Place L F, ¬ W.ord x < 0 → (∀ a : A, W.ord (x - algebraMap L F (a : L)) ≤ 0) →
      ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (algebraMap L F (b : L) * x - 1))
    (htateJq : ∀ W : Place L F, ¬ W.ord x < 0 → (∀ a : A, W.ord (xq - algebraMap L F (a : L)) ≤ 0) →
      ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (algebraMap L F (b : L) * xq - 1))
    (huniq : ∀ (W : Place L F) (g : F) (c c' : L), 0 < W.ord (algebraMap L F c * g - 1) → 0 < W.ord (algebraMap L F c' * g - 1) → c = c')
    (hxinv₁ : ∃ h : x⁻¹ ∈ R₁.integers, IsUnit (⟨x⁻¹, h⟩ : R₁.integers))
    (hxinv₂ : ∃ h : x⁻¹ ∈ R₂.integers, IsUnit (⟨x⁻¹, h⟩ : R₂.integers))
    (hxqinv₁ : ∃ h : xq⁻¹ ∈ R₁.integers, IsUnit (⟨xq⁻¹, h⟩ : R₁.integers))
    (hxqinv₂ : ∃ h : xq⁻¹ ∈ R₂.integers, IsUnit (⟨xq⁻¹, h⟩ : R₂.integers))
    (hval : ∀ W : Place L F, ¬ W.ord x < 0 →
      ((∃ a : A, 0 < W.ord (x - algebraMap L F (a : L))) ↔ (∃ a : A, 0 < W.ord (xq - algebraMap L F (a : L)))))
    (S : Set G) (D : Divisor L F)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, gal σ • V = V) :
    ∃ U : F,
      (∃ h₁ : U ∈ R₁.integers, IsUnit (⟨U, h₁⟩ : R₁.integers)) ∧
      (∃ h₂ : U ∈ R₂.integers, IsUnit (⟨U, h₂⟩ : R₂.integers)) ∧
      (∀ σ ∈ S, gal σ • U = U) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place L F, W.ord (U * f) < 0 →
        ∃ a : A, 0 < W.ord (x - algebraMap L F (a : L))) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place L F, W.ord (U * f) < 0 →
        ∃ a : A, 0 < W.ord (xq - algebraMap L F (a : L))) := by
  classical

  have hJ : ∀ W : Place L F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ W.ord x < 0 → (∀ a : A, W.ord (x - algebraMap L F (a : L)) ≤ 0) → 0 < W.ord (algebraMap L F (b : L) * x - 1)) ∧
      (b = 0 ∨ 0 < W.ord (algebraMap L F (b : L) * x - 1)) := by
    intro W
    by_cases h : ¬ W.ord x < 0 ∧ ∀ a : A, W.ord (x - algebraMap L F (a : L)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := htateJ W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos, Or.inr hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h, Or.inl rfl⟩
  have hJq : ∀ W : Place L F, ∃ b : A, b ∈ maximalIdeal A ∧
      (¬ W.ord x < 0 → (∀ a : A, W.ord (xq - algebraMap L F (a : L)) ≤ 0) → 0 < W.ord (algebraMap L F (b : L) * xq - 1)) ∧
      (b = 0 ∨ 0 < W.ord (algebraMap L F (b : L) * xq - 1)) := by
    intro W
    by_cases h : ¬ W.ord x < 0 ∧ ∀ a : A, W.ord (xq - algebraMap L F (a : L)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := htateJq W h.1 h.2
      exact ⟨b, hb, fun _ _ => hpos, Or.inr hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h3 => absurd ⟨h1, h3⟩ h, Or.inl rfl⟩
  choose bJ hbJm hbJpos hbJfix using hJ
  choose bJq hbJqm hbJqpos hbJqfix using hJq

  set T : Finset (Place L F) := D.support with hT
  set m : ℕ := (∑ V ∈ T, (D V).toNat) + 1 with hm
  have hmD : ∀ V, D V < m := by
    intro V
    by_cases hV : V ∈ T
    · have h1 : (D V).toNat ≤ ∑ V ∈ T, (D V).toNat :=
        Finset.single_le_sum (f := fun V => (D V).toNat) (fun _ _ => Nat.zero_le _) hV
      have h2 : D V ≤ (D V).toNat := Int.self_le_toNat _
      omega
    · have : D V = 0 := Finsupp.notMem_support_iff.mp hV
      omega
  set n : ℕ := m * T.card + m with hn

  set uJ : Place L F → F := fun V => algebraMap L F (bJ V : L) * x - 1 with huJ
  set uJq : Place L F → F := fun V => algebraMap L F (bJq V : L) * xq - 1 with huJq
  set U : F := ((x⁻¹) ^ n * (xq⁻¹) ^ n) * ((∏ V ∈ T, uJ V ^ m) * ∏ V ∈ T, uJq V ^ m) with hU
  have hx_ne : x ≠ 0 := by
    intro h; exact hx0 0 (by rw [h, map_zero])
  have hxq_ne : xq ≠ 0 := by
    intro h; exact hxq0 0 (by rw [h, map_zero])
  have hxinv_ne : x⁻¹ ≠ 0 := inv_ne_zero hx_ne
  have hxqinv_ne : xq⁻¹ ≠ 0 := inv_ne_zero hxq_ne
  have huJne : ∀ V, uJ V ≠ 0 := fun V => huJ0 _
  have huJqne : ∀ V, uJq V ≠ 0 := fun V => huJq0 _
  have hP1ne : ∏ V ∈ T, uJ V ^ m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun V _ => pow_ne_zero _ (huJne V)
  have hP2ne : ∏ V ∈ T, uJq V ^ m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun V _ => pow_ne_zero _ (huJqne V)
  have hX0ne : (x⁻¹) ^ n * (xq⁻¹) ^ n ≠ 0 := mul_ne_zero (pow_ne_zero _ hxinv_ne) (pow_ne_zero _ hxqinv_ne)
  have hU0 : U ≠ 0 := mul_ne_zero hX0ne (mul_ne_zero hP1ne hP2ne)
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · exact isUnit_product R₁ T n m x⁻¹ xq⁻¹ uJ uJq hxinv₁ hxqinv₁ (fun V => huJ₁ (bJ V) (hbJm V)) (fun V => huJq₁ (bJq V) (hbJqm V))
  · exact isUnit_product R₂ T n m x⁻¹ xq⁻¹ uJ uJq hxinv₂ hxqinv₂ (fun V => huJ₂ (bJ V) (hbJm V)) (fun V => huJq₂ (bJq V) (hbJqm V))
  ·
    intro σ hσ
    have hfixb : ∀ V ∈ T, gal σ • uJ V = uJ V := by
      intro V hV
      have hc' := hgalc σ (bJ V : L)
      have hsm : gal σ • uJ V = algebraMap L F (ρ σ (bJ V : L)) * x - 1 := by
        simp only [huJ]
        rw [smul_sub, smul_mul', hc', hgalx, smul_one]
      rcases hbJfix V with h | h
      · have h0 : ρ σ (bJ V : L) = 0 := by
          have e := hc'
          rw [h, ZeroMemClass.coe_zero, map_zero, smul_zero] at e
          rw [h, ZeroMemClass.coe_zero]
          exact (map_eq_zero _).mp e.symm
        rw [hsm, h0]
        simp only [huJ]
        rw [h, ZeroMemClass.coe_zero]
      · have ht := SemilinearAut.ord_smul (gal σ) V (uJ V)
        rw [hDfix V hV σ hσ, hsm] at ht
        have heq : ρ σ (bJ V : L) = (bJ V : L) := huniq V x _ _ (by rw [ht]; exact h) h
        rw [hsm, heq]
    have hfixbq : ∀ V ∈ T, gal σ • uJq V = uJq V := by
      intro V hV
      have hc' := hgalc σ (bJq V : L)
      have hsm : gal σ • uJq V = algebraMap L F (ρ σ (bJq V : L)) * xq - 1 := by
        simp only [huJq]
        rw [smul_sub, smul_mul', hc', hgalxq, smul_one]
      rcases hbJqfix V with h | h
      · have h0 : ρ σ (bJq V : L) = 0 := by
          have e := hc'
          rw [h, ZeroMemClass.coe_zero, map_zero, smul_zero] at e
          rw [h, ZeroMemClass.coe_zero]
          exact (map_eq_zero _).mp e.symm
        rw [hsm, h0]
        simp only [huJq]
        rw [h, ZeroMemClass.coe_zero]
      · have ht := SemilinearAut.ord_smul (gal σ) V (uJq V)
        rw [hDfix V hV σ hσ, hsm] at ht
        have heq : ρ σ (bJq V : L) = (bJq V : L) := huniq V xq _ _ (by rw [ht]; exact h) h
        rw [hsm, heq]
    have hfixinv : gal σ • x⁻¹ = x⁻¹ := by
      rw [SemilinearAut.smul_def, map_inv₀, ← SemilinearAut.smul_def, hgalx]
    have hfixinvq : gal σ • xq⁻¹ = xq⁻¹ := by
      rw [SemilinearAut.smul_def, map_inv₀, ← SemilinearAut.smul_def, hgalxq]
    rw [hU, smul_mul', smul_mul', smul_mul', smul_pow', smul_pow', hfixinv, hfixinvq, Finset.smul_prod', Finset.smul_prod']
    congr 2
    · exact Finset.prod_congr rfl fun V hV => by rw [smul_pow', hfixb V hV]
    · exact Finset.prod_congr rfl fun V hV => by rw [smul_pow', hfixbq V hV]
  ·
    have hordU : ∀ W : Place L F, W.ord U = (n * W.ord x⁻¹ + n * W.ord xq⁻¹) +
        ((∑ V ∈ T, m * W.ord (uJ V)) + ∑ V ∈ T, m * W.ord (uJq V)) := by
      intro W
      rw [hU, W.ord_mul hX0ne (mul_ne_zero hP1ne hP2ne), W.ord_mul (pow_ne_zero _ hxinv_ne) (pow_ne_zero _ hxqinv_ne),
        W.ord_mul hP1ne hP2ne, ord_pow, ord_pow,
        ord_prod W T _ (fun V _ => pow_ne_zero _ (huJne V)), ord_prod W T _ (fun V _ => pow_ne_zero _ (huJqne V))]
      simp only [ord_pow]

    have key : ∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place L F, W.ord (U * f) < 0 →
        ¬ (∀ a : A, W.ord (x - algebraMap L F (a : L)) ≤ 0) ∧ ¬ (∀ a : A, W.ord (xq - algebraMap L F (a : L)) ≤ 0) := by
      intro f hf hf0 W hW
      rw [W.ord_mul hU0 hf0, hordU] at hW
      have hfD : -D W ≤ W.ord f := by
        rcases (mem_riemannRochSpace_iff.mp hf) W with h | h
        · exact absurd h hf0
        · exact h
      have hDm : D W < m := hmD W
      have hm1' : 1 ≤ m := by rw [hm]; exact Nat.le_add_left 1 _
      have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm1'
      by_cases hc : W.ord x < 0
      ·
        exfalso
        have hcq : W.ord xq < 0 := (hcusp_iff W).mpr hc
        have h1 : ∀ V ∈ T, W.ord x ≤ W.ord (uJ V) := fun V _ => ord_le_ord_affine W _ x hc (huJne V)
        have h2 : ∀ V ∈ T, W.ord xq ≤ W.ord (uJq V) := fun V _ => ord_le_ord_affine W _ xq hcq (huJqne V)
        have s1 : (T.card : ℤ) * (m * W.ord x) ≤ ∑ V ∈ T, m * W.ord (uJ V) := by
          have := Finset.card_nsmul_le_sum T (fun V => m * W.ord (uJ V)) (m * W.ord x)
            (fun V hV => mul_le_mul_of_nonneg_left (h1 V hV) (by exact_mod_cast Nat.zero_le m))
          simpa [nsmul_eq_mul] using this
        have s2 : (T.card : ℤ) * (m * W.ord xq) ≤ ∑ V ∈ T, m * W.ord (uJq V) := by
          have := Finset.card_nsmul_le_sum T (fun V => m * W.ord (uJq V)) (m * W.ord xq)
            (fun V hV => mul_le_mul_of_nonneg_left (h2 V hV) (by exact_mod_cast Nat.zero_le m))
          simpa [nsmul_eq_mul] using this
        rw [W.ord_inv, W.ord_inv] at hW
        have hn' : (n : ℤ) = m * T.card + m := by simp [hn]

        nlinarith
      · have hxn : 0 ≤ W.ord x := by omega
        have hxqn : 0 ≤ W.ord xq := by
          by_contra h; exact hc ((hcusp_iff W).mp (by omega))

        have i1 : ∀ V ∈ T, 0 ≤ W.ord (uJ V) := fun V _ => by
          by_contra h; exact hc (huJ_pole (bJ V) W (by change W.ord (uJ V) < 0; omega))
        have i2 : ∀ V ∈ T, 0 ≤ W.ord (uJq V) := fun V _ => by
          by_contra h; exact hc (huJq_pole (bJq V) W (by change W.ord (uJq V) < 0; omega))
        have s1 : 0 ≤ ∑ V ∈ T, m * W.ord (uJ V) :=
          Finset.sum_nonneg fun V hV => mul_nonneg (by exact_mod_cast Nat.zero_le m) (i1 V hV)
        have s2 : 0 ≤ ∑ V ∈ T, m * W.ord (uJq V) :=
          Finset.sum_nonneg fun V hV => mul_nonneg (by exact_mod_cast Nat.zero_le m) (i2 V hV)

        by_cases hxz : 0 < W.ord x
        · have h1 : ∃ a : A, 0 < W.ord (x - algebraMap L F (a : L)) := ⟨0, by simpa using hxz⟩
          have h2 := (hval W hc).mp h1
          exact ⟨fun h => by obtain ⟨a, ha⟩ := h1; linarith [h a], fun h => by obtain ⟨a, ha⟩ := h2; linarith [h a]⟩
        by_cases hxqz : 0 < W.ord xq
        · have h2 : ∃ a : A, 0 < W.ord (xq - algebraMap L F (a : L)) := ⟨0, by simpa using hxqz⟩
          have h1 := (hval W hc).mpr h2
          exact ⟨fun h => by obtain ⟨a, ha⟩ := h1; linarith [h a], fun h => by obtain ⟨a, ha⟩ := h2; linarith [h a]⟩

        have hx00 : W.ord x⁻¹ = 0 := by rw [W.ord_inv]; omega
        have hxq00 : W.ord xq⁻¹ = 0 := by rw [W.ord_inv]; omega
        rw [hx00, hxq00, mul_zero, zero_add, zero_add] at hW
        have hDW : 0 < D W := by omega
        have hWT : W ∈ T := Finsupp.mem_support_iff.mpr hDW.ne'
        constructor
        · intro hTx
          have hpos : 0 < W.ord (uJ W) := hbJpos W hc hTx
          have hsplit := Finset.add_sum_erase T (fun V => (m : ℤ) * W.ord (uJ V)) hWT
          have hrest : 0 ≤ ∑ V ∈ T.erase W, (m : ℤ) * W.ord (uJ V) :=
            Finset.sum_nonneg fun V hV => mul_nonneg (by exact_mod_cast Nat.zero_le m) (i1 V (Finset.mem_of_mem_erase hV))
          have hmW : (m : ℤ) * 1 ≤ m * W.ord (uJ W) := mul_le_mul_of_nonneg_left (by omega) (by exact_mod_cast Nat.zero_le m)
          linarith
        · intro hTq
          have hpos : 0 < W.ord (uJq W) := hbJqpos W hc hTq
          have hsplit := Finset.add_sum_erase T (fun V => (m : ℤ) * W.ord (uJq V)) hWT
          have hrest : 0 ≤ ∑ V ∈ T.erase W, (m : ℤ) * W.ord (uJq V) :=
            Finset.sum_nonneg fun V hV => mul_nonneg (by exact_mod_cast Nat.zero_le m) (i2 V (Finset.mem_of_mem_erase hV))
          have hmW : (m : ℤ) * 1 ≤ m * W.ord (uJq W) := mul_le_mul_of_nonneg_left (by omega) (by exact_mod_cast Nat.zero_le m)
          linarith
    refine ⟨fun f hf hf0 W hW => ?_, fun f hf hf0 W hW => ?_⟩
    · obtain ⟨h, _⟩ := key f hf hf0 W hW
      simpa only [not_forall, not_le] using h
    · obtain ⟨_, h⟩ := key f hf hf0 W hW
      simpa only [not_forall, not_le] using h

end PoleUnitB

end

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open PoleUnitA in
open Classical in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : 0 ≤ D) (hgood : Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V)
    (x : ↥(xHFunctionFieldBar M H)) (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D)] :
    ∃ U : ↥(xHFunctionFieldBar M H),
      (∃ h₁ : U ∈ Rpd.R₁.integers, IsUnit (⟨U, h₁⟩ : Rpd.R₁.integers)) ∧
      (∃ h₂ : U ∈ Rpd.R₂.integers, IsUnit (⟨U, h₂⟩ : Rpd.R₂.integers)) ∧
      (∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • U = U) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) ∧
      (∀ f ∈ riemannRochSpace D, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (θ.symm x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) := by
  classical
  haveI hNeZp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p

  have hsymm : θ.symm x = θ x := theta_symm_x hpM2 hHp hα_coe hβ_coe hpb hx

  have hcusp_iff : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (θ x) < 0 ↔ W.ord x < 0 := by
    intro W
    constructor
    · intro h
      by_contra h'
      have hm : x ∈ W.toValuationSubring := mem_of_ord_nonneg W (x_ne_zero hx) (not_lt.mp h')
      have hm' := mem_of_eval22 data.monic W hm (eval22_x_thetax hα_coe hβ_coe hx data)
      exact absurd (ord_nonneg_of_mem W (thetax_ne_zero hα_coe hβ_coe hx) hm') (not_le.mpr h)
    · intro h
      by_contra h'
      have hm : θ x ∈ W.toValuationSubring := mem_of_ord_nonneg W (thetax_ne_zero hα_coe hβ_coe hx) (not_lt.mp h')
      have hm' := mem_of_eval22 data.monic W hm (eval22_thetax_x hpM2 hHp hα_coe hβ_coe hpb hx data)
      exact absurd (ord_nonneg_of_mem W (x_ne_zero hx) hm') (not_le.mpr h)

  have hxqinv₁ : ∃ h : (θ x)⁻¹ ∈ Rpd.R₁.integers, IsUnit (⟨(θ x)⁻¹, h⟩ : ↥Rpd.R₁.integers) := by
    have e : (θ x)⁻¹ = θ x⁻¹ := (map_inv₀ θ x).symm
    rw [e]
    refine isUnit₁_of_coe_eq Rpd _ _ (coe_theta_xinv hα_coe hβ_coe hx) ?_
    rw [coeffMap_qExpand, coeffMap_residue_xinv]
    exact (map_ne_zero_iff _ (qExpand_injective p)).mpr (inv_ne_zero jqModC_residueField_ne_zero)
  have hxqinv₂ : ∃ h : (θ x)⁻¹ ∈ Rpd.R₂.integers, IsUnit (⟨(θ x)⁻¹, h⟩ : ↥Rpd.R₂.integers) := by
    refine isUnit₂_of_theta Rpd _ ?_
    rw [map_inv₀, theta_theta_x hpM2 hHp hα_coe hβ_coe hpb hx]
    exact xinv_mem₁ Rpd hx

  have hval : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ W.ord x < 0 →
      ((∃ a : ↥A, 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)))) ↔
        (∃ a : ↥A, 0 < W.ord (θ x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))))) := by
    intro W _
    constructor
    · rintro ⟨a, ha⟩
      exact exists_int_value data.monic A W (degOne W) (eval22_x_thetax hα_coe hβ_coe hx data)
        (thetax_ne_algebraMap hα_coe hβ_coe hx) a (hasValue_of_ord_sub_pos W ha)
    · rintro ⟨a, ha⟩
      exact exists_int_value data.monic A W (degOne W) (eval22_thetax_x hpM2 hHp hα_coe hβ_coe hpb hx data)
        (x_ne_algebraMap hx) a (hasValue_of_ord_sub_pos W ha)
  obtain ⟨U, hU₁, hU₂, hUfix, hUx, hUxq⟩ := PoleUnitB.exists_bigU Rpd.R₁ Rpd.R₂ (fun σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ) => arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ) x (θ x)
    (x_ne_algebraMap hx) (thetax_ne_algebraMap hα_coe hβ_coe hx)
    (galois_smul_x hx) (galois_smul_thetax hα_coe hβ_coe hx)
    (fun σ c => σ c) (fun σ c => galois_smul_algebraMap σ c)
    (fun b hb => uJ_mem₁ Rpd hx b hb) (fun b hb => uJ_mem₂ hα_coe hβ_coe Rpd hx b hb)
    (fun b hb => uJq_mem₁ hα_coe hβ_coe Rpd hx b hb) (fun b hb => uJq_mem₂ hpM2 hHp hα_coe hβ_coe hpb Rpd hx b hb)
    hcusp_iff
    (fun b W h => ord_neg_of_ord_cmul_sub_one_neg W (x_ne_zero hx) _ h)
    (fun b W h => (hcusp_iff W).mp (ord_neg_of_ord_cmul_sub_one_neg W (thetax_ne_zero hα_coe hβ_coe hx) _ h))
    (fun b => cmul_sub_one_ne_zero (x_ne_algebraMap hx) _) (fun b => cmul_sub_one_ne_zero (thetax_ne_algebraMap hα_coe hβ_coe hx) _)
    (fun W hW hc => exists_tate A W (degOne W) (x_ne_algebraMap hx) hW hc)
    (fun W hW hc => exists_tate A W (degOne W) (thetax_ne_algebraMap hα_coe hβ_coe hx) (fun h => hW ((hcusp_iff W).mp h)) hc)
    (fun W g c c' h h' => eq_of_ord_sub_one_pos W g h h')
    (xinv_mem₁ Rpd hx) (xinv_mem₂ hα_coe hβ_coe Rpd hx) hxqinv₁ hxqinv₂ hval S D hDfix
  refine ⟨U, hU₁, hU₂, hUfix, hUx, ?_⟩
  rw [hsymm]
  exact hUxq

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace (solution)
