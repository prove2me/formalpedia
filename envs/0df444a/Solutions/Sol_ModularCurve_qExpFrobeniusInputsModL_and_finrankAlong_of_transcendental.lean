-- Prove2me | solution 1 for ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/655f1e12-b8ce-5265-acc9-712bf8593571

import Mathlib
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option linter.unusedSectionVars false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "Polynomial IntermediateField HahnSeries ModularCurve P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFrobeniusModL coe_qExpFrobeniusModL qExpFrobeniusModL_injective qExpFrobeniusModL_isIntegral qExpFrobeniusPlaceModL mem_qExpFrobeniusPlaceModL_iff QExpFrobeniusInputsModL qExpFrobeniusInputsModL_intro intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_coeffMap coeffMap_id coeffMap_algebraMap pow_char_eq_coeffMap_frobenius_qExpand"
namespace QExpFrobInputsSol
p2m_open "ModularCurve"

section Sigma

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

abbrev FF : Type _ := qExpFunctionFieldC K Γ

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_intSeriesC (g : K →+* K) (p : PowerSeries ℤ) : coeffMap g (intSeriesC K p) = intSeriesC K p := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · lift k to ℕ using hk with k
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, map_intCast]

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_mem (g : K →+* K) {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    coeffMap g x ∈ qExpFunctionFieldC K Γ := by
  have hx' : x ∈ (qExpFunctionFieldC K Γ).toSubfield := hx
  rw [qExpFunctionFieldC, adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ)).map
      (coeffMap g) ≤ (qExpFunctionFieldC K Γ).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨k, f, g', pf, pg, hf, hg, hg0, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (qExpFunctionFieldC K Γ).algebraMap_mem _
    · change coeffMap g (intSeriesC K pf / intSeriesC K pg) ∈ qExpFunctionFieldC K Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      exact div_mem_qExpFunctionFieldC f g' hf hg hg0
  exact key ⟨x, hx', rfl⟩

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem coeffMap_qExpand' (g : K →+* K) (n : ℕ) [NeZero n] (x : LaurentSeries K) :
    coeffMap g (qExpand K n x) = qExpand K n (coeffMap g x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

variable (ℓ)

def sigmaRingHom : FF K Γ →+* FF K Γ where
  toFun x := ⟨coeffMap (frobenius K ℓ) x, coeffMap_mem K Γ _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

def sigmaInvRingHom : FF K Γ →+* FF K Γ where
  toFun x := ⟨coeffMap ((frobeniusEquiv K ℓ).symm : K →+* K) x, coeffMap_mem K Γ _ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_sigmaRingHom (x : FF K Γ) :
    (sigmaRingHom K Γ ℓ x : LaurentSeries K) = coeffMap (frobenius K ℓ) x := rfl

@[scoped simp] theorem coe_sigmaInvRingHom (x : FF K Γ) :
    (sigmaInvRingHom K Γ ℓ x : LaurentSeries K) = coeffMap ((frobeniusEquiv K ℓ).symm : K →+* K) x := rfl

def sigma : FF K Γ ≃+* FF K Γ :=
  { sigmaRingHom K Γ ℓ with
    invFun := sigmaInvRingHom K Γ ℓ
    left_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).symm_apply_apply a
    right_inv := fun x => Subtype.ext <| by
      change coeffMap _ (coeffMap _ (x : LaurentSeries K)) = (x : LaurentSeries K)
      rw [coeffMap_coeffMap]
      convert coeffMap_id (x : LaurentSeries K)
      ext a; exact (frobeniusEquiv K ℓ).apply_symm_apply a }

@[scoped simp] theorem coe_sigma (x : FF K Γ) : (sigma K Γ ℓ x : LaurentSeries K) = coeffMap (frobenius K ℓ) x := rfl

theorem frobenius_sigma (x : FF K Γ) : qExpFrobeniusModL K Γ ℓ (sigma K Γ ℓ x) = x ^ ℓ := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL, coe_sigma, ← coeffMap_qExpand']
  push_cast
  exact (pow_char_eq_coeffMap_frobenius_qExpand ℓ (x : LaurentSeries K)).symm

theorem frobenius_eq_pow (y : FF K Γ) : qExpFrobeniusModL K Γ ℓ y = ((sigma K Γ ℓ).symm y) ^ ℓ := by
  conv_lhs => rw [← (sigma K Γ ℓ).apply_symm_apply y]
  exact frobenius_sigma K Γ ℓ _

theorem mem_range_frobenius_iff (y : FF K Γ) :
    y ∈ Set.range (qExpFrobeniusModL K Γ ℓ) ↔ ∃ u : FF K Γ, u ^ ℓ = y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(sigma K Γ ℓ).symm x, (frobenius_eq_pow K Γ ℓ x).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨sigma K Γ ℓ u, frobenius_sigma K Γ ℓ u⟩

theorem sigma_algebraMap (a : K) : sigma K Γ ℓ (algebraMap K (FF K Γ) a) = algebraMap K (FF K Γ) (a ^ ℓ) := by
  apply Subtype.ext
  change coeffMap (frobenius K ℓ) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (a ^ ℓ)
  rw [coeffMap_algebraMap, frobenius_def]

def sigmaSL : SemilinearAut K (FF K Γ) :=
  ⟨(sigma K Γ ℓ, frobeniusEquiv K ℓ), fun a => by
    change sigma K Γ ℓ (algebraMap K (FF K Γ) a) = algebraMap K (FF K Γ) (frobeniusEquiv K ℓ a)
    rw [sigma_algebraMap, frobeniusEquiv_apply, frobenius_def]⟩

@[scoped simp] theorem sigmaSL_smul (x : FF K Γ) : sigmaSL K Γ ℓ • x = sigma K Γ ℓ x := rfl

theorem sigmaSL_inv_smul (x : FF K Γ) : (sigmaSL K Γ ℓ)⁻¹ • x = (sigma K Γ ℓ).symm x := rfl

end Sigma

section Places

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

theorem pow_mem_valuationSubring_iff {F : Type*} [Field F] (O : ValuationSubring F) {n : ℕ} (hn : n ≠ 0)
    (u : F) : u ^ n ∈ O ↔ u ∈ O := by
  rw [← O.valuation_le_one_iff, ← O.valuation_le_one_iff, map_pow]
  exact pow_le_one_iff hn

theorem frobeniusPlace_eq_smul (w : Place K (FF K Γ)) :
    qExpFrobeniusPlaceModL K Γ ℓ w = sigmaSL K Γ ℓ • w := by
  apply Place.ext
  ext x
  rw [mem_qExpFrobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, sigmaSL_inv_smul, frobenius_eq_pow]
  exact pow_mem_valuationSubring_iff _ (Fact.out : ℓ.Prime).ne_zero _

theorem restrictAlong_frobenius_eq_smul (w : Place K (FF K Γ)) :
    w.restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) = sigmaSL K Γ ℓ • w :=
  frobeniusPlace_eq_smul K Γ ℓ w

theorem ord_frobenius (w : Place K (FF K Γ)) (f : FF K Γ) :
    w.ord (qExpFrobeniusModL K Γ ℓ f) = ℓ * w.ord ((sigma K Γ ℓ).symm f) := by
  rw [frobenius_eq_pow, ← zpow_natCast, Place.ord_zpow]

theorem ramificationIndexAlong_frobenius (w : Place K (FF K Γ)) :
    Place.ramificationIndexAlong (qExpFrobeniusModL K Γ ℓ) w = ℓ := by
  letI := algebraAlong (qExpFrobeniusModL K Γ ℓ)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)
  have hℓ : ℓ.Prime := Fact.out
  change w.ramificationIndex (FF K Γ) = ℓ
  have halg : ∀ f : FF K Γ, algebraMap (FF K Γ) (FF K Γ) f = qExpFrobeniusModL K Γ ℓ f := fun _ => rfl
  apply le_antisymm
  ·
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hπ1 : w.ord (π : FF K Γ) = 1 := w.ord_coe_irreducible hπ
    have hπ0 : (π : FF K Γ) ≠ 0 := fun h => by simp [h] at hπ1
    have hσπ0 : sigma K Γ ℓ π ≠ 0 := (map_ne_zero_iff _ (sigma K Γ ℓ).injective).mpr hπ0
    have hord : w.ord (algebraMap (FF K Γ) (FF K Γ) (sigma K Γ ℓ π)) = ℓ := by
      rw [halg, ord_frobenius, RingEquiv.symm_apply_apply, hπ1, mul_one]
    have h := Place.ramificationIndex_le_ord (F := FF K Γ) w hσπ0 (by rw [hord]; exact_mod_cast hℓ.pos)
    rw [hord] at h
    exact_mod_cast h
  ·
    obtain ⟨f, hf0, hfe⟩ := Place.exists_ord_eq_ramificationIndex (F := FF K Γ) w
    have hpos := Place.ramificationIndex_pos (F := FF K Γ) w
    rw [halg, ord_frobenius] at hfe
    have hk : 0 < w.ord ((sigma K Γ ℓ).symm f) := by
      by_contra hk
      push Not at hk
      have : (ℓ : ℤ) * w.ord ((sigma K Γ ℓ).symm f) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hk
      omega
    have : (ℓ : ℤ) * 1 ≤ (ℓ : ℤ) * w.ord ((sigma K Γ ℓ).symm f) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    omega

variable [hP : HasPrincipalDivisors K (FF K Γ)]

theorem fiberAlong_frobenius (v : Place K (FF K Γ)) :
    Place.fiberAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) v = {(sigmaSL K Γ ℓ)⁻¹ • v} := by
  ext W
  rw [Place.mem_fiberAlong, Finset.mem_singleton, restrictAlong_frobenius_eq_smul, smul_eq_iff_eq_inv_smul]

end Places

section Degree

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

abbrev PP : IntermediateField K (FF K Γ) := (qExpFrobeniusModL K Γ ℓ).fieldRange

theorem mem_PP_iff (y : FF K Γ) : y ∈ PP K Γ ℓ ↔ ∃ u : FF K Γ, u ^ ℓ = y := by
  rw [AlgHom.mem_fieldRange, ← mem_range_frobenius_iff, Set.mem_range]

def isoPP : FF K Γ ≃+* PP K Γ ℓ :=
  RingEquiv.ofBijective
    ((qExpFrobeniusModL K Γ ℓ).toRingHom.codRestrict (PP K Γ ℓ).toSubring
      fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    ⟨fun x y h => qExpFrobeniusModL_injective K Γ ℓ (congrArg Subtype.val h),
     fun ⟨y, hy⟩ => by
       obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
       exact ⟨x, rfl⟩⟩

@[scoped simp] theorem coe_isoPP (x : FF K Γ) : (isoPP K Γ ℓ x : FF K Γ) = qExpFrobeniusModL K Γ ℓ x := rfl

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in
theorem charP_FF [CharP K ℓ] : CharP (FF K Γ) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (FF K Γ)).injective ℓ

theorem minpoly_PP_of_not_mem {f : FF K Γ} (hf : f ∉ PP K Γ ℓ) :
    minpoly (PP K Γ ℓ) f =
      X ^ ℓ - Polynomial.C (⟨f ^ ℓ, (mem_PP_iff K Γ ℓ _).mpr ⟨f, rfl⟩⟩ : PP K Γ ℓ) := by
  haveI := charP_FF K Γ ℓ
  have hℓ : ℓ.Prime := Fact.out
  symm
  refine minpoly.eq_of_irreducible_of_monic ?_ ?_ (monic_X_pow_sub_C _ hℓ.ne_zero)
  · refine X_pow_sub_C_irreducible_of_prime hℓ fun b hb => ?_
    apply hf
    have hb' : (b : FF K Γ) ^ ℓ = f ^ ℓ := by
      have h := congrArg Subtype.val hb
      simpa using h
    have : (b : FF K Γ) = f := by
      have h := sub_pow_char (b : FF K Γ) f (p := ℓ)
      rw [hb', sub_self] at h
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h.symm.symm)
    rw [← this]; exact b.2
  · simp

variable {s : FF K Γ}

theorem finrank_PP_adjoin (hsP : s ∉ PP K Γ ℓ) : Module.finrank (PP K Γ ℓ) (PP K Γ ℓ)⟮s⟯ = ℓ := by
  have hint : IsIntegral (PP K Γ ℓ) s :=
    ⟨X ^ ℓ - Polynomial.C (⟨s ^ ℓ, (mem_PP_iff K Γ ℓ _).mpr ⟨s, rfl⟩⟩ : PP K Γ ℓ),
      monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).ne_zero, by simp⟩
  rw [adjoin.finrank hint, minpoly_PP_of_not_mem K Γ ℓ hsP, natDegree_X_pow_sub_C]

def MM (s : FF K Γ) : IntermediateField K (FF K Γ) := restrictScalars K (PP K Γ ℓ)⟮s⟯

theorem mem_MM_iff (y : FF K Γ) : y ∈ MM K Γ ℓ s ↔ y ∈ (PP K Γ ℓ)⟮s⟯ := Iff.rfl

theorem PP_le_MM : PP K Γ ℓ ≤ MM K Γ ℓ s := fun p hp =>
  (mem_MM_iff K Γ ℓ p).mpr ((PP K Γ ℓ)⟮s⟯.algebraMap_mem ⟨p, hp⟩)

theorem mem_MM_self : s ∈ MM K Γ ℓ s :=
  (mem_MM_iff K Γ ℓ _).mpr (mem_adjoin_simple_self _ _)

theorem mem_MM (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (y : FF K Γ) : y ∈ MM K Γ ℓ s := by
  haveI := charP_FF K Γ ℓ
  haveI : CharP (MM K Γ ℓ s) ℓ := IntermediateField.charP _ ℓ
  haveI : ExpChar (MM K Γ ℓ s) ℓ := ExpChar.prime Fact.out
  have hsepK : IsSeparable K⟮s⟯ y := Algebra.IsSeparable.isSeparable _ y
  have hle : K⟮s⟯ ≤ MM K Γ ℓ s := adjoin_simple_le_iff.mpr (mem_MM_self K Γ ℓ)
  let incl : K⟮s⟯ →+* MM K Γ ℓ s := (IntermediateField.inclusion hle).toRingHom
  have hsep2 : IsSeparable (MM K Γ ℓ s) y := by
    have hm : (minpoly K⟮s⟯ y).Separable := hsepK
    have hroot : aeval y ((minpoly K⟮s⟯ y).map incl) = 0 := by
      rw [aeval_def, eval₂_map, ← minpoly.aeval K⟮s⟯ y, aeval_def]
      rfl
    exact (hm.map (f := incl)).of_dvd (minpoly.dvd _ _ hroot)

  have hperf : y ∈ perfectClosure (MM K Γ ℓ s) (FF K Γ) := by
    rw [mem_perfectClosure_iff_pow_mem ℓ]
    refine ⟨1, ⟨y ^ ℓ, PP_le_MM K Γ ℓ ((mem_PP_iff K Γ ℓ _).mpr ⟨y, rfl⟩)⟩, ?_⟩
    rw [pow_one]; rfl
  have hsc : y ∈ separableClosure (MM K Γ ℓ s) (FF K Γ) := mem_separableClosure_iff.mpr hsep2
  have hbot : y ∈ (⊥ : IntermediateField (MM K Γ ℓ s) (FF K Γ)) := by
    rw [← separableClosure_inf_perfectClosure]; exact ⟨hsc, hperf⟩
  rw [IntermediateField.mem_bot] at hbot
  obtain ⟨⟨z, hz⟩, rfl⟩ := hbot
  exact hz

theorem PP_adjoin_eq_top (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) : (PP K Γ ℓ)⟮s⟯ = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_top]
  exact le_antisymm le_top fun y _ => mem_MM K Γ ℓ hsep y

theorem forall_exists_pow_eq_of_mem (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hs : s ∈ PP K Γ ℓ)
    (y : FF K Γ) : ∃ u : FF K Γ, u ^ ℓ = y := by
  rw [← mem_PP_iff]
  have htop := PP_adjoin_eq_top K Γ ℓ hsep
  have hbot : (PP K Γ ℓ)⟮s⟯ = ⊥ := adjoin_simple_eq_bot_iff.mpr ⟨⟨s, hs⟩, rfl⟩
  have hy : y ∈ (⊤ : IntermediateField (PP K Γ ℓ) (FF K Γ)) := mem_top
  rw [← htop, hbot, IntermediateField.mem_bot] at hy
  obtain ⟨⟨z, hz⟩, rfl⟩ := hy
  exact hz

theorem finrank_PP (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) :
    Module.finrank (PP K Γ ℓ) (FF K Γ) = ℓ := by
  rw [← finrank_top', ← PP_adjoin_eq_top K Γ ℓ hsep, finrank_PP_adjoin K Γ ℓ hsP]

theorem finite_PP (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) :
    Module.Finite (PP K Γ ℓ) (FF K Γ) :=
  Module.finite_of_finrank_pos (by rw [finrank_PP K Γ ℓ hsep hsP]; exact (Fact.out : ℓ.Prime).pos)

theorem isoPP_compat :
    (algebraMap (PP K Γ ℓ) (FF K Γ)).comp (isoPP K Γ ℓ).toRingHom =
      (RingEquiv.refl (FF K Γ)).toRingHom.comp
        (@algebraMap (FF K Γ) (FF K Γ) _ _ (algebraAlong (qExpFrobeniusModL K Γ ℓ))) :=
  RingHom.ext fun _ => rfl

theorem finrankAlong_frobenius (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) :
    finrankAlong K (qExpFrobeniusModL K Γ ℓ) = ℓ := by
  refine Eq.trans ?_ (finrank_PP K Γ ℓ hsep hsP)
  exact @Algebra.finrank_eq_of_equiv_equiv (FF K Γ) (FF K Γ) _ _ (algebraAlong (qExpFrobeniusModL K Γ ℓ))
    (PP K Γ ℓ) (FF K Γ) _ _ _ (isoPP K Γ ℓ) (RingEquiv.refl _) (isoPP_compat K Γ ℓ)

theorem finiteAlong_frobenius (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) :
    FiniteAlong K (qExpFrobeniusModL K Γ ℓ) :=
  @Module.Finite.of_equiv_equiv (PP K Γ ℓ) (FF K Γ) (FF K Γ) (FF K Γ) _ _ _ _ _
    (algebraAlong (qExpFrobeniusModL K Γ ℓ)) (isoPP K Γ ℓ).symm (RingEquiv.refl _)
    (by
      apply RingHom.ext; intro x
      obtain ⟨y, rfl⟩ := (isoPP K Γ ℓ).surjective x
      change (qExpFrobeniusModL K Γ ℓ) ((isoPP K Γ ℓ).symm (isoPP K Γ ℓ y)) = (isoPP K Γ ℓ y : FF K Γ)
      rw [RingEquiv.symm_apply_apply]; rfl)
    (finite_PP K Γ ℓ hsep hsP)

end Degree

section Norm

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]
variable {s : FF K Γ}

theorem coe_norm_PP (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) (f : FF K Γ) :
    ((Algebra.norm (PP K Γ ℓ) f : PP K Γ ℓ) : FF K Γ) = f ^ ℓ := by
  haveI := charP_FF K Γ ℓ
  haveI : CharP (PP K Γ ℓ) ℓ := IntermediateField.charP _ ℓ
  haveI := finite_PP K Γ ℓ hsep hsP
  have hℓ : ℓ.Prime := Fact.out
  by_cases hf : f ∈ PP K Γ ℓ
  ·
    have hfp : algebraMap (PP K Γ ℓ) (FF K Γ) ⟨f, hf⟩ = f := IntermediateField.algebraMap_apply _ _
    have h := Algebra.norm_algebraMap (S := FF K Γ) (⟨f, hf⟩ : PP K Γ ℓ)
    rw [hfp, finrank_PP K Γ ℓ hsep hsP] at h
    rw [h]
    exact SubmonoidClass.coe_pow _ _
  ·
    have hint : IsIntegral (PP K Γ ℓ) f := IsIntegral.of_finite _ f
    have hdeg : (minpoly (PP K Γ ℓ) f).natDegree = ℓ := by
      rw [minpoly_PP_of_not_mem K Γ ℓ hf, natDegree_X_pow_sub_C]
    have h1 : Module.finrank (PP K Γ ℓ) (PP K Γ ℓ)⟮f⟯ = ℓ := by
      rw [adjoin.finrank hint, hdeg]
    have htop : (PP K Γ ℓ)⟮f⟯ = ⊤ :=
      IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [h1, finrank_top', finrank_PP K Γ ℓ hsep hsP])
    have h2 : Module.finrank (PP K Γ ℓ)⟮f⟯ (FF K Γ) = 1 := finrank_eq_one_iff_eq_top.mpr htop
    rw [Algebra.norm_eq_norm_adjoin, h2, pow_one]
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)
    have hgen : (adjoin.powerBasis hint).gen = AdjoinSimple.gen (PP K Γ ℓ) f := adjoin.powerBasis_gen hint
    have hdim : (adjoin.powerBasis hint).dim = ℓ := by rw [adjoin.powerBasis_dim, hdeg]
    have hmin : minpoly (PP K Γ ℓ) (AdjoinSimple.gen (PP K Γ ℓ) f) = minpoly (PP K Γ ℓ) f := minpoly_gen _ f
    rw [hgen, hdim, hmin, minpoly_PP_of_not_mem K Γ ℓ hf] at hpb
    rw [hpb, neg_one_pow_char, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_zero,
      if_neg (Ne.symm hℓ.ne_zero), zero_sub, neg_mul_neg, one_mul]

theorem frobenius_normAlong (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) (hsP : s ∉ PP K Γ ℓ) (f : FF K Γ) :
    qExpFrobeniusModL K Γ ℓ (@Algebra.norm (FF K Γ) (FF K Γ) _ _ (algebraAlong (qExpFrobeniusModL K Γ ℓ)) f) =
      f ^ ℓ := by
  have h := @Algebra.norm_eq_of_equiv_equiv (FF K Γ) (FF K Γ) (PP K Γ ℓ) (FF K Γ) _ _ _ _
    (algebraAlong (qExpFrobeniusModL K Γ ℓ)) _ (isoPP K Γ ℓ) (RingEquiv.refl _) (isoPP_compat K Γ ℓ) f
  rw [h]
  change ((isoPP K Γ ℓ) ((isoPP K Γ ℓ).symm _) : FF K Γ) = f ^ ℓ
  rw [RingEquiv.apply_symm_apply]
  exact coe_norm_PP K Γ ℓ hsep hsP f

end Norm

section Inputs

variable (K : Type*) [Field K] [IsAlgClosed K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [hC : IsCurveOver K (FF K Γ)]

scoped instance perfectRing_of_isAlgClosed : PerfectRing K ℓ :=
  haveI := IsAlgClosed.perfectField K
  PerfectField.toPerfectRing ℓ

theorem subsingleton_kaehler_of_forall_exists_pow_eq (h : ∀ y : FF K Γ, ∃ u : FF K Γ, u ^ ℓ = y) :
    Subsingleton (Ω[FF K Γ⁄K]) := by
  haveI := charP_FF K Γ ℓ
  have hD : ∀ y : FF K Γ, KaehlerDifferential.D K (FF K Γ) y = 0 := fun y => by
    obtain ⟨u, rfl⟩ := h y
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (FF K Γ), CharP.cast_eq_zero, zero_smul]
  have htop := KaehlerDifferential.span_range_derivation (R := K) (S := FF K Γ)
  have hbot : Submodule.span (FF K Γ) (Set.range (KaehlerDifferential.D K (FF K Γ))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, rfl⟩
    exact hD y
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊤ : Submodule (FF K Γ) (Ω[FF K Γ⁄K])) := Submodule.mem_top
  have hb : b ∈ (⊤ : Submodule (FF K Γ) (Ω[FF K Γ⁄K])) := Submodule.mem_top
  rw [← htop, hbot, Submodule.mem_bot] at ha hb
  rw [ha, hb]

variable {s : FF K Γ}

theorem not_mem_PP (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) : s ∉ PP K Γ ℓ := fun hs => by
  haveI := subsingleton_kaehler_of_forall_exists_pow_eq K Γ ℓ (forall_exists_pow_eq_of_mem K Γ ℓ hsep hs)
  have h1 : Module.finrank (FF K Γ) (Ω[FF K Γ⁄K]) = 1 := IsCurveOver.finrank_kaehler
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

theorem deg_eq_one (w : Place K (FF K Γ)) : w.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed w

theorem inertiaDegAlong_frobenius (w : Place K (FF K Γ)) :
    Place.inertiaDegAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) w = 1 := by
  letI := algebraAlong (qExpFrobeniusModL K Γ ℓ)
  haveI := isScalarTower_along (qExpFrobeniusModL K Γ ℓ)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)
  have h := Place.deg_restrict_mul_inertiaDeg (F := FF K Γ) w
  rw [deg_eq_one, deg_eq_one, one_mul] at h
  exact h

theorem fundamentalIdentityAlong_frobenius (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) :
    FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) := by
  letI := algebraAlong (qExpFrobeniusModL K Γ ℓ)
  haveI := isScalarTower_along (qExpFrobeniusModL K Γ ℓ)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)
  refine ⟨fun v => ?_⟩
  change ∑ w ∈ Place.fiberAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) v,
      (Place.ramificationIndexAlong (qExpFrobeniusModL K Γ ℓ) w : ℤ) * (w.deg : ℤ) =
    (finrankAlong K (qExpFrobeniusModL K Γ ℓ) : ℤ) * (v.deg : ℤ)
  rw [fiberAlong_frobenius, Finset.sum_singleton, ramificationIndexAlong_frobenius, deg_eq_one, deg_eq_one,
    finrankAlong_frobenius K Γ ℓ hsep (not_mem_PP K Γ ℓ hsep)]

theorem normFormulaAlong_frobenius (hsep : Algebra.IsSeparable K⟮s⟯ (FF K Γ)) :
    NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) (finiteAlong_frobenius K Γ ℓ hsep (not_mem_PP K Γ ℓ hsep)) := by
  classical
  letI := algebraAlong (qExpFrobeniusModL K Γ ℓ)
  haveI := isScalarTower_along (qExpFrobeniusModL K Γ ℓ)
  haveI := isIntegral_along (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)
  intro f hf D hD v
  have hℓ : ℓ.Prime := Fact.out
  set w₀ : Place K (FF K Γ) := (sigmaSL K Γ ℓ)⁻¹ • v with hw₀

  have hres : ∀ w : Place K (FF K Γ), w.restrict (FF K Γ) = v ↔ w = w₀ := fun w => by
    change w.restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) = v ↔ _
    rw [restrictAlong_frobenius_eq_smul, smul_eq_iff_eq_inv_smul]
  have hLHS : Divisor.pushforward (FF K Γ) D v = w₀.ord f := by
    rw [Divisor.pushforward_apply]
    have : ∀ w ∈ D.support, (if w.restrict (FF K Γ) = v then D w * (w.inertiaDeg (FF K Γ) : ℤ) else 0) =
        (if w₀ = w then D w else 0) := fun w _ => by
      have hf1 : w.inertiaDeg (FF K Γ) = 1 := inertiaDegAlong_frobenius K Γ ℓ w
      simp only [hres w, hf1, Nat.cast_one, mul_one, eq_comm]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs with hmem
    · exact hD w₀
    · rw [Finsupp.mem_support_iff, not_not] at hmem
      rw [← hD w₀, hmem]

  have hw₀res : w₀.restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) = v := by
    rw [restrictAlong_frobenius_eq_smul, hw₀, smul_inv_smul]
  have hRHS : (ℓ : ℤ) * v.ord (Algebra.norm (FF K Γ) f) = ℓ * w₀.ord f := by
    have h := Place.ord_restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) w₀
      (Algebra.norm (FF K Γ) f)
    rw [hw₀res, ramificationIndexAlong_frobenius, frobenius_normAlong K Γ ℓ hsep (not_mem_PP K Γ ℓ hsep),
      ← zpow_natCast, Place.ord_zpow] at h
    exact h.symm
  rw [hLHS]
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  exact (mul_left_cancel₀ hℓ0 hRHS).symm
end Inputs

theorem main (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ))) (qExpFunctionFieldC K Γ)) :
    QExpFrobeniusInputsModL K Γ ℓ ∧ finrankAlong K (qExpFrobeniusModL K Γ ℓ) = ℓ := by
  haveI := IsAlgClosed.perfectField K
  obtain ⟨x, htr, hfd⟩ := hF

  haveI : IsCurveOver K (FF K Γ) := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  obtain ⟨s, _, _, hsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField htr hfd
  have hP : HasPrincipalDivisors K (FF K Γ) := inferInstance
  have hfin := finiteAlong_frobenius K Γ ℓ hsep (not_mem_PP K Γ ℓ hsep)
  have hFI := fundamentalIdentityAlong_frobenius K Γ ℓ hsep
  have hN := normFormulaAlong_frobenius K Γ ℓ hsep
  exact ⟨qExpFrobeniusInputsModL_intro hfin hFI hN, finrankAlong_frobenius K Γ ℓ hsep (not_mem_PP K Γ ℓ hsep)⟩

end ModularCurve.QExpFrobInputsSol
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve.QExpFrobInputsSol"
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental.ModularCurve.QExpFrobInputsSol"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.QExpFrobeniusInputsModL K Γ ℓ ∧
      AlgebraicCurve.finrankAlong K (ModularCurve.qExpFrobeniusModL K Γ ℓ) = ℓ :=
  ModularCurve.QExpFrobInputsSol.main K Γ hF

end S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
end P2MW
export P2MW.S_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental (solution)
