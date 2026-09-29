-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a547ed01-ddec-5fdc-a4e8-d64c8d11b981

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_of_surjective
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option quotPrecheck false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~laurentBaseChange_mono~coeffEmb_qExpand"
open scoped MatrixGroups

noncomputable section

namespace E4AV_CuspDicho

section hasValue
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem hvAdd {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hvNeg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem hvSub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hvAdd h (hvNeg h')

theorem hasValue_zero_of_ord_pos {g : F} (hg : g ≠ 0) (h : 0 < v.ord g) : v.HasValue g 0 := by
  have hmem : g ∈ v.toValuationSubring := v.mem_of_ord_nonneg hg h.le
  refine ⟨hmem, ?_⟩
  rw [map_zero]
  by_contra hne
  have hu : IsUnit (⟨g, hmem⟩ : v.toValuationSubring) := (residue_ne_zero_iff_isUnit _).mp hne
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  simp only at this
  omega

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have h0 := v.ord_nonneg_of_mem h.mem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have := (residue_ne_zero_iff_isUnit _).mpr hu
    exact this (by rw [h.residue_eq, map_zero])

end hasValue

section along
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem hasValue_map_of_hasValue_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') {g : F} {a : K} (h : (w.restrictAlong φ hφ).HasValue g a) :
    w.HasValue (φ g) a := by
  by_cases hga : g = algebraMap K F a
  · subst hga
    rw [AlgHom.commutes]
    exact w.hasValue_algebraMap a
  · have hsub : (w.restrictAlong φ hφ).HasValue (g - algebraMap K F a) 0 := by
      have := hvSub h ((w.restrictAlong φ hφ).hasValue_algebraMap a)
      rwa [sub_self] at this
    have hne : g - algebraMap K F a ≠ 0 := sub_ne_zero.mpr hga
    have hpos := ord_pos_of_hasValue_zero hsub hne
    have hne' : φ (g - algebraMap K F a) ≠ 0 := (map_ne_zero φ).mpr hne
    have hpos' : 0 < w.ord (φ (g - algebraMap K F a)) := by
      rw [Place.ord_restrictAlong φ hφ w]
      exact mul_pos (by exact_mod_cast ramificationIndexAlong_pos φ hφ w) hpos
    have h0 := hasValue_zero_of_ord_pos hne' hpos'
    have := hvAdd h0 (w.hasValue_algebraMap a)
    rwa [map_sub, AlgHom.commutes, sub_add_cancel, zero_add] at this

theorem isIntegral_of_finiteDimensional_adjoin_image (i : F →ₐ[K] F') (x : F)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({i x} : Set F')) F') :
    i.toRingHom.IsIntegral := by
  classical
  letI : Algebra F F' := i.toRingHom.toAlgebra
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  set Kt : IntermediateField K F' := IntermediateField.adjoin K ({i x} : Set F') with hKt
  have hmap : Kx.map i = Kt := by
    rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
  let e : ↥Kx ≃ₐ[K] ↥Kt := (Kx.equivMap i).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ y : ↥Kx, ((e y : ↥Kt) : F') = i (y : F) := fun y => rfl
  letI : Algebra ↥Kt F := ((algebraMap ↥Kx F).comp (e.symm : ↥Kt →ₐ[K] ↥Kx).toRingHom).toAlgebra
  haveI : IsScalarTower ↥Kt F F' := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    show (k : F') = i ((e.symm k : ↥Kx) : F)
    rw [← he, AlgEquiv.apply_symm_apply]
  haveI : Module.Finite ↥Kt F' := hfd
  haveI : Module.Finite F F' := Module.Finite.of_restrictScalars_finite ↥Kt F F'
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  intro z
  exact Algebra.IsIntegral.isIntegral z

end along

section level
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

scoped instance neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

scoped instance gammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange 𝕂 F₀ ≤ laurentBaseChange 𝕂 F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange 𝕂 (h hy)

theorem dvd_one_mul (hpM : p ∣ M) : 1 * p ∣ M := by rw [one_mul]; exact hpM

theorem level_le (hpM : p ∣ M) : modularFunctionFieldBar (1 * p) ≤ xHFunctionFieldBar M H := by
  apply laurentBaseChange_mono
  calc modularFunctionFieldFull (1 * p)
      ≤ modularFunctionFieldFull M := full_degeneracy_le (dvd_one_mul p M hpM)
    _ = modularFunctionFieldFullC ℚ M := (modularFunctionFieldFullC_rat M).symm
    _ ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M) := modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M
    _ ≤ xHFunctionField M H := x0_le_xHFunctionFieldC ℚ M H

def ι (hpM : p ∣ M) : ↥(modularFunctionFieldBar (1 * p)) →ₐ[𝕂] FM := IntermediateField.inclusion (level_le p M H hpM)

theorem coe_ι (hpM : p ∣ M) (f : ↥(modularFunctionFieldBar (1 * p))) : ((ι p M H hpM f : FM) : LaurentSeries 𝕂) = (f : LaurentSeries 𝕂) :=
  IntermediateField.coe_inclusion _ f

theorem coeffEmb_jq_eq_jqModC : coeffEmb 𝕂 jq = jqModC 𝕂 := by
  ext n
  rw [coeffEmb_coeff, ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ), jqModC_eq_map_intCast (K := 𝕂)]
  simp

theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb 𝕂 (qExpand ℚ n x) = qExpand 𝕂 n (coeffEmb 𝕂 x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coe_ι_jFun (hpM : p ∣ M) : ((ι p M H hpM (PlaceSpecialization.jFun (q := p)) : FM) : LaurentSeries 𝕂) = jqModC 𝕂 := by
  rw [coe_ι]
  show coeffEmb 𝕂 jq = jqModC 𝕂
  exact coeffEmb_jq_eq_jqModC

theorem coe_ι_jqFun (hpM : p ∣ M) : ((ι p M H hpM (PlaceSpecialization.jqFun (q := p)) : FM) : LaurentSeries 𝕂) =
    qExpand 𝕂 p (jqModC 𝕂) := by
  rw [coe_ι]
  show coeffEmb 𝕂 (qExpand ℚ (1 * p) jq) = qExpand 𝕂 p (jqModC 𝕂)
  rw [qExpand_congr (one_mul p), coeffEmb_qExpand, coeffEmb_jq_eq_jqModC]

theorem ι_isIntegral (hpM : p ∣ M) : (ι p M H hpM).toRingHom.IsIntegral := by
  have h := (transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC 𝕂
    (CohCarrier.GammaH M H) (translation_mem_GammaH M H) (ι p M H hpM (PlaceSpecialization.jFun (q := p)))
    (coe_ι_jFun p M H hpM)).2
  exact isIntegral_of_finiteDimensional_adjoin_image (ι p M H hpM) (PlaceSpecialization.jFun (q := p)) h

end level

section engine
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

private theorem _root_.E4AV_CuspDicho.isInftySide_or_isZeroSide_of_isCuspidal (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (W : Place 𝕂 FM)
    (hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) :
    JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W ∨
      JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W := by
  classical
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  set φ := ι p M H hpM with hφ_def
  have hι : φ.toRingHom.IsIntegral := ι_isIntegral p M H hpM
  have he : 0 < Place.ramificationIndexAlong φ W := ramificationIndexAlong_pos φ hι W
  set x : FM := φ (PlaceSpecialization.jFun (q := p)) with hx_def
  set x' : FM := φ (PlaceSpecialization.jqFun (q := p)) with hx'_def
  have hx : ((x : FM) : LaurentSeries 𝕂) = jqModC 𝕂 := coe_ι_jFun p M H hpM
  have hx' : ((x' : FM) : LaurentSeries 𝕂) = qExpand 𝕂 p (jqModC 𝕂) := coe_ι_jqFun p M H hpM
  have htI : φ (PlaceSpecialization.tInfty (q := p)) = x' / x ^ p := by
    simp only [PlaceSpecialization.tInfty, map_div₀, map_pow, one_mul, hx_def, hx'_def]
  have htZ : φ (PlaceSpecialization.tZero (q := p)) = x / x' ^ p := by
    simp only [PlaceSpecialization.tZero, map_div₀, map_pow, one_mul, hx_def, hx'_def]

  set W₁ : Place 𝕂 ↥(modularFunctionFieldBar (1 * p)) := W.restrictAlong φ hι with hW₁_def
  have hord : ∀ f : ↥(modularFunctionFieldBar (1 * p)),
      W.ord (φ f) = Place.ramificationIndexAlong φ W * W₁.ord f :=
    fun f => Place.ord_restrictAlong φ hι W f

  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime p
  obtain ⟨P₁⟩ := ModularCurve.placeSpecialization_exists_level_one_of_surjective p data hKr A
    (ResidueField ↥A) (IsLocalRing.residue ↥A) IsLocalRing.residue_surjective
    (ModularCurve.heckeAlphaBarIntegral_of_prime 𝕂 1 p)
    (ModularCurve.heckeBetaBarIntegral_of_prime 𝕂 1 p)
  have hW₁ : PlaceSpecialization.IsCuspidal P₁ W₁ := by
    intro a
    have h := hW x hx a
    have e := hord (PlaceSpecialization.jFun (q := p)
      - algebraMap 𝕂 ↥(modularFunctionFieldBar (1 * p)) (a : 𝕂))
    rw [map_sub, AlgHom.commutes] at e
    rw [e] at h
    exact nonpos_of_mul_nonpos_right h (by exact_mod_cast he)

  have h1 := ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal P₁ W₁ hW₁
  unfold PlaceSpecialization.IsInftySide PlaceSpecialization.IsZeroSide at h1
  rcases h1 with ⟨-, τ, hτ, hv⟩ | ⟨hc', τ, hτ, hv⟩
  · left
    refine ⟨hW, x, x', hx, hx', τ, hτ, ?_⟩
    have := hasValue_map_of_hasValue_restrictAlong φ hι W hv
    rwa [htI] at this
  · right
    refine ⟨?_, x, x', hx, hx', τ, hτ, ?_⟩
    · intro y hy a
      have hyx : y = x' := Subtype.ext (hy.trans hx'.symm)
      subst hyx
      have h := hc' a
      have e := hord (PlaceSpecialization.jqFun (q := p)
        - algebraMap 𝕂 ↥(modularFunctionFieldBar (1 * p)) (a : 𝕂))
      rw [map_sub, AlgHom.commutes] at e
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast (Nat.zero_le _)) h
    · have := hasValue_map_of_hasValue_restrictAlong φ hι W hv
      rwa [htZ] at this

p2m_export "E4AV_CuspDicho" "isInftySide_or_isZeroSide_of_isCuspidal"
end engine

end E4AV_CuspDicho
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal.E4AV_CuspDicho"

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal.E4AV_CuspDicho"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) :
    JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W ∨
      JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) W := by
  exact E4AV_CuspDicho.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA W hW

end S_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal (solution)
