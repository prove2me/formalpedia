-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.end_blowupChart_eq_of_on_same_component_of_drinfeldChartWitness_linked
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1b07f4fe-23ab-57d2-8efe-558e57dc3c4a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_sub_mul_mem_or_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense
import Theorems.Thm_Subalgebra_exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_end_blowupChart_eq_of_on_same_component_of_drinfeldChartWitness_linked
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace WallAsm

theorem chart_le_and_unit {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (J y : Ideal ↥C) (hy : y.IsMaximal) (B : Subalgebra A K) (O : Subring K)
    (hO : ∃ (a : ↥C) (_ : a ∈ J) (_ : ((a : ↥C) : K) ≠ 0),
      let Ba : Subalgebra A K := (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A
      ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
        (∀ f : K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : K) = (g : K)) ∧
        (∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O, ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O)) ∧
        ¬ (∀ f : K, f ∈ B → f ∈ O)) :
    (∀ c : ↥C, ((c : ↥C) : K) ∈ O) ∧
    (∀ c : ↥C, c ∉ y → ∀ hc : ((c : ↥C) : K) ∈ O, IsUnit (⟨((c : ↥C) : K), hc⟩ : ↥O)) := by
  classical
  obtain ⟨a, ha, ha0, hrest⟩ := hO
  set Ba : Subalgebra A K := (Algebra.adjoin ↥C
        {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A with hBa
  obtain ⟨P, hP, hloc, hnu, -⟩ := hrest
  have hCBa : ∀ c : ↥C, ((c : ↥C) : K) ∈ Ba := by
    intro c
    rw [hBa, Subalgebra.mem_restrictScalars]
    exact Subalgebra.algebraMap_mem _ c
  have h1P : (1 : ↥Ba) ∉ P := (Ideal.ne_top_iff_one P).mp hP.ne_top
  have hCO : ∀ c : ↥C, ((c : ↥C) : K) ∈ O := by
    intro c
    exact (hloc _).mpr ⟨⟨_, hCBa c⟩, 1, h1P, by simp⟩
  refine ⟨hCO, ?_⟩

  have hunit : ∀ c : ↥C, (⟨((c : ↥C) : K), hCBa c⟩ : ↥Ba) ∉ P → ∀ hc : ((c : ↥C) : K) ∈ O,
      IsUnit (⟨((c : ↥C) : K), hc⟩ : ↥O) := by
    intro c hcP hc
    have hc0 : ((c : ↥C) : K) ≠ 0 := by
      intro h0; apply hcP
      have : (⟨((c : ↥C) : K), hCBa c⟩ : ↥Ba) = 0 := Subtype.ext h0
      rw [this]; exact P.zero_mem
    have hinv : ((c : ↥C) : K)⁻¹ ∈ O :=
      (hloc _).mpr ⟨1, ⟨_, hCBa c⟩, hcP, by simp [inv_mul_cancel₀ hc0]⟩
    exact ⟨⟨⟨_, hc⟩, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hc0), Subtype.ext (inv_mul_cancel₀ hc0)⟩, rfl⟩

  have hyP : ∀ b : ↥C, b ∈ y → (⟨((b : ↥C) : K), hCBa b⟩ : ↥Ba) ∈ P := by
    intro b hb
    by_contra hbP
    exact hnu b hb (hCO b) (hunit b hbP (hCO b))
  intro c hcy hc
  refine hunit c ?_ hc
  intro hcP
  obtain ⟨d, e, he, hde⟩ := hy.exists_inv hcy
  apply h1P
  have h1 : (1 : ↥Ba) = ⟨((d : ↥C) : K), hCBa d⟩ * ⟨((c : ↥C) : K), hCBa c⟩ + ⟨((e : ↥C) : K), hCBa e⟩ := by
    apply Subtype.ext
    have := congrArg (fun z : ↥C => ((z : ↥C) : K)) hde
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_one] at this
    simpa [Subalgebra.coe_add, Subalgebra.coe_mul] using this.symm
  rw [h1]
  exact P.add_mem (P.mul_mem_left _ hcP) (hyP e he)

theorem comap_eq_of_loc {C T S Loc : Type*} [CommRing C] [CommRing T] [CommRing S] [CommRing Loc]
    [Algebra C Loc] (M : Submonoid C) [IsLocalization M Loc]
    (g : C →+* T) (eh : T →+* Loc) (ei : Loc →+* T)
    (hinv : ∀ x, ei (eh x) = x) (hg : ∀ c, eh (g c) = algebraMap C Loc c)
    (Φ : T →+* S) (P P' : Ideal S) (hkey : ∀ c, Φ (g c) ∈ P ↔ Φ (g c) ∈ P') :
    Ideal.comap Φ P = Ideal.comap Φ P' := by
  have aux : ∀ Q Q' : Ideal T, (∀ c, g c ∈ Q ↔ g c ∈ Q') → Q = Q' := by
    intro Q Q' h
    have h1 : (Ideal.comap ei Q).under C = (Ideal.comap ei Q').under C := by
      ext c
      rw [Ideal.mem_under, Ideal.mem_comap, Ideal.mem_under, Ideal.mem_comap, ← hg, hinv]
      exact h c
    have h2 : Ideal.comap ei Q = Ideal.comap ei Q' := by
      rw [← IsLocalization.map_under M Loc (Ideal.comap ei Q), h1, IsLocalization.map_under M Loc]
    have h3 : ∀ Q : Ideal T, Ideal.comap eh (Ideal.comap ei Q) = Q := by
      intro Q; ext x; rw [Ideal.mem_comap, Ideal.mem_comap, hinv]
    rw [← h3 Q, ← h3 Q', h2]
  exact aux _ _ (fun c => by rw [Ideal.mem_comap, Ideal.mem_comap]; exact hkey c)

end WallAsm

namespace T5Aux

theorem isUnit_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤)
    (u x : R) (hu : IsUnit u) (h : x - u ∈ I) : IsUnit x := by
  by_contra hx
  have hxm : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hx
  have hum : u ∈ IsLocalRing.maximalIdeal R := by
    have : u = x - (x - u) := by ring
    rw [this]
    exact Ideal.sub_mem _ hxm (IsLocalRing.le_maximalIdeal hI h)
  exact (IsLocalRing.mem_maximalIdeal u).1 hum hu

theorem key {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (y 𝔭 : Ideal ↥C) (a : ↥C) (ha𝔭 : a ∉ 𝔭)
    (O : Subring K) [IsLocalRing ↥O]
    (hCO : ∀ c : ↥C, ((c : ↥C) : K) ∈ O)
    (hCu : ∀ c : ↥C, c ∉ y → ∀ hc : ((c : ↥C) : K) ∈ O, IsUnit (⟨((c : ↥C) : K), hc⟩ : ↥O))
    (hnu : ∀ b : ↥C, b ∈ y → ∀ hb : ((b : ↥C) : K) ∈ O, ¬ IsUnit (⟨((b : ↥C) : K), hb⟩ : ↥O))
    (𝔮 : Ideal ↥O) (h𝔮 : 𝔮.IsPrime)
    (hiff : ∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ O), c ∈ 𝔭 ↔ (⟨((c : ↥C) : K), hc⟩ : ↥O) ∈ 𝔮)
    (hBV : ∀ c₁ c₂ : ↥C, ∃ d s : ↥C, s ∉ y ∧ (s * c₁ - d * c₂ ∈ 𝔭 ∨ s * c₂ - d * c₁ ∈ 𝔭))
    (u : K) (hu : u ∈ O) (N : ℕ) (c : ↥C) (huc : u * ((a : ↥C) : K) ^ N = ((c : ↥C) : K)) :
    ∃ d s : ↥C, s ∉ y ∧ (⟨u, hu⟩ : ↥O) * ⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩ ∈ 𝔮 := by
  classical
  have haq : (⟨((a : ↥C) : K), hCO a⟩ : ↥O) ∉ 𝔮 := fun h => ha𝔭 ((hiff a (hCO a)).2 h)
  have haNq : (⟨((a : ↥C) : K), hCO a⟩ : ↥O) ^ N ∉ 𝔮 := fun h => haq (h𝔮.mem_of_pow_mem N h)
  obtain ⟨d, s, hs, hds⟩ := hBV c (a ^ N)
  rcases hds with h1 | h2
  ·
    refine ⟨d, s, hs, ?_⟩
    have hm : (⟨((s * c - d * a ^ N : ↥C) : K), hCO _⟩ : ↥O) ∈ 𝔮 := (hiff _ (hCO _)).1 h1
    have heq : (⟨((s * c - d * a ^ N : ↥C) : K), hCO _⟩ : ↥O) =
        ⟨((a : ↥C) : K), hCO a⟩ ^ N * ((⟨u, hu⟩ : ↥O) * ⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩) := by
      apply Subtype.ext
      push_cast
      rw [← huc]; ring
    rw [heq] at hm
    rcases h𝔮.mem_or_mem hm with h | h
    · exact absurd h haNq
    · exact h
  ·
    have hm : (⟨((s * a ^ N - d * c : ↥C) : K), hCO _⟩ : ↥O) ∈ 𝔮 := (hiff _ (hCO _)).1 h2
    have heq : (⟨((s * a ^ N - d * c : ↥C) : K), hCO _⟩ : ↥O) =
        ⟨((a : ↥C) : K), hCO a⟩ ^ N * (⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O)) := by
      apply Subtype.ext
      push_cast
      rw [← huc]; ring
    rw [heq] at hm
    have hm' : (⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O)) ∈ 𝔮 := by
      rcases h𝔮.mem_or_mem hm with h | h
      · exact absurd h haNq
      · exact h
    have hdu : IsUnit (⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O)) := by
      apply isUnit_of_sub_mem 𝔮 h𝔮.ne_top _ _ (hCu s hs (hCO s))
      have : ⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O) - ⟨((s : ↥C) : K), hCO s⟩ =
          -(⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O)) := by ring
      rw [this]; exact 𝔮.neg_mem hm'
    have hd : d ∉ y := fun hdy => hnu d hdy (hCO d) (isUnit_of_mul_isUnit_left hdu)
    refine ⟨s, d, hd, ?_⟩
    have : (⟨u, hu⟩ : ↥O) * ⟨((d : ↥C) : K), hCO d⟩ - ⟨((s : ↥C) : K), hCO s⟩ =
        -(⟨((s : ↥C) : K), hCO s⟩ - ⟨((d : ↥C) : K), hCO d⟩ * (⟨u, hu⟩ : ↥O)) := by ring
    rw [this]; exact 𝔮.neg_mem hm'

theorem exists_pow_mul_mem {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (J : Ideal ↥C) (a : ↥C) (x : K)
    (hx : x ∈ Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}) :
    ∃ (N : ℕ) (c : ↥C), x * ((a : ↥C) : K) ^ N = ((c : ↥C) : K) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨1, i, by rw [pow_one, hxi]⟩
  | algebraMap c => exact ⟨0, c, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, c, hc⟩ := hx
    obtain ⟨M, d, hd⟩ := hy
    refine ⟨N + M, c * a ^ M + d * a ^ N, ?_⟩
    push_cast
    rw [← hc, ← hd]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨N, c, hc⟩ := hx
    obtain ⟨M, d, hd⟩ := hy
    refine ⟨N + M, c * d, ?_⟩
    push_cast
    rw [pow_add, ← hc, ← hd]; ring

end T5Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → γ ∈ CongruenceSubgroup.Gamma ℓ →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (γ ∈ CongruenceSubgroup.Gamma ℓ → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
                (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W))
    :
      (∀ O O' : Subring ↥K, (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O)) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O)) → (∃ (a : ↥(chartAlgFin A (↥K) j)) (_ : a ∈ J) (_ : ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) ≠ 0),
          let Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
            {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A
          ∃ (P : Ideal ↥Ba) (_ : P.IsMaximal),
            (∀ f : ↥K, f ∈ O' ↔ ∃ g h : ↥Ba, h ∉ P ∧ f * (h : ↥K) = (g : ↥K)) ∧
            (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y →
              ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', ¬ IsUnit (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O')) ∧
            ¬ (∀ f : ↥K, f ∈ B → f ∈ O')) →
        ∀ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j), (𝔭.IsPrime ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ 𝔭 ∧ 𝔭 ≤ y ∧ 𝔭 ≠ y) → (∃ 𝔮 : Ideal ↥O, 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O, (⟨algebraMap A ↥K ϖ, h⟩ : ↥O) ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O, (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O) ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O) ∈ 𝔮)) → (∃ 𝔮 : Ideal ↥O', 𝔮.IsPrime ∧
            (∀ h : algebraMap A ↥K ϖ ∈ O', (⟨algebraMap A ↥K ϖ, h⟩ : ↥O') ∈ 𝔮) ∧
            (∃ b : ↥(chartAlgFin A (↥K) j), b ∈ y ∧ ∀ hb : ((b : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O', (⟨((b : ↥(chartAlgFin A (↥K) j)) : ↥K), hb⟩ : ↥O') ∉ 𝔮) ∧
            (∀ (c : ↥(chartAlgFin A (↥K) j)) (hc : ((c : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ O'),
              c ∈ 𝔭 ↔ (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hc⟩ : ↥O') ∈ 𝔮)) → O = O') := by
  classical
  intro O O' hO hO' 𝔭 h𝔭 hon hon'
  have hOpin := hO
  have hO'pin := hO'
  obtain ⟨h𝔭p, hϖ𝔭, h𝔭y, h𝔭ne⟩ := h𝔭
  have hBV := ModularCurve.FullLevel.AuxLevel.exists_sub_mul_mem_or_of_isPrime_lt_supersingular_of_drinfeldChartWitness_linked q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ 𝔭 h𝔭p hϖ𝔭 h𝔭y h𝔭ne

  let STK : Type := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
  let CMP : Type := (AdicCompletion (IsLocalRing.maximalIdeal STK) STK)
  let S : Type := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
  let mkS : MvPowerSeries (Fin 2) W₁ →+* S := (Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁}))
  let toC : STK →+* CMP := algebraMap _ _
  let germY : ↥(chartAlgFin A (↥K) j) →+* STK := (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom))
  let Ψ : ↥(chartAlgFin A (↥K) j) →+* S := ((e₁ : CMP →+* S).comp (toC.comp germY))

  obtain ⟨PS, hPSp, hPSne, hPSϖ, hPSiff⟩ :=
    ModularCurve.FullLevel.AuxLevel.exists_isPrime_forall_mem_iff_germ_mem_comap_of_le_of_ne_of_drinfeldChartWitness q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ 𝔭 h𝔭p hϖ𝔭 h𝔭y h𝔭ne
  obtain ⟨hK1i, -, -⟩ :=
    ModularCurve.FullLevel.AuxLevel.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK2 := ModularCurve.FullLevel.AuxLevel.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁.1
  have hK2c := hK2
  obtain ⟨hcen, hdense, -, hres, -, hcomapσ, hSmax1, hSmax2, -⟩ := hK2c
  have hK3 := ModularCurve.FullLevel.AuxLevel.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hcen hdense hres ⟨hSmax1, hSmax2⟩

  obtain ⟨hCO, hCu⟩ := WallAsm.chart_le_and_unit (chartAlgFin A (↥K) j) J y hy B O hO
  obtain ⟨hCO', hCu'⟩ := WallAsm.chart_le_and_unit (chartAlgFin A (↥K) j) J y hy B O' hO'
  obtain ⟨a, haJ, ha0, hrest⟩ := hO
  set Ba : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A with hBa
  obtain ⟨P, hP, hloc, hnu, hnB⟩ := hrest
  obtain ⟨a', haJ', ha0', hrest'⟩ := hO'
  set Ba' : Subalgebra A ↥K := (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * ((a' : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A with hBa'
  obtain ⟨P', hP', hloc', hnu', hnB'⟩ := hrest'
  obtain ⟨hRO, eqv, heqv, hLR, hmO, hmP, -, -⟩ :=
    Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq Ba P hP O hloc
  obtain ⟨hRO', eqv', heqv', hLR', hmO', hmP', -, -⟩ :=
    Subalgebra.exists_ringEquiv_localizationAtPrime_of_forall_mem_iff_exists_mul_eq Ba' P' hP' O' hloc'
  haveI := hLR
  haveI := hLR'
  obtain ⟨𝔮, h𝔮p, hϖ𝔮, -, hiff⟩ := hon
  obtain ⟨𝔮', h𝔮p', hϖ𝔮', -, hiff'⟩ := hon'
  set aK : ↥K := ((a : ↥(chartAlgFin A (↥K) j)) : ↥K) with haK
  set aK' : ↥K := ((a' : ↥(chartAlgFin A (↥K) j)) : ↥K) with haK'
  have hCBa : ∀ c : ↥(chartAlgFin A (↥K) j), (c : ↥K) ∈ Ba := by
    intro c; rw [hBa, Subalgebra.mem_restrictScalars]; exact Subalgebra.algebraMap_mem _ c
  have hCBa' : ∀ c : ↥(chartAlgFin A (↥K) j), (c : ↥K) ∈ Ba' := by
    intro c; rw [hBa', Subalgebra.mem_restrictScalars]; exact Subalgebra.algebraMap_mem _ c
  have hgen : ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J → ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ ∈ Ba := by
    intro i hi; rw [hBa, Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨i, hi, by rw [haK, mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
  have hgen' : ∀ i : ↥(chartAlgFin A (↥K) j), i ∈ J → ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK'⁻¹ ∈ Ba' := by
    intro i hi; rw [hBa', Subalgebra.mem_restrictScalars]
    exact Algebra.subset_adjoin ⟨i, hi, by rw [haK', mul_assoc, inv_mul_cancel₀ ha0', mul_one]⟩

  have hJ𝔭 : ¬ (J ≤ 𝔭) := by
    intro hJle
    have hle : Ideal.map Ψ J ≤ PS := by
      rw [Ideal.map_le_iff_le_comap]
      intro c hc
      have := (hPSiff c).1 (hJle hc)
      rw [Ideal.mem_comap] at this
      rw [Ideal.mem_comap]
      exact this
    have hmap : Ideal.map Ψ J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} :=
      hK3.1
    have hX0 : mkS (MvPowerSeries.X 0) ∈ PS := hle (hmap ▸ Ideal.subset_span (by simp))
    have hX1 : mkS (MvPowerSeries.X 1) ∈ PS := hle (hmap ▸ Ideal.subset_span (by simp))
    rcases hPSne with h0 | h1
    · exact h0 hX0
    · exact h1 hX1
  have ha𝔭 : a ∉ 𝔭 := by
    intro ha
    apply hJ𝔭
    intro i hi
    have h1 : (⟨aK, hCO a⟩ : ↥O) ∈ 𝔮 := (hiff a (hCO a)).1 ha
    have h2 : (⟨((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO i⟩ : ↥O) = ⟨_, hRO ⟨_, hgen i hi⟩⟩ * ⟨aK, hCO a⟩ := by
      apply Subtype.ext
      show ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK⁻¹ * aK
      rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    exact (hiff i (hCO i)).2 (h2 ▸ 𝔮.mul_mem_left _ h1)
  have ha𝔭' : a' ∉ 𝔭 := by
    intro ha
    apply hJ𝔭
    intro i hi
    have h1 : (⟨aK', hCO' a'⟩ : ↥O') ∈ 𝔮' := (hiff' a' (hCO' a')).1 ha
    have h2 : (⟨((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' i⟩ : ↥O') = ⟨_, hRO' ⟨_, hgen' i hi⟩⟩ * ⟨aK', hCO' a'⟩ := by
      apply Subtype.ext
      show ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK'⁻¹ * aK'
      rw [mul_assoc, inv_mul_cancel₀ ha0', mul_one]
    exact (hiff' i (hCO' i)).2 (h2 ▸ 𝔮'.mul_mem_left _ h1)

  have hu1 : aK' * aK⁻¹ ∈ Ba := hgen a' haJ'
  have hu2 : aK * aK'⁻¹ ∈ Ba' := hgen' a haJ
  obtain ⟨d, s, hs, hds⟩ := T5Aux.key (chartAlgFin A (↥K) j) y 𝔭 a ha𝔭 O hCO hCu hnu 𝔮 h𝔮p hiff hBV
    (aK' * aK⁻¹) (hRO ⟨_, hu1⟩) 1 a' (by rw [pow_one, ← haK, mul_assoc, inv_mul_cancel₀ ha0, mul_one, haK'])
  obtain ⟨d', s', hs', hds'⟩ := T5Aux.key (chartAlgFin A (↥K) j) y 𝔭 a' ha𝔭' O' hCO' hCu' hnu' 𝔮' h𝔮p' hiff' hBV
    (aK * aK'⁻¹) (hRO' ⟨_, hu2⟩) 1 a (by rw [pow_one, ← haK', mul_assoc, inv_mul_cancel₀ ha0', mul_one, haK])
  have R1 : s * a' - d * a ∈ 𝔭 := by
    apply (hiff _ (hCO _)).2
    have : (⟨((s * a' - d * a : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO _⟩ : ↥O) =
        ⟨aK, hCO a⟩ * ((⟨aK' * aK⁻¹, hRO ⟨_, hu1⟩⟩ : ↥O) * ⟨((s : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO s⟩ - ⟨((d : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO d⟩) := by
      apply Subtype.ext
      push_cast
      rw [← haK, ← haK']
      field_simp
    rw [this]; exact 𝔮.mul_mem_left _ hds
  have R2 : s' * a - d' * a' ∈ 𝔭 := by
    apply (hiff' _ (hCO' _)).2
    have : (⟨((s' * a - d' * a' : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' _⟩ : ↥O') =
        ⟨aK', hCO' a'⟩ * ((⟨aK * aK'⁻¹, hRO' ⟨_, hu2⟩⟩ : ↥O') * ⟨((s' : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' s'⟩ - ⟨((d' : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' d'⟩) := by
      apply Subtype.ext
      push_cast
      rw [← haK, ← haK']
      field_simp
    rw [this]; exact 𝔮'.mul_mem_left _ hds'
  have hdd' : d * d' ∉ y := by
    intro hdd
    have hprod : (s * s' - d * d') * (a * a') ∈ 𝔭 := by
      have : (s * s' - d * d') * (a * a') = (s * a') * (s' * a - d' * a') + (d' * a') * (s * a' - d * a) := by ring
      rw [this]; exact 𝔭.add_mem (𝔭.mul_mem_left _ R2) (𝔭.mul_mem_left _ R1)
    rcases h𝔭p.mem_or_mem hprod with h | h
    · have hss' : s * s' ∈ y := by
        have := y.add_mem (h𝔭y h) hdd
        simpa using this
      exact (hy.isPrime.mem_or_mem hss').elim hs hs'
    · exact (h𝔭p.mem_or_mem h).elim ha𝔭 ha𝔭'
  have hd' : d' ∉ y := fun h => hdd' (y.mul_mem_left _ h)
  have hu2unit : IsUnit (⟨aK * aK'⁻¹, hRO' ⟨_, hu2⟩⟩ : ↥O') :=
    isUnit_of_mul_isUnit_left (T5Aux.isUnit_of_sub_mem 𝔮' h𝔮p'.ne_top _ _ (hCu' d' hd' (hCO' d')) hds')
  have hinvO' : aK' * aK⁻¹ ∈ O' := by
    obtain ⟨w, hw⟩ := hu2unit.exists_right_inv
    have h1 : (aK * aK'⁻¹) * (w : ↥K) = 1 := by
      have := congrArg (fun z : ↥O' => (z : ↥K)) hw
      simpa using this
    have h2 : (w : ↥K) = aK' * aK⁻¹ := by
      have h3 := inv_eq_of_mul_eq_one_right h1
      rw [← h3, mul_inv, inv_inv, mul_comm]
    rw [← h2]; exact w.2

  have hBaO' : ∀ x : ↥K, x ∈ Ba → x ∈ O' := by
    intro x hx
    rw [hBa, Subalgebra.mem_restrictScalars] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      have : x = (((i : ↥(chartAlgFin A (↥K) j)) : ↥K) * aK'⁻¹) * (aK' * aK⁻¹) := by
        rw [← hxi]; field_simp
      rw [this]
      exact O'.mul_mem (hRO' ⟨_, hgen' i hi⟩) hinvO'
    | algebraMap c => exact hCO' c
    | add x y _ _ hx hy => exact O'.add_mem hx hy
    | mul x y _ _ hx hy => exact O'.mul_mem hx hy

  have hqq' : ∀ (x : ↥K) (hx : x ∈ Ba), (⟨x, hRO ⟨x, hx⟩⟩ : ↥O) ∈ 𝔮 → (⟨x, hBaO' x hx⟩ : ↥O') ∈ 𝔮' := by
    intro x hx hxq
    obtain ⟨N, c, hc⟩ := T5Aux.exists_pow_mul_mem (chartAlgFin A (↥K) j) J a x
      (by rw [hBa, Subalgebra.mem_restrictScalars] at hx; exact hx)
    have hcq : (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO c⟩ : ↥O) ∈ 𝔮 := by
      have : (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO c⟩ : ↥O) = ⟨x, hRO ⟨x, hx⟩⟩ * ⟨aK, hCO a⟩ ^ N := by
        apply Subtype.ext; push_cast; rw [← hc, haK]
      rw [this]; exact 𝔮.mul_mem_right _ hxq
    have hc𝔭 : c ∈ 𝔭 := (hiff c (hCO c)).2 hcq
    have hcq' : (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' c⟩ : ↥O') ∈ 𝔮' := (hiff' c (hCO' c)).1 hc𝔭
    have : (⟨((c : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' c⟩ : ↥O') = ⟨x, hBaO' x hx⟩ * ⟨aK, hCO' a⟩ ^ N := by
      apply Subtype.ext; push_cast; rw [← hc, haK]
    rw [this] at hcq'
    rcases h𝔮p'.mem_or_mem hcq' with h | h
    · exact h
    · exact absurd ((hiff' a (hCO' a)).2 (h𝔮p'.mem_of_pow_mem N h)) ha𝔭

  have hunit' : ∀ (h : ↥Ba), h ∉ P → IsUnit (⟨(h : ↥K), hBaO' h h.2⟩ : ↥O') := by
    intro h hhP
    have hhu : IsUnit (⟨(h : ↥K), hRO h⟩ : ↥O) := by
      have h1 : (⟨(h : ↥K), hRO h⟩ : ↥O) ∉ IsLocalRing.maximalIdeal ↥O := fun hm => hhP ((hmP h).1 hm)
      exact not_not.1 ((IsLocalRing.mem_maximalIdeal _).not.1 h1)
    obtain ⟨N, c, hc⟩ := T5Aux.exists_pow_mul_mem (chartAlgFin A (↥K) j) J a (h : ↥K)
      h.2
    obtain ⟨d₁, s₁, hs₁, hds₁⟩ := T5Aux.key (chartAlgFin A (↥K) j) y 𝔭 a ha𝔭 O hCO hCu hnu 𝔮 h𝔮p hiff hBV
      (h : ↥K) (hRO h) N c hc
    have hdunit : IsUnit (⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO d₁⟩ : ↥O) := by
      apply T5Aux.isUnit_of_sub_mem 𝔮 h𝔮p.ne_top _ _ (hhu.mul (hCu s₁ hs₁ (hCO s₁)))
      have : (⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO d₁⟩ : ↥O) - ⟨(h : ↥K), hRO h⟩ * ⟨((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO s₁⟩ =
          -((⟨(h : ↥K), hRO h⟩ : ↥O) * ⟨((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO s₁⟩ - ⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO d₁⟩) := by ring
      rw [this]; exact 𝔮.neg_mem hds₁
    have hd₁ : d₁ ∉ y := fun hdy => hnu d₁ hdy (hCO d₁) hdunit
    have hmemBa : (h : ↥K) * ((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K) - ((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ Ba :=
      Ba.sub_mem (Ba.mul_mem h.2 (hCBa s₁)) (hCBa d₁)
    have hq1 : (⟨(h : ↥K) * ((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K) - ((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hRO ⟨_, hmemBa⟩⟩ : ↥O) ∈ 𝔮 := by
      have : (⟨(h : ↥K) * ((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K) - ((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hRO ⟨_, hmemBa⟩⟩ : ↥O) =
          (⟨(h : ↥K), hRO h⟩ : ↥O) * ⟨((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO s₁⟩ - ⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO d₁⟩ := Subtype.ext rfl
      rw [this]; exact hds₁
    have hq2 := hqq' _ hmemBa hq1
    have hq3 : (⟨(h : ↥K), hBaO' h h.2⟩ : ↥O') * ⟨((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' s₁⟩ - ⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' d₁⟩ ∈ 𝔮' := by
      have : (⟨(h : ↥K), hBaO' h h.2⟩ : ↥O') * ⟨((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' s₁⟩ - ⟨((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hCO' d₁⟩ =
          ⟨(h : ↥K) * ((s₁ : ↥(chartAlgFin A (↥K) j)) : ↥K) - ((d₁ : ↥(chartAlgFin A (↥K) j)) : ↥K), hBaO' _ hmemBa⟩ := Subtype.ext rfl
      rw [this]; exact hq2
    exact isUnit_of_mul_isUnit_left (T5Aux.isUnit_of_sub_mem 𝔮' h𝔮p'.ne_top _ _ (hCu' d₁ hd₁ (hCO' d₁)) hq3)

  have hsub : ∀ f : ↥K, f ∈ O → f ∈ O' := by
    intro f hf
    obtain ⟨g, h, hhP, hfh⟩ := (hloc f).1 hf
    have hh0 : (h : ↥K) ≠ 0 := by
      intro h0; apply hhP
      have : h = 0 := Subtype.ext h0
      rw [this]; exact P.zero_mem
    obtain ⟨w, hw⟩ := (hunit' h hhP).exists_right_inv
    have hw1 : (h : ↥K) * (w : ↥K) = 1 := by
      have := congrArg (fun z : ↥O' => (z : ↥K)) hw
      simpa using this
    have hw2 : (w : ↥K) = ((h : ↥K))⁻¹ := (inv_eq_of_mul_eq_one_right hw1).symm
    have : f = (g : ↥K) * ((h : ↥K))⁻¹ := by
      rw [← hfh, mul_assoc, mul_inv_cancel₀ hh0, mul_one]
    rw [this, ← hw2]
    exact O'.mul_mem (hBaO' _ g.2) w.2
  exact (ModularCurve.FullLevel.AuxLevel.eq_of_forall_mem_of_isEnd_blowupChart_of_drinfeldChartWitness_linked q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss hArig z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB W hBW hR1 hR2 hR3 hEQ O' O hO'pin hOpin hsub).symm

end S_ModularCurve_FullLevel_AuxLevel_end_blowupChart_eq_of_on_same_component_of_drinfeldChartWitness_linked
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_end_blowupChart_eq_of_on_same_component_of_drinfeldChartWitness_linked (solution)
