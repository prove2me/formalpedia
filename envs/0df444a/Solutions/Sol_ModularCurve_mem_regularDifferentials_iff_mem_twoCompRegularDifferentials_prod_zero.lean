-- Prove2me | solution 1 for ModularCurve.mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d08dbc8f-f756-5fdc-b38d-d39bec641538

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Theorems.Thm_AlgebraicCurve_existsUnique_hasSimpleResidue_of_hasSimplePoleAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

noncomputable section

p2m_open "KaehlerDifferential AlgebraicCurve P2MW.S_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero.AlgebraicCurve ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place regularDifferentials mem_regularDifferentials_iff polarDifferentials hasSimplePoleAt_of_mem_polarDifferentials regularDifferentials_le_polarDifferentials IsGluedPolarPair gluedPolarDifferentials mem_gluedPolarDifferentials_of_isGluedPolarPair gluedPolarDifferentials_eq_span gluedPolarDifferentials.fst IsCurveOver HasCanonicalDivisor existsUnique_hasSimpleResidue_of_hasSimplePoleAt isCurveOver_of_transcendental_of_perfectField essFiniteType_of_transcendental_of_finiteDimensional hasCanonicalDivisor_of_isCurveOver"
p2m_open "AlgebraicCurve"

namespace RegCritSnd

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
  [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]

def res (v : Place K F) (ω : Ω[F⁄K]) (h : v.HasSimplePoleAt ω) : K :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).choose

theorem res_spec (v : Place K F) (ω : Ω[F⁄K]) (h : v.HasSimplePoleAt ω) :
    v.HasSimpleResidue ω (res v ω h) :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).choose_spec.1

theorem eq_res {v : Place K F} {ω : Ω[F⁄K]} (h : v.HasSimplePoleAt ω) {a : K}
    (ha : v.HasSimpleResidue ω a) : a = res v ω h :=
  (existsUnique_hasSimpleResidue_of_hasSimplePoleAt v ω h).unique ha (res_spec v ω h)

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasSimpleResidue_add {v : Place K F} {ω η : Ω[F⁄K]} {a b : K}
    (hω : v.HasSimpleResidue ω a) (hη : v.HasSimpleResidue η b) : v.HasSimpleResidue (ω + η) (a + b) := by
  obtain ⟨f, rfl, hf⟩ := hω
  obtain ⟨g, rfl, hg⟩ := hη
  refine ⟨f + g, by rw [add_smul], ?_⟩
  rw [mul_add]
  exact hasValue_add hf hg

theorem hasSimpleResidue_smul {v : Place K F} {ω : Ω[F⁄K]} {a : K} (c : K)
    (hω : v.HasSimpleResidue ω a) : v.HasSimpleResidue (c • ω) (c * a) := by
  obtain ⟨f, rfl, hf⟩ := hω
  refine ⟨algebraMap K F c * f, by rw [mul_smul, algebraMap_smul], ?_⟩
  rw [mul_left_comm]
  exact (v.hasValue_algebraMap c).mul hf

theorem hasSimpleResidue_zero (v : Place K F) : v.HasSimpleResidue (0 : Ω[F⁄K]) 0 := by
  have h := v.hasSimpleResidue_zero_of_mem (zero_mem v.toValuationSubring)
  rwa [zero_smul] at h

theorem eq_zero_of_hasSimpleResidue_zero {v : Place K F} {a : K} (h : v.HasSimpleResidue (0 : Ω[F⁄K]) a) :
    a = 0 :=
  (eq_res (v.hasSimplePoleAt_zero) h).trans (eq_res (v.hasSimplePoleAt_zero) (hasSimpleResidue_zero v)).symm

theorem isRegularAt_of_hasSimpleResidue_zero {v : Place K F} {ω : Ω[F⁄K]} (h : v.HasSimpleResidue ω 0) :
    v.IsRegularAt ω := by
  obtain ⟨f, rfl, hm, hres⟩ := h
  refine ⟨f, ?_, rfl⟩
  rw [map_zero, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp v.irreducible_mk_uniformizer,
    Ideal.mem_span_singleton'] at hres
  obtain ⟨g, hg⟩ := hres
  have hgF : (g : F) * v.uniformizer = v.uniformizer * f := by
    have := congrArg (fun x : v.toValuationSubring => (x : F)) hg
    simpa using this
  have hf : f = (g : F) := by
    have h2 : v.uniformizer * f = v.uniformizer * (g : F) := by rw [← hgF, mul_comm]
    exact mul_left_cancel₀ v.uniformizer_ne_zero h2
  rw [hf]
  exact g.2

section Admissible

variable (S : Set (Place K F × Place K F))

theorem isGluedPolarPair_zero : IsGluedPolarPair K F S 0 :=
  ⟨Submodule.zero_mem _, Submodule.zero_mem _, fun s _ a b ha hb => by
    rw [eq_zero_of_hasSimpleResidue_zero ha, eq_zero_of_hasSimpleResidue_zero hb, add_zero]⟩

variable {S}

theorem isGluedPolarPair_add {ω η : Ω[F⁄K] × Ω[F⁄K]} (hω : IsGluedPolarPair K F S ω)
    (hη : IsGluedPolarPair K F S η) : IsGluedPolarPair K F S (ω + η) := by
  obtain ⟨hω1, hω2, hωr⟩ := hω
  obtain ⟨hη1, hη2, hηr⟩ := hη
  refine ⟨Submodule.add_mem _ hω1 hη1, Submodule.add_mem _ hω2 hη2, fun s hs a b ha hb => ?_⟩

  have p1 := hasSimplePoleAt_of_mem_polarDifferentials hω1 s.1
  have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
  have q1 := hasSimplePoleAt_of_mem_polarDifferentials hη1 s.1
  have q2 := hasSimplePoleAt_of_mem_polarDifferentials hη2 s.2

  have ha' : a = res s.1 ω.1 p1 + res s.1 η.1 q1 :=
    (eq_res ha.hasSimplePoleAt ha).trans
      (eq_res ha.hasSimplePoleAt (hasSimpleResidue_add (res_spec s.1 ω.1 p1) (res_spec s.1 η.1 q1))).symm
  have hb' : b = res s.2 ω.2 p2 + res s.2 η.2 q2 :=
    (eq_res hb.hasSimplePoleAt hb).trans
      (eq_res hb.hasSimplePoleAt (hasSimpleResidue_add (res_spec s.2 ω.2 p2) (res_spec s.2 η.2 q2))).symm
  rw [ha', hb', add_add_add_comm, hωr s hs _ _ (res_spec s.1 ω.1 p1) (res_spec s.2 ω.2 p2),
    hηr s hs _ _ (res_spec s.1 η.1 q1) (res_spec s.2 η.2 q2), add_zero]

theorem isGluedPolarPair_smul (c : K) {ω : Ω[F⁄K] × Ω[F⁄K]} (hω : IsGluedPolarPair K F S ω) :
    IsGluedPolarPair K F S (c • ω) := by
  obtain ⟨hω1, hω2, hωr⟩ := hω
  refine ⟨Submodule.smul_mem _ c hω1, Submodule.smul_mem _ c hω2, fun s hs a b ha hb => ?_⟩
  have p1 := hasSimplePoleAt_of_mem_polarDifferentials hω1 s.1
  have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
  have ha' : a = c * res s.1 ω.1 p1 :=
    (eq_res ha.hasSimplePoleAt ha).trans
      (eq_res ha.hasSimplePoleAt (hasSimpleResidue_smul c (res_spec s.1 ω.1 p1))).symm
  have hb' : b = c * res s.2 ω.2 p2 :=
    (eq_res hb.hasSimplePoleAt hb).trans
      (eq_res hb.hasSimplePoleAt (hasSimpleResidue_smul c (res_spec s.2 ω.2 p2))).symm
  rw [ha', hb', ← mul_add, hωr s hs _ _ (res_spec s.1 ω.1 p1) (res_spec s.2 ω.2 p2), mul_zero]

variable (S) in

def admissiblePairs : Submodule K (Ω[F⁄K] × Ω[F⁄K]) where
  carrier := {ω | IsGluedPolarPair K F S ω}
  zero_mem' := isGluedPolarPair_zero S
  add_mem' := isGluedPolarPair_add
  smul_mem' := isGluedPolarPair_smul

variable (S) in

theorem mem_gluedPolarDifferentials_iff (ω : Ω[F⁄K] × Ω[F⁄K]) :
    ω ∈ gluedPolarDifferentials K F S ↔ IsGluedPolarPair K F S ω := by
  constructor
  · intro h
    have hle : gluedPolarDifferentials K F S ≤ admissiblePairs S := by
      rw [gluedPolarDifferentials_eq_span, Submodule.span_le]
      exact fun x hx => hx
    exact hle h
  · exact mem_gluedPolarDifferentials_of_isGluedPolarPair

end Admissible

theorem mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_fst_eq_zero
    (S : Set (Place K F × Place K F)) {ω : Ω[F⁄K] × Ω[F⁄K]} (hω : ω ∈ gluedPolarDifferentials K F S)
    (h0 : ω.1 = 0) : ω.2 ∈ regularDifferentials K F := by
  rw [mem_gluedPolarDifferentials_iff] at hω
  obtain ⟨-, hω2, hr⟩ := hω
  rw [mem_regularDifferentials_iff]
  intro v
  by_cases hv : v ∈ Prod.snd '' S
  · obtain ⟨s, hs, rfl⟩ := hv
    have p2 := hasSimplePoleAt_of_mem_polarDifferentials hω2 s.2
    have hb : res s.2 ω.2 p2 = 0 := by
      have h := hr s hs 0 (res s.2 ω.2 p2) (by rw [h0]; exact hasSimpleResidue_zero s.1) (res_spec s.2 ω.2 p2)
      rwa [zero_add] at h
    have hreg := isRegularAt_of_hasSimpleResidue_zero (hb ▸ res_spec s.2 ω.2 p2)
    obtain ⟨g, hg, hωg⟩ := hreg
    exact ⟨g, hg, hωg⟩
  · obtain ⟨g, hg, hωg⟩ := (hω2 v).1 hv
    exact ⟨g, hg, hωg⟩

theorem fst_eq_zero_iff (S : Set (Place K F × Place K F)) (ω : gluedPolarDifferentials K F S) :
    gluedPolarDifferentials.fst K F S ω = 0 ↔
      (ω : Ω[F⁄K] × Ω[F⁄K]).1 = 0 ∧ (ω : Ω[F⁄K] × Ω[F⁄K]).2 ∈ regularDifferentials K F := by
  constructor
  · intro h
    have h0 : (ω : Ω[F⁄K] × Ω[F⁄K]).1 = 0 := by
      have := congrArg (fun x : polarDifferentials K F (Prod.fst '' S) => (x : Ω[F⁄K])) h
      simpa using this
    exact ⟨h0, mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_fst_eq_zero S ω.2 h0⟩
  · rintro ⟨h0, -⟩
    exact Subtype.ext h0

theorem zero_prod_mem_gluedPolarDifferentials (S : Set (Place K F × Place K F)) {ω₂ : Ω[F⁄K]}
    (h : ω₂ ∈ regularDifferentials K F) : ((0 : Ω[F⁄K]), ω₂) ∈ gluedPolarDifferentials K F S := by
  refine mem_gluedPolarDifferentials_of_isGluedPolarPair ⟨Submodule.zero_mem _,
    regularDifferentials_le_polarDifferentials _ h, fun s hs a b ha hb => ?_⟩
  rw [eq_zero_of_hasSimpleResidue_zero ha, zero_add]
  obtain ⟨g, hg, hωg⟩ := (mem_regularDifferentials_iff.mp h) s.2
  exact (eq_res hb.hasSimplePoleAt hb).trans
    (eq_res hb.hasSimplePoleAt (hωg ▸ s.2.hasSimpleResidue_zero_of_mem hg)).symm

theorem mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_snd_eq_zero
    (S : Set (Place K F × Place K F)) {ω : Ω[F⁄K] × Ω[F⁄K]} (hω : ω ∈ gluedPolarDifferentials K F S)
    (h0 : ω.2 = 0) : ω.1 ∈ regularDifferentials K F := by
  rw [mem_gluedPolarDifferentials_iff] at hω
  obtain ⟨hω1, -, hr⟩ := hω
  rw [mem_regularDifferentials_iff]
  intro v
  by_cases hv : v ∈ Prod.fst '' S
  · obtain ⟨s, hs, rfl⟩ := hv
    have p1 := hasSimplePoleAt_of_mem_polarDifferentials hω1 s.1
    have ha : res s.1 ω.1 p1 = 0 := by
      have h := hr s hs (res s.1 ω.1 p1) 0 (res_spec s.1 ω.1 p1) (by rw [h0]; exact hasSimpleResidue_zero s.2)
      rwa [add_zero] at h
    have hreg := isRegularAt_of_hasSimpleResidue_zero (ha ▸ res_spec s.1 ω.1 p1)
    obtain ⟨g, hg, hωg⟩ := hreg
    exact ⟨g, hg, hωg⟩
  · obtain ⟨g, hg, hωg⟩ := (hω1 v).1 hv
    exact ⟨g, hg, hωg⟩

theorem prod_zero_mem_gluedPolarDifferentials (S : Set (Place K F × Place K F)) {ω₁ : Ω[F⁄K]}
    (h : ω₁ ∈ regularDifferentials K F) : (ω₁, (0 : Ω[F⁄K])) ∈ gluedPolarDifferentials K F S := by
  refine mem_gluedPolarDifferentials_of_isGluedPolarPair ⟨regularDifferentials_le_polarDifferentials _ h,
    Submodule.zero_mem _, fun s hs a b ha hb => ?_⟩
  rw [eq_zero_of_hasSimpleResidue_zero hb, add_zero]
  obtain ⟨g, hg, hωg⟩ := (mem_regularDifferentials_iff.mp h) s.1
  exact (eq_res ha.hasSimplePoleAt ha).trans
    (eq_res ha.hasSimplePoleAt (hωg ▸ s.1.hasSimpleResidue_zero_of_mem hg)).symm

end RegCritSnd

end AlgebraicCurve

end

open KaehlerDifferential _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero.AlgebraicCurve ModularCurve in

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (ω₁ : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])
    (hω₁ : ω₁ ∈ ModularCurve.ssPolarDifferentials K Γ p) :
    ω₁ ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K Γ) ↔
      (ω₁, (0 : Ω[ModularCurve.qExpFunctionFieldC K Γ⁄K])) ∈ ModularCurve.twoCompRegularDifferentials K Γ p := by
  classical
  obtain ⟨x, -, hxt, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  haveI : PerfectField K := IsAlgClosed.perfectField K
  haveI : IsCurveOver K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hxt hfd
  haveI : Algebra.EssFiniteType K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxt hfd
  haveI : HasCanonicalDivisor (K := K) (F := ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  constructor
  · intro h
    exact AlgebraicCurve.RegCritSnd.prod_zero_mem_gluedPolarDifferentials (ModularCurve.ssNodePairsQExp K Γ p) h
  · intro h
    exact AlgebraicCurve.RegCritSnd.mem_regularDifferentials_of_mem_gluedPolarDifferentials_of_snd_eq_zero
      (ModularCurve.ssNodePairsQExp K Γ p) h rfl

end S_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero
end P2MW
export P2MW.S_ModularCurve_mem_regularDifferentials_iff_mem_twoCompRegularDifferentials_prod_zero (solution)
