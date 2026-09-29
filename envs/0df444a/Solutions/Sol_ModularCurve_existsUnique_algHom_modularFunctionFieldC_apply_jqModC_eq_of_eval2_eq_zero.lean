-- Prove2me | solution 1 for ModularCurve.existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e00d65d2-4034-5ce2-8d07-b8c0a7e08c56

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModularEquationQ
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData jGen jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem jqNField jqNGen ModularPolynomialData.toJqNField transcendental_jqModC transcendental_jqNModC ModularPolynomialData.eval_jqNModC_mul_eq_zero"
p2m_open "ModularCurve"

namespace UnivPropC

section Shortcuts

variable (K : Type*) [Field K]

noncomputable scoped instance (priority := high) instMulActionLaurentSeriesShortcut :
    MulAction K (LaurentSeries K) :=
  (Module.toDistribMulAction (R := K) (M := LaurentSeries K)).toMulAction

end Shortcuts

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev jAdj : IntermediateField K (LaurentSeries K) := K⟮jqModC K⟯

abbrev jGen : jAdj K := AdjoinSimple.gen K (jqModC K)

variable {N} in

abbrev ΦJ (data : ModularPolynomialData N) : Polynomial (jAdj K) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (jAdj K)) (jGen K))

theorem jqNModC_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) :
    jqNModC K m = jqNModC K n := by
  subst h
  rfl

theorem eval₂_Φ_jqModC_jqNModC (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K))
      (jqNModC K N) = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero K 1
  have hhom : (Polynomial.aeval (R := ℤ) (jqNModC K 1)).toRingHom =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    show Polynomial.aeval (jqNModC K 1) (Polynomial.X : Polynomial ℤ) = _
    rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, jqNModC_one]
  rw [hhom, jqNModC_congr K (one_mul N)] at h
  exact h

variable {N} in
theorem monic_ΦJ (data : ModularPolynomialData N) : (ΦJ K data).Monic :=
  data.monic.map _

theorem aeval_jqNModC_ΦJ (data : ModularPolynomialData N) :
    Polynomial.aeval (jqNModC K N) (ΦJ K data) = 0 := by
  have hcomp : (algebraMap (jAdj K) (LaurentSeries K)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (jAdj K)) (jGen K)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact eval₂_Φ_jqModC_jqNModC K N data

def jIso : jqNField K N ≃ₐ[K] jAdj K :=
  (RatFunc.algEquivOfTranscendental (jqNModC K N) (transcendental_jqNModC K N)).symm.trans
    (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K))

theorem jIso_gen : jIso K N (jqNGen K N) = jGen K := by
  have h1 : (RatFunc.algEquivOfTranscendental (jqNModC K N) (transcendental_jqNModC K N)).symm
      (jqNGen K N) = RatFunc.X :=
    RatFunc.algEquivOfTranscendental_symm_gen (jqNModC K N) (transcendental_jqNModC K N)
  apply Subtype.ext
  show ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K))
    ((RatFunc.algEquivOfTranscendental (jqNModC K N) (transcendental_jqNModC K N)).symm
      (jqNGen K N)) : LaurentSeries K) = jqModC K
  rw [h1]
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

theorem irreducible_ΦJ (data : ModularPolynomialData N) (hirr : Irreducible (data.toJqNField K)) :
    Irreducible (ΦJ K data) := by
  set e : jqNField K N ≃+* jAdj K := (jIso K N).toRingEquiv with he
  have hmap : (data.toJqNField K).map (e : jqNField K N →+* jAdj K) = ΦJ K data := by
    rw [ModularPolynomialData.toJqNField, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.eval₂_X]
    show (jIso K N) (jqNGen K N) = jGen K
    exact jIso_gen K N
  rw [← hmap, ← Polynomial.mapEquiv_apply, MulEquiv.irreducible_iff]
  exact hirr

theorem minpoly_eq (data : ModularPolynomialData N) (hirr : Irreducible (data.toJqNField K)) :
    minpoly (jAdj K) (jqNModC K N) = ΦJ K data :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_ΦJ K N data hirr) (aeval_jqNModC_ΦJ K N data)
    (monic_ΦJ K data)).symm

variable {K N} in

theorem ringHom_ext_gens {A : Type*} [Field A]
    {f g : modularFunctionFieldC K N →+* A}
    (h0 : ∀ k : K, f (algebraMap K (modularFunctionFieldC K N) k) =
      g (algebraMap K (modularFunctionFieldC K N) k))
    (h1 : f ⟨jqModC K, jqModC_mem K N⟩ = g ⟨jqModC K, jqModC_mem K N⟩)
    (h2 : f ⟨jqNModC K N, jqNModC_mem K N⟩ = g ⟨jqNModC K N, jqNModC_mem K N⟩) : f = g := by
  refine RingHom.ext ?_
  rintro ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact h1
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h2
  | algebraMap k => exact h0 k
  | add a b ha hb iha ihb =>
    have e : (⟨a + b, add_mem ha hb⟩ : modularFunctionFieldC K N) = ⟨a, ha⟩ + ⟨b, hb⟩ :=
      Subtype.ext (IntermediateField.coe_add (modularFunctionFieldC K N) ⟨a, ha⟩ ⟨b, hb⟩).symm
    rw [e, f.map_add, g.map_add, iha, ihb]
  | inv a ha iha =>
    have e : (⟨a⁻¹, inv_mem ha⟩ : modularFunctionFieldC K N) = (⟨a, ha⟩ : modularFunctionFieldC K N)⁻¹ :=
      Subtype.ext (IntermediateField.coe_inv (modularFunctionFieldC K N) ⟨a, ha⟩).symm
    rw [e, map_inv₀, map_inv₀, iha]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, mul_mem ha hb⟩ : modularFunctionFieldC K N) = ⟨a, ha⟩ * ⟨b, hb⟩ :=
      Subtype.ext (IntermediateField.coe_mul (modularFunctionFieldC K N) ⟨a, ha⟩ ⟨b, hb⟩).symm
    rw [e, f.map_mul, g.map_mul, iha, ihb]

variable {K N} in

theorem algHom_ext_gens {A : Type*} [Field A] [Algebra K A]
    {ψ ψ' : modularFunctionFieldC K N →ₐ[K] A}
    (h1 : ψ ⟨jqModC K, jqModC_mem K N⟩ = ψ' ⟨jqModC K, jqModC_mem K N⟩)
    (h2 : ψ ⟨jqNModC K N, jqNModC_mem K N⟩ = ψ' ⟨jqNModC K N, jqNModC_mem K N⟩) : ψ = ψ' :=
  AlgHom.coe_ringHom_injective
    (ringHom_ext_gens (f := (ψ : modularFunctionFieldC K N →+* A))
      (g := (ψ' : modularFunctionFieldC K N →+* A))
      (fun k => (ψ.commutes k).trans (ψ'.commutes k).symm) h1 h2)

section BaseHom

variable {A : Type*} [Field A] [Algebra K A]

def baseHom {c : A} (hc : Transcendental K c) : jAdj K →ₐ[K] A :=
  ((K⟮c⟯.val).comp (RatFunc.algEquivOfTranscendental c hc).toAlgHom).comp
    (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).symm.toAlgHom

theorem baseHom_jGen {c : A} (hc : Transcendental K c) : baseHom K hc (jGen K) = c := by
  have h1 : (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).symm
      (jGen K) = RatFunc.X :=
    RatFunc.algEquivOfTranscendental_symm_gen (jqModC K) (transcendental_jqModC K)
  show K⟮c⟯.val ((RatFunc.algEquivOfTranscendental c hc)
    ((RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).symm (jGen K))) = c
  rw [h1]
  exact RatFunc.algEquivOfTranscendental_X c hc

end BaseHom

theorem exists_algHom (data : ModularPolynomialData N) (hirr : Irreducible (data.toJqNField K))
    {A : Type*} [Field A] [Algebra K A] (c y : A) (hc : Transcendental K c)
    (hy : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) c).toRingHom y = 0) :
    ∃ ψ : modularFunctionFieldC K N →ₐ[K] A,
      ψ ⟨jqModC K, jqModC_mem K N⟩ = c ∧ ψ ⟨jqNModC K N, jqNModC_mem K N⟩ = y := by

  have hφ₀c : baseHom K hc (jGen K) = c := baseHom_jGen K hc
  letI : Algebra (jAdj K) A := (baseHom K hc).toRingHom.toAlgebra
  have hamap : ∀ x, algebraMap (jAdj K) A x = baseHom K hc x := fun _ => rfl
  haveI : IsScalarTower K (jAdj K) A :=
    IsScalarTower.of_algebraMap_eq fun x => ((baseHom K hc).commutes x).symm

  have hmin := minpoly_eq K N data hirr
  have hint : IsIntegral (jAdj K) (jqNModC K N) :=
    ⟨ΦJ K data, monic_ΦJ K data, by rw [← Polynomial.aeval_def]; exact aeval_jqNModC_ΦJ K N data⟩

  have hminmap : (minpoly (jAdj K) (jqNModC K N)).map (algebraMap (jAdj K) A)
      = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c) := by
    rw [hmin, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.eval₂_X, hamap]
    exact hφ₀c
  have hhomc : (Polynomial.aeval (R := ℤ) c).toRingHom =
      Polynomial.eval₂RingHom (Int.castRingHom A) c := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    show Polynomial.aeval c (Polynomial.X : Polynomial ℤ) = _
    rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hy' : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)).eval y = 0 := by
    rw [Polynomial.eval_map, ← hhomc]
    exact hy
  have hyroots : y ∈ (minpoly (jAdj K) (jqNModC K N)).aroots A := by
    rw [Polynomial.mem_aroots', Polynomial.aeval_def, ← Polynomial.eval_map, hminmap]
    exact ⟨(data.monic.map _).ne_zero, hy'⟩
  let ψ₁ : (jAdj K)⟮jqNModC K N⟯ →ₐ[jAdj K] A :=
    (algHomAdjoinIntegralEquiv (jAdj K) hint).symm ⟨y, hyroots⟩
  have hψ₁gen : ψ₁ (AdjoinSimple.gen (jAdj K) (jqNModC K N)) = y :=
    algHomAdjoinIntegralEquiv_symm_apply_gen (jAdj K) hint ⟨y, hyroots⟩
  have hadj : ((jAdj K)⟮jqNModC K N⟯).restrictScalars K = modularFunctionFieldC K N :=
    adjoin_simple_adjoin_simple K (jqModC K) (jqNModC K N)
  let ψ : modularFunctionFieldC K N →ₐ[K] A :=
    (ψ₁.restrictScalars K).comp (IntermediateField.equivOfEq hadj).symm.toAlgHom
  have hψj : ψ ⟨jqModC K, jqModC_mem K N⟩ = c := by
    have hamb : ((equivOfEq hadj).symm ⟨jqModC K, jqModC_mem K N⟩ : (jAdj K)⟮jqNModC K N⟯)
        = algebraMap (jAdj K) ((jAdj K)⟮jqNModC K N⟯) (jGen K) :=
      Subtype.ext rfl
    show ψ₁ ((equivOfEq hadj).symm ⟨jqModC K, jqModC_mem K N⟩) = c
    rw [hamb, ψ₁.commutes, hamap, hφ₀c]
  have hψjN : ψ ⟨jqNModC K N, jqNModC_mem K N⟩ = y := by
    have hamb' : ((equivOfEq hadj).symm ⟨jqNModC K N, jqNModC_mem K N⟩ : (jAdj K)⟮jqNModC K N⟯)
        = AdjoinSimple.gen (jAdj K) (jqNModC K N) :=
      Subtype.ext rfl
    show ψ₁ ((equivOfEq hadj).symm ⟨jqNModC K N, jqNModC_mem K N⟩) = y
    rw [hamb', hψ₁gen]
  exact ⟨ψ, hψj, hψjN⟩

theorem main (data : ModularPolynomialData N) (hirr : Irreducible (data.toJqNField K))
    {A : Type*} [Field A] [Algebra K A] (c y : A) (hc : Transcendental K c)
    (hy : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) c).toRingHom y = 0) :
    ∃! ψ : modularFunctionFieldC K N →ₐ[K] A,
      ψ ⟨jqModC K, jqModC_mem K N⟩ = c ∧ ψ ⟨jqNModC K N, jqNModC_mem K N⟩ = y := by
  obtain ⟨ψ, h1, h2⟩ := exists_algHom K N data hirr c y hc hy
  exact ⟨ψ, ⟨h1, h2⟩, fun ψ' h' => algHom_ext_gens (h'.1.trans h1.symm) (h'.2.trans h2.symm)⟩

end UnivPropC
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve.UnivPropC"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve.UnivPropC P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve.UnivPropC P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero.ModularCurve"

theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (data : ModularCurve.ModularPolynomialData N)
    (hirr : Irreducible (data.toJqNField K))
    {A : Type*} [Field A] [Algebra K A] (c y : A) (hc : Transcendental K c)
    (hy : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) c).toRingHom y = 0) :
    ∃! ψ : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] A,
      ψ ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ = c ∧
        ψ ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩ = y :=
  ModularCurve.UnivPropC.main K N data hirr c y hc hy

#print axioms solution

end S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero
end P2MW
export P2MW.S_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero (solution)
