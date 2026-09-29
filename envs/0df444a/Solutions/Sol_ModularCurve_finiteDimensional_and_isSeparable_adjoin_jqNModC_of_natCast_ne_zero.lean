-- Prove2me | solution 1 for ModularCurve.finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/87c81b16-9fde-54cb-8c1c-fd57fb8ed447

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_open "ModularCurve~coeffMap_injective~coeffMap_jqModC~coeffMap_jqNModC P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero.ModularCurve IntermediateField"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

noncomputable section
open HahnSeries Polynomial IntermediateField

namespace ModularCurve
p2m_export "ModularCurve" "ModularPolynomialData jqModC jqNModC jqNModC_one jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem jqNModC_mem evalAtJ_def EvalSymm swapBivar swapBivar_X swapBivar_C_X coeffMap coeffMap_coeff coeffMap_qExpand transcendental_jqNModC ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero ModularPolynomialData.evalSymm_of_one_lt swapBivar_eq_of_evalSymm"
p2m_open "ModularCurve~coeffMap_injective~coeffMap_jqModC~coeffMap_jqNModC"
namespace SepSwapGlue

section eval
variable {A B : Type*} [CommRing A] [CommRing B]

def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A := Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

theorem map_ev (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map, mapRingHom_comp,
    RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

end eval

section rel
variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

theorem ev_jq_int : ev data.Φ (jqModC ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero, jqModC_rat, jqNModC, jqModC_rat]
  have h0 := data.eval_eq_zero
  rw [evalAtJ_def, aeval_toRingHom_eq] at h0
  exact h0

theorem ev_jq (A : Type*) [CommRing A] : ev data.Φ (jqModC A) (jqNModC A N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom A)) (ev_jq_int data)
  rwa [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

end rel

section slice
variable {A B : Type*} [CommRing A] [CommRing B]

def slice (Φ : Polynomial (Polynomial ℤ)) (x : A) : Polynomial A :=
  (Φ.map (mapRingHom (Int.castRingHom A))).map (evalRingHom x)

theorem eval_slice (Φ : Polynomial (Polynomial ℤ)) (x y : A) : (slice Φ x).eval y = ev Φ x y := by
  rw [slice, map_evalRingHom_eval, ev_eq_evalEval]

theorem slice_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : A) : (slice Φ x).Monic :=
  (hΦ.map _).map _

theorem slice_natDegree [Nontrivial A] {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : A) :
    (slice Φ x).natDegree = Φ.natDegree := by
  rw [slice, (hΦ.map _).natDegree_map, hΦ.natDegree_map]

theorem slice_map (Φ : Polynomial (Polynomial ℤ)) (x : A) (φ : A →+* B) :
    (slice Φ x).map φ = slice Φ (φ x) := by
  simp only [slice, Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* B => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

end slice

section swap
variable {A : Type*} [CommRing A]

theorem ev_swapBivar (Φ : Polynomial (Polynomial ℤ)) (x y : A) : ev (swapBivar Φ) x y = ev Φ y x := by
  have h : (eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y).comp swapBivar
      = eval₂RingHom (eval₂RingHom (Int.castRingHom A) y) x := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp only [RingHom.comp_apply, swapBivar_C_X, coe_eval₂RingHom, eval₂_X, eval₂_C]
    · simp only [RingHom.comp_apply, swapBivar_X, coe_eval₂RingHom, eval₂_X, eval₂_C]
  have h' := congrArg (fun g : Polynomial (Polynomial ℤ) →+* A => g Φ) h
  simpa only [ev, RingHom.comp_apply, coe_eval₂RingHom] using h'

end swap

section bridge
variable (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

theorem slice_jqNModC_separable_of_ratFunc
    (hsep : ((data.Φ.map (mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable) :
    (slice data.Φ (jqNModC K N)).Separable := by

  have hinj : Function.Injective
      (Polynomial.aeval (R := K) (jqNModC K N)).toRingHom :=
    (transcendental_iff_injective).mp (transcendental_jqNModC K N)
  let φ' : RatFunc K →+* LaurentSeries K :=
    IsFractionRing.lift (A := Polynomial K) (g := (Polynomial.aeval (R := K) (jqNModC K N)).toRingHom) hinj
  have hφ'alg : ∀ p : Polynomial K,
      φ' (algebraMap (Polynomial K) (RatFunc K) p) = Polynomial.aeval (R := K) (jqNModC K N) p :=
    fun p => IsFractionRing.lift_algebraMap hinj p
  have heq : slice data.Φ (jqNModC K N)
      = ((data.Φ.map (mapRingHom (Int.castRingHom K))).map
          (algebraMap (Polynomial K) (RatFunc K))).map φ' := by
    simp only [slice, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    change Polynomial.eval (jqNModC K N) (Polynomial.map (Int.castRingHom (LaurentSeries K)) X)
      = φ' ((algebraMap (Polynomial K) (RatFunc K)) (Polynomial.map (Int.castRingHom K) X))
    rw [Polynomial.map_X, Polynomial.map_X, Polynomial.eval_X, hφ'alg, Polynomial.aeval_X]
  exact heq ▸ hsep.map

theorem ev_jqN_jq : ev data.Φ (jqNModC K N) (jqModC K) = 0 := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · rw [← ev_swapBivar, swapBivar_eq_of_evalSymm (ModularPolynomialData.evalSymm_of_one_lt N hN data)]
    exact ev_jq data K
  · have h1 : N = 1 := le_antisymm hN NeZero.one_le
    subst h1
    have h := ev_jq data K
    rwa [jqNModC_one] at h ⊢

end bridge

end SepSwapGlue
end ModularCurve

p2m_open "ModularCurve~coeffMap_injective~coeffMap_jqModC~coeffMap_jqNModC" in open _root_.P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero.ModularCurve ModularCurve.SepSwapGlue Polynomial in
theorem solution
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (data : ModularPolynomialData N) :
    FiniteDimensional
      (IntermediateField.adjoin K
        ({(⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) ∧
    Algebra.IsSeparable
      (IntermediateField.adjoin K
        ({(⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N)} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := by

  set E := IntermediateField.adjoin K ({jqNModC K N} : Set (LaurentSeries K)) with hEdef
  let jE : E := ⟨jqNModC K N, IntermediateField.mem_adjoin_simple_self K (jqNModC K N)⟩
  have hmap : (slice data.Φ jE).map (algebraMap E (LaurentSeries K)) = slice data.Φ (jqNModC K N) :=
    slice_map _ _ _
  have hsepE : (slice data.Φ jE).Separable :=
    (separable_map (algebraMap E (LaurentSeries K))).mp
      (hmap ▸ slice_jqNModC_separable_of_ratFunc K data
        (ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero K N data hNK))
  have h0 : Polynomial.aeval (jqModC K) (slice data.Φ jE) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap, eval_slice]
    exact ev_jqN_jq K data
  have hsepL : IsSeparable E (jqModC K) := hsepE.of_dvd (minpoly.dvd E _ h0)
  have hintL : IsIntegral E (jqModC K) := ⟨slice data.Φ jE, slice_monic data.monic jE, by
    rw [← Polynomial.aeval_def]; exact h0⟩

  set F : IntermediateField K (LaurentSeries K) := modularFunctionFieldC K N
  set x : ↥F := ⟨jqNModC K N, jqNModC_mem K N⟩
  set y : ↥F := ⟨jqModC K, jqModC_mem K N⟩
  set Kx : IntermediateField K ↥F := IntermediateField.adjoin K ({x} : Set ↥F)
  have hlift : IntermediateField.lift Kx = E := by
    show IntermediateField.lift K⟮x⟯ = K⟮jqNModC K N⟯
    rw [IntermediateField.lift_adjoin_simple]
  have hle : E ≤ F :=
    adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqNModC_mem K N))
  have hmemKx : ∀ c : ↥E, IntermediateField.inclusion hle c ∈ Kx := by
    intro c
    have hmem : ((IntermediateField.inclusion hle c : ↥F) : LaurentSeries K) ∈ lift Kx := by
      rw [hlift]; exact c.2
    rwa [IntermediateField.mem_lift] at hmem
  let φ : ↥E →ₐ[K] ↥Kx :=
    (IntermediateField.inclusion hle).codRestrict Kx.toSubalgebra hmemKx
  have hφinj : Function.Injective φ := fun a b hab =>
    (IntermediateField.inclusion hle).injective (Subtype.ext_iff.mp hab)
  have hφsurj : Function.Surjective φ := by
    intro z
    have hzL : ((z : ↥F) : LaurentSeries K) ∈ E := by
      have : ((z : ↥F) : LaurentSeries K) ∈ lift Kx := (IntermediateField.mem_lift (z : ↥F)).mpr z.2
      rwa [hlift] at this
    exact ⟨⟨_, hzL⟩, Subtype.ext (Subtype.ext rfl)⟩
  let φe : ↥E ≃+* ↥Kx := RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφecoe : ∀ c : ↥E, (((φe c : ↥Kx) : ↥F) : LaurentSeries K) = (c : LaurentSeries K) :=
    fun c => rfl
  have hcomp : (algebraMap ↥F (LaurentSeries K)).comp
        ((algebraMap ↥Kx ↥F).comp (φe : ↥E →+* ↥Kx))
      = algebraMap ↥E (LaurentSeries K) :=
    RingHom.ext hφecoe
  have hinty : IsIntegral ↥Kx y := by
    obtain ⟨p, hmonic, hroot⟩ := hintL
    refine ⟨p.map φe, hmonic.map _, ?_⟩
    apply (algebraMap ↥F (LaurentSeries K)).injective
    rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, RingHom.comp_assoc, hcomp]
    exact hroot
  have hsepy : IsSeparable ↥Kx y := by
    refine Polynomial.Separable.of_dvd (Polynomial.Separable.map hsepL (f := (φe : ↥E →+* ↥Kx))) ?_
    refine minpoly.dvd ↥Kx y ?_
    apply (algebraMap ↥F (LaurentSeries K)).injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
      RingHom.comp_assoc, hcomp]
    exact minpoly.aeval ↥E (jqModC K)
  have hgenF : IntermediateField.adjoin K ({x, y} : Set ↥F) = ⊤ := by
    rw [eq_top_iff]; intro z _
    have hliftxy : IntermediateField.lift (IntermediateField.adjoin K ({x, y} : Set ↥F))
        = IntermediateField.adjoin K ({jqModC K, jqNModC K N} : Set (LaurentSeries K)) := by
      rw [IntermediateField.lift_adjoin, Set.image_insert_eq, Set.image_singleton, Set.pair_comm]
    have hmem : ((z : ↥F) : LaurentSeries K)
        ∈ IntermediateField.lift (IntermediateField.adjoin K ({x, y} : Set ↥F)) := by
      rw [hliftxy]; exact z.2
    rwa [IntermediateField.mem_lift] at hmem
  have htop : (↥Kx)⟮y⟯ = ⊤ := by
    rw [eq_top_iff]; intro z _
    have hzxy : z ∈ IntermediateField.adjoin K ({x, y} : Set ↥F) :=
      hgenF ▸ IntermediateField.mem_top
    have hle2 : IntermediateField.adjoin K ({x, y} : Set ↥F)
        ≤ IntermediateField.restrictScalars K ((↥Kx)⟮y⟯) := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ (rfl | heq)
      · exact (IntermediateField.mem_restrictScalars _).mpr
          (IntermediateField.algebraMap_mem _ (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : ↥Kx))
      · obtain rfl := Set.mem_singleton_iff.mp heq
        exact (IntermediateField.mem_restrictScalars _).mpr
          (IntermediateField.mem_adjoin_simple_self ↥Kx y)
    exact (IntermediateField.mem_restrictScalars _).mp (hle2 hzxy)
  haveI : FiniteDimensional ↥Kx ↥((↥Kx)⟮y⟯) := IntermediateField.adjoin.finiteDimensional hinty
  haveI : Algebra.IsSeparable ↥Kx ↥((↥Kx)⟮y⟯) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).mpr hsepy
  let e : ↥((↥Kx)⟮y⟯) ≃ₐ[↥Kx] ↥F := (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  refine ⟨e.toLinearEquiv.finiteDimensional, ?_⟩
  exact Algebra.IsSeparable.of_algHom ↥Kx ↥((↥Kx)⟮y⟯) e.symm.toAlgHom

end
end S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero (solution)
