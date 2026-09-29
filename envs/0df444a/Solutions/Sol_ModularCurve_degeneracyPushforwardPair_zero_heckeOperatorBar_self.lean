-- Prove2me | solution 1 for ModularCurve.degeneracyPushforwardPair_zero_heckeOperatorBar_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/59cbab27-261f-5643-aee9-e25065c63d45

import Mathlib
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeNamedInputs
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_heckeDiagonalIdentity_of_prime_of_not_dvd
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_full_eq_adjoin_full_div_prime
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_jqN_prime_not_mem_full
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_PhiGen_splits_prime_at_slot
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

section WPart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "ModularCurve~coeffEmb_qExpand P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ModularCurve ModularCurve.PhiGen IntermediateField Polynomial"

private scoped instance ALGenSol.instIsScalarTowerRat {L : Type*} [Field L] [Algebra ℚ L]
    (F : IntermediateField ℚ L) : IsScalarTower ℚ F L :=
  IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)

p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"
namespace ALGenSol

private theorem map_eval₂_aeval {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B)
    (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    f (Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (f x)).toRingHom (f y) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

private theorem rel_push {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B)
    (Φ : Polynomial (Polynomial ℤ)) (x y : A) (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) (f x)).toRingHom (f y) = 0 := by
  rw [← map_eval₂_aeval, h, map_zero]

private theorem jqN_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) : jqN M = jqN K := by subst h; rfl

private theorem full_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) :
    modularFunctionFieldFull M = modularFunctionFieldFull K := by subst h; rfl

section Pin

variable (q : ℕ) [hq : Fact q.Prime]
variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem coeffEmb_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb K (qExpand ℚ n x) = qExpand K n (coeffEmb K x) :=
  coeffMap_qExpand (algebraMap ℚ K) n x

private theorem coeff_twist_neg (e : ℕ) [NeZero e] (u : Kˣ) :
    (qExpand K e (qTwist u (coeffEmb K jq))).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := qExpand_coeff_mul (R := K) (N := e) (qTwist u (coeffEmb K jq)) (-1)
  rw [mul_neg_one] at h
  rw [h, qTwist_coeff, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_one, zpow_neg_one]

omit [Algebra ℚ K] in
private theorem coeff_spread_neg_eq_zero (e m : ℕ) [NeZero e] [NeZero m] (hm : 2 ≤ m) (f : LaurentSeries K) :
    (qExpand K (m * e) f).coeff (-(e : ℤ)) = 0 := by
  refine qExpand_coeff_of_not_dvd (R := K) (N := m * e) f ?_
  intro hd
  have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  have h1 : ((m * e : ℕ) : ℤ) ∣ (e : ℤ) := (dvd_neg.mp hd)
  have h2 : ((m * e : ℕ) : ℤ) ≤ (e : ℤ) := Int.le_of_dvd he h1
  have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
  push_cast at h2
  nlinarith

private theorem root_eq_jqNp_of_isPrimitiveRoot (dq : ModularPolynomialData q) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (z : LaurentSeries ℚ) (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom z = 0) : z = jqN q := by
  set ι : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ q) with hι
  have hιinj : Function.Injective ι := (coeffEmb K).injective.comp (qExpand_injective (R := ℚ) q)
  have ι_jq : ι jq = qExpand K (q * 1) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq)) := by
    rw [one_pow, qTwist_one_apply, hι, RingHom.comp_apply, coeffEmb_qExpand]
    exact qExpand_congr (Nat.mul_one q).symm _
  have ι_jqNq : ι (jqN q) = qExpand K (q * (q * 1)) (qTwist ((1 : Kˣ) ^ (q * q)) (coeffEmb K jq)) := by
    rw [one_pow, qTwist_one_apply, hι, RingHom.comp_apply, jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  have hA' : (dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (q * 1) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq))))).eval (ι z) = 0 := by
    have h' := rel_push ι dq.Φ jq z hA
    rw [ι_jq] at h'
    rw [Polynomial.eval_map]
    convert h' using 2 <;> try rfl
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [splits_prime_at_slot q ζ hζ q dvd_rfl dq 1 1, Polynomial.eval_mul, Polynomial.eval_prod] at hA'
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_range, sub_eq_zero] at hA'
  rcases hA' with hz | ⟨b, -, hz⟩
  · apply hιinj
    rw [hz, ι_jqNq]
  · exfalso
    have h := congrArg (fun y : LaurentSeries K => y.coeff (-((1 : ℕ) : ℤ))) hz
    beta_reduce at h
    rw [coeff_twist_neg 1] at h
    have h0 : (ι z).coeff (-((1 : ℕ) : ℤ)) = 0 := by
      rw [hι, RingHom.comp_apply, coeffEmb_qExpand, qExpand_congr (Nat.mul_one q).symm (coeffEmb K z)]
      exact coeff_spread_neg_eq_zero 1 q hq.out.two_le _
    rw [h0] at h
    exact (Units.ne_zero _) h.symm

end Pin
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

private theorem root_eq_jqNp (q : ℕ) [hq : Fact q.Prime] (dq : ModularPolynomialData q) (z : LaurentSeries ℚ)
    (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom z = 0) : z = jqN q := by
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne q)⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  obtain ⟨ζ0, hζ0⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField q ℚ)
    (Set.mem_singleton q) (NeZero.ne q)
  have hζ : IsPrimitiveRoot (((hζ0.isUnit (NeZero.ne q)).unit : (CyclotomicField q ℚ)ˣ) : CyclotomicField q ℚ) q := by
    rw [IsUnit.unit_spec]; exact hζ0
  exact root_eq_jqNp_of_isPrimitiveRoot q dq _ hζ z hA

variable (N₀ p : ℕ) [NeZero N₀] [hp : Fact p.Prime]

private abbrev KN : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull N₀

private theorem jqNd_mem_K {d : ℕ} [NeZero d] (hd : d ∣ N₀) : jqN d ∈ KN N₀ := jqd_mem_full N₀ hd

private theorem jq_mem_K : jq ∈ KN N₀ := by simpa [qExpand_one_apply] using jqd_mem_full N₀ (one_dvd N₀)

private theorem jqNp_not_mem_K (hpN₀ : ¬ p ∣ N₀) : jqN p ∉ KN N₀ := by
  refine jqN_prime_not_mem_full N₀ p hpN₀ (fun d hd _ => ?_)
  haveI : NeZero d := ⟨fun h => NeZero.ne N₀ (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  exact ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩

private abbrev MNp : IntermediateField (KN N₀) (LaurentSeries ℚ) :=
  IntermediateField.adjoin (KN N₀) ({jqN p} : Set (LaurentSeries ℚ))

private theorem finrank_MNp (hpN₀ : ¬ p ∣ N₀) : Module.finrank (KN N₀) (MNp N₀ p) = p + 1 :=
  finrank_adjoin_jqN_prime_of_not_mem (KN N₀) (jq_mem_K N₀) p (jqNp_not_mem_K N₀ p hpN₀)

private theorem full_mul_eq (hpN₀ : ¬ p ∣ N₀) :
    modularFunctionFieldFull (N₀ * p)
      = IntermediateField.adjoin ℚ (insert (jqN p) (KN N₀ : Set (LaurentSeries ℚ))) := by
  have h := full_eq_adjoin_full_div_prime N₀ p 0 hpN₀
  have e1 : N₀ * p ^ (0 + 1) = N₀ * p := by rw [zero_add, pow_one]
  have e2 : p ^ (0 + 1) = p := by rw [zero_add, pow_one]
  have e3 : N₀ * p ^ 0 = N₀ := by rw [pow_zero, mul_one]
  rw [full_congr e1, jqN_congr e2, full_congr e3] at h
  exact h

private theorem KN_le_full :
    KN N₀ ≤ IntermediateField.adjoin ℚ (insert (jqN p) (KN N₀ : Set (LaurentSeries ℚ))) :=
  fun _ hx => subset_adjoin ℚ _ (Set.mem_insert_of_mem _ hx)

private theorem MNp_restrictScalars (hpN₀ : ¬ p ∣ N₀) :
    (MNp N₀ p).restrictScalars ℚ = modularFunctionFieldFull (N₀ * p) := by
  rw [full_mul_eq N₀ p hpN₀]
  refine le_antisymm ?_ ?_
  · have h1 : MNp N₀ p ≤ extendScalars (KN_le_full N₀ p) :=
      adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        ((mem_extendScalars _).mpr (subset_adjoin ℚ _ (Set.mem_insert _ _))))
    intro x hx
    exact (mem_extendScalars _).mp (h1 ((mem_restrictScalars ℚ).mp hx))
  · refine adjoin_le_iff.mpr ?_
    intro x hx
    rw [SetLike.mem_coe, mem_restrictScalars]
    rcases hx with rfl | hx
    · exact subset_adjoin (KN N₀) _ (Set.mem_singleton _)
    · exact (MNp N₀ p).algebraMap_mem ⟨x, hx⟩

private theorem finiteDimensional_MNp (hpN₀ : ¬ p ∣ N₀) : FiniteDimensional (KN N₀) (MNp N₀ p) :=
  Module.finite_of_finrank_pos (by rw [finrank_MNp N₀ p hpN₀]; exact Nat.succ_pos p)

private theorem isIntegral_jp (hpN₀ : ¬ p ∣ N₀) : IsIntegral (KN N₀) (jqN p) := by
  haveI := finiteDimensional_MNp N₀ p hpN₀
  have h : IsIntegral (KN N₀) (AdjoinSimple.gen (KN N₀) (jqN p)) := IsIntegral.of_finite (KN N₀) _
  exact isIntegral_iff.mp h

private theorem natDegree_minpoly (hpN₀ : ¬ p ∣ N₀) : (minpoly (KN N₀) (jqN p)).natDegree = p + 1 := by
  rw [← adjoin.finrank (isIntegral_jp N₀ p hpN₀), finrank_MNp N₀ p hpN₀]

private def base : KN N₀ →+* LaurentSeries ℚ := (qExpand ℚ p).comp (algebraMap (KN N₀) (LaurentSeries ℚ))

private theorem base_apply (x : KN N₀) : base N₀ p x = qExpand ℚ p (x : LaurentSeries ℚ) := rfl

private theorem base_jqNd {d : ℕ} [NeZero d] (hd : d ∣ N₀) :
    base N₀ p ⟨jqN d, jqNd_mem_K N₀ hd⟩ = jqN (d * p) :=
  (qExpand_qExpand d p jq).trans (qExpand_congr (Nat.mul_comm p d) jq)

private theorem base_jq : base N₀ p ⟨jq, jq_mem_K N₀⟩ = jqN p := rfl

variable (dp : ModularPolynomialData p)

private def evalAtJK : Polynomial ℤ →+* KN N₀ := (Polynomial.aeval (R := ℤ) (⟨jq, jq_mem_K N₀⟩ : KN N₀)).toRingHom

private def QK : Polynomial (KN N₀) := dp.Φ.map (evalAtJK N₀)

private theorem QK_monic : (QK N₀ p dp).Monic := dp.monic.map _

private theorem QK_natDegree : (QK N₀ p dp).natDegree = p + 1 := by
  rw [QK, dp.monic.natDegree_map, dp.natDegree_eq, dedekindPsi_prime hp.out]

private theorem algebraMap_comp_evalAtJK :
    (algebraMap (KN N₀) (LaurentSeries ℚ)).comp (evalAtJK N₀) = evalAtJ := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [evalAtJK]

private theorem QK_aeval_jp : Polynomial.aeval (jqN p) (QK N₀ p dp) = 0 := by
  rw [Polynomial.aeval_def, QK, Polynomial.eval₂_map, algebraMap_comp_evalAtJK]
  exact dp.eval_eq_zero

private theorem minpoly_eq_QK (hpN₀ : ¬ p ∣ N₀) : minpoly (KN N₀) (jqN p) = QK N₀ p dp := by
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (isIntegral_jp N₀ p hpN₀)) (QK_monic N₀ p dp)
    (minpoly.dvd _ _ (QK_aeval_jp N₀ p dp)) ?_
  rw [QK_natDegree, natDegree_minpoly N₀ p hpN₀]

private theorem base_comp_evalAtJK :
    (base N₀ p).comp (evalAtJK N₀) = (Polynomial.aeval (R := ℤ) (jqN p)).toRingHom := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.comp_apply, evalAtJK, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]
  exact base_jq N₀ p

private theorem minpoly_eval₂_base (hpN₀ : ¬ p ∣ N₀) (hsymm : EvalSymm dp.Φ) :
    (minpoly (KN N₀) (jqN p)).eval₂ (base N₀ p) jq = 0 := by
  rw [minpoly_eq_QK N₀ p dp hpN₀, QK, Polynomial.eval₂_map, base_comp_evalAtJK, hsymm (jqN p) jq]
  exact dp.eval_eq_zero

variable (hpN₀ : ¬ p ∣ N₀) (hsymm : EvalSymm dp.Φ)

private def liftHom : MNp N₀ p →+* LaurentSeries ℚ :=
  (AdjoinRoot.lift (base N₀ p) jq (minpoly_eval₂_base N₀ p dp hpN₀ hsymm)).comp
    (adjoinRootEquivAdjoin (KN N₀) (isIntegral_jp N₀ p hpN₀)).symm.toAlgHom.toRingHom

include hpN₀ hsymm in
private theorem liftHom_gen : liftHom N₀ p dp hpN₀ hsymm (AdjoinSimple.gen (KN N₀) (jqN p)) = jq := by
  rw [liftHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin (KN N₀) (isIntegral_jp N₀ p hpN₀)).symm.toAlgHom.toRingHom
        (AdjoinSimple.gen (KN N₀) (jqN p))
      = AdjoinRoot.root (minpoly (KN N₀) (jqN p)) from
    adjoinRootEquivAdjoin_symm_apply_gen (KN N₀) (isIntegral_jp N₀ p hpN₀)]
  exact AdjoinRoot.lift_root _

include hpN₀ hsymm in
private theorem liftHom_algebraMap (c : KN N₀) :
    liftHom N₀ p dp hpN₀ hsymm (algebraMap (KN N₀) (MNp N₀ p) c) = base N₀ p c := by
  rw [liftHom, RingHom.comp_apply]
  rw [show (adjoinRootEquivAdjoin (KN N₀) (isIntegral_jp N₀ p hpN₀)).symm.toAlgHom.toRingHom
        (algebraMap (KN N₀) (MNp N₀ p) c)
      = algebraMap (KN N₀) (AdjoinRoot (minpoly (KN N₀) (jqN p))) c from
    (adjoinRootEquivAdjoin (KN N₀) (isIntegral_jp N₀ p hpN₀)).symm.commutes c]
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of _

private def carrierEquiv : MNp N₀ p ≃+* modularFunctionFieldFull (N₀ * p) where
  toFun x := ⟨(x : LaurentSeries ℚ), (SetLike.ext_iff.mp (MNp_restrictScalars N₀ p hpN₀) _).mp x.2⟩
  invFun y := ⟨(y : LaurentSeries ℚ), (SetLike.ext_iff.mp (MNp_restrictScalars N₀ p hpN₀) _).mpr y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private abbrev LN : IntermediateField ℚ (LaurentSeries ℚ) := modularFunctionFieldFull (N₀ * p)

private theorem jqNe_mem_L {e : ℕ} [NeZero e] (he : e ∣ N₀ * p) : jqN e ∈ LN N₀ p := jqd_mem_full (N₀ * p) he

private theorem jq_mem_L : jq ∈ LN N₀ p := by simpa [qExpand_one_apply] using jqd_mem_full (N₀ * p) (one_dvd _)

private theorem jqNp_mem_L : jqN p ∈ LN N₀ p := jqd_mem_full (N₀ * p) (dvd_mul_left p N₀)

private theorem jqNd_mem_L {d : ℕ} [NeZero d] (hd : d ∣ N₀) : jqN d ∈ LN N₀ p :=
  jqd_mem_full (N₀ * p) (hd.mul_right p)

private theorem jqNdp_mem_L {d : ℕ} [NeZero d] (hd : d ∣ N₀) : jqN (d * p) ∈ LN N₀ p :=
  jqd_mem_full (N₀ * p) (mul_dvd_mul_right hd p)

private def sigmaHom : LN N₀ p →+* LaurentSeries ℚ :=
  (liftHom N₀ p dp hpN₀ hsymm).comp (carrierEquiv N₀ p hpN₀).symm.toRingHom

include hpN₀ hsymm in

private theorem sigmaHom_jqNd {d : ℕ} [NeZero d] (hd : d ∣ N₀) :
    sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN d, jqNd_mem_L N₀ p hd⟩ = jqN (d * p) := by
  show liftHom N₀ p dp hpN₀ hsymm ((carrierEquiv N₀ p hpN₀).symm ⟨jqN d, jqNd_mem_L N₀ p hd⟩) = _
  rw [show (carrierEquiv N₀ p hpN₀).symm ⟨jqN d, jqNd_mem_L N₀ p hd⟩ =
      algebraMap (KN N₀) (MNp N₀ p) ⟨jqN d, jqNd_mem_K N₀ hd⟩ from Subtype.ext rfl,
    liftHom_algebraMap, base_jqNd N₀ p hd]

include hpN₀ hsymm in
private theorem sigmaHom_jq : sigmaHom N₀ p dp hpN₀ hsymm ⟨jq, jq_mem_L N₀ p⟩ = jqN p := by
  show liftHom N₀ p dp hpN₀ hsymm ((carrierEquiv N₀ p hpN₀).symm ⟨jq, jq_mem_L N₀ p⟩) = _
  rw [show (carrierEquiv N₀ p hpN₀).symm ⟨jq, jq_mem_L N₀ p⟩ = algebraMap (KN N₀) (MNp N₀ p) ⟨jq, jq_mem_K N₀⟩
    from Subtype.ext rfl, liftHom_algebraMap, base_jq]

include hpN₀ hsymm in
private theorem sigmaHom_jqNp : sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN p, jqNp_mem_L N₀ p⟩ = jq := by
  show liftHom N₀ p dp hpN₀ hsymm ((carrierEquiv N₀ p hpN₀).symm ⟨jqN p, jqNp_mem_L N₀ p⟩) = _
  rw [show (carrierEquiv N₀ p hpN₀).symm ⟨jqN p, jqNp_mem_L N₀ p⟩ = AdjoinSimple.gen (KN N₀) (jqN p) from
    Subtype.ext rfl]
  exact liftHom_gen N₀ p dp hpN₀ hsymm

include hpN₀ hsymm in
private theorem sigmaHom_rel (Φ : Polynomial (Polynomial ℤ)) (x y : LN N₀ p)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) (x : LaurentSeries ℚ)).toRingHom (y : LaurentSeries ℚ) = 0) :
    Φ.eval₂ (Polynomial.aeval (R := ℤ) (sigmaHom N₀ p dp hpN₀ hsymm x)).toRingHom
      (sigmaHom N₀ p dp hpN₀ hsymm y) = 0 := by
  have hL : Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0 := by
    have e := map_eval₂_aeval (algebraMap (LN N₀ p) (LaurentSeries ℚ)) Φ x y
    have e' : algebraMap (LN N₀ p) (LaurentSeries ℚ) (Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y) = 0 :=
      e.trans h
    exact (map_eq_zero_iff _ (algebraMap (LN N₀ p) (LaurentSeries ℚ)).injective).mp e'
  exact rel_push (sigmaHom N₀ p dp hpN₀ hsymm) Φ x y hL

private theorem rel_qp (q : ℕ) [hq : Fact q.Prime] (dq : ModularPolynomialData q) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN p)).toRingHom (jqN (q * p)) = 0 := by
  have h0 : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom (jqN q) = 0 := dq.eval_eq_zero
  have h := rel_push (qExpand ℚ p) dq.Φ jq (jqN q) h0
  have e0 : (qExpand ℚ p) jq = jqN p := rfl
  have e1 : (qExpand ℚ p) (jqN q) = jqN (q * p) :=
    (qExpand_qExpand q p jq).trans (qExpand_congr (Nat.mul_comm p q) jq)
  rw [e0, e1] at h
  exact h

include hpN₀ hsymm in

private theorem sigmaHom_jqNqp (q : ℕ) [hq : Fact q.Prime] (hqN₀ : q ∣ N₀) (dq : ModularPolynomialData q) :
    sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (q * p), jqNdp_mem_L N₀ p hqN₀⟩ = jqN q := by
  refine root_eq_jqNp q dq _ ?_
  have h := sigmaHom_rel N₀ p dp hpN₀ hsymm dq.Φ ⟨jqN p, jqNp_mem_L N₀ p⟩
    ⟨jqN (q * p), jqNdp_mem_L N₀ p hqN₀⟩ (rel_qp p q dq)
  rwa [sigmaHom_jqNp] at h

section OneRootGen

variable (q : ℕ) [hq : Fact q.Prime]
variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem root_eq_jqNqm_of_isPrimitiveRoot (m : ℕ) [NeZero m] (hqm : ¬ q ∣ m)
    (dq : ModularPolynomialData q) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (z : LaurentSeries ℚ) (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN m)).toRingHom z = 0) :
    z = jqN (q * m) := by
  set ι : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ q) with hι
  have hιinj : Function.Injective ι := (coeffEmb K).injective.comp (qExpand_injective (R := ℚ) q)
  have ι_jm : ι (jqN m) = qExpand K (q * m) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq)) := by
    rw [one_pow, qTwist_one_apply, hι, RingHom.comp_apply, jqN, coeffEmb_qExpand, coeffEmb_qExpand,
      qExpand_qExpand]
  have ι_jqm : ι (jqN (q * m)) = qExpand K (q * (q * m)) (qTwist ((1 : Kˣ) ^ (q * q)) (coeffEmb K jq)) := by
    rw [one_pow, qTwist_one_apply, hι, RingHom.comp_apply, jqN, coeffEmb_qExpand, coeffEmb_qExpand,
      qExpand_qExpand]
  have hA' : (dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (q * m) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq))))).eval (ι z) = 0 := by
    have h' := rel_push ι dq.Φ (jqN m) z hA
    rw [ι_jm] at h'
    rw [Polynomial.eval_map]
    convert h' using 2 <;> try rfl
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [splits_prime_at_slot q ζ hζ q dvd_rfl dq m 1, Polynomial.eval_mul, Polynomial.eval_prod] at hA'
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_range, sub_eq_zero] at hA'
  rcases hA' with hz | ⟨b, -, hz⟩
  · apply hιinj
    rw [hz, ι_jqm]
  · exfalso

    have h := congrArg (fun y : LaurentSeries K => y.coeff (-((m : ℕ) : ℤ))) hz
    beta_reduce at h
    rw [coeff_twist_neg m] at h
    have h0 : (ι z).coeff (-((m : ℕ) : ℤ)) = 0 := by
      rw [hι, RingHom.comp_apply, coeffEmb_qExpand]
      refine qExpand_coeff_of_not_dvd (R := K) q _ ?_
      simp only [dvd_neg]
      exact_mod_cast hqm
    rw [h0] at h
    exact (Units.ne_zero _) h.symm

end OneRootGen
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

private theorem root_eq_jqNqm (q : ℕ) [hq : Fact q.Prime] (m : ℕ) [NeZero m] (hqm : ¬ q ∣ m)
    (dq : ModularPolynomialData q) (z : LaurentSeries ℚ)
    (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN m)).toRingHom z = 0) : z = jqN (q * m) := by
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne q)⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  obtain ⟨ζ0, hζ0⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField q ℚ)
    (Set.mem_singleton q) (NeZero.ne q)
  have hζ : IsPrimitiveRoot (((hζ0.isUnit (NeZero.ne q)).unit : (CyclotomicField q ℚ)ˣ) : CyclotomicField q ℚ) q := by
    rw [IsUnit.unit_spec]; exact hζ0
  exact root_eq_jqNqm_of_isPrimitiveRoot q m hqm dq _ hζ z hA

private theorem rel_qmp (q : ℕ) [hq : Fact q.Prime] (m : ℕ) [NeZero m] (dq : ModularPolynomialData q) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (m * p))).toRingHom (jqN (q * m * p)) = 0 := by
  have h0 : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom (jqN q) = 0 := dq.eval_eq_zero
  have h := rel_push (qExpand ℚ (m * p)) dq.Φ jq (jqN q) h0
  have e0 : (qExpand ℚ (m * p)) jq = jqN (m * p) := rfl
  have e1 : (qExpand ℚ (m * p)) (jqN q) = jqN (q * m * p) := by
    refine (qExpand_qExpand q (m * p) jq).trans (qExpand_congr ?_ jq)
    ring
  rw [e0, e1] at h
  exact h

include hpN₀ hsymm in

private theorem sigmaHom_jqNdp_step_sf (q m : ℕ) [hq : Fact q.Prime] [NeZero m] (hqm : ¬ q ∣ m)
    (dq : ModularPolynomialData q) (hdN₀ : q * m ∣ N₀) (hmN₀ : m ∣ N₀)
    (IH : sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (m * p), jqNdp_mem_L N₀ p hmN₀⟩ = jqN m) :
    sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ = jqN (q * m) := by
  refine root_eq_jqNqm q m hqm dq _ ?_
  have h := sigmaHom_rel N₀ p dp hpN₀ hsymm dq.Φ ⟨jqN (m * p), jqNdp_mem_L N₀ p hmN₀⟩
    ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ (rel_qmp p q m dq)
  rwa [IH] at h

section RootBook

variable (q : ℕ) [hq : Fact q.Prime]
variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem root_cases_of_isPrimitiveRoot (dq : ModularPolynomialData q) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (e : ℕ) [NeZero e] (y : LaurentSeries ℚ)
    (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * e))).toRingHom y = 0) :
    coeffEmb K y = coeffEmb K (jqN (q * (q * e))) ∨
      ∃ b < q, coeffEmb K y = qExpand K e (qTwist (1 * ζ ^ (b * (q / q))) (coeffEmb K jq)) := by
  have ι_X : coeffEmb K (jqN (q * e)) = qExpand K (q * e) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq)) := by
    rw [one_pow, qTwist_one_apply, jqN, coeffEmb_qExpand]
  have hA' : (dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (q * e) (qTwist ((1 : Kˣ) ^ q) (coeffEmb K jq))))).eval (coeffEmb K y) = 0 := by
    have h' := rel_push (coeffEmb K) dq.Φ (jqN (q * e)) y hA
    rw [ι_X] at h'
    rw [Polynomial.eval_map]
    convert h' using 2 <;> try rfl
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  rw [splits_prime_at_slot q ζ hζ q dvd_rfl dq e 1, Polynomial.eval_mul, Polynomial.eval_prod] at hA'
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_range, sub_eq_zero] at hA'
  rcases hA' with hz | ⟨b, hb, hz⟩
  · left
    rw [hz, one_pow, qTwist_one_apply, jqN, coeffEmb_qExpand]
  · right
    exact ⟨b, hb, hz⟩

private theorem not_root_of_two_le_of_isPrimitiveRoot (dq : ModularPolynomialData q) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) q) (e n : ℕ) [NeZero e] [NeZero n] (hn : 2 ≤ n) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * e))).toRingHom (jqN (q * (q * e) * n)) ≠ 0 := by
  intro hA
  rcases root_cases_of_isPrimitiveRoot q dq ζ hζ e _ hA with hz | ⟨b, -, hz⟩
  ·
    have h := congrArg (fun y : LaurentSeries K => y.coeff ((q * (q * e) * n : ℕ) * (-1 : ℤ))) hz
    beta_reduce at h
    rw [jqN, coeffEmb_qExpand, qExpand_coeff_mul, coeffEmb_coeff, coeff_jq_neg_one, map_one, jqN,
      coeffEmb_qExpand, show ((q * (q * e) * n : ℕ) : ℤ) * (-1 : ℤ) = ((q * (q * e) : ℕ) : ℤ) * (-(n : ℤ)) by
        push_cast; ring,
      qExpand_coeff_mul, coeffEmb_coeff, coeff_jq_of_lt (by omega), map_zero] at h
    exact one_ne_zero h
  ·
    have h := congrArg (fun y : LaurentSeries K => y.coeff (-((e : ℕ) : ℤ))) hz
    beta_reduce at h
    haveI : NeZero (q * q * n) := ⟨mul_ne_zero (mul_ne_zero hq.out.ne_zero hq.out.ne_zero) (NeZero.ne n)⟩
    rw [coeff_twist_neg e, jqN, coeffEmb_qExpand, qExpand_congr (show q * (q * e) * n = (q * q * n) * e by ring)] at h
    rw [coeff_spread_neg_eq_zero e (q * q * n)
      (le_trans hn (Nat.le_mul_of_pos_left n (Nat.mul_pos hq.out.pos hq.out.pos))) _] at h
    exact (Units.ne_zero _) h.symm

private theorem not_root_mul_of_isPrimitiveRoot (dq : ModularPolynomialData q) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) q) (k M : ℕ) [NeZero k] [NeZero M] (hM : 2 ≤ M) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * (M * k)))).toRingHom (jqN k) ≠ 0 := by
  intro hA
  rcases root_cases_of_isPrimitiveRoot q dq ζ hζ (M * k) _ hA with hz | ⟨b, -, hz⟩
  ·
    have h := congrArg (fun y : LaurentSeries K => y.coeff ((k : ℕ) * (-1 : ℤ))) hz
    beta_reduce at h
    haveI : NeZero (q * q * M) := ⟨mul_ne_zero (mul_ne_zero hq.out.ne_zero hq.out.ne_zero) (NeZero.ne M)⟩
    rw [jqN, coeffEmb_qExpand, qExpand_coeff_mul, coeffEmb_coeff, coeff_jq_neg_one, map_one, jqN,
      coeffEmb_qExpand, mul_neg_one, qExpand_congr (show q * (q * (M * k)) = (q * q * M) * k by ring),
      coeff_spread_neg_eq_zero k (q * q * M)
        (le_trans hM (Nat.le_mul_of_pos_left M (Nat.mul_pos hq.out.pos hq.out.pos))) _] at h
    exact one_ne_zero h
  · have h := congrArg (fun y : LaurentSeries K => y.coeff ((k : ℕ) * (-1 : ℤ))) hz
    beta_reduce at h
    rw [jqN, coeffEmb_qExpand, qExpand_coeff_mul, coeffEmb_coeff, coeff_jq_neg_one, map_one, mul_neg_one,
      coeff_spread_neg_eq_zero k M hM _] at h
    exact one_ne_zero h

private theorem root_pair_of_odd_of_isPrimitiveRoot (dq : ModularPolynomialData q) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) q) (hodd : q ≠ 2) (e : ℕ) [NeZero e] (z : LaurentSeries ℚ)
    (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * e))).toRingHom z = 0) :
    z = jqN (q * (q * e)) ∨ z = jqN e := by
  rcases root_cases_of_isPrimitiveRoot q dq ζ hζ e z hA with hz | ⟨b, hb, hz⟩
  · exact Or.inl ((coeffEmb K).injective hz)
  · right

    have h := congrArg (fun y : LaurentSeries K => y.coeff (-((e : ℕ) : ℤ))) hz
    beta_reduce at h
    rw [coeff_twist_neg e, coeffEmb_coeff, Nat.div_self hq.out.pos, mul_one, one_mul] at h
    set c : ℚ := z.coeff (-((e : ℕ) : ℤ)) with hc
    have hζq : (ζ : K) ^ q = 1 := hζ.pow_eq_one
    have hcp : c ^ q = 1 := by
      apply (algebraMap ℚ K).injective
      rw [map_pow, h, map_one, Units.val_inv_eq_inv_val, inv_pow, Units.val_pow_eq_pow_val, ← pow_mul,
        mul_comm, pow_mul, hζq, one_pow, inv_one]
    have hqodd : Odd q := hq.out.odd_of_ne_two hodd
    have hc1 : c = 1 := hqodd.pow_inj.mp (by rw [hcp, one_pow])
    have hζb : (ζ : K) ^ b = 1 := by
      have h1 : ((ζ ^ b)⁻¹ : Kˣ) = 1 := by
        apply Units.ext
        rw [← h, hc1, map_one, Units.val_one]
      have h2 : ζ ^ b = 1 := inv_eq_one.mp h1
      have h3 := congrArg (fun u : Kˣ => (u : K)) h2
      simpa using h3
    have hb0 : b = 0 := by
      have hdvd : q ∣ b := (hζ.pow_eq_one_iff_dvd b).mp hζb
      exact Nat.eq_zero_of_dvd_of_lt hdvd hb
    subst hb0
    apply (coeffEmb K).injective
    rw [hz, zero_mul, pow_zero, mul_one, qTwist_one_apply, jqN, coeffEmb_qExpand]

end RootBook
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

section RootBookQ

variable (q : ℕ) [hq : Fact q.Prime]

private theorem exists_primitiveRoot_unit :
    ∃ ζ : (CyclotomicField q ℚ)ˣ, IsPrimitiveRoot (ζ : CyclotomicField q ℚ) q := by
  haveI : NeZero ((q : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne q)⟩
  haveI : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  obtain ⟨ζ0, hζ0⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField q ℚ)
    (Set.mem_singleton q) (NeZero.ne q)
  exact ⟨(hζ0.isUnit (NeZero.ne q)).unit, by rw [IsUnit.unit_spec]; exact hζ0⟩

private theorem not_root_of_two_le (dq : ModularPolynomialData q) (e n : ℕ) [NeZero e] [NeZero n] (hn : 2 ≤ n) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * e))).toRingHom (jqN (q * (q * e) * n)) ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_unit q
  exact not_root_of_two_le_of_isPrimitiveRoot q dq ζ hζ e n hn

private theorem not_root_mul (dq : ModularPolynomialData q) (k M : ℕ) [NeZero k] [NeZero M] (hM : 2 ≤ M) :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * (M * k)))).toRingHom (jqN k) ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_unit q
  exact not_root_mul_of_isPrimitiveRoot q dq ζ hζ k M hM

private theorem root_pair_of_odd (dq : ModularPolynomialData q) (hodd : q ≠ 2) (e : ℕ) [NeZero e] (z : LaurentSeries ℚ)
    (hA : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * e))).toRingHom z = 0) :
    z = jqN (q * (q * e)) ∨ z = jqN e := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_unit q
  exact root_pair_of_odd_of_isPrimitiveRoot q dq ζ hζ hodd e z hA

private theorem rel_slot (dq : ModularPolynomialData q) (e : ℕ) [NeZero e] :
    dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN e)).toRingHom (jqN (e * q)) = 0 := by
  have h0 : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) jq).toRingHom (jqN q) = 0 := dq.eval_eq_zero
  have h := rel_push (qExpand ℚ e) dq.Φ jq (jqN q) h0
  have e0 : (qExpand ℚ e) jq = jqN e := rfl
  have e1 : (qExpand ℚ e) (jqN q) = jqN (e * q) := qExpand_qExpand q e jq
  rw [e0, e1] at h
  exact h

end RootBookQ
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

section GenDiscrim

include hpN₀ hsymm in

private theorem sigmaHom_jqNdp_step_sq (q m : ℕ) [hq : Fact q.Prime] [NeZero m] (hqm : q ∣ m)
    (dq : ModularPolynomialData q) (hdN₀ : q * m ∣ N₀) (hmN₀ : m ∣ N₀)
    (IH : sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (m * p), jqNdp_mem_L N₀ p hmN₀⟩ = jqN m) :
    sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ = jqN (q * m) := by

  haveI : NeZero (q * m) := ⟨mul_ne_zero hq.out.ne_zero (NeZero.ne m)⟩
  obtain ⟨m', hm'⟩ := hqm
  haveI : NeZero m' := ⟨fun h => NeZero.ne m (by rw [hm', h, mul_zero])⟩
  have hqq : 2 ≤ q * q := le_trans hq.out.two_le (Nat.le_mul_of_pos_left q hq.out.pos)
  haveI : NeZero (q * q) := ⟨by omega⟩
  set z := sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ with hz
  have hRq : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN m)).toRingHom z = 0 := by
    have h := sigmaHom_rel N₀ p dp hpN₀ hsymm dq.Φ ⟨jqN (m * p), jqNdp_mem_L N₀ p hmN₀⟩
      ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ (rel_qmp p q m dq)
    rwa [IH] at h
  have hRp : dp.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * m * p))).toRingHom z = 0 := by
    have h := sigmaHom_rel N₀ p dp hpN₀ hsymm dp.Φ ⟨jqN (q * m), jqNd_mem_L N₀ p hdN₀⟩
      ⟨jqN (q * m * p), jqNdp_mem_L N₀ p hdN₀⟩ (rel_slot p dp (q * m))
    rwa [sigmaHom_jqNd N₀ p dp hpN₀ hsymm hdN₀] at h
  by_cases hp2 : p = 2
  ·
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hpN₀ (hp2 ▸ dvd_trans (dvd_mul_right 2 m) hdN₀)
    have hRq' : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (q * m'))).toRingHom z = 0 := by
      rw [← jqN_congr hm']
      exact hRq
    rcases root_pair_of_odd q dq hq2 m' z hRq' with h1 | h2
    · rw [h1]
      exact jqN_congr (by rw [hm'])
    · exfalso
      refine not_root_mul p dp m' (q * q) hqq ?_
      rw [jqN_congr (show p * (q * q * m') = q * m * p by rw [hm']; ring), ← h2]
      exact hRp
  ·
    have hRp' : dp.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN (p * (q * m)))).toRingHom z = 0 := by
      rw [jqN_congr (show p * (q * m) = q * m * p by ring)]
      exact hRp
    rcases root_pair_of_odd p dp hp2 (q * m) z hRp' with hbig | hgood
    · exfalso
      haveI : NeZero (p * p) := ⟨mul_ne_zero hp.out.ne_zero hp.out.ne_zero⟩
      have hpp : 2 ≤ p * p := le_trans hp.out.two_le (Nat.le_mul_of_pos_left p hp.out.pos)
      refine not_root_of_two_le q dq m' (p * p) hpp ?_
      rw [← jqN_congr hm', jqN_congr (show q * (q * m') * (p * p) = p * (p * (q * m)) by rw [hm']; ring), ← hbig]
      exact hRq
    · exact hgood

end GenDiscrim
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

include hpN₀ hsymm in
private theorem sigmaHom_jqNdp_aux :
    ∀ d : ℕ, ∀ [NeZero d], ∀ hd : d ∣ N₀,
      sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (d * p), jqNdp_mem_L N₀ p hd⟩ = jqN d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro _ hd
    rcases eq_or_ne d 1 with rfl | hd1
    · rw [show (⟨jqN (1 * p), jqNdp_mem_L N₀ p hd⟩ : LN N₀ p) = ⟨jqN p, jqNp_mem_L N₀ p⟩ from
          Subtype.ext (jqN_congr (one_mul p)),
        sigmaHom_jqNp, jqN_one]
    · obtain ⟨q, hqp, hqd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hd1
      haveI : Fact q.Prime := ⟨hqp⟩
      obtain ⟨m, rfl⟩ := hqd
      haveI : NeZero m := ⟨fun h => (NeZero.ne (q * m)) (by rw [h, mul_zero])⟩
      have hmd : m < q * m :=
        (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero (NeZero.ne m))).mpr hqp.one_lt
      have hmN₀ : m ∣ N₀ := dvd_of_mul_left_dvd hd
      have IHm := IH m hmd hmN₀
      obtain ⟨dq, -⟩ := modularPolynomialFamily q hqp
      by_cases hqm : q ∣ m
      · exact sigmaHom_jqNdp_step_sq N₀ p dp hpN₀ hsymm q m hqm dq hd hmN₀ IHm
      · exact sigmaHom_jqNdp_step_sf N₀ p dp hpN₀ hsymm q m hqm dq hd hmN₀ IHm

include hpN₀ hsymm in

private theorem sigmaHom_jqNdp (d : ℕ) [NeZero d] (hd : d ∣ N₀) :
    sigmaHom N₀ p dp hpN₀ hsymm ⟨jqN (d * p), jqNdp_mem_L N₀ p hd⟩ = jqN d :=
  sigmaHom_jqNdp_aux N₀ p dp hpN₀ hsymm d hd

private theorem mem_of_apply_gens_mem {M : ℕ} (f : modularFunctionFieldFull M →+* LaurentSeries ℚ)
    (E : IntermediateField ℚ (LaurentSeries ℚ))
    (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ M), f ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ ∈ E)
    (x : modularFunctionFieldFull M) : f x ∈ E := by
  obtain ⟨x, hx⟩ := x
  induction hx using IntermediateField.adjoin_induction with
  | mem y hyS =>
      obtain ⟨d, hne, hdvd, rfl⟩ := hyS
      exact h d hne hdvd
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r, (modularFunctionFieldFull M).algebraMap_mem r⟩ :
          modularFunctionFieldFull M) = (r : modularFunctionFieldFull M) := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r = ((r : modularFunctionFieldFull M) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r]; norm_cast
      have hmem : f (r : modularFunctionFieldFull M) ∈ E := by
        rw [map_ratCast]; exact SubfieldClass.ratCast_mem E r
      exact (congrArg f hr).symm ▸ hmem
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) ∈ E
      rw [map_add]; exact add_mem ihx ihy
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) ∈ E
      rw [map_inv₀]; exact inv_mem ih
  | mul x y hx hy ihx ihy =>
      have key : (⟨x * y, mul_mem hx hy⟩ : modularFunctionFieldFull M) = ⟨x, hx⟩ * ⟨y, hy⟩ :=
        Subtype.ext ((modularFunctionFieldFull M).coe_mul ⟨x, hx⟩ ⟨y, hy⟩).symm
      have hmem : f (⟨x, hx⟩ * ⟨y, hy⟩) ∈ E := by
        rw [map_mul]; exact mul_mem ihx ihy
      exact (congrArg f key).symm ▸ hmem

private theorem divisors_mul_prime {e : ℕ} (hpN₀ : ¬ p ∣ N₀) (he : e ∣ N₀ * p) :
    (∃ d, ∃ _ : NeZero d, d ∣ N₀ ∧ e = d) ∨ (∃ d, ∃ _ : NeZero d, d ∣ N₀ ∧ e = d * p) := by
  have _ := hpN₀
  obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp he
  rcases (Nat.dvd_prime hp.out).mp hz with rfl | rfl
  · left
    exact ⟨y, ⟨fun h => NeZero.ne N₀ (Nat.eq_zero_of_zero_dvd (h ▸ hy))⟩, hy, mul_one y⟩
  · right
    refine ⟨y, ⟨fun h => NeZero.ne N₀ (Nat.eq_zero_of_zero_dvd (h ▸ hy))⟩, hy, rfl⟩

private theorem gen_eq {e e' : ℕ} [NeZero e] [NeZero e'] (he : e ∣ N₀ * p) (hee' : e = e')
    (he' : jqN e' ∈ LN N₀ p) :
    (⟨qExpand ℚ e jq, jqd_mem_full (N₀ * p) he⟩ : LN N₀ p) = ⟨jqN e', he'⟩ :=
  Subtype.ext (qExpand_congr hee' jq)

include hpN₀ hsymm in
private theorem sigmaHom_mem (x : LN N₀ p) : sigmaHom N₀ p dp hpN₀ hsymm x ∈ LN N₀ p := by
  refine mem_of_apply_gens_mem (sigmaHom N₀ p dp hpN₀ hsymm) (LN N₀ p) (fun e he0 he => ?_) x
  rcases divisors_mul_prime N₀ p hpN₀ he with ⟨d, hd0, hdN₀, rfl⟩ | ⟨d, hd0, hdN₀, rfl⟩
  · rw [gen_eq N₀ p he rfl (jqNd_mem_L N₀ p hdN₀), sigmaHom_jqNd N₀ p dp hpN₀ hsymm hdN₀]
    exact jqNdp_mem_L N₀ p hdN₀
  · rw [gen_eq N₀ p he rfl (jqNdp_mem_L N₀ p hdN₀), sigmaHom_jqNdp N₀ p dp hpN₀ hsymm d hdN₀]
    exact jqNd_mem_L N₀ p hdN₀

private def sigmaEndoRingHom : LN N₀ p →+* LN N₀ p :=
  (sigmaHom N₀ p dp hpN₀ hsymm).codRestrict (LN N₀ p) (sigmaHom_mem N₀ p dp hpN₀ hsymm)

private def sigmaEndo : LN N₀ p →ₐ[ℚ] LN N₀ p where
  toRingHom := sigmaEndoRingHom N₀ p dp hpN₀ hsymm
  commutes' r := by
    rw [eq_ratCast (algebraMap ℚ (LN N₀ p)) r]
    exact map_ratCast (sigmaEndoRingHom N₀ p dp hpN₀ hsymm) r

include hpN₀ hsymm in
private theorem sigmaEndo_jqNd {d : ℕ} [NeZero d] (hd : d ∣ N₀) :
    sigmaEndo N₀ p dp hpN₀ hsymm ⟨jqN d, jqNd_mem_L N₀ p hd⟩ = ⟨jqN (d * p), jqNdp_mem_L N₀ p hd⟩ :=
  Subtype.ext (sigmaHom_jqNd N₀ p dp hpN₀ hsymm hd)

include hpN₀ hsymm in
private theorem sigmaEndo_jqNdp {d : ℕ} [NeZero d] (hd : d ∣ N₀) :
    sigmaEndo N₀ p dp hpN₀ hsymm ⟨jqN (d * p), jqNdp_mem_L N₀ p hd⟩ = ⟨jqN d, jqNd_mem_L N₀ p hd⟩ :=
  Subtype.ext (sigmaHom_jqNdp N₀ p dp hpN₀ hsymm d hd)

include hpN₀ hsymm in
private theorem sigmaEndo_comp_self :
    (sigmaEndo N₀ p dp hpN₀ hsymm).comp (sigmaEndo N₀ p dp hpN₀ hsymm) = AlgHom.id ℚ (LN N₀ p) := by
  refine modularFunctionFieldFull_algHom_ext (fun e he0 he => ?_)
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  rcases divisors_mul_prime N₀ p hpN₀ he with ⟨d, hd0, hdN₀, rfl⟩ | ⟨d, hd0, hdN₀, rfl⟩
  · rw [gen_eq N₀ p he rfl (jqNd_mem_L N₀ p hdN₀), sigmaEndo_jqNd N₀ p dp hpN₀ hsymm hdN₀,
      sigmaEndo_jqNdp N₀ p dp hpN₀ hsymm hdN₀]
  · rw [gen_eq N₀ p he rfl (jqNdp_mem_L N₀ p hdN₀), sigmaEndo_jqNdp N₀ p dp hpN₀ hsymm hdN₀,
      sigmaEndo_jqNd N₀ p dp hpN₀ hsymm hdN₀]

private def sigma : LN N₀ p ≃ₐ[ℚ] LN N₀ p :=
  AlgEquiv.ofAlgHom (sigmaEndo N₀ p dp hpN₀ hsymm) (sigmaEndo N₀ p dp hpN₀ hsymm)
    (sigmaEndo_comp_self N₀ p dp hpN₀ hsymm) (sigmaEndo_comp_self N₀ p dp hpN₀ hsymm)

private theorem sigma_apply (x : LN N₀ p) : sigma N₀ p dp hpN₀ hsymm x = sigmaEndo N₀ p dp hpN₀ hsymm x := rfl

include hpN₀ hsymm in

private theorem isAtkinLehnerAutFull_sigma : IsAtkinLehnerAutFull N₀ p (sigma N₀ p dp hpN₀ hsymm) := by
  intro d hd0 hd
  refine ⟨?_, ?_⟩
  · rw [sigma_apply,
      show (⟨qExpand ℚ d jq, jqd_mem_full (N₀ * p) (Dvd.dvd.mul_right hd p)⟩ : LN N₀ p)
        = ⟨jqN d, jqNd_mem_L N₀ p hd⟩ from rfl,
      sigmaEndo_jqNd N₀ p dp hpN₀ hsymm hd]
    exact Subtype.ext rfl
  · rw [sigma_apply,
      show (⟨qExpand ℚ (d * p) jq, jqd_mem_full (N₀ * p) (Nat.mul_dvd_mul_right hd p)⟩ : LN N₀ p)
        = ⟨jqN (d * p), jqNdp_mem_L N₀ p hd⟩ from rfl,
      sigmaEndo_jqNdp N₀ p dp hpN₀ hsymm hd]
    exact Subtype.ext rfl

end ALGenSol
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

end
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

namespace ModularCurve p2m_export "ModularCurve" "degeneracyPushforwardPair degeneracyPushforwardPair_eq heckeAlphaBar heckeBetaBar heckeDivBar modularFunctionFieldBar JZero qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN jqN_one evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff laurentBaseChange heckeOperatorBar heckeOperatorBar_apply heckeOperatorAlong_eq HeckeDiagonalIdentity IsAtkinLehnerAutFull geomAut hasPrincipalDivisors_modularFunctionFieldBar_unconditional heckeInputsAll degeneracyPushforwardInputs geomAut_atkinLehner_comp_legs heckeDiagonalIdentity_of_prime_of_not_dvd qTwist qTwist_coeff qTwist_one_apply EvalSymm full_eq_adjoin_full_div_prime finrank_adjoin_jqN_prime_of_not_mem finrank_adjoin_jqN_eq_dedekindPsi modularPolynomialFamily modularFunctionFieldFull_algHom_ext modularFunctionField_eq_full jqN_prime_not_mem_full dedekindPsi_prime coeffMap_qExpand" namespace WK2AlphaW end ModularCurve.WK2AlphaW
p2m_open_scoped "ModularCurve" in
p2m_open "ModularCurve~coeffEmb_qExpand" in

private theorem ModularCurve.WK2AlphaW.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∃ σ : modularFunctionFieldFull (N * p) ≃ₐ[ℚ] modularFunctionFieldFull (N * p),
      IsAtkinLehnerAutFull N p σ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨dp, hsymm⟩ := modularPolynomialFamily p hp
  exact ⟨ALGenSol.sigma N p dp hpN hsymm, ALGenSol.isAtkinLehnerAutFull_sigma N p dp hpN hsymm⟩

end WPart
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "degeneracyPushforwardPair degeneracyPushforwardPair_eq heckeAlphaBar heckeBetaBar heckeDivBar modularFunctionFieldBar JZero qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one coeff_jq_of_lt jqN jqN_one evalAtJ ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb coeffEmb_coeff laurentBaseChange heckeOperatorBar heckeOperatorBar_apply heckeOperatorAlong_eq HeckeDiagonalIdentity IsAtkinLehnerAutFull geomAut hasPrincipalDivisors_modularFunctionFieldBar_unconditional heckeInputsAll degeneracyPushforwardInputs geomAut_atkinLehner_comp_legs heckeDiagonalIdentity_of_prime_of_not_dvd qTwist qTwist_coeff qTwist_one_apply EvalSymm full_eq_adjoin_full_div_prime finrank_adjoin_jqN_prime_of_not_mem finrank_adjoin_jqN_eq_dedekindPsi modularPolynomialFamily modularFunctionFieldFull_algHom_ext modularFunctionField_eq_full jqN_prime_not_mem_full dedekindPsi_prime coeffMap_qExpand"
p2m_open "ModularCurve~coeffEmb_qExpand"

namespace WK2AlphaAux

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem pushforwardAlong_congr {φ ψ : F →ₐ[K] F'} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h; rfl

end Congr
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

section DivGrain

variable (N₀ p : ℕ) [NeZero N₀] [NeZero p]

local notation "LL" => AlgebraicClosure ℚ
local notation "FF" n => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull n)

private theorem pushforwardAlong_heckeAlphaBar_heckeDivBar_self
    (ha : (heckeAlphaBar LL N₀ p).toRingHom.IsIntegral) (hb : (heckeBetaBar LL N₀ p).toRingHom.IsIntegral)
    (hαu : (heckeAlphaBar LL (N₀ * p) p).toRingHom.IsIntegral)
    (hβu : (heckeBetaBar LL (N₀ * p) p).toRingHom.IsIntegral)
    [HasPrincipalDivisors LL (FF (N₀ * p))] [HasPrincipalDivisors LL (FF (N₀ * p * p))]
    (hdiag : HeckeDiagonalIdentity LL N₀ p)
    (τ : (FF (N₀ * p)) ≃ₐ[LL] (FF (N₀ * p)))
    (hτa : τ.toAlgHom.comp (heckeAlphaBar LL N₀ p) = heckeBetaBar LL N₀ p)
    (hτb : τ.toAlgHom.comp (heckeBetaBar LL N₀ p) = heckeAlphaBar LL N₀ p)
    (D : Divisor LL (FF (N₀ * p))) :
    Divisor.pushforwardAlong (heckeAlphaBar LL N₀ p) ha
        (Divisor.correspondence (heckeBetaBar LL (N₀ * p) p) (heckeAlphaBar LL (N₀ * p) p) hβu hαu D) =
      Divisor.correspondence (heckeBetaBar LL N₀ p) (heckeAlphaBar LL N₀ p) hb ha
          (Divisor.pushforwardAlong (heckeAlphaBar LL N₀ p) ha D) -
        Divisor.pushforwardAlong (heckeBetaBar LL N₀ p) hb D := by
  have hτi : τ.toAlgHom.toRingHom.IsIntegral := RingHom.isIntegral_of_surjective _ τ.surjective
  have h := hdiag ha hb hαu hβu τ hτb hτi D
  rw [eq_sub_iff_add_eq, Divisor.correspondence_apply (heckeBetaBar LL N₀ p) (heckeAlphaBar LL N₀ p) hb ha, h,
    map_add, heckeDivBar,
    Divisor.pushforwardAlong_pushforwardAlong _ _ ha hτi (RingHom.IsIntegral.trans _ _ ha hτi),
    pushforwardAlong_congr hτa _ hb]

end DivGrain
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

section MkSub

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem Pic0_mk_sub' (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (D - E) = Pic0.mk D - Pic0.mk E :=
  map_sub (QuotientAddGroup.mk' _) D E

end MkSub
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

section Descent

variable {K F₁ F₂ E₁ : Type*} [Field K] [Field F₁] [Field F₂] [Field E₁]
  [Algebra K F₁] [Algebra K F₂] [Algebra K E₁] [HasPrincipalDivisors K E₁] [HasPrincipalDivisors K F₁]

private theorem pushforwardAlongHom_correspondence_eq_sub
    (φβ : F₂ →ₐ[K] F₁) (hφβ : φβ.toRingHom.IsIntegral) (hfinβ : FiniteAlong K φβ) (hNβ : NormFormulaAlong K φβ hfinβ)
    (φα : F₂ →ₐ[K] F₁) (hφα : φα.toRingHom.IsIntegral) (hfinα : FiniteAlong K φα) (hNα : NormFormulaAlong K φα hfinα)
    (hFIβ : FundamentalIdentityAlong K φβ hφβ)
    (βu αu : F₁ →ₐ[K] E₁) (hβu : βu.toRingHom.IsIntegral) (hαu : αu.toRingHom.IsIntegral)
    (hFIu : FundamentalIdentityAlong K βu hβu) (hfinu : FiniteAlong K αu) (hNu : NormFormulaAlong K αu hfinu)
    (hdiv : ∀ D : Divisor K F₁, Divisor.pushforwardAlong φα hφα (Divisor.correspondence βu αu hβu hαu D) =
      Divisor.correspondence φβ φα hφβ hφα (Divisor.pushforwardAlong φα hφα D) - Divisor.pushforwardAlong φβ hφβ D)
    (c : Pic0 K F₁) :
    Pic0.pushforwardAlongHom φα hφα hfinα hNα (Pic0.correspondence βu αu hβu hαu hFIu hfinu hNu c) =
      Pic0.correspondence φβ φα hφβ hφα hFIβ hfinα hNα (Pic0.pushforwardAlongHom φα hφα hfinα hNα c) -
        Pic0.pushforwardAlongHom φβ hφβ hfinβ hNβ c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Pic0.correspondence_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk,
    Pic0.correspondence_mk, ← Pic0_mk_sub']
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_degZeroCorrespondence, AddSubgroupClass.coe_sub,
    Pic0.coe_degZeroCorrespondence, Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pushforwardAlongDegZero]
  exact hdiv (D : Divisor K F₁)

end Descent
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

end WK2AlphaAux
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

local instance instNeZeroPrimesWK2A (ℓ : Nat.Primes) : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩

local instance instHasPrincipalDivisorsBarWK2A (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar_unconditional M

private theorem degeneracyPushforwardPair_zero_heckeOperatorBar_self_of_diag_of_AL
    (N₀ p : ℕ) [NeZero N₀] [NeZero p] (hp : p.Prime)
    (hdiag : HeckeDiagonalIdentity (AlgebraicClosure ℚ) N₀ p)
    (hAL : ∃ σ : modularFunctionFieldFull (N₀ * p) ≃ₐ[ℚ] modularFunctionFieldFull (N₀ * p),
      IsAtkinLehnerAutFull N₀ p σ)
    (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 0 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      heckeOperatorBar N₀ ⟨p, hp⟩ (degeneracyPushforwardPair N₀ p 0 y) -
        degeneracyPushforwardPair N₀ p 1 y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hαu, hβu, _, hfinu, hFIu, hNu⟩ := heckeInputsAll (N₀ * p) ⟨p, hp⟩
  obtain ⟨hα, hβ, _, hfin, hFI, hN⟩ := heckeInputsAll N₀ ⟨p, hp⟩
  obtain ⟨hαδ, hβδ, hfinαδ, hfinβδ, hNαδ, hNβδ⟩ := degeneracyPushforwardInputs N₀ p hp
  obtain ⟨σ, hσ⟩ := hAL
  obtain ⟨hτa, hτb⟩ := geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N₀ p σ hσ
  rw [heckeOperatorBar_apply, heckeOperatorBar_apply, heckeOperatorAlong_eq hαu hβu hFIu hfinu hNu,
    heckeOperatorAlong_eq hα hβ hFI hfin hN, degeneracyPushforwardPair_eq hαδ hβδ hfinαδ hNαδ hfinβδ hNβδ]
  exact WK2AlphaAux.pushforwardAlongHom_correspondence_eq_sub _ hβδ hfinβδ hNβδ _ hαδ hfinαδ hNαδ hFI _ _ hβu hαu
    hFIu hfinu hNu (fun D => WK2AlphaAux.pushforwardAlong_heckeAlphaBar_heckeDivBar_self N₀ p hαδ hβδ hαu hβu hdiag
      _ hτa hτb D) y

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

end
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ALGenSol"

p2m_open "ModularCurve~coeffEmb_qExpand" in open _root_.P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self.ModularCurve in

theorem solution (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀) (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p 0 (heckeOperatorBar (N₀ * p) ⟨p, hp⟩ y) =
      heckeOperatorBar N₀ ⟨p, hp⟩ (degeneracyPushforwardPair N₀ p 0 y) -
        degeneracyPushforwardPair N₀ p 1 y :=
  ModularCurve.degeneracyPushforwardPair_zero_heckeOperatorBar_self_of_diag_of_AL N₀ p hp
    (heckeDiagonalIdentity_of_prime_of_not_dvd (AlgebraicClosure ℚ) N₀ p hp hpN₀)
    (ModularCurve.WK2AlphaW.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N₀ p hp hpN₀) y

end S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self
end P2MW
export P2MW.S_ModularCurve_degeneracyPushforwardPair_zero_heckeOperatorBar_self (solution)
