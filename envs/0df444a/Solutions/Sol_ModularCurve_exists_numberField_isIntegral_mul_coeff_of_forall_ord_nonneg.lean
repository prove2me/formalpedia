-- Prove2me | solution 1 for ModularCurve.exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/26780878-acb0-5e50-b86d-9d555caa4d5f

import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve Polynomial

noncomputable section

namespace NumberFieldCoeffSol

section NumberFieldPart

def HasNFCoeffs (z : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ ∀ n, z.coeff n ∈ K

theorem hasNFCoeffs_of_le {z : LaurentSeries (AlgebraicClosure ℚ)}
    {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hK' : FiniteDimensional ℚ K') (hle : K ≤ K')
    (h : ∀ n, z.coeff n ∈ K) : HasNFCoeffs z :=
  ⟨K', hK', fun n => hle (h n)⟩

def packK (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (z : LaurentSeries (AlgebraicClosure ℚ))
    (hz : ∀ n, z.coeff n ∈ K) : LaurentSeries K where
  coeff := fun n => ⟨z.coeff n, hz n⟩
  isPWO_support' := z.isPWO_support.mono fun _ hn h => hn (Subtype.ext h)

theorem coeffMap_packK (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : ∀ n, z.coeff n ∈ K) :
    coeffMap (algebraMap K (AlgebraicClosure ℚ)) (packK K z hz) = z := by
  ext n
  rw [coeffMap_coeff]
  rfl

theorem hasNFCoeffs_algebraMap (a : AlgebraicClosure ℚ) :
    HasNFCoeffs (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a) := by
  have ha : IsIntegral ℚ a := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a).isIntegral
  refine ⟨IntermediateField.adjoin ℚ {a}, IntermediateField.adjoin.finiteDimensional ha, fun n => ?_⟩
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  split_ifs
  · exact IntermediateField.mem_adjoin_simple_self ℚ a
  · exact zero_mem _

theorem hasNFCoeffs_coeffEmb (w : LaurentSeries ℚ) : HasNFCoeffs (coeffEmb (AlgebraicClosure ℚ) w) := by
  refine ⟨⊥, inferInstance, fun n => ?_⟩
  rw [coeffEmb_coeff]
  exact ⟨w.coeff n, rfl⟩

theorem hasNFCoeffs_one : HasNFCoeffs (1 : LaurentSeries (AlgebraicClosure ℚ)) := by
  have := hasNFCoeffs_algebraMap (1 : AlgebraicClosure ℚ)
  rwa [map_one] at this

theorem hasNFCoeffs_add {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : HasNFCoeffs x)
    (hy : HasNFCoeffs y) : HasNFCoeffs (x + y) := by
  obtain ⟨K, hK, hxK⟩ := hx
  obtain ⟨K', hK', hyK⟩ := hy
  haveI := hK; haveI := hK'
  refine ⟨K ⊔ K', IntermediateField.finiteDimensional_sup K K', fun n => ?_⟩
  rw [HahnSeries.coeff_add]
  exact add_mem (le_sup_left (a := K) (b := K') (hxK n)) (le_sup_right (a := K) (b := K') (hyK n))

theorem hasNFCoeffs_neg {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : HasNFCoeffs x) :
    HasNFCoeffs (-x) := by
  obtain ⟨K, hK, hxK⟩ := hx
  exact ⟨K, hK, fun n => by rw [HahnSeries.coeff_neg]; exact neg_mem (hxK n)⟩

theorem hasNFCoeffs_mul {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : HasNFCoeffs x)
    (hy : HasNFCoeffs y) : HasNFCoeffs (x * y) := by
  obtain ⟨K, hK, hxK⟩ := hx
  obtain ⟨K', hK', hyK⟩ := hy
  haveI := hK; haveI := hK'
  refine ⟨K ⊔ K', IntermediateField.finiteDimensional_sup K K', fun n => ?_⟩
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (le_sup_left (a := K) (b := K') (hxK _))
    (le_sup_right (a := K) (b := K') (hyK _))

theorem hasNFCoeffs_inv {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : HasNFCoeffs x) :
    HasNFCoeffs x⁻¹ := by
  obtain ⟨K, hK, hxK⟩ := hx
  refine ⟨K, hK, fun n => ?_⟩
  have h : x⁻¹ = coeffMap (algebraMap K (AlgebraicClosure ℚ)) ((packK K x hxK)⁻¹) := by
    rw [map_inv₀, coeffMap_packK]
  rw [h, coeffMap_coeff]
  exact ((packK K x hxK)⁻¹.coeff n).2

theorem hasNFCoeffs_of_mem (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {z : LaurentSeries (AlgebraicClosure ℚ)} (hz : z ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    HasNFCoeffs z := by
  rw [mem_laurentBaseChange_iff] at hz
  induction hz using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨w, hw, rfl⟩
      · exact hasNFCoeffs_algebraMap a
      · exact hasNFCoeffs_coeffEmb w
  | one => exact hasNFCoeffs_one
  | add x y _ _ hx hy => exact hasNFCoeffs_add hx hy
  | neg x _ hx => exact hasNFCoeffs_neg hx
  | inv x _ hx => exact hasNFCoeffs_inv hx
  | mul x y _ _ hx hy => exact hasNFCoeffs_mul hx hy

end NumberFieldPart

section IntegralPart

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

theorem mem_of_isIntegral_int {L : Type*} [Field L] (A : ValuationSubring L) {x : L}
    (hx : IsIntegral ℤ x) : x ∈ A := by
  by_contra hxA
  have hx0 : x ≠ 0 := fun h => hxA (h ▸ A.zero_mem)
  have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hxA
  obtain ⟨f, hf, hfx⟩ := hx
  set n := f.natDegree with hn
  have hlead : f.coeff n = 1 := hf.coeff_natDegree
  have hn0 : n ≠ 0 := by
    intro h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [hC, Polynomial.eval₂_C] at hfx
    have h01 : f.coeff 0 = 1 := by rw [← h0]; exact hlead
    rw [h01, map_one] at hfx
    exact one_ne_zero hfx
  have hsum : x ^ n = -∑ i ∈ Finset.range n, (algebraMap ℤ L (f.coeff i)) * x ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hfx
    rw [hlead, map_one, one_mul] at hfx
    linear_combination hfx
  have hxpow : ∀ i ∈ Finset.range n,
      (algebraMap ℤ L (f.coeff i)) * x ^ i * (x⁻¹) ^ (n - 1) ∈ A := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : x ^ i * (x⁻¹) ^ (n - 1) = (x⁻¹) ^ (n - 1 - i) := by
      rw [show n - 1 = i + (n - 1 - i) by omega, pow_add, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hx0, one_pow, one_mul]
      congr 1; omega
    rw [mul_assoc, this]
    refine mul_mem ?_ (pow_mem hxi _)
    rw [eq_intCast]
    exact intCast_mem A _
  have hx_eq : x = -(∑ i ∈ Finset.range n,
      (algebraMap ℤ L (f.coeff i)) * x ^ i * (x⁻¹) ^ (n - 1)) := by
    have h1 : x = x ^ n * (x⁻¹) ^ (n - 1) := by
      conv_lhs => rw [← mul_one x, ← one_pow (n - 1), ← mul_inv_cancel₀ hx0, mul_pow, ← mul_assoc,
        ← pow_succ', show n - 1 + 1 = n by omega]
    calc x = x ^ n * x⁻¹ ^ (n - 1) := h1
      _ = _ := by rw [hsum, neg_mul, Finset.sum_mul]
  apply hxA
  rw [hx_eq]
  exact neg_mem (sum_mem fun i hi => hxpow i hi)

theorem isIntegral_of_forall_mem {x : AlgebraicClosure ℚ}
    (h : ∀ A : ValuationSubring (AlgebraicClosure ℚ), x ∈ A) : IsIntegral ℤ x := by
  have key := Subring.eq_iInf_of_isIntegrallyClosedIn
    (R := (integralClosure ℤ (AlgebraicClosure ℚ)).toSubring)
  have hx : x ∈ (integralClosure ℤ (AlgebraicClosure ℚ)).toSubring := by
    rw [key, Subring.mem_iInf]
    intro V; exact h V.1
  exact hx

theorem exists_nat_denominator (S : Finset (AlgebraicClosure ℚ)) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ z ∈ S, IsIntegral ℤ ((d : AlgebraicClosure ℚ) * z) := by
  have h1 : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h2 : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) :=
    Algebra.IsAlgebraic.trans ℤ ℚ (AlgebraicClosure ℚ)
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ S
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy0, fun z hz => ?_⟩
  have hyz := hy z hz
  rw [Algebra.smul_def, eq_intCast] at hyz
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) := by
      rw [h]; simp
    rw [this]; exact hyz
  · have : ((y.natAbs : ℕ) : AlgebraicClosure ℚ) = -(y : AlgebraicClosure ℚ) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hyz.neg

variable (N : ℕ) [NeZero N]

abbrev jB : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

theorem aeval_mem_affineBaseFin (A : ValuationSubring (AlgebraicClosure ℚ))
    (q : Polynomial (AlgebraicClosure ℚ)) (hq : ∀ l, IsIntegral ℤ (q.coeff l)) :
    Polynomial.aeval (jB N) q ∈ CharPModel.affineBaseFin N A := by
  unfold CharPModel.affineBaseFin
  have hj : (jB N : modularFunctionFieldBar N) ∈
      Subring.closure (Set.range (CharPModel.constantsHom N A) ∪ {CharPModel.jBar N}) :=
    Subring.subset_closure (Or.inr rfl)
  have hc : ∀ l, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (q.coeff l) ∈
      Subring.closure (Set.range (CharPModel.constantsHom N A) ∪ {CharPModel.jBar N}) := fun l =>
    Subring.subset_closure (Or.inl ⟨⟨q.coeff l, mem_of_isIntegral_int A (hq l)⟩, rfl⟩)
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun l _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (hc l) (Subring.pow_mem _ hj _)

theorem main (f : modularFunctionFieldBar N)
    (hf : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ v.ord (jB N) → 0 ≤ v.ord f) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ℕ), FiniteDimensional ℚ K ∧ d ≠ 0 ∧
      ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K ∧
        IsIntegral ℤ ((d : AlgebraicClosure ℚ) * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) := by
  classical

  obtain ⟨K, hK, hfK⟩ := hasNFCoeffs_of_mem (modularFunctionFieldFull N) f.2

  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jB N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (modularFunctionFieldBar N))) f :=
    AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (jB N)
      (ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N) f hf
  set R := Algebra.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (modularFunctionFieldBar N)) with hR
  obtain ⟨p, hpmonic, hpf⟩ := hint

  have hcoefR : ∀ k, ∃ q : Polynomial (AlgebraicClosure ℚ),
      Polynomial.aeval (jB N) q = ((p.coeff k : R) : modularFunctionFieldBar N) := by
    intro k
    have hmem : ((p.coeff k : R) : modularFunctionFieldBar N) ∈
        (Polynomial.aeval (R := AlgebraicClosure ℚ) (jB N)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (p.coeff k).2
    exact (AlgHom.mem_range _).mp hmem
  choose q hq using hcoefR

  set nP := p.natDegree with hnP
  set S : Finset (AlgebraicClosure ℚ) :=
    (Finset.range (nP + 1)).biUnion fun k => (q k).coeffs with hS
  obtain ⟨d, hd0, hdS⟩ := exists_nat_denominator S
  have hdq : ∀ k ≤ nP, ∀ l, IsIntegral ℤ ((d : AlgebraicClosure ℚ) * (q k).coeff l) := by
    intro k hk l
    by_cases h0 : (q k).coeff l = 0
    · rw [h0, mul_zero]; exact isIntegral_zero
    · refine hdS _ ?_
      rw [hS, Finset.mem_biUnion]
      exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), Polynomial.coeff_mem_coeffs h0⟩

  set P : Polynomial (modularFunctionFieldBar N) :=
    (Polynomial.scaleRoots p (d : R)).map (algebraMap R (modularFunctionFieldBar N)) with hP
  have hPmonic : P.Monic := ((Polynomial.monic_scaleRoots_iff (d : R)).mpr hpmonic).map _
  set e : modularFunctionFieldBar N := (d : modularFunctionFieldBar N) * f with he
  have hPe : P.eval e = 0 := by
    rw [hP, Polynomial.eval_map, he]
    have := Polynomial.scaleRoots_eval₂_eq_zero (algebraMap R (modularFunctionFieldBar N))
      (s := (d : R)) hpf
    rwa [map_natCast] at this

  have hPcoef : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ),
      P.coeff m ∈ CharPModel.affineBaseFin N A := by
    intro A m
    rw [hP, Polynomial.coeff_map, Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy m nP with hm | hm | hm
    ·
      have hcast : (algebraMap R (modularFunctionFieldBar N)) (p.coeff m * (d : R) ^ (nP - m))
          = Polynomial.aeval (jB N) (Polynomial.C ((d : AlgebraicClosure ℚ) ^ (nP - m)) * q m) := by
        rw [map_mul, map_pow, map_natCast, map_mul, Polynomial.aeval_C, hq m, map_pow, map_natCast,
          mul_comm]
        rfl
      rw [hcast]
      refine aeval_mem_affineBaseFin N A _ fun l => ?_
      rw [Polynomial.coeff_C_mul]
      obtain ⟨k, hk⟩ : ∃ k, nP - m = k + 1 := ⟨nP - m - 1, by omega⟩
      rw [hk, pow_succ, mul_assoc]
      refine IsIntegral.mul ?_ (hdq m hm.le l)
      have : ((d : AlgebraicClosure ℚ) ^ k) = algebraMap ℤ (AlgebraicClosure ℚ) ((d : ℤ) ^ k) := by simp
      rw [this]; exact isIntegral_algebraMap
    ·
      subst hm
      have h1 : p.coeff nP = 1 := hpmonic.coeff_natDegree
      rw [h1, one_mul, Nat.sub_self, pow_zero, map_one]
      exact Subring.one_mem _
    ·
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hm, zero_mul, map_zero]
      exact Subring.zero_mem _

  have hcoefA : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (n : ℤ),
      (d : AlgebraicClosure ℚ) * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := by
    intro A n
    have hlift : P ∈ Polynomial.lifts (CharPModel.affineBaseFin N A).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro m
      exact ⟨⟨P.coeff m, hPcoef A m⟩, rfl⟩
    obtain ⟨PA, hPA, -, hPAmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hPmonic
    have heval : Polynomial.eval₂ (CharPModel.affineBaseFin N A).subtype e PA = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, hPA, hPe]
    have hmem := ModularCurve.mem_integralCoeffs_of_integral_affineBaseFin A N e ⟨PA, hPAmonic, heval⟩
    have hn := (CharPReduction.mem_integralCoeffs A.toSubring).mp hmem n
    have hcoe : ((e : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)).coeff n
        = (d : AlgebraicClosure ℚ) * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n := by
      rw [he, MulMemClass.coe_mul]
      have hd : ((d : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (d : AlgebraicClosure ℚ) := by
        rw [map_natCast]; norm_cast
      rw [hd, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
    rw [← hcoe]
    exact hn
  refine ⟨K, d, hK, hd0, fun n => ⟨hfK n, isIntegral_of_forall_mem fun A => hcoefA A n⟩⟩

end IntegralPart

end NumberFieldCoeffSol

end

open AlgebraicCurve ModularCurve in
theorem solution
    (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N)
    (hf : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        0 ≤ v.ord f) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (d : ℕ), FiniteDimensional ℚ K ∧ d ≠ 0 ∧
      ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K ∧
        IsIntegral ℤ ((d : AlgebraicClosure ℚ) * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) :=
  NumberFieldCoeffSol.main N f hf

end S_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg
end P2MW
export P2MW.S_ModularCurve_exists_numberField_isIntegral_mul_coeff_of_forall_ord_nonneg (solution)
