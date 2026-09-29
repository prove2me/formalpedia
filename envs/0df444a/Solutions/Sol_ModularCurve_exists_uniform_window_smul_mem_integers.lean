-- Prove2me | solution 1 for ModularCurve.exists_uniform_window_smul_mem_integers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5e48ad65-8cfe-50c1-b9c6-f3dec132e14d

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_AlgebraicCurve_ConstantReduction_isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace P2MW

open IsLocalRing Polynomial

theorem mem_maximalIdeal_of_mem_nonunits {L : Type*} [Field L] (A : ValuationSubring L) {x : L}
    (hx : x ∈ A.nonunits) (hxA : x ∈ A) : (⟨x, hxA⟩ : A) ∈ maximalIdeal A := by
  obtain ⟨h, hm⟩ := (A.mem_nonunits_iff_exists_mem_maximalIdeal).mp hx
  exact hm

theorem inv_mem_of_isUnit {L : Type*} [Field L] (A : ValuationSubring L) {f : L} (hf : f ∈ A)
    (hu : IsUnit (⟨f, hf⟩ : A)) : f⁻¹ ∈ A := by
  obtain ⟨u, hu'⟩ := hu
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have hval : (((u⁻¹ : Aˣ) : A) : L) * f = 1 := by
    have h := congrArg (Subtype.val : A → L) u.inv_mul
    rwa [hu'] at h
  have hinv_eq : (((u⁻¹ : Aˣ) : A) : L) = f⁻¹ := eq_inv_of_mul_eq_one_left hval
  exact hinv_eq ▸ ((u⁻¹ : Aˣ) : A).2

theorem isUnit_natCast_of_not_dvd {L : Type*} [Field L] (A : ValuationSubring L) {p : ℕ}
    (hp : p.Prime) (hA : (p : L) ∈ A.nonunits) {m : ℕ} (hm : ¬ p ∣ m) :
    IsUnit (⟨(m : L), natCast_mem A m⟩ : A) := by
  by_contra hnu
  have hmmax : (⟨(m : L), natCast_mem A m⟩ : A) ∈ maximalIdeal A :=
    (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hpmax : (⟨(p : L), natCast_mem A p⟩ : A) ∈ maximalIdeal A :=
    mem_maximalIdeal_of_mem_nonunits A hA _
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hcopZ : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, huv⟩ := hcopZ
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have key : (1 : A) = (u : A) * ⟨(p : L), natCast_mem A p⟩ + (v : A) * ⟨(m : L), natCast_mem A m⟩ := by
      apply Subtype.ext
      have huv' := congrArg (fun z : ℤ => (z : L)) huv
      push_cast at huv' ⊢
      exact huv'.symm
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpmax) (Ideal.mul_mem_left _ _ hmmax)
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem mem_of_isIntegral {L : Type*} [Field L] (A : ValuationSubring L) {x : L}
    (hx : IsIntegral ℤ x) : x ∈ A := by
  have hxA : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp hxA
  rw [← hy]
  exact y.2

theorem exists_pow_mul_mem (p : ℕ) (hp : p.Prime) (α : AlgebraicClosure ℚ) :
    ∃ k : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), (p : AlgebraicClosure ℚ) ∈ A.nonunits →
      (p : AlgebraicClosure ℚ) ^ k * α ∈ A := by
  have halgQ : IsAlgebraic ℚ α := by
    have h := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic α
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  have halgZ : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨m, hm0, hint⟩ := halgZ.exists_integral_multiple
  obtain ⟨k, m', hm', hmk⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hm0) p hp.ne_one
  refine ⟨k, fun A hA => ?_⟩
  have hm'0 : ((m' : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hm'
    have : (m' : ℕ) = 0 := by exact_mod_cast h0
    rw [this]
    exact dvd_zero p
  have hmem : (m : AlgebraicClosure ℚ) * α ∈ A := by
    have := mem_of_isIntegral A hint
    simpa [Algebra.smul_def] using this
  have habs : ((m.natAbs : ℤ) : AlgebraicClosure ℚ) * α ∈ A := by
    rcases Int.natAbs_eq m with h | h
    · rw [← h]; exact hmem
    · have : ((m.natAbs : ℤ) : AlgebraicClosure ℚ) * α = -((m : AlgebraicClosure ℚ) * α) := by
        conv_rhs => rw [h]
        push_cast
        ring
      rw [this]
      exact neg_mem hmem
  rw [hmk] at habs
  push_cast at habs
  have hu := isUnit_natCast_of_not_dvd A hp hA hm'
  have hinv : ((m' : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ A := inv_mem_of_isUnit A _ hu
  have : (p : AlgebraicClosure ℚ) ^ k * α
      = ((p : AlgebraicClosure ℚ) ^ k * (m' : AlgebraicClosure ℚ) * α) * ((m' : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
    field_simp
  rw [this]
  exact mul_mem habs hinv

theorem pow_mul_mem_of_le {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) {k B : ℕ} (hkB : k ≤ B)
    {x : L} (hx : (p : L) ^ k * x ∈ A) : (p : L) ^ B * x ∈ A := by
  have : (p : L) ^ B * x = (p : L) ^ (B - k) * ((p : L) ^ k * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkB]
  rw [this]
  exact mul_mem (pow_mem (natCast_mem A p) _) hx

theorem teichmueller_root_mem {L : Type*} [Field L] (A : ValuationSubring L) {q : ℕ} (hq : 2 ≤ q)
    {x : L} (hx : x ^ q = x) : x ∈ A := by
  refine mem_of_isIntegral A ⟨X ^ q - X, ?_, ?_⟩
  · exact (monic_X_pow q).sub_of_left (by
      rw [degree_X_pow, degree_X]; exact_mod_cast (by omega : 1 < q))
  · simp [hx]

theorem isUnit_sub_of_pow_eq {L : Type*} [Field L] (A : ValuationSubring L) {p : ℕ}
    (hA : (p : L) ∈ A.nonunits) (f : ℕ) {x y : L}
    (hx : x ^ (p ^ (f + 1)) = x) (hy : y ^ (p ^ (f + 1)) = y) (hxy : x ≠ y)
    (hxA : x ∈ A) (hyA : y ∈ A) : IsUnit (⟨x - y, sub_mem hxA hyA⟩ : A) := by
  set q : ℕ := p ^ (f + 1) with hqdef
  set X' : A := ⟨x, hxA⟩
  set Y' : A := ⟨y, hyA⟩
  have hX : X' ^ q = X' := Subtype.ext (by simpa using hx)
  have hY : Y' ^ q = Y' := Subtype.ext (by simpa using hy)
  have hXY : X' - Y' ≠ 0 := by
    intro h
    apply hxy
    have := congrArg (Subtype.val : A → L) h
    simpa [X', Y', sub_eq_zero] using this

  have hgeom : (∑ i ∈ Finset.range q, X' ^ i * Y' ^ (q - 1 - i)) = 1 := by
    have h := Commute.geom_sum₂_mul (Commute.all X' Y') q
    rw [hX, hY] at h

    have h' : (∑ i ∈ Finset.range q, X' ^ i * Y' ^ (q - 1 - i)) * (X' - Y') = 1 * (X' - Y') := by
      rw [one_mul]; exact h
    exact mul_right_cancel₀ hXY h'
  by_contra hnu
  have hmax : X' - Y' ∈ maximalIdeal A := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hres : residue A X' = residue A Y' := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hmax
  have hp0 : residue A (p : A) = 0 := by
    rw [residue_eq_zero_iff]
    have : (p : A) = ⟨(p : L), natCast_mem A p⟩ := Subtype.ext (by simp)
    rw [this]
    exact mem_maximalIdeal_of_mem_nonunits A hA _
  have hq0 : (q : ResidueField A) = 0 := by
    rw [hqdef, Nat.cast_pow, ← map_natCast (residue A), hp0, zero_pow (Nat.succ_ne_zero f)]
  have h1 : residue A (∑ i ∈ Finset.range q, X' ^ i * Y' ^ (q - 1 - i)) = 0 := by
    rw [map_sum]
    have : ∀ i ∈ Finset.range q,
        residue A (X' ^ i * Y' ^ (q - 1 - i)) = (residue A X') ^ (q - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, ← hres, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hq0, zero_mul]
  rw [hgeom, map_one] at h1
  exact one_ne_zero h1

theorem exists_teichmueller (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∃ a : Fin n → AlgebraicClosure ℚ, Function.Injective a ∧ ∀ i, a i ^ (p ^ (n + 1)) = a i := by
  set q : ℕ := p ^ (n + 1) with hqdef
  have hq2 : n + 2 ≤ q := by
    have h1 : 2 ^ (n + 1) ≤ p ^ (n + 1) := Nat.pow_le_pow_left hp.two_le _
    have h2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
    omega

  haveI : NeZero ((q - 1 : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast (by omega : q - 1 ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (q - 1) := by
    obtain ⟨ζ, hz⟩ := IsAlgClosed.exists_root (cyclotomic (q - 1) (AlgebraicClosure ℚ))
      (by rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr (by omega)).ne')
    exact ⟨ζ, (isRoot_cyclotomic_iff).mp hz⟩
  refine ⟨fun i => ζ ^ (i : ℕ), ?_, ?_⟩
  · intro i j hij
    have := hζ.pow_inj (by omega) (by omega) hij
    exact Fin.ext this
  · intro i
    show (ζ ^ (i : ℕ)) ^ q = ζ ^ (i : ℕ)
    rw [← pow_mul, mul_comm, pow_mul]
    have : ζ ^ q = ζ := by
      conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
    rw [this]

open Classical in
theorem mapDomain_apply_eq_sum {α β : Type*} (r : α → β) (D : α →₀ ℤ) (q : β) :
    Finsupp.mapDomain r D q = ∑ P ∈ D.support.filter (fun P => r P = q), D P := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finset.sum_filter]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

open Classical in

theorem exists_mapDomain_apply_eq_zero {α β : Type*} (r : α → β) (D : α →₀ ℤ)
    (hD0 : D.sum (fun _ n => n) = 0) (x0 : α) (e : ℕ) (hneg : -(e : ℤ) ≤ D x0)
    (hpos : ∀ x, x ≠ x0 → 0 ≤ D x) {M : ℕ} (Q : Fin M → β) (hQinj : Function.Injective Q)
    (hQ : ∀ i, Q i ≠ r x0) (hM : e < M) :
    ∃ i, Finsupp.mapDomain r D (Q i) = 0 := by
  set G := Finsupp.mapDomain r D with hGdef
  have hG_nonneg : ∀ q, q ≠ r x0 → 0 ≤ G q := by
    intro q hq
    rw [hGdef, mapDomain_apply_eq_sum]
    refine Finset.sum_nonneg fun x hx => hpos x ?_
    rintro rfl
    exact hq (Finset.mem_filter.mp hx).2.symm
  have hG_x0 : -(e : ℤ) ≤ G (r x0) := by
    rw [hGdef, mapDomain_apply_eq_sum]
    set S := D.support.filter (fun P => r P = r x0) with hS
    by_cases hx0 : x0 ∈ S
    · rw [← Finset.add_sum_erase S _ hx0]
      have : 0 ≤ ∑ x ∈ S.erase x0, D x :=
        Finset.sum_nonneg fun x hx => hpos x (Finset.ne_of_mem_erase hx)
      linarith
    · have : 0 ≤ ∑ x ∈ S, D x := by
        refine Finset.sum_nonneg fun x hx => hpos x ?_
        rintro rfl
        exact hx0 hx
      have he : (0 : ℤ) ≤ e := Int.natCast_nonneg e
      linarith
  have htot : G.sum (fun _ n => n) = 0 := by
    rw [hGdef, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact hD0
  by_contra hall
  push Not at hall
  have hge1 : ∀ i, 1 ≤ G (Q i) := by
    intro i
    have h0 := hG_nonneg (Q i) (hQ i)
    have hne := hall i
    omega

  set T : Finset β := Finset.univ.image Q with hT
  have hTcard : T.card = M := by
    rw [hT, Finset.card_image_of_injective _ hQinj, Finset.card_univ, Fintype.card_fin]
  have hTsub : T ⊆ G.support.erase (r x0) := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_erase.mpr ⟨hQ i, Finsupp.mem_support_iff.mpr ?_⟩
    have := hge1 i
    omega
  have hsumT : (M : ℤ) ≤ ∑ q ∈ T, G q := by
    have : ∑ q ∈ T, (1 : ℤ) ≤ ∑ q ∈ T, G q := by
      refine Finset.sum_le_sum fun q hq => ?_
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
      exact hge1 i
    simpa [hTcard] using this
  have hsumE : ∑ q ∈ T, G q ≤ ∑ q ∈ G.support.erase (r x0), G q := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hTsub fun q hq _ => ?_
    exact hG_nonneg q (Finset.ne_of_mem_erase hq)
  have htot' : G.sum (fun _ n => n) = ∑ q ∈ G.support, G q := rfl
  have key : -(e : ℤ) + M ≤ ∑ q ∈ G.support, G q := by
    by_cases hmem : r x0 ∈ G.support
    · rw [← Finset.add_sum_erase _ _ hmem]
      linarith
    · rw [show G.support = G.support.erase (r x0) from (Finset.erase_eq_of_notMem hmem).symm]
      have he : (0 : ℤ) ≤ e := Int.natCast_nonneg e
      linarith
  rw [← htot', htot] at key
  have : (e : ℤ) < M := by exact_mod_cast hM
  linarith

end P2MW

namespace P2MW

open AlgebraicCurve ModularCurve IsLocalRing

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ne_zero_of_ord_ne_zero (v : Place K F) {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem not_isUnit_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : ¬ IsUnit (⟨g, hg⟩ : v.toValuationSubring) := by
  rintro ⟨u, hu⟩
  have h0 := v.ord_coe_unit u
  rw [hu] at h0
  change v.ord g = 0 at h0
  omega

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (not_isUnit_of_ord_pos v hg h))

theorem mem_of_ord_pos (v : Place K F) {g : F} (h : 0 < v.ord g) : g ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (ne_zero_of_ord_ne_zero v h.ne') h.le

theorem isUnit_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) :
    IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  exact ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
    Subtype.ext (by simp [mul_inv_cancel₀ hc']),
    Subtype.ext (by simp [inv_mul_cancel₀ hc'])⟩, rfl⟩

theorem eq_of_ord_sub_algebraMap_pos (v : Place K F) (J : F) {a b : K}
    (ha : 0 < v.ord (J - algebraMap K F a)) (hb : 0 < v.ord (J - algebraMap K F b)) : a = b := by
  by_contra hab
  have hma := mem_of_ord_pos v ha
  have hmb := mem_of_ord_pos v hb
  have hIa := mem_maximalIdeal_of_ord_pos v hma ha
  have hIb := mem_maximalIdeal_of_ord_pos v hmb hb
  have hdiff : (⟨_, hmb⟩ : v.toValuationSubring) - ⟨_, hma⟩ ∈ maximalIdeal v.toValuationSubring :=
    Ideal.sub_mem _ hIb hIa
  have hval : ((⟨_, hmb⟩ : v.toValuationSubring) - ⟨_, hma⟩)
      = ⟨algebraMap K F (a - b), v.algebraMap_mem' _⟩ := by
    apply Subtype.ext
    show (J - algebraMap K F b) - (J - algebraMap K F a) = algebraMap K F (a - b)
    rw [map_sub]
    ring
  rw [hval] at hdiff
  exact ((mem_maximalIdeal _).mp hdiff) (isUnit_algebraMap v (sub_ne_zero.mpr hab))

theorem ord_sub_algebraMap_neg (v : Place K F) {J : F} (hJ : v.ord J < 0) (a : K) :
    v.ord (J - algebraMap K F a) < 0 := by
  by_contra h
  push Not at h
  have hJ0 : J ≠ 0 := ne_zero_of_ord_ne_zero v hJ.ne
  by_cases hg : J - algebraMap K F a = 0
  · have hJa : J = algebraMap K F a := sub_eq_zero.mp hg
    rcases eq_or_ne a 0 with rfl | ha
    · exact hJ0 (by simpa using hJa)
    · rw [hJa, ConstantReduction.ord_algebraMap v ha] at hJ
      exact lt_irrefl _ hJ
  · have hmem := v.mem_toValuationSubring_of_ord_nonneg_alt hg h
    have hJmem : J ∈ v.toValuationSubring := by
      have := add_mem hmem (v.algebraMap_mem' a)
      rwa [sub_add_cancel] at this
    have := ord_nonneg_of_mem v hJmem
    omega

theorem degree_eq_sum (D : Divisor K F) :
    Divisor.degree D = D.sum (fun v n => n * (v.deg : ℤ)) := by
  simp [Divisor.degree]

theorem exists_ord_pos [HasPrincipalDivisors K F] (hdeg : ∀ v : Place K F, v.deg = 1) {g : F}
    (hg : g ≠ 0) {w : Place K F} (hw : w.ord g < 0) : ∃ v : Place K F, 0 < v.ord g := by
  classical
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  by_contra hall
  push Not at hall
  have hsum : Divisor.degree D = ∑ v ∈ D.support, D v := by
    rw [degree_eq_sum]
    unfold Finsupp.sum
    exact Finset.sum_congr rfl (fun v _ => by simp [hdeg v])
  have hw' : w ∈ D.support := Finsupp.mem_support_iff.mpr (by rw [hD]; exact hw.ne)
  have hlt : ∑ v ∈ D.support, D v < 0 := by
    rw [← Finset.add_sum_erase _ _ hw']
    have h1 : D w < 0 := by rw [hD]; exact hw
    have h2 : ∑ v ∈ D.support.erase w, D v ≤ 0 :=
      Finset.sum_nonpos (fun v _ => by rw [hD]; exact hall v)
    linarith
  rw [← hsum, hdeg0] at hlt
  exact lt_irrefl _ hlt

end PlaceFacts

end P2MW

open AlgebraicCurve ModularCurve IsLocalRing P2MW

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N),
      R.IsGood → IsPlaceReductionModL A N R.placeMap →
    ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ R.integers, R.residue ⟨c • s l, h⟩ ≠ 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hdeg : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.deg = 1 :=
    fun P => deg_eq_one_modularFunctionFieldBar N P
  have hrat : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.IsRational :=
    fun P => (Place.isRational_iff_deg_eq_one P).mpr (hdeg P)

  set J : modularFunctionFieldBar N := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
    with hJdef
  have hJord : (cuspInftyBar N).ord J = -1 := ord_cuspInftyBar_coeffEmb_jq N
  have hJneg : (cuspInftyBar N).ord J < 0 := by rw [hJord]; norm_num

  set e : ℕ := embDegree N with hedef
  obtain ⟨a, hainj, hapow⟩ := exists_teichmueller p hp (e + 1)
  have hq2 : 2 ≤ p ^ (e + 1 + 1) := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (e + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  have hPex : ∀ i : Fin (e + 1), ∃ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      0 < P.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a i)) := by
    intro i
    have hneg := ord_sub_algebraMap_neg (cuspInftyBar N) hJneg (a i)
    exact exists_ord_pos hdeg (ne_zero_of_ord_ne_zero _ hneg.ne) hneg
  choose P hPord using hPex
  have hPne : ∀ i, P i ≠ cuspInftyBar N := by
    intro i h
    have h1 := hPord i
    rw [h] at h1
    have h2 := ord_sub_algebraMap_neg (cuspInftyBar N) hJneg (a i)
    omega

  have hkex : ∀ (l : Fin r) (i : Fin (e + 1)), ∃ k : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      (p : AlgebraicClosure ℚ) ∈ A.nonunits →
      (p : AlgebraicClosure ℚ) ^ k * (P i).evalAt (s l) ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ k * ((P i).evalAt (s l))⁻¹ ∈ A := by
    intro l i
    obtain ⟨k1, hk1⟩ := exists_pow_mul_mem p hp ((P i).evalAt (s l))
    obtain ⟨k2, hk2⟩ := exists_pow_mul_mem p hp ((P i).evalAt (s l))⁻¹
    exact ⟨max k1 k2, fun A hA =>
      ⟨pow_mul_mem_of_le A p (le_max_left _ _) (hk1 A hA),
       pow_mul_mem_of_le A p (le_max_right _ _) (hk2 A hA)⟩⟩
  choose k hk using hkex
  refine ⟨Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2), ?_⟩
  intro A hA R _hgood hspec l
  have hpA : (p : AlgebraicClosure ℚ) ∈ A.nonunits := hA

  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField A) p := ValuationSubring.residueField_charP_of_liesOverPrime A hp hA
  obtain ⟨hcl1, hcl2, -, -⟩ := IsPlaceReductionModL.coordinate_clauses N p hpN A hA R.placeMap hspec

  have hf0 : s l ≠ 0 := hs.1.ne_zero l
  have hfE : s l ∈ riemannRochSpace (embDivisor N) := by
    rw [← hs.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hford : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
      0 ≤ v.ord (s l) := by
    intro v hv
    rcases (mem_riemannRochSpace_iff.mp hfE) v with h | h
    · exact absurd h hf0
    · have h0 : (embDivisor N) v = 0 := by
        rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hv), smul_zero]
      rw [h0, neg_zero] at h
      exact h
  have hfcusp : -(e : ℤ) ≤ (cuspInftyBar N).ord (s l) := by
    rcases (mem_riemannRochSpace_iff.mp hfE) (cuspInftyBar N) with h | h
    · exact absurd h hf0
    · have h0 : (embDivisor N) (cuspInftyBar N) = (e : ℤ) := by
        rw [embDivisor, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      rw [h0] at h
      exact h

  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem (s l) hf0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : AlgebraicClosure ℚ) • s l, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]

  obtain ⟨D, hD, hDdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (c • s l) (smul_ne_zero hc0 hf0)
  have hDord : ∀ v, D v = v.ord (s l) := fun v => by rw [hD, ConstantReduction.ord_smul v hc0]
  have hD0 : D.sum (fun _ n => n) = 0 := by
    have : D.sum (fun _ n => n) = Divisor.degree D := by
      rw [degree_eq_sum]
      unfold Finsupp.sum
      exact Finset.sum_congr rfl (fun v _ => by simp [hdeg v])
    rw [this, hDdeg]

  have haA : ∀ i, a i ∈ A := fun i => teichmueller_root_mem A hq2 (hapow i)

  have hcl1i : ∀ i, 0 < (R.placeMap (P i)).ord
      ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
          modularFunctionFieldFullC (ResidueField A) N)
        - algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N)
            (IsLocalRing.residue A ⟨a i, haA i⟩)) :=
    fun i => hcl1 (P i) ⟨a i, haA i⟩ (hPord i)
  have hcuspole : (R.placeMap (cuspInftyBar N)).ord
      ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
          modularFunctionFieldFullC (ResidueField A) N)) < 0 :=
    hcl2 (cuspInftyBar N) (fun b => (ord_sub_algebraMap_neg (cuspInftyBar N) hJneg (b : AlgebraicClosure ℚ)).le)
  have hQinj : Function.Injective (fun i => R.placeMap (P i)) := by
    intro i j hij
    by_contra hne
    have h1 := hcl1i i
    have h2 := hcl1i j
    simp only at hij
    rw [hij] at h1
    have hreseq := eq_of_ord_sub_algebraMap_pos _ _ h1 h2
    have hu := isUnit_sub_of_pow_eq A hpA (e + 1) (hapow i) (hapow j)
      (fun h => hne (hainj h)) (haA i) (haA j)
    apply (mem_maximalIdeal _).mp _ hu
    rw [← residue_eq_zero_iff]
    have : (⟨a i - a j, sub_mem (haA i) (haA j)⟩ : A) = ⟨a i, haA i⟩ - ⟨a j, haA j⟩ := rfl
    rw [this, map_sub, hreseq, sub_self]
  have hQcusp : ∀ i, R.placeMap (P i) ≠ R.placeMap (cuspInftyBar N) := by
    intro i h
    have h1 := hcl1i i
    rw [h] at h1
    have hmem := mem_of_ord_pos _ h1
    have hJmem := add_mem hmem ((R.placeMap (cuspInftyBar N)).algebraMap_mem'
      (IsLocalRing.residue A ⟨a i, haA i⟩))
    rw [sub_add_cancel] at hJmem
    have := ord_nonneg_of_mem _ hJmem
    omega

  obtain ⟨i₀, hi₀⟩ := exists_mapDomain_apply_eq_zero R.placeMap D hD0 (cuspInftyBar N) e
      (by rw [hDord]; exact hfcusp) (fun v hv => by rw [hDord]; exact hford v hv)
      (fun i => R.placeMap (P i)) hQinj hQcusp (Nat.lt_succ_self e)
  have hord0 : (R.placeMap (P i₀)).ord (R.residue ⟨c • s l, hc⟩) = 0 := by
    rw [← R.mapDomain_placeMap ⟨c • s l, hc⟩ hres D hD]
    exact hi₀
  have hfib : ∀ w, R.placeMap w = R.placeMap (P i₀) → c • s l ∈ w.toValuationSubring := by
    intro w hw
    have hw' : w ≠ cuspInftyBar N := by
      rintro rfl
      exact hQcusp i₀ hw.symm
    exact w.mem_toValuationSubring_of_ord_nonneg_alt (smul_ne_zero hc0 hf0)
      (by rw [ConstantReduction.ord_smul w hc0]; exact hford w hw')
  obtain ⟨hvalA, hunit⟩ :=
    R.isUnit_evalAt_of_ord_eq_zero_of_hasPrincipalDivisors (hrat (P i₀)) hc hres hord0 hfib
  have hinvA := inv_mem_of_isUnit A hvalA hunit
  have hval0 : (P i₀).evalAt (c • s l) ≠ 0 := fun h0 =>
    hunit.ne_zero (Subtype.ext h0)

  have hfmem : s l ∈ (P i₀).toValuationSubring :=
    (P i₀).mem_toValuationSubring_of_ord_nonneg_alt hf0 (hford _ (hPne i₀))
  have heval : (P i₀).evalAt (c • s l) = c * (P i₀).evalAt (s l) := by
    rw [Algebra.smul_def, (P i₀).evalAt_mul_of_mem (hrat _) ((P i₀).algebraMap_mem' c) hfmem,
      (P i₀).evalAt_algebraMap_eq]
  set α := (P i₀).evalAt (s l) with hαdef
  have h1 : c * α ∈ A := heval ▸ hvalA
  have h2 : (c * α)⁻¹ ∈ A := heval ▸ hinvA
  have hcα0 : c * α ≠ 0 := heval ▸ hval0
  have hα0 : α ≠ 0 := fun h => hcα0 (by rw [h, mul_zero])

  have hkB : k l i₀ ≤ Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2) :=
    Finset.le_sup (f := fun li : Fin r × Fin (e + 1) => k li.1 li.2) (Finset.mem_univ (l, i₀))
  obtain ⟨hb1, hb2⟩ := hk l i₀ A hpA
  refine ⟨c, hc0, ?_, ?_, hc, hres⟩
  · have : (p : AlgebraicClosure ℚ) ^ (Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2)) * c
        = ((p : AlgebraicClosure ℚ) ^ (Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2)) * α⁻¹)
          * (c * α) := by
      field_simp
    rw [this]
    exact mul_mem (pow_mul_mem_of_le A p hkB hb2) h1
  · have : (p : AlgebraicClosure ℚ) ^ (Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2)) * c⁻¹
        = ((p : AlgebraicClosure ℚ) ^ (Finset.univ.sup (fun li : Fin r × Fin (e + 1) => k li.1 li.2)) * α)
          * (c * α)⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (pow_mul_mem_of_le A p hkB hb1) h2

end S_ModularCurve_exists_uniform_window_smul_mem_integers
end P2MW
export P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers (solution)
