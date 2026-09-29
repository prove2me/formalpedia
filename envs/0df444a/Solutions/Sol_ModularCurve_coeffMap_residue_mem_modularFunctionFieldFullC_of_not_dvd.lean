-- Prove2me | solution 1 for ModularCurve.coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3bc91a38-403c-5423-969e-93d00c09093e

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open ModularCurve IntermediateField Polynomial

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace W7F_ES9A_PORT

noncomputable section

open scoped Classical

def gen (R : Type*) [CommRing R] (i : ℕ) : LaurentSeries R :=
  qExpand R (i + 1) (jqModC R)

def divIdx (N : ℕ) : Finset ℕ := (Finset.range N).filter (fun i => i + 1 ∣ N)

lemma mem_divIdx {N i : ℕ} : i ∈ divIdx N ↔ i < N ∧ i + 1 ∣ N := by
  simp [divIdx]

private def _root_.W7F_ES9A_PORT.mono (R : Type*) [CommRing R] (N : ℕ) (e : ℕ → ℕ) : LaurentSeries R :=
  ∏ i ∈ divIdx N, gen R i ^ e i

p2m_export "W7F_ES9A_PORT" "mono"
lemma coeffMap_gen {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (i : ℕ) :
    coeffMap f (gen R i) = gen S i := by
  simp only [gen, coeffMap_qExpand, coeffMap_jqModC]

lemma coeffMap_mono {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ)
    (e : ℕ → ℕ) : coeffMap f (mono R N e) = mono S N e := by
  simp only [mono, map_prod, map_pow, coeffMap_gen]

lemma mono_add (R : Type*) [CommRing R] (N : ℕ) (e e' : ℕ → ℕ) :
    mono R N (e + e') = mono R N e * mono R N e' := by
  simp only [mono, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

lemma mono_zero (R : Type*) [CommRing R] (N : ℕ) : mono R N 0 = 1 := by
  simp [mono]

lemma mono_single (R : Type*) [CommRing R] (N : ℕ) {i : ℕ} (hi : i ∈ divIdx N) :
    mono R N (Pi.single i 1) = gen R i := by
  classical
  unfold mono
  rw [← Finset.mul_prod_erase _ _ hi]
  rw [Finset.prod_eq_one]
  · simp
  · intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hji]

lemma gen_zero (R : Type*) [CommRing R] : gen R 0 = jqModC R := by
  unfold gen
  rw [qExpand_congr (K := 1) (by norm_num) (jqModC R), qExpand_one_apply]

lemma gen_mem_fullC (K : Type*) [Field K] (N : ℕ) [NeZero N] {i : ℕ} (hi : i + 1 ∣ N) :
    gen K i ∈ modularFunctionFieldFullC K N :=
  jqModCd_mem_full K N hi

lemma mono_mem_fullC (K : Type*) [Field K] (N : ℕ) [NeZero N] (e : ℕ → ℕ) :
    mono K N e ∈ modularFunctionFieldFullC K N := by
  unfold mono
  refine prod_mem fun i hi => pow_mem (gen_mem_fullC K N (mem_divIdx.mp hi).2) _

section charzero

variable (L : Type*) [Field L] [Algebra ℚ L]

lemma coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    coeffEmb L (qExpand ℚ d jq) = qExpand L d (jqModC L) := by
  simp only [coeffEmb, coeffMap_qExpand, ← jqModC_rat, coeffMap_jqModC]

lemma coeffEmb_jq' : coeffEmb L jq = jqModC L := by
  simp only [coeffEmb, ← jqModC_rat, coeffMap_jqModC]

lemma gen_mem_baseChange (N : ℕ) [NeZero N] {i : ℕ} (hi : i + 1 ∣ N) :
    gen L i ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  have := coeffEmb_mem_laurentBaseChange L (jqd_mem_full N hi)
  rwa [coeffEmb_qExpand_jq] at this

lemma mono_mem_baseChange (N : ℕ) [NeZero N] (e : ℕ → ℕ) :
    mono L N e ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  unfold mono
  refine prod_mem fun i hi => pow_mem (gen_mem_baseChange L N (mem_divIdx.mp hi).2) _

lemma jqModC_mem_baseChange (N : ℕ) [NeZero N] :
    jqModC L ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
  rw [← gen_zero]; exact gen_mem_baseChange L N (one_dvd N)

end charzero

lemma coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) := by
  simp only [HahnSeries.C_apply, coeffMap_single]

lemma coeffMap_aeval {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (p : R[X]) :
    coeffMap f (aeval (jqModC R) p) = aeval (jqModC S) (p.map f) := by
  have h : (algebraMap S (LaurentSeries S)).comp f = (coeffMap f).comp
      (algebraMap R (LaurentSeries R)) := by
    apply RingHom.ext
    intro r
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
    exact (coeffMap_C f r).symm
  rw [Polynomial.map_aeval_eq_aeval_map h, coeffMap_jqModC]

lemma coeffMap_subtype_injective (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective (coeffMap A.subtype) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff n) h
  simpa [coeffMap_coeff] using this

lemma exists_scale (A : ValuationSubring (AlgebraicClosure ℚ))
    (s : Finset (AlgebraicClosure ℚ)) (hs : ∃ x ∈ s, x ≠ 0) :
    ∃ a ∈ s, a ≠ 0 ∧ ∀ b ∈ s, a⁻¹ * b ∈ A := by
  classical
  set s' := s.filter (fun x => x ≠ 0) with hs'
  have hne : s'.Nonempty := by
    obtain ⟨x, hx, hx0⟩ := hs
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s' (fun x => A.valuation x) hne
  obtain ⟨has, ha0⟩ := Finset.mem_filter.mp ha
  refine ⟨a, has, ha0, fun b hb => ?_⟩
  by_cases hb0 : b = 0
  · simp [hb0]
  have hle : A.valuation b ≤ A.valuation a := hmax b (Finset.mem_filter.mpr ⟨hb, hb0⟩)
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hva : A.valuation a ≠ 0 := by
    intro h; exact ha0 ((Valuation.zero_iff _).mp h)
  calc (A.valuation a)⁻¹ * A.valuation b ≤ (A.valuation a)⁻¹ * A.valuation a :=
        mul_le_mul_right hle _
    _ = 1 := inv_mul_cancel₀ hva

section transfer

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "kA" => IsLocalRing.ResidueField A

theorem transfer {ι : Type*} [Fintype ι] (x : ι → LaurentSeries A) (c : ι → ℚbar[X])
    (hc : ∃ i, c i ≠ 0)
    (hrel : ∑ i, aeval (jqModC ℚbar) (c i) * coeffMap A.subtype (x i) = 0) :
    ∃ C : ι → kA[X], (∃ i, C i ≠ 0) ∧
      ∑ i, aeval (jqModC kA) (C i) * coeffMap (IsLocalRing.residue A) (x i) = 0 := by
  classical

  set s : Finset ℚbar := Finset.univ.biUnion (fun i => (c i).coeffs) with hs_def
  have hs : ∃ a ∈ s, a ≠ 0 := by
    obtain ⟨i, hi⟩ := hc
    obtain ⟨n, hn⟩ : ∃ n, (c i).coeff n ≠ 0 := by
      by_contra h
      push Not at h
      exact hi (Polynomial.ext (by simpa using h))
    exact ⟨(c i).coeff n, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, coeff_mem_coeffs hn⟩, hn⟩
  obtain ⟨a, has, ha0, hscale⟩ := exists_scale A s hs

  have hcoeffA : ∀ i n, a⁻¹ * (c i).coeff n ∈ A := by
    intro i n
    by_cases h0 : (c i).coeff n = 0
    · simp [h0]
    exact hscale _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, coeff_mem_coeffs h0⟩)
  have hsub : ∀ i, (↑(Polynomial.C a⁻¹ * c i).coeffs : Set ℚbar) ⊆ (A.toSubring : Set ℚbar) := by
    intro i z hz
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp (Finset.mem_coe.mp hz)
    rw [Polynomial.coeff_C_mul]
    exact hcoeffA i n
  set Cp : ι → (A : Type _)[X] := fun i => (Polynomial.C a⁻¹ * c i).toSubring A.toSubring (hsub i)
    with hCp_def
  have hCp_map : ∀ i, (Cp i).map A.subtype = Polynomial.C a⁻¹ * c i := fun i =>
    Polynomial.map_toSubring _ _ _

  have hrelA : ∑ i, aeval (jqModC A) (Cp i) * x i = 0 := by
    apply coeffMap_subtype_injective A
    rw [map_sum, map_zero]
    simp only [map_mul, coeffMap_aeval, hCp_map, map_mul, Polynomial.aeval_C, mul_assoc]
    rw [← Finset.mul_sum, hrel, mul_zero]
  refine ⟨fun i => (Cp i).map (IsLocalRing.residue A), ?_, ?_⟩
  ·
    obtain ⟨i₀, -, hi₀⟩ := Finset.mem_biUnion.mp has
    obtain ⟨n₀, -, hn₀⟩ := mem_coeffs_iff.mp hi₀
    refine ⟨i₀, fun h => ?_⟩
    have h1 : (Cp i₀).coeff n₀ = 1 := by
      apply Subtype.val_injective
      have := congrArg (fun p : ℚbar[X] => p.coeff n₀) (hCp_map i₀)
      simp only [Polynomial.coeff_map] at this
      change ((Cp i₀).coeff n₀ : ℚbar) = _ at this
      rw [this, Polynomial.coeff_C_mul, ← hn₀, inv_mul_cancel₀ ha0]
      rfl
    have := congrArg (fun p : kA[X] => p.coeff n₀) h
    simp only [Polynomial.coeff_map, h1, map_one, Polynomial.coeff_zero] at this
    exact one_ne_zero this
  · have := congrArg (coeffMap (IsLocalRing.residue A)) hrelA
    rw [map_sum, map_zero] at this
    simpa only [map_mul, coeffMap_aeval] using this

end transfer

lemma dedekindPsi_pos' (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    simp [Nat.mem_divisors, NeZero.ne N]
  calc 0 < N / 1 := by simpa using Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ ∑ d ∈ N.divisors.filter Squarefree, N / d :=
        Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

section charell

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev jE : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩

abbrev K₀ : IntermediateField K ↥(modularFunctionFieldFullC K N) := K⟮jE K N⟯

def monoE (e : ℕ → ℕ) : ↥(modularFunctionFieldFullC K N) := ⟨mono K N e, mono_mem_fullC K N e⟩

@[scoped simp] lemma coe_monoE (e : ℕ → ℕ) : (monoE K N e : LaurentSeries K) = mono K N e := rfl

lemma aeval_jqModC_mem_fullC (p : K[X]) : aeval (jqModC K) p ∈ modularFunctionFieldFullC K N := by
  rw [show jqModC K = (modularFunctionFieldFullC K N).val (jE K N) from rfl, aeval_algHom_apply]
  exact SetLike.coe_mem _

lemma val_aeval_jE (p : K[X]) :
    ((aeval (jE K N) p : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) = aeval (jqModC K) p := by
  rw [show jqModC K = (modularFunctionFieldFullC K N).val (jE K N) from rfl, aeval_algHom_apply]
  rfl

theorem indep_poly {ι : Type*} [Fintype ι] (v : ι → ↥(modularFunctionFieldFullC K N))
    (hv : LinearIndependent (K₀ K N) v) (C : ι → K[X])
    (hC : ∑ i, aeval (jqModC K) (C i) * (v i : LaurentSeries K) = 0) : ∀ i, C i = 0 := by
  have hmem : ∀ i, aeval (jE K N) (C i) ∈ K₀ K N := fun i =>
    algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)
  set g : ι → K₀ K N := fun i => ⟨aeval (jE K N) (C i), hmem i⟩ with hg_def
  have hsum : ∑ i, g i • v i = 0 := by
    apply Subtype.val_injective
    change (modularFunctionFieldFullC K N).val (∑ i, g i • v i) =
      ((0 : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K)
    rw [map_sum, ZeroMemClass.coe_zero, ← hC]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
    change ((aeval (jE K N) (C i) : ↥(modularFunctionFieldFullC K N)) : LaurentSeries K) * _ = _
    rw [val_aeval_jE]
    rfl
  intro i
  have hgi : g i = 0 := Fintype.linearIndependent_iff.mp hv g hsum i
  have h1 : (aeval (jE K N) (C i) : ↥(modularFunctionFieldFullC K N)) = 0 :=
    congrArg Subtype.val hgi
  have h2 : aeval (jqModC K) (C i) = 0 := by
    rw [← val_aeval_jE K N, h1]; rfl
  by_contra hne
  exact transcendental_jqModC K ⟨C i, hne, h2⟩

variable {K N} in
lemma monoE_add (e e' : ℕ → ℕ) : monoE K N (e + e') = monoE K N e * monoE K N e' := by
  apply Subtype.val_injective
  simp [mono_add]

lemma adjoin_gens_eq_top :
    IntermediateField.adjoin K
      (Set.range fun i : divIdx N => monoE K N (Pi.single i.1 1)) = ⊤ := by
  apply lift_injective (modularFunctionFieldFullC K N)
  erw [lift_adjoin K (modularFunctionFieldFullC K N), lift_top K (modularFunctionFieldFullC K N)]
  apply le_antisymm
  · erw [← lift_adjoin K (modularFunctionFieldFullC K N)]; exact lift_le _
  · unfold modularFunctionFieldFullC
    apply adjoin.mono
    rintro x ⟨d, hd, hdN, rfl⟩
    have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd.ne
    have hdle : d ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdN
    have hmem : d - 1 ∈ divIdx N := by
      rw [mem_divIdx, Nat.sub_add_cancel hd1]; exact ⟨by omega, hdN⟩
    refine ⟨monoE K N (Pi.single (d - 1) 1), ⟨⟨d - 1, hmem⟩, rfl⟩, ?_⟩
    rw [coe_monoE, mono_single K N hmem, gen]
    exact qExpand_congr (Nat.sub_add_cancel hd1) _

theorem span_monoE_eq_top (hN : (N : K) ≠ 0) :
    Submodule.span (K₀ K N) (Set.range (monoE K N)) = ⊤ := by
  classical
  haveI : Module.Finite (K₀ K N) ↥(modularFunctionFieldFullC K N) :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN]
      exact dedekindPsi_pos' N)
  haveI : Algebra.IsAlgebraic (K₀ K N) ↥(modularFunctionFieldFullC K N) :=
    Algebra.IsAlgebraic.of_finite _ _
  set S : Set ↥(modularFunctionFieldFullC K N) :=
    Set.range fun i : divIdx N => monoE K N (Pi.single i.1 1) with hS_def

  have hadjK₀ : IntermediateField.adjoin (K₀ K N) S = ⊤ := by
    apply restrictScalars_injective K
    rw [restrictScalars_top]
    apply top_le_iff.mp
    rw [← adjoin_gens_eq_top K N]
    exact adjoin_le_iff.mpr (subset_adjoin (K₀ K N) S)

  have halg : Algebra.adjoin (K₀ K N) S = ⊤ := by
    rw [← adjoin_toSubalgebra_of_isAlgebraic (fun x _ => Algebra.IsAlgebraic.isAlgebraic x), hadjK₀,
      top_toSubalgebra]

  set M : Submodule (K₀ K N) ↥(modularFunctionFieldFullC K N) :=
    Submodule.span (K₀ K N) (Set.range (monoE K N)) with hM_def
  have hmul : ∀ x y, x ∈ M → y ∈ M → x * y ∈ M := by
    intro x y hx hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [hM_def, Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨a, ⟨e, rfl⟩, b, ⟨e', rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨e + e', monoE_add e e'⟩
  have hone : (1 : ↥(modularFunctionFieldFullC K N)) ∈ M :=
    Submodule.subset_span ⟨0, by apply Subtype.val_injective; simp [mono_zero]⟩
  let Alg : Subalgebra (K₀ K N) ↥(modularFunctionFieldFullC K N) :=
    { carrier := M
      mul_mem' := fun hx hy => hmul _ _ hx hy
      add_mem' := fun hx hy => M.add_mem hx hy
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]; exact M.smul_mem r hone }
  have hle : Algebra.adjoin (K₀ K N) S ≤ Alg := by
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Pi.single i.1 1, rfl⟩
  rw [halg] at hle
  exact eq_top_iff.mpr fun x _ => hle Algebra.mem_top

theorem exists_indep_monomials (hN : (N : K) ≠ 0) :
    ∃ e : Fin (dedekindPsi N) → ℕ → ℕ, LinearIndependent (K₀ K N) (fun i => monoE K N (e i)) := by
  classical
  haveI : Module.Finite (K₀ K N) ↥(modularFunctionFieldFullC K N) :=
    Module.finite_of_finrank_pos (by
      rw [finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN]
      exact dedekindPsi_pos' N)
  obtain ⟨b, hb_sub, hb_span, hb_li⟩ :=
    exists_linearIndependent (K₀ K N) (Set.range (monoE K N))
  haveI : Fintype b := (hb_li.setFinite).fintype
  have hcard : Fintype.card b = dedekindPsi N := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hb_li, Set.finrank, Subtype.range_coe,
      hb_span, span_monoE_eq_top K N hN, finrank_top,
      finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN]
  have he : ∀ x : b, ∃ e : ℕ → ℕ, monoE K N e = x := fun x => hb_sub x.2
  choose e he using he
  refine ⟨fun i => e ((Fintype.equivFinOfCardEq hcard).symm i), ?_⟩
  have : (fun i => monoE K N (e ((Fintype.equivFinOfCardEq hcard).symm i))) =
      (fun x : b => (x : ↥(modularFunctionFieldFullC K N))) ∘ (Fintype.equivFinOfCardEq hcard).symm := by
    funext i; simp [he]
  rw [this]
  exact hb_li.comp _ (Equiv.injective _)

end charell

section charzero

local notation "ℚbar" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N]

abbrev L₀ : IntermediateField ℚbar ↥(modularFunctionFieldBar N) :=
  (ℚbar⟮jqModC ℚbar⟯).comap (modularFunctionFieldBar N).val

theorem finrank_L₀ : Module.finrank (L₀ N) ↥(modularFunctionFieldBar N) = dedekindPsi N := by
  have h := finrank_comap (ℚbar⟮jqModC ℚbar⟯) (modularFunctionFieldBar N).val
  rw [fieldRange_val] at h
  refine h.trans ?_
  have h1 := relfinrank_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N
  rw [coeffEmb_jq'] at h1
  rw [show modularFunctionFieldBar N = laurentBaseChange ℚbar (modularFunctionFieldFull N) from rfl, h1,
    relfinrank_full_eq_dedekindPsi]

theorem clear_denominators {ι : Type*} [Fintype ι] (g : ι → L₀ N) :
    ∃ D : ℚbar[X], D ≠ 0 ∧ ∃ c : ι → ℚbar[X],
      (∀ i, aeval (jqModC ℚbar) (c i) =
        aeval (jqModC ℚbar) D * ((g i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar)) ∧
      (∀ i, c i = 0 → g i = 0) := by
  classical
  have hg : ∀ i, ∃ rs : ℚbar[X] × ℚbar[X], aeval (jqModC ℚbar) rs.2 ≠ 0 ∧
      ((g i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar) =
        aeval (jqModC ℚbar) rs.1 / aeval (jqModC ℚbar) rs.2 := by
    intro i
    have hmem : (modularFunctionFieldBar N).val (g i) ∈ ℚbar⟮jqModC ℚbar⟯ := (g i).2
    rw [mem_adjoin_simple_iff] at hmem
    obtain ⟨r, s, hrs⟩ := hmem
    by_cases hs : aeval (jqModC ℚbar) s = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      change (modularFunctionFieldBar N).val (g i) = _
      rw [hrs, hs, div_zero]; simp
    · exact ⟨(r, s), hs, hrs⟩
  choose rs hrs0 hrs using hg
  set D : ℚbar[X] := ∏ i, (rs i).2 with hD_def
  have hD : aeval (jqModC ℚbar) D = ∏ i, aeval (jqModC ℚbar) (rs i).2 := map_prod _ _ _
  have hDne : aeval (jqModC ℚbar) D ≠ 0 := by
    rw [hD]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hrs0 i
  refine ⟨D, fun h => hDne (by rw [h, map_zero]),
    fun i => (rs i).1 * ∏ j ∈ Finset.univ.erase i, (rs j).2, ?_, ?_⟩
  · intro i
    have hgi : ((g i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar) =
        aeval (jqModC ℚbar) (rs i).1 / aeval (jqModC ℚbar) (rs i).2 := hrs i
    have hs0 := hrs0 i
    rw [map_mul, map_prod, hgi, hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    field_simp
  · intro i hc
    have h1 : (rs i).1 = 0 := by
      rcases mul_eq_zero.mp hc with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨j, -, hj⟩ := h
        exact hrs0 j (by rw [hj, map_zero])
    apply Subtype.val_injective
    apply Subtype.val_injective
    change ((g i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar) =
      ((0 : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar)
    rw [hrs i, h1, map_zero, zero_div]
    rfl

lemma val_sum_smul {ι : Type*} [Fintype ι] (g : ι → L₀ N) (v : ι → ↥(modularFunctionFieldBar N)) :
    ((∑ i, g i • v i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar) =
      ∑ i, ((g i : ↥(modularFunctionFieldBar N)) : LaurentSeries ℚbar) * (v i : LaurentSeries ℚbar) := by
  change (modularFunctionFieldBar N).val (∑ i, g i • v i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
  rfl

theorem linearIndependent_of_poly {ι : Type*} [Fintype ι] (v : ι → ↥(modularFunctionFieldBar N))
    (hv : ∀ c : ι → ℚbar[X],
      ∑ i, aeval (jqModC ℚbar) (c i) * (v i : LaurentSeries ℚbar) = 0 → ∀ i, c i = 0) :
    LinearIndependent (L₀ N) v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  obtain ⟨D, -, c, hc, hc0⟩ := clear_denominators N g
  have hrel : ∑ i, aeval (jqModC ℚbar) (c i) * (v i : LaurentSeries ℚbar) = 0 := by
    simp_rw [hc, mul_assoc, ← Finset.mul_sum]
    rw [← val_sum_smul, hg, ZeroMemClass.coe_zero, mul_zero]
  intro i
  exact hc0 i (hv c hrel i)

theorem exists_poly_relation {ι : Type*} [Fintype ι] (v : ι → ↥(modularFunctionFieldBar N))
    (hspan : Submodule.span (L₀ N) (Set.range v) = ⊤) (y : ↥(modularFunctionFieldBar N)) :
    ∃ D : ℚbar[X], D ≠ 0 ∧ ∃ c : ι → ℚbar[X],
      aeval (jqModC ℚbar) D * (y : LaurentSeries ℚbar) =
        ∑ i, aeval (jqModC ℚbar) (c i) * (v i : LaurentSeries ℚbar) := by
  have hy : y ∈ Submodule.span (L₀ N) (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  obtain ⟨D, hD, c, hc, -⟩ := clear_denominators N g
  refine ⟨D, hD, c, ?_⟩
  simp_rw [hc, mul_assoc, ← Finset.mul_sum]
  rw [← val_sum_smul, hg]

end charzero

section main

local notation "ℚbar" => AlgebraicClosure ℚ

theorem main (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime ℓ) (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    coeffMap (IsLocalRing.residue A) y ∈
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N := by
  classical
  set k := IsLocalRing.ResidueField A with hk

  have hℓk : ((ℓ : ℕ) : k) = 0 := by
    have h1 : ((ℓ : A) : ℚbar) ∈ A.nonunits := by first | simpa using hA | (have h_1 := hA; simp at h_1; exact h_1) | (have h_1 := hA; simp at h_1 ⊢; exact h_1) | exact (hA)
    have h2 : (ℓ : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp h1
    have h3 : IsLocalRing.residue A (ℓ : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
    simpa using h3
  haveI : CharP k ℓ := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hℓk
  have hNk : (N : k) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff k ℓ N).mp h)

  obtain ⟨e, he⟩ := exists_indep_monomials k N hNk

  let v₀ : Fin (dedekindPsi N) → ↥(modularFunctionFieldBar N) :=
    fun i => ⟨mono ℚbar N (e i), mono_mem_baseChange ℚbar N (e i)⟩
  have hpoly : ∀ c : Fin (dedekindPsi N) → ℚbar[X],
      ∑ i, aeval (jqModC ℚbar) (c i) * (v₀ i : LaurentSeries ℚbar) = 0 → ∀ i, c i = 0 := by
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨C, ⟨i₀, hi₀⟩, hC⟩ := transfer A (fun i => mono A N (e i)) c hne
      (by simpa only [coeffMap_mono] using hc)
    simp only [coeffMap_mono] at hC
    exact hi₀ (indep_poly k N _ he C (by simpa only [coe_monoE] using hC) i₀)
  have hli : LinearIndependent (L₀ N) v₀ := linearIndependent_of_poly N v₀ hpoly
  have hspan : Submodule.span (L₀ N) (Set.range v₀) = ⊤ := by
    haveI : Nonempty (Fin (dedekindPsi N)) := ⟨⟨0, dedekindPsi_pos' N⟩⟩
    exact hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_L₀])

  obtain ⟨D, hD, c, hrel⟩ := exists_poly_relation N v₀ hspan ⟨coeffMap A.subtype y, hy⟩

  obtain ⟨C, hCne, hC⟩ := transfer A
    (fun o : Option (Fin (dedekindPsi N)) => o.elim y (fun i => mono A N (e i)))
    (fun o => o.elim D (fun i => - c i)) ⟨none, hD⟩ (by
      rw [Fintype.sum_option]
      simp only [Option.elim, coeffMap_mono, map_neg, neg_mul, Finset.sum_neg_distrib]
      change aeval (jqModC ℚbar) D * coeffMap A.subtype y +
        -∑ i, aeval (jqModC ℚbar) (c i) * (v₀ i : LaurentSeries ℚbar) = 0
      rw [← hrel]; ring)
  rw [Fintype.sum_option] at hC
  simp only [Option.elim, coeffMap_mono] at hC
  by_cases h0 : C none = 0
  ·
    exfalso
    rw [h0, map_zero, zero_mul, zero_add] at hC
    have hall := indep_poly k N _ he (fun i => C (some i)) (by simpa only [coe_monoE] using hC)
    obtain ⟨o, ho⟩ := hCne
    cases o with
    | none => exact ho h0
    | some i => exact ho (hall i)
  ·
    have hCj : aeval (jqModC k) (C none) ≠ 0 := fun h =>
      transcendental_jqModC k ⟨C none, h0, h⟩
    have hyeq : coeffMap (IsLocalRing.residue A) y =
        -((aeval (jqModC k) (C none))⁻¹ *
          ∑ i, aeval (jqModC k) (C (some i)) * mono k N (e i)) := by
      have h1 := eq_neg_of_add_eq_zero_left hC
      calc coeffMap (IsLocalRing.residue A) y
          = (aeval (jqModC k) (C none))⁻¹ *
              (aeval (jqModC k) (C none) * coeffMap (IsLocalRing.residue A) y) := by
            rw [← mul_assoc, inv_mul_cancel₀ hCj, one_mul]
        _ = _ := by rw [h1, mul_neg]
    rw [hyeq]
    refine neg_mem (mul_mem (inv_mem (aeval_jqModC_mem_fullC k N _))
      (sum_mem fun i _ => mul_mem (aeval_jqModC_mem_fullC k N _) (mono_mem_fullC k N (e i))))

end main

end

end W7F_ES9A_PORT
p2m_reactivate "P2MW.S_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd.W7F_ES9A_PORT"

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) (y : LaurentSeries A)
    (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N) :
    ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
      ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N :=
  W7F_ES9A_PORT.main N hℓN A hA y hy

end S_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_coeffMap_residue_mem_modularFunctionFieldFullC_of_not_dvd (solution)
