-- Prove2me | solution 1 for ModularCurve.exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6a51d9a2-dba1-5074-b5c8-0537bed17312

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical MatrixGroups
p2m_open "IntermediateField AlgebraicCurve ModularCurve~order_qExpand~order_jqModC CongruenceSubgroup"

namespace GaussFixedByCofactorAL

section Orders

variable (K : Type*) [Field K]

theorem coeff_order_ne_zero' {x : LaurentSeries K} (hx : x ≠ 0) : x.coeff x.order ≠ 0 :=
  fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

theorem order_jqModC : (jqModC K).order = -1 := by
  have h1 : (jqModC K).coeff (-1) ≠ 0 := by
    rw [coeff_jqModC_neg_one]; exact one_ne_zero
  have hne : jqModC K ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push Not at hlt
  exact coeff_order_ne_zero' K hne (coeff_jqModC_of_lt K hlt)

variable (N : ℕ) [NeZero N]

theorem order_qExpand {x : LaurentSeries K} (hx : x ≠ 0) :
    (qExpand K N x).order = (N : ℤ) * x.order := by
  have hq0 : qExpand K N x ≠ 0 :=
    fun h => hx (qExpand_injective (R := K) (N := N) (by rw [h, map_zero]))
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [qExpand_coeff_mul]; exact coeff_order_ne_zero' K hx
  · by_contra hlt
    push Not at hlt
    have hc := coeff_order_ne_zero' K hq0
    by_cases hdvd : (N : ℤ) ∣ (qExpand K N x).order
    · obtain ⟨k, hk⟩ := hdvd
      rw [hk, qExpand_coeff_mul] at hc
      have hle := HahnSeries.order_le_of_coeff_ne_zero hc
      rw [hk] at hlt
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      nlinarith
    · exact hc (qExpand_coeff_of_not_dvd N x hdvd)

theorem jqNModC_ne_zero : jqNModC K N ≠ 0 := by
  intro h
  rw [jqNModC] at h
  exact jqModC_ne_zero_of_nontrivial K (qExpand_injective (R := K) (N := N) (by rw [h, map_zero]))

theorem order_jqNModC : (jqNModC K N).order = -(N : ℤ) := by
  rw [jqNModC, order_qExpand K N (jqModC_ne_zero_of_nontrivial K), order_jqModC, mul_neg, mul_one]

theorem pow_ne_jqNModC (q : ℕ) [Fact q.Prime] (hqN : ¬ q ∣ N) (z : LaurentSeries K) :
    z ^ q ≠ jqNModC K N := by
  intro h
  by_cases hz : z = 0
  · rw [hz, zero_pow (Fact.out : q.Prime).ne_zero] at h
    exact jqNModC_ne_zero K N h.symm
  · have h1 : (z ^ q).order = (jqNModC K N).order := by rw [h]
    rw [HahnSeries.order_pow, order_jqNModC, nsmul_eq_mul] at h1
    have h2 : (q : ℤ) ∣ (N : ℤ) := ⟨-z.order, by linear_combination h1⟩
    exact hqN (Int.natCast_dvd_natCast.mp h2)

theorem transcendental_jqNModC : Transcendental K (jqNModC K N) := by
  intro halg
  have h : IsAlgebraic K (qExpandAlgHomC K N (jqModC K)) := by
    rw [qExpandAlgHomC_apply]; exact halg
  exact ModularCurve.transcendental_jqModC K
    ((isAlgebraic_algHom_iff (qExpandAlgHomC K N) (qExpand_injective (R := K) (N := N))).mp h)

theorem transcendental_of_coe {F : IntermediateField K (LaurentSeries K)} (x : F)
    (h : Transcendental K (x : LaurentSeries K)) : Transcendental K x :=
  fun halg => h (halg.algHom F.val)

end Orders

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]

theorem mem_comap_iff (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : F) :
    x ∈ R.integers.comap (w : F →+* F) ↔ w x ∈ R.integers := Iff.rfl

def comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers.comap (w : F →+* F) →+* R.integers :=
  (w : F →+* F).restrict _ _ (fun _ hx => (mem_comap_iff A R w _).mp hx)

@[scoped simp] theorem coe_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : (comapHom A R w x : F) = w x := rfl

def symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    R.integers →+* R.integers.comap (w : F →+* F) :=
  (w.symm : F →+* F).restrict _ _ (fun x hx => by
    rw [mem_comap_iff]
    change w (w.symm x) ∈ R.integers
    rw [AlgEquiv.apply_symm_apply]; exact hx)

@[scoped simp] theorem coe_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers) : (symmHom A R w x : F) = w.symm x := rfl

theorem comapHom_symmHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) (x : R.integers) :
    comapHom A R w (symmHom A R w x) = x :=
  Subtype.ext (by simp)

theorem symmHom_comapHom (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (x : R.integers.comap (w : F →+* F)) : symmHom A R w (comapHom A R w x) = x :=
  Subtype.ext (by simp)

def transport (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) : RegularProlongation A F Fb where
  integers := R.integers.comap (w : F →+* F)
  residue := R.residue.comp (comapHom A R w)
  algebraMap_mem_iff x := by
    rw [mem_comap_iff, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective z := by
    obtain ⟨f, hf⟩ := R.residue_surjective z
    exact ⟨symmHom A R w f, by rw [RingHom.comp_apply, comapHom_symmHom, hf]⟩
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, not_iff_not]
    constructor
    · intro hu; simpa [symmHom_comapHom] using hu.map (symmHom A R w)
    · intro hu; exact hu.map (comapHom A R w)
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (by simp)
  exists_smul_mem f hf := by
    have hwf : w f ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hf
    obtain ⟨c, hc, hne⟩ := R.exists_smul_mem (w f) hwf
    have hmem : c • f ∈ R.integers.comap (w : F →+* F) := by
      rw [mem_comap_iff, map_smul]; exact hc
    refine ⟨c, hmem, ?_⟩
    rw [RingHom.comp_apply]
    have h : comapHom A R w ⟨c • f, hmem⟩ = ⟨c • w f, hc⟩ := Subtype.ext (by simp)
    rwa [h]

@[scoped simp] theorem transport_integers (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) :
    (transport A R w).integers = R.integers.comap (w : F →+* F) := rfl

theorem transport_residue_apply (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F)
    (f : F) (h₁ : f ∈ (transport A R w).integers) (h₀ : w f ∈ R.integers) :
    (transport A R w).residue ⟨f, h₁⟩ = R.residue ⟨w f, h₀⟩ := rfl

end Transport

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (q : ℕ) [Fact q.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A

local notation "EE" => laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * q))

local notation "Fb" => xHFunctionFieldC (IsLocalRing.ResidueField A) M H

set_option maxHeartbeats 6400000 in

theorem main (hqM : ¬ q ∣ M) (hA : A.LiesOverPrime q)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (w : EE ≃ₐ[ℚ̄] EE) (J : EE) (hJ : (J : LaurentSeries ℚ̄) = jqModC ℚ̄)
    (hwJ : ((w J : EE) : LaurentSeries ℚ̄) = jqNModC ℚ̄ N) (f : EE) :
    (∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) ↔
    (∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        ((w f : EE) : LaurentSeries ℚ̄) * coeffMap A.subtype y = coeffMap A.subtype x) := by
  obtain ⟨R, ω, -, -, h1, h1', -, -, -, h4, h5⟩ :=
    ModularCurve.exists_regularProlongation_pair_xHTopFunctionFieldC_eq_or_eq_of_not_dvd M H hqM A hA

  let P : RegularProlongation A EE Fb := transport A (R 0) w

  obtain ⟨hj, h40, h41, -, -⟩ := h4 J hJ

  have hwJ' : ((w J : EE) : LaurentSeries ℚ̄) = coeffMap A.subtype (jqNModC A N) := by
    rw [hwJ, coeffMap_jqNModC]
  have hmemE : coeffMap A.subtype (jqNModC A N) ∈ (EE) := by
    rw [← hwJ']; exact (w J).2
  obtain ⟨hint, hres⟩ := h1' (jqNModC A N) hmemE
  have hwJeq : w J = ⟨coeffMap A.subtype (jqNModC A N), hmemE⟩ := Subtype.ext hwJ'
  have hwJmem : w J ∈ (R 0).integers := by rw [hwJeq]; exact hint
  have hJP : J ∈ P.integers := (mem_comap_iff A (R 0) w J).mpr hwJmem

  have hresP : ((P.residue ⟨J, hJP⟩ : Fb) : LaurentSeries kk) = jqNModC kk N := by
    have h' : P.residue ⟨J, hJP⟩ = (R 0).residue ⟨w J, hwJmem⟩ :=
      transport_residue_apply A (R 0) w J hJP hwJmem
    have h'' : (⟨w J, hwJmem⟩ : (R 0).integers) =
        ⟨⟨coeffMap A.subtype (jqNModC A N), hmemE⟩, hint⟩ := Subtype.ext hwJeq
    rw [h', h'', hres, coeffMap_jqNModC]

  have htrP : Transcendental kk (P.residue ⟨J, hJP⟩) :=
    transcendental_of_coe kk _ (by rw [hresP]; exact transcendental_jqNModC kk N)
  have htr0 : Transcendental kk ((R 0).residue ⟨J, hj 0⟩) :=
    transcendental_of_coe kk _ (by rw [h40]; exact ModularCurve.transcendental_jqModC kk)

  have hagree : ∀ e ∈ IntermediateField.adjoin ℚ̄ ({J} : Set EE),
      e ∈ P.integers ↔ e ∈ (R 0).integers := fun e he =>
    AlgebraicCurve.RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
      A P (R 0) J hJP (hj 0) htrP htr0 e he

  have hV0 : P.integers = (R 0).integers := by
    rcases h5 J hJ P.integers hagree with h | h
    · exact h
    · exfalso

      set c : Fb := (R 0).residue ⟨J, hj 0⟩ with hc
      have h1c : (R 1).residue ⟨J, hj 1⟩ = c ^ q := by
        apply Subtype.ext
        rw [h41]
        show jqModC kk ^ q = ((c ^ q : Fb) : LaurentSeries kk)
        rw [SubmonoidClass.coe_pow, hc, h40]
      obtain ⟨t, ht⟩ := (R 1).residue_surjective c
      have hker : (⟨J, hj 1⟩ : (R 1).integers) - t ^ q ∈ RingHom.ker (R 1).residue := by
        rw [RingHom.mem_ker, map_sub, map_pow, ht, h1c, sub_self]
      rw [(R 1).ker_residue] at hker
      have hnu1 : ((J : EE) - (t : EE) ^ q) ∈ (R 1).integers.nonunits := by
        have h' := (ValuationSubring.coe_mem_nonunits_iff (A := (R 1).integers)
          (a := (⟨J, hj 1⟩ : (R 1).integers) - t ^ q)).mpr hker
        simpa using h'
      have hnu : ((J : EE) - (t : EE) ^ q) ∈ P.integers.nonunits := by
        have key : ∀ V : ValuationSubring EE, (R 1).integers = V →
            ((J : EE) - (t : EE) ^ q) ∈ V.nonunits := by
          rintro V rfl; exact hnu1
        exact key _ h.symm
      have htP : (t : EE) ∈ P.integers := by rw [h]; exact t.2
      have hdiff : (J : EE) - (t : EE) ^ q ∈ P.integers := sub_mem hJP (pow_mem htP q)
      have hker' : (⟨(J : EE) - (t : EE) ^ q, hdiff⟩ : P.integers) ∈
          IsLocalRing.maximalIdeal P.integers :=
        (ValuationSubring.coe_mem_nonunits_iff).mp hnu
      rw [← P.ker_residue, RingHom.mem_ker] at hker'
      have heq : P.residue ⟨J, hJP⟩ = (P.residue ⟨(t : EE), htP⟩) ^ q := by
        have h' : (⟨(J : EE) - (t : EE) ^ q, hdiff⟩ : P.integers) =
            ⟨J, hJP⟩ - ⟨(t : EE), htP⟩ ^ q := Subtype.ext (by simp)
        rw [h', map_sub, map_pow, sub_eq_zero] at hker'
        exact hker'
      have hser := congrArg (fun z : Fb => (z : LaurentSeries kk)) heq
      simp only [SubmonoidClass.coe_pow] at hser
      rw [hresP] at hser
      exact pow_ne_jqNModC kk N q hqN _ hser.symm

  have key : f ∈ P.integers ↔ w f ∈ (R 0).integers := mem_comap_iff A (R 0) w f
  rw [hV0, h1 f, h1 (w f)] at key
  exact key

end Main

end GaussFixedByCofactorAL
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd.GaussFixedByCofactorAL"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd.GaussFixedByCofactorAL"

open GaussFixedByCofactorAL in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {q : ℕ} [Fact q.Prime] (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)) ≃ₐ[AlgebraicClosure ℚ]
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
    (J : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q)))
    (hJ : (J : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hwJ : ((w J : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.jqNModC (AlgebraicClosure ℚ) N)
    (f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) :
    (∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A.subtype y =
          ModularCurve.coeffMap A.subtype x) ↔
    (∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        ((w f : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ M H (M * q))) : LaurentSeries (AlgebraicClosure ℚ)) *
            ModularCurve.coeffMap A.subtype y =
          ModularCurve.coeffMap A.subtype x) :=
  main M H q A hqM hA N hqN w J hJ hwJ f

end S_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_mul_coeffMap_eq_iff_of_algEquiv_apply_jq_eq_jqN_of_not_dvd (solution)
