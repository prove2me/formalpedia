-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c27b34a3-6682-55b6-bc7d-0e6a828cc4da

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
import Theorems.Thm_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd
import Theorems.Thm_ModularCurve_CharPReduction_exists_modularRedLocHom_eq
import Theorems.Thm_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_jqNModC_mul_eq_pow
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option Elab.async false

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~dedekindPsi_prime P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_C qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence transcendental_jqNModC transcendental_jqModC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb coeff_jqModC_eq_intCast coeff_jqModC_of_lt modularFunctionFieldFullC jqModC_mem_full coeffMap_qExpand coeff_jqModC_pow_self CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.localizedAtKer CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc_spec CharPReduction.redLocHom CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.jqNModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPReduction.exists_modularRedLocHom_eq CharPReduction.mem_or_inv_mem_modularLocalized CharPReduction.modularRedLocHom_eq_coeffRed CharPReduction.modularRedLocHom_mem CompEq.finrank_adjoin_jBar_eq_dedekindPsi coeffEmb_jq coeffEmb_jqN dedekindPsi_mul_of_coprime exists_isAtkinLehnerAutFull_of_prime_of_not_dvd finiteDimensional_adjoin_coeffEmb_jq_full finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi geomAut_atkinLehner_comp_legs jqNModC_mul_eq_pow nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~dedekindPsi_prime"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable (A red) in

private def locRing (M : ℕ) [NeZero M] : Subring ↥(modularFunctionFieldBar M) :=
  (CharPReduction.modularLocalized M A.toSubring red).comap
    (algebraMap ↥(modularFunctionFieldBar M) (LaurentSeries (AlgebraicClosure ℚ)))

variable (A red) in

private def biLocRing (N q : ℕ) [NeZero N] [NeZero q] : Subring ↥(modularFunctionFieldBar (N * q)) :=
  locRing A red (N * q) ⊓ (locRing A red (N * q)).comap
    (ProlongationTuple.atkinLehnerBar N q).toAlgHom.toRingHom

section QExpandReduction

variable {L₀ : Type*} [CommRing L₀] (B : Subring L₀) {k₀ : Type*} [CommRing k₀] (ρ : B →+* k₀)
variable (M : ℕ) [NeZero M]

private theorem qExpand_mem_integralCoeffs {x : LaurentSeries L₀}
    (hx : x ∈ CharPReduction.integralCoeffs B) :
    qExpand L₀ M x ∈ CharPReduction.integralCoeffs B := by
  intro n
  by_cases h : (M : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul]
    exact hx m
  · rw [qExpand_coeff_of_not_dvd M x h]
    exact B.zero_mem

private theorem coeffRed_qExpand (x : CharPReduction.integralCoeffs B) :
    CharPReduction.coeffRed B ρ ⟨qExpand L₀ M x, qExpand_mem_integralCoeffs B M x.2⟩ =
      qExpand k₀ M (CharPReduction.coeffRed B ρ x) := by
  ext n
  rw [CharPReduction.coeffRed_coeff]
  by_cases h : (M : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    conv_rhs => rw [qExpand_coeff_mul, CharPReduction.coeffRed_coeff]
    exact congrArg ρ (Subtype.ext (qExpand_coeff_mul M (x : LaurentSeries L₀) m))
  · conv_rhs => rw [qExpand_coeff_of_not_dvd M _ h]
    exact (congrArg ρ (Subtype.ext (qExpand_coeff_of_not_dvd M (x : LaurentSeries L₀) h) :
      (⟨_, _⟩ : B) = 0)).trans (map_zero ρ)

private theorem coeffRed_qExpand_eq_zero_iff (x : CharPReduction.integralCoeffs B) :
    CharPReduction.coeffRed B ρ ⟨qExpand L₀ M x, qExpand_mem_integralCoeffs B M x.2⟩ = 0 ↔
      CharPReduction.coeffRed B ρ x = 0 := by
  rw [coeffRed_qExpand]
  constructor
  · intro h0
    exact qExpand_injective M (h0.trans (map_zero (qExpand k₀ M)).symm)
  · intro h0
    rw [h0, map_zero]

end QExpandReduction

section IntegralBridge

private theorem mem_valuationSubring_of_eval₂_eq_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    {K' : IntermediateField F E} (V : ValuationSubring K') (Φ : Polynomial (Polynomial ℤ))
    (hΦ : Φ.Monic) {a x : K'} (ha : a ∈ V)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) (a : E)).toRingHom (x : E) = 0) : x ∈ V := by
  have h' : Φ.eval₂ (Polynomial.aeval (R := ℤ) a).toRingHom x = 0 := by
    apply (algebraMap K' E).injective
    rw [map_zero, Polynomial.hom_eval₂]
    convert h using 2 <;> first | rfl | (refine Polynomial.ringHom_ext (fun n => ?_) ?_ <;> simp [IntermediateField.algebraMap_apply])
  have hint : IsIntegral V x :=
    ⟨Φ.map (Polynomial.aeval (R := ℤ) (⟨a, ha⟩ : V)).toRingHom, hΦ.map _, by
      rw [Polynomial.eval₂_map]
      convert h' using 2 <;> first | rfl | (refine Polynomial.ringHom_ext (fun n => ?_) ?_ <;> simp [ValuationSubring.algebraMap_apply])⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

end IntegralBridge

omit [CharP k q] in

private theorem mem_locRing_of_coe_eq_jqNModC
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {M : ℕ} [NeZero M] (dataM : ModularPolynomialData M) {a x : modularFunctionFieldBar (N * q)}
    (ha : (a : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) M) :
    x ∈ locRing A red (N * q) := by
  have haO : a ∈ locRing A red (N * q) := by
    show (a : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red
    rw [ha]
    exact CharPReduction.subring_le_localizedAtKer _ _ _ _
      (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)
  have hrel := dataM.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) 1
  have h1 : jqNModC (AlgebraicClosure ℚ) (1 * M) = jqNModC (AlgebraicClosure ℚ) M :=
    qExpand_congr (one_mul M) _
  rw [h1, jqNModC_one] at hrel
  exact mem_valuationSubring_of_eval₂_eq_zero (ValuationSubring.ofSubring (locRing A red (N * q)) hval₁)
    dataM.Φ dataM.monic haO (by
      rw [ha, hx]

      convert hrel <;> first | rfl | exact Subsingleton.elim _ _)

section LocalizedApparatus

variable {L₁ : Type*} [Field L₁] {B : Subring L₁} {k₁ : Type*} [Field k₁] {ρ : B →+* k₁}

private theorem inv_mem_localizedAtKer {R₂ : Subring (LaurentSeries L₁)}
    {h₂ : R₂ ≤ CharPReduction.integralCoeffs B} {t : LaurentSeries L₁}
    (ht : t ∈ CharPReduction.localizedAtKer B ρ R₂ h₂) (hti : t ∈ CharPReduction.integralCoeffs B)
    (hred : CharPReduction.coeffRed B ρ ⟨t, hti⟩ ≠ 0) :
    t⁻¹ ∈ CharPReduction.localizedAtKer B ρ R₂ h₂ := by
  obtain ⟨r₂, s₂, hs₂, hts⟩ := (CharPReduction.mem_localizedAtKer B ρ R₂ h₂).mp ht
  have hr₂ : r₂ ∉ CharPReduction.redKer B ρ R₂ h₂ := by
    rw [CharPReduction.notMem_redKer_iff, CharPReduction.redRes_apply] at hs₂ ⊢
    have e : (⟨(r₂ : LaurentSeries L₁), h₂ r₂.2⟩ : CharPReduction.integralCoeffs B) =
        ⟨t, hti⟩ * ⟨(s₂ : LaurentSeries L₁), h₂ s₂.2⟩ := Subtype.ext hts.symm
    rw [e, map_mul]
    exact mul_ne_zero hred hs₂
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hred
    have e : (⟨(0 : LaurentSeries L₁), hti⟩ : CharPReduction.integralCoeffs B) = 0 := Subtype.ext rfl
    rw [e, map_zero]
  refine (CharPReduction.mem_localizedAtKer B ρ R₂ h₂).mpr ⟨s₂, r₂, hr₂, ?_⟩
  rw [← hts]
  exact inv_mul_cancel_left₀ ht0 _

private theorem map_mem_localizedAtKer {R₁ R₂ : Subring (LaurentSeries L₁)}
    {h₁ : R₁ ≤ CharPReduction.integralCoeffs B} {h₂ : R₂ ≤ CharPReduction.integralCoeffs B}
    (ψ : LaurentSeries L₁ →+* LaurentSeries L₁)
    (hgen : ∀ r ∈ R₁, ψ r ∈ CharPReduction.localizedAtKer B ρ R₂ h₂)
    (hker : ∀ s : R₁, s ∉ CharPReduction.redKer B ρ R₁ h₁ →
      (ψ s)⁻¹ ∈ CharPReduction.localizedAtKer B ρ R₂ h₂)
    {f : LaurentSeries L₁} (hf : f ∈ CharPReduction.localizedAtKer B ρ R₁ h₁) :
    ψ f ∈ CharPReduction.localizedAtKer B ρ R₂ h₂ := by
  obtain ⟨r, s, hs, hfs⟩ := (CharPReduction.mem_localizedAtKer B ρ R₁ h₁).mp hf
  have hs0 : (s : LaurentSeries L₁) ≠ 0 := by
    intro h0
    apply hs
    have e : s = 0 := Subtype.ext h0
    rw [e]
    exact zero_mem _
  have hf' : f = r * (s : LaurentSeries L₁)⁻¹ := by
    rw [← hfs, mul_inv_cancel_right₀ hs0]
  rw [hf', map_mul, map_inv₀]
  exact mul_mem (hgen r r.2) (hker s hs)

end LocalizedApparatus

omit [CharP k q] in

private theorem modularLocalized_le_of_jqN_mem
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    CharPReduction.modularLocalized N A.toSubring red ≤
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
  have hgen : CharPReduction.modularRing N A.toSubring ≤
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    refine Subring.closure_le.mpr ?_
    rintro g (⟨a, rfl⟩ | rfl | rfl)
    · exact CharPReduction.subring_le_localizedAtKer _ _ _ _
        (CharPReduction.constSeries_mem_modularRing (N * q) A.toSubring a)
    · exact CharPReduction.subring_le_localizedAtKer _ _ _ _
        (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)
    · exact hjN
  intro f hf
  refine map_mem_localizedAtKer (RingHom.id _) (fun r hr => hgen hr) (fun s hs => ?_) hf
  rw [CharPReduction.notMem_redKer_iff, CharPReduction.redRes_apply] at hs
  exact inv_mem_localizedAtKer (hgen s.2) (CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2) hs

omit [CharP k q] in

private theorem qExpand_mem_modularLocalized_of_jqQ_mem
    (hjQ : jqNModC (AlgebraicClosure ℚ) q ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ CharPReduction.modularLocalized N A.toSubring red) :
    qExpand (AlgebraicClosure ℚ) q f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
  have hgen : ∀ r ∈ CharPReduction.modularRing N A.toSubring,
      qExpand (AlgebraicClosure ℚ) q r ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have hle : CharPReduction.modularRing N A.toSubring ≤
        (CharPReduction.modularLocalized (N * q) A.toSubring red).comap (qExpand (AlgebraicClosure ℚ) q) := by
      refine Subring.closure_le.mpr ?_
      intro g hg
      rw [SetLike.mem_coe, Subring.mem_comap]
      rcases hg with ⟨a, rfl⟩ | rfl | rfl
      ·
        have hc : CharPReduction.constSeries A.toSubring a = HahnSeries.C (a : AlgebraicClosure ℚ) := by
          show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
          rw [HahnSeries.algebraMap_apply', show algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ))
            (a : AlgebraicClosure ℚ) = PowerSeries.C (a : AlgebraicClosure ℚ) from by simp, HahnSeries.ofPowerSeries_C]
        rw [hc, qExpand_C, ← hc]
        exact CharPReduction.subring_le_localizedAtKer _ _ _ _
          (CharPReduction.constSeries_mem_modularRing (N * q) A.toSubring a)
      · rw [← show jqNModC (AlgebraicClosure ℚ) q = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ))
            from rfl]
        exact hjQ
      · rw [show jqNModC (AlgebraicClosure ℚ) N = qExpand (AlgebraicClosure ℚ) N (jqModC (AlgebraicClosure ℚ))
            from rfl,
          qExpand_qExpand, qExpand_congr (mul_comm q N),
          ← show jqNModC (AlgebraicClosure ℚ) (N * q)
              = qExpand (AlgebraicClosure ℚ) (N * q) (jqModC (AlgebraicClosure ℚ)) from rfl]
        exact CharPReduction.subring_le_localizedAtKer _ _ _ _
          (CharPReduction.jqNModC_mem_modularRing (N * q) A.toSubring)
    exact fun r hr => hle hr
  refine map_mem_localizedAtKer (qExpand (AlgebraicClosure ℚ) q) hgen (fun s hs => ?_) hf
  rw [CharPReduction.notMem_redKer_iff, CharPReduction.redRes_apply] at hs
  refine inv_mem_localizedAtKer (hgen s s.2)
    (qExpand_mem_integralCoeffs A.toSubring q (CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2))
    (fun h0 => hs ?_)
  exact (coeffRed_qExpand_eq_zero_iff A.toSubring red q
    ⟨s, CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2⟩).mp h0

private theorem isAtkinLehnerAutFull_of_not_dvd (hqN : ¬ q ∣ N) :
    IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)

private theorem atkinLehnerBar_expansion (hqN : ¬ q ∣ N) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    ProlongationTuple.atkinLehnerBar N q
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (Dvd.dvd.mul_right hd q))⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (d * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (Nat.mul_dvd_mul_right hd q))⟩ := by
  have h := (isAtkinLehnerAutFull_of_not_dvd hqN d inferInstance hd).1
  exact (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ d jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right hd q)⟩).trans (by rw [h])

private theorem atkinLehnerBar_expansion' (hqN : ¬ q ∣ N) {d : ℕ} [NeZero d] (hd : d ∣ N) :
    ProlongationTuple.atkinLehnerBar N q
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (d * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (Nat.mul_dvd_mul_right hd q))⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (Dvd.dvd.mul_right hd q))⟩ := by
  have h := (isAtkinLehnerAutFull_of_not_dvd hqN d inferInstance hd).2
  exact (geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ (d * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right hd q)⟩).trans (by rw [h])

private theorem jFun_eq_expansion_one :
    ProlongationTuple.jFun N q =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q))⟩ :=
  Subtype.ext (by
    show coeffEmb (AlgebraicClosure ℚ) jq = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq)
    rw [qExpand_one_apply])

private theorem jQFun_eq_expansion_one :
    ProlongationTuple.jQFun N q =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q))⟩ :=
  Subtype.ext (by
    show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
    rw [qExpand_congr (one_mul q)])

private theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q (ProlongationTuple.jFun N q) = ProlongationTuple.jQFun N q := by
  rw [jFun_eq_expansion_one, atkinLehnerBar_expansion hqN (one_dvd N), jQFun_eq_expansion_one]

private theorem atkinLehnerBar_jQFun (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q (ProlongationTuple.jQFun N q) = ProlongationTuple.jFun N q := by
  rw [jQFun_eq_expansion_one, atkinLehnerBar_expansion' hqN (one_dvd N), jFun_eq_expansion_one]

private theorem atkinLehnerBar_jNQ (hqN : ¬ q ∣ N) :
    ProlongationTuple.atkinLehnerBar N q
        ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) dvd_rfl)⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩ :=
  atkinLehnerBar_expansion' hqN dvd_rfl

omit [CharP k q] in

private theorem jFun_coe_mem :
    ((ProlongationTuple.jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
  rw [show ((ProlongationTuple.jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) from coeffEmb_jq (AlgebraicClosure ℚ)]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _
    (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)

omit [CharP k q] in

private theorem jNQ_coe_mem :
    ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) dvd_rfl)⟩ :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (N * q) A.toSubring red := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red
  rw [show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq) = jqNModC (AlgebraicClosure ℚ) (N * q) from
    coeffEmb_jqN (AlgebraicClosure ℚ) (N * q)]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _
    (CharPReduction.jqNModC_mem_modularRing (N * q) A.toSubring)

omit [CharP k q] in

private theorem jQFun_coe_mem
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ((ProlongationTuple.jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red :=
  mem_locRing_of_coe_eq_jqNModC hval₁ (nonempty_modularPolynomialData q).some
    (a := ProlongationTuple.jFun N q) (x := ProlongationTuple.jQFun N q)
    (coeffEmb_jq (AlgebraicClosure ℚ)) (coeffEmb_jqN (AlgebraicClosure ℚ) q)

omit [CharP k q] in

private theorem jN_coe_mem
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩ :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (N * q) A.toSubring red :=
  mem_locRing_of_coe_eq_jqNModC hval₁ (nonempty_modularPolynomialData N).some
    (a := ProlongationTuple.jFun N q)
    (x := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩)
    (coeffEmb_jq (AlgebraicClosure ℚ)) (coeffEmb_jqN (AlgebraicClosure ℚ) N)

private scoped instance algebraLocRing :
    Algebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) :=
  ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (locRing A red N).subtype).toAlgebra

omit [CharP k q] in
private theorem algebraMap_locRing_apply (v : ↥(locRing A red N)) :
    algebraMap ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) v =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) := rfl

omit [CharP k q] in

private theorem isScalarTower_locRing :
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    IsScalarTower ↥(locRing A red N) ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q)) := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem heckeAlphaBar_mem_biLocRing (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (v : ↥(modularFunctionFieldBar N)) (hv : v ∈ locRing A red N) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q v ∈ biLocRing A red N q := by
  have _ := ‹CharP k q›
  have hv' : (v : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := hv
  have hjN : jqNModC (AlgebraicClosure ℚ) N ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := jN_coe_mem hval₁
    rw [← show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N from
      coeffEmb_jqN (AlgebraicClosure ℚ) N]
    exact h
  have hjQ : jqNModC (AlgebraicClosure ℚ) q ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have h := jQFun_coe_mem hval₁
    rw [← show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = jqNModC (AlgebraicClosure ℚ) q from
      coeffEmb_jqN (AlgebraicClosure ℚ) q]
    exact h
  have hleg : ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) =
      heckeBetaBar (AlgebraicClosure ℚ) N q v := by
    have h := AlgHom.congr_fun
      (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ (isAtkinLehnerAutFull_of_not_dvd hqN)).1 v
    rw [AlgHom.comp_apply] at h
    exact h
  rw [biLocRing, Subring.mem_inf, Subring.mem_comap]
  refine ⟨?_, ?_⟩
  · show ((heckeAlphaBar (AlgebraicClosure ℚ) N q v : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red
    rw [coe_heckeAlphaBar]
    exact modularLocalized_le_of_jqN_mem hjN hv'
  · show ((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (N * q) A.toSubring red
    rw [hleg, coe_heckeBetaBar]
    exact qExpand_mem_modularLocalized_of_jqQ_mem hjQ hv'

private def orderS (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) :=
  { (biLocRing A red N q).toSubsemiring with
    algebraMap_mem' := fun v => heckeAlphaBar_mem_biLocRing hqN hval₁ v.1 v.2 }

private theorem mem_orderS (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (g : ↥(modularFunctionFieldBar (N * q))) :
    g ∈ orderS hqN hval₁ ↔
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
        ((ProlongationTuple.atkinLehnerBar N q g : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red :=
  Iff.rfl

private theorem jQFun_mem_orderS (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ProlongationTuple.jQFun N q ∈ orderS (A := A) (red := red) hqN hval₁ := by
  have _ := ‹CharP k q›
  refine (mem_orderS hqN hval₁ _).mpr ⟨jQFun_coe_mem hval₁, ?_⟩
  rw [atkinLehnerBar_jQFun hqN]
  exact jFun_coe_mem

private theorem jNQ_mem_orderS (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) dvd_rfl)⟩ :
        modularFunctionFieldBar (N * q)) ∈ orderS (A := A) (red := red) hqN hval₁ := by
  have _ := ‹CharP k q›
  refine (mem_orderS hqN hval₁ _).mpr ⟨jNQ_coe_mem, ?_⟩
  rw [atkinLehnerBar_jNQ hqN]
  exact jN_coe_mem hval₁

section SeriesFurniture

variable {K₀ K₁ : Type*} [CommRing K₀] [CommRing K₁]

private theorem coeffMap_qExpand_series (φ : K₀ →+* K₁) (M : ℕ) [NeZero M] (x : LaurentSeries K₀) :
    coeffMap φ (qExpand K₀ M x) = qExpand K₁ M (coeffMap φ x) := by
  ext n
  rw [coeffMap_coeff]
  by_cases h : (M : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd M _ h, qExpand_coeff_of_not_dvd M _ h, map_zero]

private theorem coeffMap_jqModC_series (φ : K₀ →+* K₁) : coeffMap φ (jqModC K₀) = jqModC K₁ :=
  map_jqModC φ

private theorem coeffMap_jqNModC_series (φ : K₀ →+* K₁) (M : ℕ) [NeZero M] :
    coeffMap φ (jqNModC K₀ M) = jqNModC K₁ M := by
  simp only [jqNModC, coeffMap_qExpand_series, coeffMap_jqModC_series]

end SeriesFurniture

section LocalizedUnits

variable {L₁ : Type*} [Field L₁] {B : Subring L₁} {k₁ : Type*} [Field k₁] {ρ : B →+* k₁}
  {R₀ : Subring (LaurentSeries L₁)} {h₀ : R₀ ≤ CharPReduction.integralCoeffs B}

private theorem inv_mem_of_redLocHom_ne_zero (f : CharPReduction.localizedAtKer B ρ R₀ h₀)
    (hf : CharPReduction.redLocHom (A := B) (red := ρ) (R := R₀) (hR := h₀) f ≠ 0) :
    (f : LaurentSeries L₁)⁻¹ ∈ CharPReduction.localizedAtKer B ρ R₀ h₀ := by
  obtain ⟨r, s, hs, hfs⟩ :=
    (CharPReduction.mem_localizedAtKer (A := B) (red := ρ) (R := R₀) (hR := h₀)).mp f.2
  have hspec := CharPReduction.redLoc_spec (A := B) (red := ρ) (R := R₀) (hR := h₀) f hfs
  rw [CharPReduction.redLocHom_apply] at hf
  have hr : r ∉ CharPReduction.redKer B ρ R₀ h₀ := by
    rw [CharPReduction.notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hf
      ((CharPReduction.notMem_redKer_iff (A := B) (red := ρ) (R := R₀) (hR := h₀)).mp hs)
  have hf0 : (f : LaurentSeries L₁) ≠ 0 := by
    intro h0
    apply hr
    have hr0 : r = 0 := Subtype.ext (by rw [← hfs, h0, zero_mul]; rfl)
    rw [hr0]
    exact Ideal.zero_mem _
  refine (CharPReduction.mem_localizedAtKer (A := B) (red := ρ) (R := R₀) (hR := h₀)).mpr
    ⟨s, r, hr, ?_⟩
  rw [← hfs, inv_mul_cancel_left₀ hf0]

end LocalizedUnits

section LevelBlindness

omit [CharP k q] in

private theorem modularRedLocHom_level_eq (hjN : jqNModC (AlgebraicClosure ℚ) N ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red)
    {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hfN : f ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hfNq : f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hfNq⟩ =
      CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hfN⟩ := by
  obtain ⟨r, s, hs, hfs⟩ :=
    (CharPReduction.mem_localizedAtKer (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hfN
  have hle := modularLocalized_le_of_jqN_mem hjN
  have hrO : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red :=
    hle (CharPReduction.subring_le_localizedAtKer _ _ _ _ r.2)
  have hsO : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red :=
    hle (CharPReduction.subring_le_localizedAtKer _ _ _ _ s.2)
  have hrI := CharPReduction.modularRing_le_integralCoeffs N A.toSubring r.2
  have hsI := CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2

  have hmul : (⟨f, hfNq⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) * ⟨s, hsO⟩ =
      ⟨r, hrO⟩ := Subtype.ext hfs
  have hNq : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hfNq⟩ *
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨s, hsO⟩ =
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨r, hrO⟩ :=
    (map_mul (CharPReduction.modularRedLocHom (N * q) A.toSubring red) _ _).symm.trans
      (congrArg (CharPReduction.modularRedLocHom (N * q) A.toSubring red) hmul)
  have hs' := CharPReduction.modularRedLocHom_eq_coeffRed A.toSubring red (N * q) ⟨s, hsO⟩ hsI
  have hr' := CharPReduction.modularRedLocHom_eq_coeffRed A.toSubring red (N * q) ⟨r, hrO⟩ hrI
  rw [hs', hr'] at hNq

  have hN := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨f, hfN⟩ hfs
  rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply] at hN
  have hsne := (CharPReduction.notMem_redKer_iff (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hs
  rw [CharPReduction.redRes_apply] at hsne
  have key := mul_right_cancel₀ hsne (hNq.trans hN.symm)
  exact key.trans (CharPReduction.redLocHom_apply (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨f, hfN⟩).symm

end LevelBlindness

section CoefficientMembership

private theorem mem_modularLocalized_of_mem_adjoin (hqN : ¬ q ∣ N)
    (hjN : jqNModC (AlgebraicClosure ℚ) N ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hxj : x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N})
    (hxNq : x ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    x ∈ CharPReduction.modularLocalized N A.toSubring red := by
  rcases CharPReduction.mem_or_inv_mem_modularLocalized A red N
      (nonempty_modularPolynomialData N).some
      (relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN) hxj with h | h
  · exact h
  by_cases hx0 : x = 0
  · rw [hx0]
    exact zero_mem _
  by_cases hred : CharPReduction.modularRedLocHom N A.toSubring red ⟨x⁻¹, h⟩ ≠ 0
  · have := inv_mem_of_redLocHom_ne_zero ⟨x⁻¹, h⟩ hred
    rwa [inv_inv] at this
  push Not at hred
  exfalso
  have hinvNq : x⁻¹ ∈ CharPReduction.modularLocalized (N * q) A.toSubring red :=
    modularLocalized_le_of_jqN_mem hjN h
  have hzero : CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨x⁻¹, hinvNq⟩ = 0 := by
    rw [modularRedLocHom_level_eq hjN h hinvNq, hred]
  have hone : (⟨x, hxNq⟩ : CharPReduction.modularLocalized (N * q) A.toSubring red) * ⟨x⁻¹, hinvNq⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ hx0)
  have := congrArg (CharPReduction.modularRedLocHom (N * q) A.toSubring red) hone
  rw [map_mul, map_one, hzero, mul_zero] at this
  exact zero_ne_one this

omit [CharP k q] in

private theorem jqNModC_mem_modularLocalized_mul
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    jqNModC (AlgebraicClosure ℚ) N ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
  let e : modularFunctionFieldBar (N * q) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) (dvd_mul_right N q))⟩
  have he : (e : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) N :=
    coeffMap_jqNModC_series (algebraMap ℚ (AlgebraicClosure ℚ)) N
  have ha : ((ProlongationTuple.jFun N q : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
    coeffMap_jqModC_series (algebraMap ℚ (AlgebraicClosure ℚ))
  have hmem := mem_locRing_of_coe_eq_jqNModC hval₁ (nonempty_modularPolynomialData N).some ha he
  rw [← he]
  exact Subring.mem_comap.mp hmem

private theorem coe_mem_adjoin_jqModC {c : modularFunctionFieldBar (N * q)}
    (hcj : c ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) :
    (c : LaurentSeries (AlgebraicClosure ℚ)) ∈
      IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)} := by
  have hle : IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q))) ≤
      (IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)}).comap
        (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    show ((ProlongationTuple.jFun N q : modularFunctionFieldBar (N * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) _
    rw [show ((ProlongationTuple.jFun N q : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) from
      coeffMap_jqModC_series (algebraMap ℚ (AlgebraicClosure ℚ))]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  exact hle hcj

private theorem adjoin_jqModC_le_bar :
    IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ)} ≤
      modularFunctionFieldBar N := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  rw [← coeffMap_jqModC_series (algebraMap ℚ (AlgebraicClosure ℚ))]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
    (modularFunctionField_le_full N (jq_mem N))

private theorem coe_mem_bar_of_mem_adjoin {c : modularFunctionFieldBar (N * q)}
    (hcj : c ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) :
    (c : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N :=
  adjoin_jqModC_le_bar (coe_mem_adjoin_jqModC hcj)

private theorem coe_mem_adjoin_pair_of_mem_adjoin {c : modularFunctionFieldBar (N * q)}
    (hcj : c ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set (modularFunctionFieldBar (N * q)))) :
    (c : LaurentSeries (AlgebraicClosure ℚ)) ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} :=
  IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    (coe_mem_adjoin_jqModC hcj)

private theorem mk_mem_locRing {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ modularFunctionFieldBar N)
    (hxN : x ∈ CharPReduction.modularLocalized N A.toSubring red) :
    (⟨x, hx⟩ : modularFunctionFieldBar N) ∈ locRing A red N := by
  rw [locRing, Subring.mem_comap, IntermediateField.algebraMap_apply]
  exact hxN

private theorem heckeAlphaBar_mk_eq {c : modularFunctionFieldBar (N * q)}
    (hc : (c : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (⟨(c : LaurentSeries (AlgebraicClosure ℚ)), hc⟩ :
      modularFunctionFieldBar N) = c :=
  Subtype.ext (coe_heckeAlphaBar N q _)

end CoefficientMembership

section GaussSheet

set_option synthInstance.maxHeartbeats 1600000

section ResidueIdentifications

set_option synthInstance.maxHeartbeats 1600000

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private theorem residue₁_coe_eq_of_coe_eq (y : LaurentSeries A) {f : modularFunctionFieldBar (N * q)}
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) (h : f ∈ R.R₁.integers) :
    ((R.R₁.residue ⟨f, h⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [← hf]
    exact f.2
  obtain ⟨h', hres⟩ := R.residue₁_coeffMap y hy
  have hfe : (⟨f, h⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hy⟩, h'⟩ :=
    Subtype.ext (Subtype.ext hf)
  rw [hfe]
  exact hres

private theorem residue₁_jFun_coe (h : ProlongationTuple.jFun N q ∈ R.R₁.integers) :
    ((R.R₁.residue ⟨ProlongationTuple.jFun N q, h⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = jqModC (IsLocalRing.ResidueField A) := by
  rw [residue₁_coe_eq_of_coe_eq R (jqModC A) _ h, coeffMap_jqModC_series]
  show coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC A)
  rw [coeffMap_jqModC_series]
  exact coeffMap_jqModC_series (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem residue₁_jQFun_coe (h : ProlongationTuple.jQFun N q ∈ R.R₁.integers) :
    ((R.R₁.residue ⟨ProlongationTuple.jQFun N q, h⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = jqNModC (IsLocalRing.ResidueField A) q := by
  rw [residue₁_coe_eq_of_coe_eq R (jqNModC A q) _ h, coeffMap_jqNModC_series]
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffMap A.subtype (jqNModC A q)
  rw [coeffMap_jqNModC_series]
  exact coeffMap_jqNModC_series (algebraMap ℚ (AlgebraicClosure ℚ)) q

private theorem residue₂_jFun_coe (hqN : ¬ q ∣ N) (h : ProlongationTuple.jFun N q ∈ R.R₂.integers) :
    ((R.R₂.residue ⟨ProlongationTuple.jFun N q, h⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
        LaurentSeries (IsLocalRing.ResidueField A)) = jqNModC (IsLocalRing.ResidueField A) q := by
  rw [R.residue₂_eq, residue₁_coe_eq_of_coe_eq R (jqNModC A q) _ _, coeffMap_jqNModC_series]
  rw [atkinLehnerBar_jFun hqN, coeffMap_jqNModC_series]
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = jqNModC (AlgebraicClosure ℚ) q
  exact coeffMap_jqNModC_series (algebraMap ℚ (AlgebraicClosure ℚ)) q

end ResidueIdentifications

section WitnessSeries

private theorem charP_residueField {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) :
    CharP (IsLocalRing.ResidueField ↥A) q :=
  R.redBar.charP R.redBar.injective q

private theorem pow_jqModC_eq_jqNModC (K : Type*) [CommRing K] [CharP K q] :
    jqModC K ^ q = jqNModC K q := by
  rw [← jqNModC_one (K := K), ← jqNModC_mul_eq_pow K 1]
  show qExpand K (1 * q) (jqModC K) = qExpand K q (jqModC K)
  exact qExpand_congr (one_mul q) _

private theorem coeff_neg_one_jqModC (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  have hZ : (jqModC ℤ).coeff (-1) = 1 := by
    have h : (jqModC ℚ).coeff (-1) = Int.castRingHom ℚ ((jqModC ℤ).coeff (-1)) := by
      rw [jqModC_eq_map_intCast ℚ]; rfl
    rw [jqModC_rat, coeff_jq_neg_one, eq_intCast] at h
    exact_mod_cast h.symm
  rw [jqModC_eq_map_intCast K]
  show Int.castRingHom K ((jqModC ℤ).coeff (-1)) = 1
  rw [hZ, map_one]

private theorem jqModC_sub_pow_ne_zero (K : Type*) [CommRing K] [Nontrivial K] [CharP K q] :
    jqModC K - jqNModC K q ^ q ≠ 0 := by
  intro h
  have hq2 : ¬ ((q * q : ℕ) : ℤ) ∣ (-1 : ℤ) := by
    intro hd
    have h1 : ((q * q : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) (dvd_neg.mp hd)
    have h2 : q * q = 1 := by exact_mod_cast h1
    exact (Fact.out : q.Prime).ne_one (Nat.eq_one_of_mul_eq_one_right h2)
  have hc : (jqModC K - jqNModC K q ^ q).coeff (-1) = 0 := by rw [h]; rfl
  rw [HahnSeries.coeff_sub, ← jqNModC_mul_eq_pow K q, coeff_neg_one_jqModC] at hc
  have h0 : (jqNModC K (q * q)).coeff (-1) = 0 := qExpand_coeff_of_not_dvd (q * q) (jqModC K) hq2
  rw [h0, sub_zero] at hc
  exact one_ne_zero hc

end WitnessSeries

section PurelyInseparableStep

variable {κ : Type*} [Field κ] [PerfectField κ] {M₀ : Type*} [Field M₀] [Algebra κ M₀]
  (p : ℕ) [hp : Fact p.Prime] [CharP κ p]

private theorem exists_pow_eq_of_mem_adjoin_pow (x : M₀) {y : M₀}
    (hy : y ∈ IntermediateField.adjoin κ ({x ^ p} : Set M₀)) : ∃ z : M₀, z ^ p = y := by
  haveI : ExpChar κ p := ExpChar.prime hp.out
  haveI : CharP M₀ p := charP_of_injective_algebraMap (algebraMap κ M₀).injective p
  haveI : ExpChar M₀ p := ExpChar.prime hp.out
  have hconst : ∀ c : κ, algebraMap κ M₀ c ∈ (frobenius M₀ p).fieldRange := by
    intro c
    obtain ⟨d, hd⟩ := surjective_frobenius κ p c
    refine ⟨algebraMap κ M₀ d, ?_⟩
    rw [← hd, frobenius_def, frobenius_def, map_pow]
  have hle : IntermediateField.adjoin κ ({x ^ p} : Set M₀) ≤
      (frobenius M₀ p).fieldRange.toIntermediateField hconst := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨x, frobenius_def p x⟩
  obtain ⟨z, hz⟩ := hle hy
  exact ⟨z, by rw [← frobenius_def]; exact hz⟩

private theorem relfinrank_adjoin_pow_adjoin (x : M₀) (hx : ∀ z : M₀, z ^ p ≠ x) :
    (IntermediateField.adjoin κ ({x ^ p} : Set M₀)).relfinrank
      (IntermediateField.adjoin κ ({x} : Set M₀)) = p := by
  haveI : CharP M₀ p := charP_of_injective_algebraMap (algebraMap κ M₀).injective p
  haveI : ExpChar M₀ p := ExpChar.prime hp.out
  have hle : IntermediateField.adjoin κ ({x ^ p} : Set M₀) ≤
      IntermediateField.adjoin κ ({x} : Set M₀) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (pow_mem (IntermediateField.mem_adjoin_simple_self κ x) p)
  let a : IntermediateField.adjoin κ ({x ^ p} : Set M₀) :=
    ⟨x ^ p, IntermediateField.mem_adjoin_simple_self κ (x ^ p)⟩
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C a) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out (fun b hb => ?_)
    have hb' : (b : M₀) ^ p = x ^ p := by
      have h1 := congrArg (fun t : IntermediateField.adjoin κ ({x ^ p} : Set M₀) => (t : M₀)) hb
      simpa [a] using h1
    have hbx : (b : M₀) = x := by
      apply frobenius_inj M₀ p
      rw [frobenius_def, frobenius_def]
      exact hb'
    have hxmem : x ∈ IntermediateField.adjoin κ ({x ^ p} : Set M₀) := by
      have hb2 := b.2
      rw [hbx] at hb2
      exact hb2
    obtain ⟨z, hz⟩ := exists_pow_eq_of_mem_adjoin_pow p x hxmem
    exact hx z hz
  have hmonic : (Polynomial.X ^ p - Polynomial.C a).Monic := Polynomial.monic_X_pow_sub_C a hp.out.ne_zero
  have haev : Polynomial.aeval x (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    simp [a]
  have hmin : minpoly (IntermediateField.adjoin κ ({x ^ p} : Set M₀)) x =
      Polynomial.X ^ p - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hirr haev hmonic).symm
  have hint : IsIntegral (IntermediateField.adjoin κ ({x ^ p} : Set M₀)) x :=
    ⟨Polynomial.X ^ p - Polynomial.C a, hmonic, by simpa [Polynomial.eval₂_eq_eval_map] using haev⟩
  have hext : IntermediateField.extendScalars hle =
      IntermediateField.adjoin (IntermediateField.adjoin κ ({x ^ p} : Set M₀)) ({x} : Set M₀) := by
    apply IntermediateField.restrictScalars_injective κ
    rw [IntermediateField.extendScalars_restrictScalars, IntermediateField.restrictScalars_adjoin_eq_sup]
    exact (sup_eq_right.mpr hle).symm
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle, hext, IntermediateField.adjoin.finrank hint,
    hmin, Polynomial.natDegree_X_pow_sub_C]

end PurelyInseparableStep

section FullCDegree

variable (K : Type*) [Field K] [PerfectField K] [CharP K q]

omit [PerfectField K] in

private theorem pow_ne_jqModC (z : LaurentSeries K) : z ^ q ≠ jqModC K := by
  intro h
  have hq : ¬ ((q : ℕ) : ℤ) ∣ (-1 : ℤ) := by
    intro hd
    have h1 : ((q : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) (dvd_neg.mp hd)
    exact (Fact.out : q.Prime).ne_one (by exact_mod_cast h1)
  have h0 := LaurentSeries.coeff_pow_ringChar_eq_zero_of_not_dvd q z (-1) hq
  rw [h, coeff_neg_one_jqModC] at h0
  exact one_ne_zero h0

omit [PerfectField K] [NeZero N] in

private theorem pow_ne_jqModC_fullC (z : modularFunctionFieldFullC K N) :
    z ^ q ≠ ⟨jqModC K, jqModC_mem_full K N⟩ := by
  intro h
  apply pow_ne_jqModC K (z : LaurentSeries K)
  have h1 := congrArg (fun t : modularFunctionFieldFullC K N => (t : LaurentSeries K)) h
  simpa using h1

private theorem finrank_adjoin_jqModC_pow_fullC (hN : (N : K) ≠ 0) :
    Module.finrank
        (IntermediateField.adjoin K
          ({(⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ^ q} :
            Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = q * dedekindPsi N := by
  have hle : IntermediateField.adjoin K
      ({(⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) ^ q} :
        Set (modularFunctionFieldFullC K N)) ≤
      IntermediateField.adjoin K
        ({(⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)} :
          Set (modularFunctionFieldFullC K N)) :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (pow_mem (IntermediateField.mem_adjoin_simple_self K _) q)
  rw [← IntermediateField.relfinrank_mul_finrank_top hle,
    relfinrank_adjoin_pow_adjoin q _ (pow_ne_jqModC_fullC K),
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN]

end FullCDegree

private theorem inst_hf {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ∀ i, ProlongationTuple.jFun N q ∈
      ((![R.R₁, R.R₂] : Fin 2 → RegularProlongation A ↥(modularFunctionFieldBar (N * q))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) i).integers := by

  have hser : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := coeffEmb_jq (AlgebraicClosure ℚ)
  have h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers := by
    refine (R.mem_integersFst_iff _).mpr ?_
    rw [hser]
    exact CharPReduction.subring_le_localizedAtKer _ _ _ _
      (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)
  have hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers :=
    (R.mem_integersFst_iff _).mpr ((mem_orderS hqN hval₁ _).mp (jQFun_mem_orderS hqN hval₁)).1
  have h₂ : ProlongationTuple.jFun N q ∈ R.R₂.integers := by
    refine (R.mem_integers₂_iff _).mpr ?_
    rw [atkinLehnerBar_jFun hqN]
    exact hQ
  exact Fin.forall_fin_two.mpr ⟨by simpa using h₁, by simpa using h₂⟩

private theorem residue₁_congr {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    {f g : ↥(modularFunctionFieldBar (N * q))} (hfg : f = g) (hf : f ∈ R.R₁.integers) (hg : g ∈ R.R₁.integers) :
    R.R₁.residue ⟨f, hf⟩ = R.R₁.residue ⟨g, hg⟩ := by
  subst hfg
  rfl

private theorem residue₁_witness_eq_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers) (hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers) :
    R.R₁.residue (⟨ProlongationTuple.jQFun N q, hQ⟩ - ⟨ProlongationTuple.jFun N q, h₁⟩ ^ q) = 0 := by
  haveI := charP_residueField R
  have _ := hqN
  apply (algebraMap ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)
    (LaurentSeries (IsLocalRing.ResidueField ↥A))).injective
  rw [RingHom.map_sub, RingHom.map_pow, RingHom.map_sub, RingHom.map_pow, map_zero,
    IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply, residue₁_jQFun_coe R hQ,
    residue₁_jFun_coe R h₁, pow_jqModC_eq_jqNModC, sub_self]

private theorem residue₂_witness_ne_zero {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers) (hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers)
    (h₂ : ProlongationTuple.jFun N q ∈ R.R₂.integers) (hQ₂ : ProlongationTuple.jQFun N q ∈ R.R₂.integers) :
    R.R₂.residue (⟨ProlongationTuple.jQFun N q, hQ₂⟩ - ⟨ProlongationTuple.jFun N q, h₂⟩ ^ q) ≠ 0 := by
  haveI := charP_residueField R
  rw [RingHom.map_sub, RingHom.map_pow, R.residue₂_eq _ hQ₂, R.residue₂_eq _ h₂,
    residue₁_congr R (atkinLehnerBar_jQFun hqN) _ h₁, residue₁_congr R (atkinLehnerBar_jFun hqN) _ hQ]
  intro h0
  apply jqModC_sub_pow_ne_zero (q := q) (IsLocalRing.ResidueField ↥A)
  have h := congrArg (algebraMap ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)
    (LaurentSeries (IsLocalRing.ResidueField ↥A))) h0
  rwa [RingHom.map_sub, RingHom.map_pow, map_zero, IntermediateField.algebraMap_apply,
    IntermediateField.algebraMap_apply, residue₁_jFun_coe R h₁, residue₁_jQFun_coe R hQ] at h

private theorem inv_witness_mem₂ {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers) (hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers)
    (h₂ : ProlongationTuple.jFun N q ∈ R.R₂.integers) (hQ₂ : ProlongationTuple.jQFun N q ∈ R.R₂.integers) :
    (ProlongationTuple.jQFun N q - ProlongationTuple.jFun N q ^ q) ≠ 0 ∧
      (ProlongationTuple.jQFun N q - ProlongationTuple.jFun N q ^ q)⁻¹ ∈ R.R₂.integers := by
  have hunit := R.R₂.isUnit_of_residue_ne_zero (residue₂_witness_ne_zero R hqN h₁ hQ h₂ hQ₂)
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hw' : (ProlongationTuple.jQFun N q - ProlongationTuple.jFun N q ^ q) *
      (w : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    have h := congrArg Subtype.val hw
    push_cast at h
    exact h
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, zero_mul] at hw'
    exact zero_ne_one hw'
  · rw [inv_eq_of_mul_eq_one_right hw']
    exact w.2

private theorem inv_witness_not_mem₁ {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers) (hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers)
    (hu : (ProlongationTuple.jQFun N q - ProlongationTuple.jFun N q ^ q) ≠ 0) :
    (ProlongationTuple.jQFun N q - ProlongationTuple.jFun N q ^ q)⁻¹ ∉ R.R₁.integers := by
  intro hx
  have hprod : ((⟨_, hx⟩ : ↥R.R₁.integers) *
      (⟨ProlongationTuple.jQFun N q, hQ⟩ - ⟨ProlongationTuple.jFun N q, h₁⟩ ^ q)) = 1 :=
    Subtype.ext (by push_cast; exact inv_mul_cancel₀ hu)
  have h := congrArg R.R₁.residue hprod
  rw [RingHom.map_mul, residue₁_witness_eq_zero R hqN h₁ hQ, mul_zero, RingHom.map_one] at h
  exact zero_ne_one h

private theorem inst_hR {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    Function.Injective fun i => ((![R.R₁, R.R₂] : Fin 2 → RegularProlongation A ↥(modularFunctionFieldBar (N * q))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) i).integers := by
  have h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers := by simpa using inst_hf R hqN hval₁ 0
  have h₂ : ProlongationTuple.jFun N q ∈ R.R₂.integers := by simpa using inst_hf R hqN hval₁ 1
  have hQ : ProlongationTuple.jQFun N q ∈ R.R₁.integers :=
    (R.mem_integersFst_iff _).mpr ((mem_orderS hqN hval₁ _).mp (jQFun_mem_orderS hqN hval₁)).1
  have hQ₂ : ProlongationTuple.jQFun N q ∈ R.R₂.integers := by
    refine (R.mem_integers₂_iff _).mpr ?_
    rw [atkinLehnerBar_jQFun hqN]
    exact h₁
  obtain ⟨hu, hx₂⟩ := inv_witness_mem₂ R hqN h₁ hQ h₂ hQ₂
  have hx₁ := inv_witness_not_mem₁ R hqN h₁ hQ hu
  have hne : R.R₁.integers ≠ R.R₂.integers := fun h => hx₁ (by rw [h]; exact hx₂)
  intro i i' h
  fin_cases i <;> fin_cases i'
  · rfl
  · exact absurd (by simpa using h) hne
  · exact absurd (by simpa using h) hne.symm
  · rfl

omit [CharP k q] in

private theorem inst_htrL : Transcendental (AlgebraicClosure ℚ) (ProlongationTuple.jFun N q) := by
  have h : Transcendental (AlgebraicClosure ℚ) (algebraMap ↥(modularFunctionFieldBar (N * q))
      (LaurentSeries (AlgebraicClosure ℚ)) (ProlongationTuple.jFun N q)) := by
    rw [IntermediateField.algebraMap_apply,
      show ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = coeffEmb (AlgebraicClosure ℚ) jq from rfl,
      coeffEmb_jq]
    exact transcendental_jqModC _
  exact (transcendental_algebraMap_iff
    (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h

omit [CharP k q] in

private theorem inst_hfd :
    FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q)))) ↥(modularFunctionFieldBar (N * q)) :=
  finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) (N * q)

private theorem transcendental_residue₁_jFun
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (h : ProlongationTuple.jFun N q ∈ R.R₁.integers) :
    Transcendental (IsLocalRing.ResidueField A) (R.R₁.residue ⟨ProlongationTuple.jFun N q, h⟩) := by
  refine (transcendental_algebraMap_iff (algebraMap
    (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (LaurentSeries (IsLocalRing.ResidueField A))).injective).mp ?_
  rw [IntermediateField.algebraMap_apply, residue₁_jFun_coe R h]
  exact transcendental_jqModC _

private theorem transcendental_residue₂_jFun
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (h : ProlongationTuple.jFun N q ∈ R.R₂.integers) :
    Transcendental (IsLocalRing.ResidueField A) (R.R₂.residue ⟨ProlongationTuple.jFun N q, h⟩) := by
  refine (transcendental_algebraMap_iff (algebraMap
    (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)
    (LaurentSeries (IsLocalRing.ResidueField A))).injective).mp ?_
  rw [IntermediateField.algebraMap_apply, residue₂_jFun_coe R hqN h]
  exact transcendental_jqNModC _ q

private theorem inst_htr {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ∀ i, Transcendental (IsLocalRing.ResidueField ↥A)
      (((![R.R₁, R.R₂] : Fin 2 → RegularProlongation A ↥(modularFunctionFieldBar (N * q))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) i).residue
      ⟨ProlongationTuple.jFun N q, inst_hf R hqN hval₁ i⟩) := by
  have h₁ : ProlongationTuple.jFun N q ∈ R.R₁.integers := inst_hf R hqN hval₁ 0
  have h₂ : ProlongationTuple.jFun N q ∈ R.R₂.integers := inst_hf R hqN hval₁ 1
  intro i
  fin_cases i
  · exact transcendental_residue₁_jFun R h₁
  · exact transcendental_residue₂_jFun R hqN h₂

private theorem dedekindPsi_prime : dedekindPsi q = q + 1 := by
  have hq : q.Prime := Fact.out
  unfold dedekindPsi
  rw [hq.divisors, Finset.filter_true_of_mem, Finset.sum_pair hq.one_lt.ne, Nat.div_one, Nat.div_self hq.pos]
  intro d hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact squarefree_one
  · rw [Finset.mem_singleton.mp hd]
    exact hq.prime.squarefree

private theorem finrank_adjoin_residue₁_jFun {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (h : ProlongationTuple.jFun N q ∈ R.R₁.integers) :
    Module.finrank
        ↥(IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
          ({R.R₁.residue ⟨ProlongationTuple.jFun N q, h⟩} :
            Set ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) = dedekindPsi N := by
  haveI := charP_residueField R
  have hN : (N : IsLocalRing.ResidueField ↥A) ≠ 0 := fun h0 => hqN ((CharP.cast_eq_zero_iff _ q N).mp h0)
  rw [show R.R₁.residue ⟨ProlongationTuple.jFun N q, h⟩ = ⟨jqModC _, jqModC_mem_full _ N⟩ from
    Subtype.ext (residue₁_jFun_coe R h)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi _ N hN

private theorem finrank_adjoin_residue₂_jFun {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (h : ProlongationTuple.jFun N q ∈ R.R₂.integers) :
    Module.finrank
        ↥(IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
          ({R.R₂.residue ⟨ProlongationTuple.jFun N q, h⟩} :
            Set ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) = q * dedekindPsi N := by
  haveI := charP_residueField R
  have hN : ((N : ℕ) : IsLocalRing.ResidueField A) ≠ 0 :=
    (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) q N).not.mpr hqN
  have hgen : R.R₂.residue ⟨ProlongationTuple.jFun N q, h⟩ =
      (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) N⟩ :
        modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) ^ q := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, residue₂_jFun_coe R hqN h]
    exact (pow_jqModC_eq_jqNModC (IsLocalRing.ResidueField A)).symm
  rw [hgen]
  exact finrank_adjoin_jqModC_pow_fullC (IsLocalRing.ResidueField A) hN

omit [CharP k q] in

private theorem finrank_adjoin_jFun_bar :
    Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q)))) ↥(modularFunctionFieldBar (N * q))
      = dedekindPsi (N * q) :=
  CompEq.finrank_adjoin_jBar_eq_dedekindPsi (N * q)

private theorem inst_heq {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
        ({((![R.R₁, R.R₂] : Fin 2 → RegularProlongation A ↥(modularFunctionFieldBar (N * q))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) i).residue
          ⟨ProlongationTuple.jFun N q, inst_hf R hqN hval₁ i⟩} :
          Set ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)))
        ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)
      = Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q))))
          ↥(modularFunctionFieldBar (N * q)) := by
  haveI := charP_residueField R
  have hq : q.Prime := Fact.out
  have hcop : Nat.Coprime N q := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN)

  have e₁ := finrank_adjoin_residue₁_jFun R hqN (by simpa using inst_hf R hqN hval₁ 0)
  have e₂ := finrank_adjoin_residue₂_jFun R hqN (by simpa using inst_hf R hqN hval₁ 1)

  have e₃ : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q)))) ↥(modularFunctionFieldBar (N * q))
      = dedekindPsi N + q * dedekindPsi N := by
    rw [finrank_adjoin_jFun_bar, dedekindPsi_mul_of_coprime N q hcop, dedekindPsi_prime (q := q)]
    ring
  rw [Fin.sum_univ_two, e₃]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

  congr 1

private theorem inst_coeff_mem {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (c : ↥(modularFunctionFieldBar (N * q)))
    (hcj : c ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({ProlongationTuple.jFun N q} : Set ↥(modularFunctionFieldBar (N * q))))
    (hc : c ∈ R.R₁.integers) :
    ∃ v : ↥(locRing A red N), heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) = c := by
  exact ⟨⟨⟨(c : LaurentSeries (AlgebraicClosure ℚ)), coe_mem_bar_of_mem_adjoin hcj⟩,
    mk_mem_locRing (coe_mem_bar_of_mem_adjoin hcj)
      (mem_modularLocalized_of_mem_adjoin hqN (jqNModC_mem_modularLocalized_mul hval₁)
        (coe_mem_adjoin_pair_of_mem_adjoin hcj) ((R.mem_integersFst_iff c).mp hc))⟩,
    heckeAlphaBar_mk_eq (coe_mem_bar_of_mem_adjoin hcj)⟩

private theorem finite_of_repr {V F' : Type*} [CommRing V] [Field F'] [Algebra V F'] (S : Subalgebra V F')
    {d : ℕ} (z : Fin d → F') (hz : ∀ σ, z σ ∈ S)
    (hrep : ∀ b ∈ S, ∃ v : Fin d → V, b = ∑ σ, algebraMap V F' (v σ) * z σ) :
    Module.Finite V ↥S := by
  refine Module.Finite.of_surjective (Fintype.linearCombination V fun σ => (⟨z σ, hz σ⟩ : ↥S)) ?_
  rintro ⟨b, hb⟩
  obtain ⟨v, hv⟩ := hrep b hb
  refine ⟨v, Subtype.ext ?_⟩
  change S.val (Fintype.linearCombination V (fun σ => (⟨z σ, hz σ⟩ : ↥S)) v) = b
  rw [Fintype.linearCombination_apply, map_sum, hv]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_smul, Algebra.smul_def]
  rfl

private def gaussFamily {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :=
  RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq
    (L := AlgebraicClosure ℚ) A (ι := Fin 2)
    (fun _ => ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) ![R.R₁, R.R₂]
    (inst_hR R hqN hval₁) (ProlongationTuple.jFun N q) (inst_hf R hqN hval₁) inst_htrL inst_hfd
    (inst_htr R hqN hval₁) 0
    (@RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed
      (AlgebraicClosure ℚ) _ _ A _ _ _ (Fin 2) _ _
      (fun _ => ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N)) _ _ ![R.R₁, R.R₂]
      (inst_hR R hqN hval₁) (ProlongationTuple.jFun N q) (inst_hf R hqN hval₁) (inst_htr R hqN hval₁)
      inst_hfd (inst_heq R hqN hval₁) 0)
    (inst_heq R hqN hval₁)

private theorem orderS_finite {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    Module.Finite ↥(locRing A red N) ↥(orderS hqN hval₁) := by
  obtain ⟨d', z, hzO, -, -, hrep⟩ := gaussFamily R hqN hval₁
  refine finite_of_repr (orderS hqN hval₁) z (fun σ => ?_) (fun b hb => ?_)
  · have h₁ := hzO σ 0
    have h₂ := hzO σ 1
    simp only [Matrix.cons_val_zero] at h₁
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h₂
    exact (mem_orderS hqN hval₁ (z σ)).mpr ⟨(R.mem_integersFst_iff (z σ)).mp h₁, (R.mem_integersSnd_iff (z σ)).mp h₂⟩
  · have hb' := (mem_orderS hqN hval₁ b).mp hb
    have hb₁ := (R.mem_integersFst_iff b).mpr hb'.1
    have hb₂ := (R.mem_integersSnd_iff b).mpr hb'.2
    obtain ⟨c, hc, hbc⟩ := hrep b (Fin.forall_fin_two.mpr ⟨by simpa using hb₁, by simpa using hb₂⟩)
    have hv : ∀ σ, ∃ v : ↥(locRing A red N),
        heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) = c σ := fun σ => by
      have hc₁ := hc σ
      simp only [Matrix.cons_val_zero] at hc₁
      exact inst_coeff_mem R hqN hval₁ (c σ) (c σ).2 hc₁
    choose v hv using hv
    refine ⟨v, ?_⟩
    rw [hbc]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [algebraMap_locRing_apply, hv]

end GaussSheet

section ThinHelpers

variable {L : Type*} [Field L] {B : ValuationSubring L}

private theorem exists_smul_mem_two {F F₁ F₂ : Type*} [Field F] [Algebra L F] [Field F₁] [Field F₂]
    [Algebra (IsLocalRing.ResidueField B) F₁] [Algebra (IsLocalRing.ResidueField B) F₂]
    (S₁ : RegularProlongation B F F₁) (S₂ : RegularProlongation B F F₂) (x : F) (hx : x ≠ 0) :
    ∃ c : L, c ≠ 0 ∧ c • x ∈ S₁.integers ∧ c • x ∈ S₂.integers := by
  obtain ⟨c₁, h₁, hr₁⟩ := S₁.exists_smul_mem x hx
  obtain ⟨c₂, h₂, hr₂⟩ := S₂.exists_smul_mem x hx
  have hc₁ : c₁ ≠ 0 := by
    rintro rfl
    apply hr₁
    have h0 : (⟨(0 : L) • x, h₁⟩ : S₁.integers) = 0 := Subtype.ext (by simp)
    rw [h0, map_zero]
  have hc₂ : c₂ ≠ 0 := by
    rintro rfl
    apply hr₂
    have h0 : (⟨(0 : L) • x, h₂⟩ : S₂.integers) = 0 := Subtype.ext (by simp)
    rw [h0, map_zero]
  rcases B.mem_or_inv_mem (c₂ / c₁) with h | h
  · refine ⟨c₂, hc₂, ?_, h₂⟩
    have e : c₂ • x = algebraMap L F (c₂ / c₁) * (c₁ • x) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₁]
    rw [e]
    exact mul_mem ((S₁.algebraMap_mem_iff _).mpr h) h₁
  · rw [inv_div] at h
    refine ⟨c₁, hc₁, h₁, ?_⟩
    have e : c₁ • x = algebraMap L F (c₁ / c₂) * (c₂ • x) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₂]
    rw [e]
    exact mul_mem ((S₂.algebraMap_mem_iff _).mpr h) h₂

private theorem span_eq_top_of_prolongations {K F' F₁ F₂ : Type*} [Field K] [Algebra L K]
    [Field F'] [Algebra L F'] [Field F₁] [Field F₂]
    [Algebra (IsLocalRing.ResidueField B) F₁] [Algebra (IsLocalRing.ResidueField B) F₂]
    (φ : K →ₐ[L] F') (S₁ : RegularProlongation B F' F₁) (S₂ : RegularProlongation B F' F₂)
    (T : Set F') (hT : ∀ y, y ∈ S₁.integers → y ∈ S₂.integers → y ∈ T) :
    letI := algebraAlong φ
    Submodule.span K T = ⊤ := by
  letI := algebraAlong φ
  rw [Submodule.eq_top_iff']
  intro x
  by_cases hx : x = 0
  · rw [hx]
    exact Submodule.zero_mem _
  obtain ⟨c, hc, h₁, h₂⟩ := exists_smul_mem_two S₁ S₂ x hx
  have hx' : x = (algebraMap L K c⁻¹) • (c • x) := by
    show x = φ (algebraMap L K c⁻¹) * (c • x)
    rw [φ.commutes, Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hT _ h₁ h₂))

end ThinHelpers

set_option synthInstance.maxHeartbeats 1600000 in

private theorem span_orderS_eq_top {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    Submodule.span ↥(modularFunctionFieldBar N)
        ((orderS (A := A) (red := red) hqN hval₁ : Set ↥(modularFunctionFieldBar (N * q)))) = ⊤ := by
  exact span_eq_top_of_prolongations (heckeAlphaBar (AlgebraicClosure ℚ) N q) R.R₁ R.R₂ _
    (fun y hy₁ hy₂ => SetLike.mem_coe.mpr ((mem_orderS hqN hval₁ y).mpr
      ⟨(R.mem_integersFst_iff y).mp hy₁, (R.mem_integersSnd_iff y).mp hy₂⟩))

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

section J3Splice

p2m_open "ModularCurve~dedekindPsi_prime P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization.ProlongationTuple"

namespace J3X1

section Generic

variable {L : Type*} [CommRing L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

private theorem qExpand_mem_integralCoeffs (n : ℕ) [NeZero n] {x : LaurentSeries L}
    (hx : x ∈ CharPReduction.integralCoeffs A) :
    qExpand L n x ∈ CharPReduction.integralCoeffs A := by
  intro m
  by_cases h : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul]
    exact hx m
  · rw [qExpand_coeff_of_not_dvd _ _ h]
    exact A.zero_mem

private theorem coeffRed_qExpand (n : ℕ) [NeZero n] (x : LaurentSeries L)
    (hx : x ∈ CharPReduction.integralCoeffs A)
    (hqx : qExpand L n x ∈ CharPReduction.integralCoeffs A) :
    CharPReduction.coeffRed A red ⟨qExpand L n x, hqx⟩ =
      qExpand k n (CharPReduction.coeffRed A red ⟨x, hx⟩) := by
  ext m
  rw [CharPReduction.coeffRed_coeff]
  by_cases h : (n : ℤ) ∣ m
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul n (CharPReduction.coeffRed A red ⟨x, hx⟩) m, CharPReduction.coeffRed_coeff]
    congr 1
    exact Subtype.ext (qExpand_coeff_mul n x m)
  · have h0 : (⟨(qExpand L n x).coeff m, hqx m⟩ : A) = 0 :=
      Subtype.ext (qExpand_coeff_of_not_dvd _ _ h)
    rw [h0, map_zero, qExpand_coeff_of_not_dvd _ _ h]

private theorem _root_.J3X1.modularRedLocHom_eq_coeffRed (M : ℕ) [NeZero M] {g : LaurentSeries L}
    (hg : g ∈ CharPReduction.modularLocalized M A red)
    (hgi : g ∈ CharPReduction.integralCoeffs A) :
    CharPReduction.modularRedLocHom M A red ⟨g, hg⟩ = CharPReduction.coeffRed A red ⟨g, hgi⟩ := by
  obtain ⟨r, s, hs, hgs⟩ := (CharPReduction.mem_localizedAtKer A red
    (CharPReduction.modularRing M A) (CharPReduction.modularRing_le_integralCoeffs M A)).mp hg
  have h1 := CharPReduction.redLoc_spec (A := A) (red := red) (R := CharPReduction.modularRing M A)
    (hR := CharPReduction.modularRing_le_integralCoeffs M A) ⟨g, hg⟩ hgs
  have hsne := (CharPReduction.notMem_redKer_iff A red (CharPReduction.modularRing M A)
    (CharPReduction.modularRing_le_integralCoeffs M A)).mp hs
  have h2 : CharPReduction.coeffRed A red ⟨g, hgi⟩ *
      CharPReduction.redRes A red (CharPReduction.modularRing M A)
        (CharPReduction.modularRing_le_integralCoeffs M A) s =
      CharPReduction.redRes A red (CharPReduction.modularRing M A)
        (CharPReduction.modularRing_le_integralCoeffs M A) r := by
    rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply, ← map_mul]
    congr 1
    exact Subtype.ext hgs
  exact mul_right_cancel₀ hsne (h1.trans h2.symm)

p2m_export "J3X1" "modularRedLocHom_eq_coeffRed"

private theorem coeffRed_eq_jqNModC (M : ℕ) [NeZero M] {x : LaurentSeries L}
    (hxi : x ∈ CharPReduction.integralCoeffs A) (hxe : x = jqNModC L M) :
    CharPReduction.coeffRed A red ⟨x, hxi⟩ = jqNModC k M := by
  have key : ∀ (y : L) (hy : y ∈ A) (z : ℤ), y = (z : L) → red ⟨y, hy⟩ = (z : k) := by
    rintro y hy z rfl
    have e : (⟨(z : L), hy⟩ : A) = (z : A) := Subtype.ext (by simp)
    rw [e, map_intCast]
  have key0 : ∀ (y : L) (hy : y ∈ A), y = 0 → red ⟨y, hy⟩ = 0 := by
    rintro y hy rfl
    exact map_zero red
  ext n
  rw [CharPReduction.coeffRed_coeff]
  by_cases h : (M : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [jqNModC, qExpand_coeff_mul, coeff_jqModC_eq_intCast]
    apply key
    show x.coeff _ = _
    rw [hxe, jqNModC, qExpand_coeff_mul, coeff_jqModC_eq_intCast]
  · rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]
    apply key0
    show x.coeff _ = _
    rw [hxe, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

section PthPowers

variable {E : Type*} [Field E] {p : ℕ} [Fact p.Prime] [CharP E p]

private theorem pow_mem_of_mem_closure (K₀ : Subfield E) (s : Set E) (hs : ∀ x ∈ s, x ^ p ∈ K₀)
    {z : E} (hz : z ∈ Subring.closure ((K₀ : Set E) ∪ s)) : z ^ p ∈ K₀ := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · exact K₀.pow_mem hx p
      · exact hs x hx
  | zero =>
      rw [zero_pow (Fact.out : p.Prime).ne_zero]
      exact K₀.zero_mem
  | one =>
      rw [one_pow]
      exact K₀.one_mem
  | add x y _ _ ihx ihy =>
      rw [add_pow_char]
      exact K₀.add_mem ihx ihy
  | neg x _ ih =>
      rw [neg_pow]
      exact K₀.mul_mem (K₀.pow_mem (K₀.neg_mem K₀.one_mem) p) ih
  | mul x y _ _ ihx ihy =>
      rw [mul_pow]
      exact K₀.mul_mem ihx ihy

private theorem inv_mem_closure (K₀ : Subfield E) (s : Set E) (hs : ∀ x ∈ s, x ^ p ∈ K₀)
    {z : E} (hz : z ∈ Subring.closure ((K₀ : Set E) ∪ s)) :
    z⁻¹ ∈ Subring.closure ((K₀ : Set E) ∪ s) := by
  by_cases hz0 : z = 0
  · rw [hz0, inv_zero]
    exact Subring.zero_mem _
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have e : z⁻¹ = z ^ (p - 1) * (z ^ p)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero p hz0)]
    conv_lhs => rw [← Nat.sub_add_cancel hp1, pow_succ']
    exact inv_mul_cancel_left₀ hz0 _
  rw [e]
  exact Subring.mul_mem _ (Subring.pow_mem _ hz (p - 1))
    (Subring.subset_closure (Or.inl (K₀.inv_mem (pow_mem_of_mem_closure K₀ s hs hz))))

end PthPowers
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

section Field

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] {N : ℕ} [NeZero N]

private theorem jqModC_pow_pow_sub_ne_zero : (jqModC k ^ q) ^ q - jqModC k ≠ 0 := by
  rw [← pow_mul]
  have hlt : (-((q * q : ℕ) : ℤ)) < -1 := by
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    have h4 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq2 hq2
    omega
  have h1 : (jqModC k ^ (q * q) - jqModC k).coeff (-((q * q : ℕ) : ℤ)) = 1 := by
    rw [HahnSeries.coeff_sub, coeff_jqModC_pow_self, coeff_jqModC_of_lt k hlt, sub_zero]
  intro h0
  rw [h0] at h1
  simp at h1

variable [CharP k q]

private theorem jqModC_pow_eq_qExpand [NeZero q] : jqModC k ^ q = qExpand k q (jqModC k) := by
  have h := jqNModC_mul_eq_pow k 1 (ℓ := q)
  rw [jqNModC_one] at h
  rw [← h]
  exact qExpand_congr (one_mul q) _

private theorem jqNModC_pow_eq_qExpand [NeZero q] :
    jqNModC k N ^ q = qExpand k q (jqNModC k N) := by
  rw [← jqNModC_mul_eq_pow k N]
  show qExpand k (N * q) (jqModC k) = qExpand k q (qExpand k N (jqModC k))
  rw [qExpand_qExpand, qExpand_congr (Nat.mul_comm N q)]

private theorem modularFunctionFieldC_mul_le :
    modularFunctionFieldC k (N * q) ≤ modularFunctionFieldC k N := by
  show IntermediateField.adjoin k {jqModC k, jqNModC k (N * q)} ≤ modularFunctionFieldC k N
  rw [IntermediateField.adjoin_le_iff]
  rintro y (rfl | rfl)
  · exact jqModC_mem k N
  · rw [jqNModC_mul_eq_pow]
    exact pow_mem (jqNModC_mem k N) q

private theorem mem_of_qExpand_mem (B : Subring (LaurentSeries k))
    (hB : ∀ y ∈ modularFunctionFieldC k N, qExpand k q y ∈ B)
    (hj : jqModC k ∈ B) (hjN : jqNModC k N ∈ B)
    {b : LaurentSeries k} (hb : b ∈ modularFunctionFieldC k N) : b ∈ B := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : CharP (LaurentSeries k) q :=
    charP_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective q
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : Subfield (LaurentSeries k),
      ∀ x, x ∈ K₀ ↔ ∃ y ∈ modularFunctionFieldC k N, qExpand k q y = x :=
    ⟨(modularFunctionFieldC k N).toSubfield.map (qExpand k q), fun x => Subfield.mem_map⟩
  have hK₀q : ∀ y ∈ modularFunctionFieldC k N, qExpand k q y ∈ K₀ := fun y hy =>
    (hK₀ _).mpr ⟨y, hy, rfl⟩
  have hs : ∀ x ∈ ({jqModC k, jqNModC k N} : Set (LaurentSeries k)), x ^ q ∈ K₀ := by
    rintro x (rfl | rfl)
    · rw [jqModC_pow_eq_qExpand]
      exact hK₀q _ (jqModC_mem k N)
    · rw [jqNModC_pow_eq_qExpand]
      exact hK₀q _ (jqNModC_mem k N)
  let F : Subfield (LaurentSeries k) :=
    { Subring.closure ((K₀ : Set (LaurentSeries k)) ∪ {jqModC k, jqNModC k N}) with
      inv_mem' := fun z hz => inv_mem_closure K₀ _ hs hz }
  have hb' : b ∈ Subfield.closure
      (Set.range (algebraMap k (LaurentSeries k)) ∪ {jqModC k, jqNModC k N}) := hb
  have hsub : Set.range (algebraMap k (LaurentSeries k)) ∪ {jqModC k, jqNModC k N} ⊆
      (F : Set (LaurentSeries k)) := by
    rintro x (⟨c, rfl⟩ | hx)
    · show algebraMap k (LaurentSeries k) c ∈
        Subring.closure ((K₀ : Set (LaurentSeries k)) ∪ {jqModC k, jqNModC k N})
      have e : algebraMap k (LaurentSeries k) c = qExpand k q (algebraMap k (LaurentSeries k) c) := by
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
      rw [e]
      exact Subring.subset_closure (Or.inl (hK₀q _ ((modularFunctionFieldC k N).algebraMap_mem c)))
    · show x ∈ Subring.closure ((K₀ : Set (LaurentSeries k)) ∪ {jqModC k, jqNModC k N})
      exact Subring.subset_closure (Or.inr hx)
  have hbF : b ∈ F := (Subfield.closure_le (t := F)).mpr hsub hb'
  have hbR : b ∈ Subring.closure ((K₀ : Set (LaurentSeries k)) ∪ {jqModC k, jqNModC k N}) := hbF
  refine (Subring.closure_le (t := B)).mpr ?_ hbR
  rintro x (hx | hx)
  · obtain ⟨y, hy, rfl⟩ := (hK₀ x).mp hx
    exact hB y hy
  · rcases hx with rfl | rfl
    · exact hj
    · exact hjN

end Field
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

section Level

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k]

private theorem mem_bar_of_mem_modularRing (M : ℕ) [NeZero M]
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ CharPReduction.modularRing M A.toSubring) :
    x ∈ modularFunctionFieldBar M := by
  have hle : CharPReduction.modularRing M A.toSubring ≤ (modularFunctionFieldBar M).toSubring := by
    rw [CharPReduction.modularRing, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl | rfl)
    · exact (modularFunctionFieldBar M).algebraMap_mem (a : AlgebraicClosure ℚ)
    · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
        show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ)
        exact (map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full M (jq_mem M))
    · have h : jqNModC (AlgebraicClosure ℚ) M =
          coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
        show qExpand _ M (jqModC _) = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ M (jqModC ℚ))
        rw [coeffMap_qExpand]
        congr 1
        exact (map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M dvd_rfl)
  exact hle hx

private def IsRedPair (red : A →+* k) (S : Subring (modularFunctionFieldBar (N * q)))
    (x y : LaurentSeries k) : Prop :=
  ∃ s ∈ S,
    ∃ (h₁ : (s : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
      (h₂ : ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ = x ∧
      CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₂⟩ = y

variable {red : A →+* k} {S : Subring (modularFunctionFieldBar (N * q))}

private theorem isRedPair_one
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    IsRedPair red S 1 1 := by
  refine ⟨1, S.one_mem, (hS 1 S.one_mem).1, (hS 1 S.one_mem).2, ?_, ?_⟩
  · exact map_one (CharPReduction.modularRedLocHom (N * q) A.toSubring red)
  · have e : (⟨((atkinLehnerBar N q 1 : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ)), (hS 1 S.one_mem).2⟩ :
        CharPReduction.modularLocalized (N * q) A.toSubring red) = 1 :=
      Subtype.ext (by dsimp only; rw [map_one (atkinLehnerBar N q)]; rfl)
    rw [e, map_one]

private theorem isRedPair_add
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x y x' y' : LaurentSeries k} (h : IsRedPair red S x y) (h' : IsRedPair red S x' y') :
    IsRedPair red S (x + x') (y + y') := by
  obtain ⟨s, hs, h₁, h₂, rfl, rfl⟩ := h
  obtain ⟨s', hs', h₁', h₂', rfl, rfl⟩ := h'
  refine ⟨s + s', S.add_mem hs hs', (hS _ (S.add_mem hs hs')).1, (hS _ (S.add_mem hs hs')).2,
    ?_, ?_⟩
  · rw [← map_add (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    rfl
  · rw [← map_add (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    congr 1
    apply Subtype.ext
    dsimp only
    rw [map_add (atkinLehnerBar N q)]
    rfl

private theorem isRedPair_mul
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x y x' y' : LaurentSeries k} (h : IsRedPair red S x y) (h' : IsRedPair red S x' y') :
    IsRedPair red S (x * x') (y * y') := by
  obtain ⟨s, hs, h₁, h₂, rfl, rfl⟩ := h
  obtain ⟨s', hs', h₁', h₂', rfl, rfl⟩ := h'
  refine ⟨s * s', S.mul_mem hs hs', (hS _ (S.mul_mem hs hs')).1, (hS _ (S.mul_mem hs hs')).2,
    ?_, ?_⟩
  · rw [← map_mul (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    rfl
  · rw [← map_mul (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    congr 1
    apply Subtype.ext
    dsimp only
    rw [map_mul (atkinLehnerBar N q)]
    rfl

private theorem isRedPair_neg
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x y : LaurentSeries k} (h : IsRedPair red S x y) : IsRedPair red S (-x) (-y) := by
  obtain ⟨s, hs, h₁, h₂, rfl, rfl⟩ := h
  refine ⟨-s, S.neg_mem hs, (hS _ (S.neg_mem hs)).1, (hS _ (S.neg_mem hs)).2, ?_, ?_⟩
  · rw [← map_neg (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    rfl
  · rw [← map_neg (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    congr 1
    apply Subtype.ext
    dsimp only
    rw [map_neg (atkinLehnerBar N q)]
    rfl

private theorem isRedPair_sub
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x y x' y' : LaurentSeries k} (h : IsRedPair red S x y) (h' : IsRedPair red S x' y') :
    IsRedPair red S (x - x') (y - y') := by
  simpa [sub_eq_add_neg] using isRedPair_add hS h (isRedPair_neg hS h')

private theorem isRedPair_pow
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {x y : LaurentSeries k} (h : IsRedPair red S x y) (n : ℕ) :
    IsRedPair red S (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using isRedPair_one hS
  | succ n ih => simpa [pow_succ] using isRedPair_mul hS ih h

private theorem isAtkinLehnerAutFull_of_not_dvd [NeZero q] (hqN : ¬ q ∣ N) :
    IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)

private theorem coe_atkinLehnerBar_of_coe_eq [NeZero q] (hqN : ¬ q ∣ N)
    (v : modularFunctionFieldBar N) (s : modularFunctionFieldBar (N * q))
    (hsv : (s : LaurentSeries (AlgebraicClosure ℚ)) = (v : LaurentSeries (AlgebraicClosure ℚ))) :
    ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) q (v : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hcomp := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _
    (isAtkinLehnerAutFull_of_not_dvd hqN)).1
  have e : s = heckeAlphaBar (AlgebraicClosure ℚ) N q v :=
    Subtype.ext (by rw [hsv, coe_heckeAlphaBar])
  rw [e]
  show _ = ((heckeBetaBar (AlgebraicClosure ℚ) N q v : modularFunctionFieldBar (N * q)) :
    LaurentSeries (AlgebraicClosure ℚ))
  unfold atkinLehnerBar
  exact congrArg Subtype.val (AlgHom.congr_fun hcomp v)

private theorem isRedPair_jQFun [CharP k q] (hqN : ¬ q ∣ N)
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hjQ : jQFun N q ∈ S) : IsRedPair red S (jqModC k ^ q) (jqModC k) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨-, h1⟩ := isAtkinLehnerAutFull_of_not_dvd (N := N) hqN 1 inferInstance (one_dvd N)
  have hv : ((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqNModC (AlgebraicClosure ℚ) q := by
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q (jqModC ℚ)) =
      qExpand _ q (jqModC _)
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC _
  have hw : ((atkinLehnerBar N q (jQFun N q) : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    have e : jQFun N q =
        ⟨coeffEmb (AlgebraicClosure ℚ)
            ((⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
              modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
              modularFunctionFieldFull (N * q)).2⟩ := by
      apply Subtype.ext
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) =
        coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
      rw [qExpand_congr (one_mul q)]
    rw [e]
    unfold atkinLehnerBar
    rw [coe_geomAut_coeffEmb, h1]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ 1 (jqModC ℚ)) = _
    rw [qExpand_one_apply]
    exact map_jqModC _
  refine ⟨jQFun N q, hjQ, (hS _ hjQ).1, (hS _ hjQ).2, ?_, ?_⟩
  · rw [modularRedLocHom_eq_coeffRed A.toSubring red (N * q) (hS _ hjQ).1
        (by rw [hv]; exact CharPReduction.jqNModC_mem_integralCoeffs q A.toSubring),
      coeffRed_eq_jqNModC A.toSubring red q _ hv, jqModC_pow_eq_qExpand]
    rfl
  · rw [modularRedLocHom_eq_coeffRed A.toSubring red (N * q) (hS _ hjQ).2
        (by rw [hw]; exact CharPReduction.jqModC_mem_integralCoeffs A.toSubring),
      coeffRed_eq_jqNModC A.toSubring red 1 _ (hw.trans (jqNModC_one _).symm), jqNModC_one]

private theorem isRedPair_jNQ [CharP k q] (hqN : ¬ q ∣ N)
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    {s : modularFunctionFieldBar (N * q)} (hsS : s ∈ S)
    (hs : (s : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq)) :
    IsRedPair red S (jqNModC k N ^ q) (jqNModC k N) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨-, hN⟩ := isAtkinLehnerAutFull_of_not_dvd (N := N) hqN N inferInstance (dvd_refl N)
  have e : s =
      ⟨coeffEmb (AlgebraicClosure ℚ)
          ((⟨qExpand ℚ (N * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (dvd_refl N) q)⟩ :
            modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (⟨qExpand ℚ (N * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (dvd_refl N) q)⟩ :
            modularFunctionFieldFull (N * q)).2⟩ :=
    Subtype.ext hs
  have hw : ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) N := by
    rw [e]
    unfold atkinLehnerBar
    rw [coe_geomAut_coeffEmb, hN]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N (jqModC ℚ)) =
      qExpand _ N (jqModC _)
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC _
  have hv : (s : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (N * q) := by
    rw [hs]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (N * q) (jqModC ℚ)) =
      qExpand _ (N * q) (jqModC _)
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC _
  refine ⟨s, hsS, (hS _ hsS).1, (hS _ hsS).2, ?_, ?_⟩
  · rw [modularRedLocHom_eq_coeffRed A.toSubring red (N * q) (hS _ hsS).1
        (by rw [hv]; exact CharPReduction.jqNModC_mem_integralCoeffs (N * q) A.toSubring),
      coeffRed_eq_jqNModC A.toSubring red (N * q) _ hv]
    exact jqNModC_mul_eq_pow k N
  · rw [modularRedLocHom_eq_coeffRed A.toSubring red (N * q) (hS _ hsS).2
        (by rw [hw]; exact CharPReduction.jqNModC_mem_integralCoeffs N A.toSubring),
      coeffRed_eq_jqNModC A.toSubring red N _ hw]

private theorem isRedPair_qExpand (hqN : ¬ q ∣ N) (hred : Function.Surjective red)
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hV : ∀ v : modularFunctionFieldBar N,
      (v : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red →
      ∃ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ)) = (v : LaurentSeries (AlgebraicClosure ℚ)))
    {y : LaurentSeries k} (hy : y ∈ modularFunctionFieldC k N) :
    IsRedPair red S y (qExpand k q y) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := CharPReduction.exists_modularRedLocHom_eq A.toSubring red N hred hy
  obtain ⟨r, t, ht, hft⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red
    (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp f.2
  have htI : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
    CharPReduction.modularRing_le_integralCoeffs N A.toSubring t.2
  have hrI : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring :=
    CharPReduction.modularRing_le_integralCoeffs N A.toSubring r.2
  have hqtI := qExpand_mem_integralCoeffs A.toSubring q htI
  have hqrI := qExpand_mem_integralCoeffs A.toSubring q hrI

  have hy' : y * CharPReduction.coeffRed A.toSubring red ⟨_, htI⟩ =
      CharPReduction.coeffRed A.toSubring red ⟨_, hrI⟩ := by
    have h := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) f hft
    rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply] at h
    rw [← hf]
    exact h
  have hct0 : CharPReduction.coeffRed A.toSubring red ⟨_, htI⟩ ≠ 0 := by
    have h := (CharPReduction.notMem_redKer_iff A.toSubring red
      (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp ht
    rwa [CharPReduction.redRes_apply] at h
  have ht0 : (t : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h0 =>
    hct0 (by
      rw [show (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), htI⟩ :
          CharPReduction.integralCoeffs A.toSubring) = 0 from Subtype.ext h0, map_zero])

  have htB : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N :=
    mem_bar_of_mem_modularRing N t.2
  have hfB : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N := by
    have hfe : (f : LaurentSeries (AlgebraicClosure ℚ)) = r / t := by
      rw [eq_div_iff ht0]
      exact hft
    rw [hfe]
    exact div_mem (mem_bar_of_mem_modularRing N r.2) htB
  have htO : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized N A.toSubring red :=
    CharPReduction.subring_le_localizedAtKer A.toSubring red
      (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) t.2
  obtain ⟨sf, hsf, hsfe⟩ := hV ⟨_, hfB⟩ f.2
  obtain ⟨st, hst, hste⟩ := hV ⟨_, htB⟩ htO
  have hsfe' : (sf : LaurentSeries (AlgebraicClosure ℚ)) = f := hsfe
  have hste' : (st : LaurentSeries (AlgebraicClosure ℚ)) = t := hste
  have hwf := coe_atkinLehnerBar_of_coe_eq hqN ⟨_, hfB⟩ sf hsfe
  have hwt := coe_atkinLehnerBar_of_coe_eq hqN ⟨_, htB⟩ st hste
  obtain ⟨hf₁, hf₂⟩ := hS sf hsf
  obtain ⟨ht₁, ht₂⟩ := hS st hst
  have hfO' : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hsfe']; exact hf₁
  have htO' : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hste']; exact ht₁
  have hqfO : qExpand (AlgebraicClosure ℚ) q (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hwf]; exact hf₂
  have hqtO : qExpand (AlgebraicClosure ℚ) q (t : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hwt]; exact ht₂
  have hrO' : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hft]; exact mul_mem hfO' htO'
  have hqrO : qExpand (AlgebraicClosure ℚ) q (r : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hft, map_mul]; exact mul_mem hqfO hqtO
  refine ⟨sf, hsf, hf₁, hf₂, ?_, ?_⟩
  · have e1 : (⟨(sf : LaurentSeries (AlgebraicClosure ℚ)), hf₁⟩ :
        CharPReduction.modularLocalized (N * q) A.toSubring red) = ⟨_, hfO'⟩ := Subtype.ext hsfe'
    rw [e1]
    apply mul_right_cancel₀ hct0
    rw [hy', ← modularRedLocHom_eq_coeffRed A.toSubring red (N * q) htO' htI,
      ← modularRedLocHom_eq_coeffRed A.toSubring red (N * q) hrO' hrI,
      ← map_mul (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    congr 1
    exact Subtype.ext hft
  · have e2 : (⟨((atkinLehnerBar N q sf : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ)), hf₂⟩ :
        CharPReduction.modularLocalized (N * q) A.toSubring red) = ⟨_, hqfO⟩ := Subtype.ext hwf
    rw [e2]
    have hqct0 : qExpand k q (CharPReduction.coeffRed A.toSubring red ⟨_, htI⟩) ≠ 0 :=
      (map_ne_zero_iff _ (qExpand_injective (R := k) q)).mpr hct0
    apply mul_right_cancel₀ hqct0
    rw [← map_mul (qExpand k q), hy', ← coeffRed_qExpand A.toSubring red q _ htI hqtI,
      ← coeffRed_qExpand A.toSubring red q _ hrI hqrI,
      ← modularRedLocHom_eq_coeffRed A.toSubring red (N * q) hqtO hqtI,
      ← modularRedLocHom_eq_coeffRed A.toSubring red (N * q) hqrO hqrI,
      ← map_mul (CharPReduction.modularRedLocHom (N * q) A.toSubring red)]
    congr 1
    apply Subtype.ext
    show qExpand _ q (f : LaurentSeries (AlgebraicClosure ℚ)) *
        qExpand _ q (t : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand _ q (r : LaurentSeries (AlgebraicClosure ℚ))
    rw [← map_mul, hft]

end Level
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

end J3X1
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_C qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence transcendental_jqNModC transcendental_jqModC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb coeff_jqModC_eq_intCast coeff_jqModC_of_lt modularFunctionFieldFullC jqModC_mem_full coeffMap_qExpand coeff_jqModC_pow_self CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.localizedAtKer CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc_spec CharPReduction.redLocHom CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.jqNModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPReduction.exists_modularRedLocHom_eq CharPReduction.mem_or_inv_mem_modularLocalized CharPReduction.modularRedLocHom_eq_coeffRed CharPReduction.modularRedLocHom_mem CompEq.finrank_adjoin_jBar_eq_dedekindPsi coeffEmb_jq coeffEmb_jqN dedekindPsi_mul_of_coprime exists_isAtkinLehnerAutFull_of_prime_of_not_dvd finiteDimensional_adjoin_coeffEmb_jq_full finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi geomAut_atkinLehner_comp_legs jqNModC_mul_eq_pow nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar jFun jQFun mem_integers₂_iff residue₁ residue₂ R₁ ι mem_integersFst_iff R₂ residue₁_eq_modularRedLocHom redBar residue₁_coeffMap mem_integersSnd_iff residue₂_eq" end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in
open J3X1 in

private theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_modularRedLocHom_eq_and_modularRedLocHom_atkinLehnerBar_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] (red : A →+* k)
    (hqN : ¬ q ∣ N) (hred : Function.Surjective red)
    (S : Subring (modularFunctionFieldBar (N * q)))
    (hjQ : jQFun N q ∈ S)
    (hjNQ : ∃ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq))
    (hS : ∀ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
      ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
          LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
    (hV : ∀ v : modularFunctionFieldBar N,
      (v : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red →
      ∃ s ∈ S, (s : LaurentSeries (AlgebraicClosure ℚ)) = (v : LaurentSeries (AlgebraicClosure ℚ)))
    (a b : modularFunctionFieldC k N) :
    ∃ s ∈ S,
      ∃ (h₁ : (s : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
        (h₂ : ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
              LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ = (a : LaurentSeries k) ∧
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₂⟩ = (b : LaurentSeries k) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨sNQ, hsNQ, hsNQe⟩ := hjNQ

  let B : Subring (LaurentSeries k) :=
    { carrier := {y | ∃ x, J3X1.IsRedPair red S x y}
      mul_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨x', hx'⟩
        exact ⟨_, isRedPair_mul hS hx hx'⟩
      one_mem' := ⟨_, isRedPair_one hS⟩
      add_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨x', hx'⟩
        exact ⟨_, isRedPair_add hS hx hx'⟩
      zero_mem' := ⟨0, by simpa using isRedPair_qExpand hqN hred hS hV (zero_mem _)⟩
      neg_mem' := by
        rintro _ ⟨x, hx⟩
        exact ⟨_, isRedPair_neg hS hx⟩ }
  have hB : ∀ y ∈ modularFunctionFieldC k N, qExpand k q y ∈ B := fun y hy =>
    ⟨y, isRedPair_qExpand hqN hred hS hV hy⟩
  have hP1 : J3X1.IsRedPair red S (jqModC k ^ q) (jqModC k) := isRedPair_jQFun hqN hS hjQ
  have hP2 : J3X1.IsRedPair red S (jqNModC k N ^ q) (jqNModC k N) :=
    isRedPair_jNQ hqN hS hsNQ hsNQe

  obtain ⟨x, hx⟩ : (b : LaurentSeries k) ∈ B := mem_of_qExpand_mem B hB ⟨_, hP1⟩ ⟨_, hP2⟩ b.2
  have hxC : x ∈ modularFunctionFieldC k N := by
    obtain ⟨s, -, h₁, -, hx1, -⟩ := hx
    rw [← hx1]
    exact modularFunctionFieldC_mul_le (CharPReduction.modularRedLocHom_mem A.toSubring red (N * q) _)

  have hPj : J3X1.IsRedPair red S (jqModC k) (jqModC k ^ q) := by
    have h := isRedPair_qExpand hqN hred hS hV (jqModC_mem k N)
    rwa [← jqModC_pow_eq_qExpand] at h
  have hD : J3X1.IsRedPair red S ((jqModC k ^ q) ^ q - jqModC k) 0 := by
    have h := isRedPair_sub hS (isRedPair_pow hS hP1 q) hPj
    rwa [sub_self] at h
  have hcC : ((a : LaurentSeries k) - x) / ((jqModC k ^ q) ^ q - jqModC k) ∈
      modularFunctionFieldC k N :=
    div_mem (sub_mem a.2 hxC) (sub_mem (pow_mem (pow_mem (jqModC_mem k N) q) q) (jqModC_mem k N))
  have h3 : J3X1.IsRedPair red S ((a : LaurentSeries k) - x) 0 := by
    have h := isRedPair_mul hS (isRedPair_qExpand hqN hred hS hV hcC) hD
    rwa [mul_zero, div_mul_cancel₀ _ jqModC_pow_pow_sub_ne_zero] at h
  have h4 : J3X1.IsRedPair red S (a : LaurentSeries k) (b : LaurentSeries k) := by
    have h := isRedPair_add hS h3 hx
    rwa [sub_add_cancel, zero_add] at h
  exact h4

end J3Splice
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_C qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand jq coeff_jq_neg_one dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence transcendental_jqNModC transcendental_jqModC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull geomAut geomAut_coeffEmb coe_geomAut_coeffEmb coeff_jqModC_eq_intCast coeff_jqModC_of_lt modularFunctionFieldFullC jqModC_mem_full coeffMap_qExpand coeff_jqModC_pow_self CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.localizedAtKer CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc_spec CharPReduction.redLocHom CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.jqNModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPReduction.exists_modularRedLocHom_eq CharPReduction.mem_or_inv_mem_modularLocalized CharPReduction.modularRedLocHom_eq_coeffRed CharPReduction.modularRedLocHom_mem CompEq.finrank_adjoin_jBar_eq_dedekindPsi coeffEmb_jq coeffEmb_jqN dedekindPsi_mul_of_coprime exists_isAtkinLehnerAutFull_of_prime_of_not_dvd finiteDimensional_adjoin_coeffEmb_jq_full finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi geomAut_atkinLehner_comp_legs jqNModC_mul_eq_pow nonempty_modularPolynomialData relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve~dedekindPsi_prime"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem coe_atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (v : ↥(modularFunctionFieldBar N)) :
    ((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) q (v : LaurentSeries (AlgebraicClosure ℚ)) := by
  have hleg : ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) =
      heckeBetaBar (AlgebraicClosure ℚ) N q v := by
    have h := AlgHom.congr_fun
      (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ (isAtkinLehnerAutFull_of_not_dvd hqN)).1 v
    rw [AlgHom.comp_apply] at h
    exact h
  rw [hleg, coe_heckeBetaBar]

omit [CharP k q] in

private theorem modularRedLocHom_qExpand {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hfN : f ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hqf : qExpand (AlgebraicClosure ℚ) q f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨qExpand (AlgebraicClosure ℚ) q f, hqf⟩ =
      qExpand k q (CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hfN⟩) := by
  obtain ⟨r, s, hs, hfs⟩ :=
    (CharPReduction.mem_localizedAtKer (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hfN
  obtain ⟨r', s', hs', hws⟩ :=
    (CharPReduction.mem_localizedAtKer (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing (N * q) A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)).mp hqf
  have hrI := CharPReduction.modularRing_le_integralCoeffs N A.toSubring r.2
  have hsI := CharPReduction.modularRing_le_integralCoeffs N A.toSubring s.2
  have hr'I := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring r'.2
  have hs'I := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring s'.2

  have hN := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨f, hfN⟩ hfs
  rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply] at hN
  have hNq := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (N * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)
    ⟨qExpand (AlgebraicClosure ℚ) q f, hqf⟩ hws
  rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply] at hNq

  have hsne := (CharPReduction.notMem_redKer_iff (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hs
  rw [CharPReduction.redRes_apply] at hsne
  have hs'ne := (CharPReduction.notMem_redKer_iff (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (N * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)).mp hs'
  rw [CharPReduction.redRes_apply] at hs'ne
  have hQsne := (map_ne_zero_iff (qExpand k q) (qExpand_injective q)).mpr hsne

  have hcross :
      (⟨(r' : LaurentSeries (AlgebraicClosure ℚ)), hr'I⟩ : CharPReduction.integralCoeffs A.toSubring) *
        ⟨qExpand (AlgebraicClosure ℚ) q ((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), hsI⟩ :
            CharPReduction.integralCoeffs A.toSubring) : LaurentSeries (AlgebraicClosure ℚ)),
          qExpand_mem_integralCoeffs A.toSubring q hsI⟩ =
      ⟨qExpand (AlgebraicClosure ℚ) q ((⟨(r : LaurentSeries (AlgebraicClosure ℚ)), hrI⟩ :
            CharPReduction.integralCoeffs A.toSubring) : LaurentSeries (AlgebraicClosure ℚ)),
          qExpand_mem_integralCoeffs A.toSubring q hrI⟩ *
        ⟨(s' : LaurentSeries (AlgebraicClosure ℚ)), hs'I⟩ := by
    apply Subtype.ext
    have h1 : qExpand (AlgebraicClosure ℚ) q f *
          qExpand (AlgebraicClosure ℚ) q (s : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) q (r : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← map_mul, hfs]
    show (r' : LaurentSeries (AlgebraicClosure ℚ)) *
          qExpand (AlgebraicClosure ℚ) q (s : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) q (r : LaurentSeries (AlgebraicClosure ℚ)) *
          (s' : LaurentSeries (AlgebraicClosure ℚ))
    rw [← hws, ← h1]
    ring
  have es := coeffRed_qExpand A.toSubring red q ⟨(s : LaurentSeries (AlgebraicClosure ℚ)), hsI⟩
  have er := coeffRed_qExpand A.toSubring red q ⟨(r : LaurentSeries (AlgebraicClosure ℚ)), hrI⟩
  have hc := congrArg (CharPReduction.coeffRed A.toSubring red) hcross
  rw [map_mul, map_mul, es, er] at hc
  have hNQ := congrArg (qExpand k q) hN
  rw [map_mul] at hNQ

  refine (CharPReduction.redLocHom_apply (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (N * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)
    ⟨qExpand (AlgebraicClosure ℚ) q f, hqf⟩).trans ?_
  refine Eq.trans ?_ (congrArg (qExpand k q)
    (CharPReduction.redLocHom_apply (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing N A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨f, hfN⟩)).symm
  apply mul_right_cancel₀ (mul_ne_zero hs'ne hQsne)
  linear_combination
    qExpand k q (CharPReduction.coeffRed A.toSubring red ⟨(s : LaurentSeries (AlgebraicClosure ℚ)), hsI⟩) *
        hNq +
      hc - CharPReduction.coeffRed A.toSubring red ⟨(s' : LaurentSeries (AlgebraicClosure ℚ)), hs'I⟩ * hNQ

omit [CharP k q] in

private theorem modularRedLocHom_atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N)
    (v : ↥(modularFunctionFieldBar N))
    (hv : (v : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
    (hw : ((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (N * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (N * q) A.toSubring red
        ⟨((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
            modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hw⟩ =
      qExpand k q
        (CharPReduction.modularRedLocHom N A.toSubring red ⟨(v : LaurentSeries (AlgebraicClosure ℚ)), hv⟩) := by
  have hser := coe_atkinLehnerBar_heckeAlphaBar hqN v
  have hqf : qExpand (AlgebraicClosure ℚ) q (v : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (N * q) A.toSubring red := by
    rw [← hser]
    exact hw
  have hx : (⟨((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hw⟩ :
          CharPReduction.modularLocalized (N * q) A.toSubring red) =
      ⟨qExpand (AlgebraicClosure ℚ) q (v : LaurentSeries (AlgebraicClosure ℚ)), hqf⟩ :=
    Subtype.ext hser
  rw [hx]
  exact modularRedLocHom_qExpand hv hqf

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization"

set_option synthInstance.maxHeartbeats 1600000 in
open _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N) (hred : Function.Surjective red) :
    letI : Algebra
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))))
        ↥(modularFunctionFieldBar (N * q)) :=
      ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp
        ((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)))).subtype).toAlgebra
    ∃ S : Subalgebra
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))))
        ↥(modularFunctionFieldBar (N * q)),
      (∀ g : modularFunctionFieldBar (N * q), g ∈ S ↔
        (g : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
          ((atkinLehnerBar N q g : modularFunctionFieldBar (N * q)) :
              LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) ∧
      (∀ v : modularFunctionFieldBar N,
        (v : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized N A.toSubring red →
          heckeAlphaBar (AlgebraicClosure ℚ) N q v ∈ S) ∧
      jQFun N q ∈ S ∧
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) dvd_rfl)⟩ :
          modularFunctionFieldBar (N * q)) ∈ S ∧
      Module.Finite
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)))) ↥S ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
       Submodule.span (modularFunctionFieldBar N) (S : Set (modularFunctionFieldBar (N * q))) = ⊤) ∧
      (∀ a b : modularFunctionFieldC k N, ∃ s ∈ S,
        ∃ (h₁ : (s : LaurentSeries (AlgebraicClosure ℚ))
              ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
          (h₂ : ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
                LaurentSeries (AlgebraicClosure ℚ))
              ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
          CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ = (a : LaurentSeries k) ∧
          CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₂⟩ = (b : LaurentSeries k)) ∧
      (∀ (f : LaurentSeries (AlgebraicClosure ℚ))
          (hfN : f ∈ CharPReduction.modularLocalized N A.toSubring red)
          (hfNq : f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hfNq⟩ =
          CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hfN⟩) ∧
      (∀ (v : modularFunctionFieldBar N)
          (hv : (v : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized N A.toSubring red)
          (hw : ((atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
              modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red
            ⟨((atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
                modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hw⟩ =
          qExpand k q (CharPReduction.modularRedLocHom N A.toSubring red
            ⟨(v : LaurentSeries (AlgebraicClosure ℚ)), hv⟩)) := by

  have hval₁ : ∀ g : modularFunctionFieldBar (N * q),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∨
        ((g⁻¹ : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          ∈ CharPReduction.modularLocalized (N * q) A.toSubring red :=
    fun g => (R.R₁.integers.mem_or_inv_mem g).imp (R.mem_integersFst_iff g).mp (R.mem_integersFst_iff g⁻¹).mp

  have hjN : jqNModC (AlgebraicClosure ℚ) N ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have hh := jN_coe_mem hval₁
    rw [← show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N from
      coeffEmb_jqN (AlgebraicClosure ℚ) N]
    exact hh
  refine ⟨orderS hqN hval₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact mem_orderS hqN hval₁
  ·
    exact fun v hv => heckeAlphaBar_mem_biLocRing hqN hval₁ v hv
  ·
    exact jQFun_mem_orderS hqN hval₁
  ·
    exact jNQ_mem_orderS hqN hval₁
  ·
    exact orderS_finite R hqN hval₁
  ·
    exact span_orderS_eq_top R hqN hval₁
  ·
    exact fun a b =>
      exists_mem_modularRedLocHom_eq_and_modularRedLocHom_atkinLehnerBar_eq red hqN hred
        (orderS hqN hval₁).toSubring (jQFun_mem_orderS hqN hval₁) ⟨_, jNQ_mem_orderS hqN hval₁, rfl⟩
        (fun t ht => (mem_orderS hqN hval₁ t).mp ht)
        (fun w hw => ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q w, heckeAlphaBar_mem_biLocRing hqN hval₁ w hw,
          coe_heckeAlphaBar N q w⟩)
        a b
  ·
    exact fun f hfN hfNq => modularRedLocHom_level_eq hjN hfN hfNq
  ·
    exact fun v hv hw => modularRedLocHom_atkinLehnerBar_heckeAlphaBar hqN v hv hw

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top (solution)
