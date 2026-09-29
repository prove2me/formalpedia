-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_smul_gaussUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/941186f0-6d9b-55db-a5b1-a811d43917b9

import Mathlib
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_smul_gaussUnit
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_smul_gaussUnit.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "placeSpecialization_exists_level_one_residueField PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar PlaceSpecialization.LevelOneProlongationPair.exists_isModel PlaceSpecialization.LevelOneProlongationPair CharPReduction.modularLocalized CharPReduction.modularRedLocHom PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec modularRing modularRing_le_integralCoeffs modularLocalized modularRedLocHom"
p2m_open "ModularCurve.CharPReduction"

section Transport
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] {A : Subring L}
  {k : Type*} [Field k] {k' : Type*} [Field k'] (red : A →+* k) (red' : A →+* k')
  (hker : ∀ c : A, red c = 0 ↔ red' c = 0)

include hker in

theorem mem_redKer_iff_of_ker_eq (s : modularRing N A) :
    s ∈ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) ↔
      s ∈ redKer A red' (modularRing N A) (modularRing_le_integralCoeffs N A) := by
  simp only [redKer, RingHom.mem_ker]
  constructor <;> intro h
  · ext n
    have := congrArg (fun x : LaurentSeries k => x.coeff n) h
    simp only [redRes_apply, coeffRed_coeff, HahnSeries.coeff_zero] at this ⊢
    exact (hker _).mp this
  · ext n
    have := congrArg (fun x : LaurentSeries k' => x.coeff n) h
    simp only [redRes_apply, coeffRed_coeff, HahnSeries.coeff_zero] at this ⊢
    exact (hker _).mpr this

include hker in

theorem mem_modularLocalized_iff_of_ker_eq (x : LaurentSeries L) :
    x ∈ modularLocalized N A red ↔ x ∈ modularLocalized N A red' := by
  rw [modularLocalized, modularLocalized, mem_localizedAtKer, mem_localizedAtKer]
  constructor
  · rintro ⟨r, s, hs, h⟩
    exact ⟨r, s, fun hs' => hs ((mem_redKer_iff_of_ker_eq red red' hker s).mpr hs'), h⟩
  · rintro ⟨r, s, hs, h⟩
    exact ⟨r, s, fun hs' => hs ((mem_redKer_iff_of_ker_eq red red' hker s).mp hs'), h⟩

include hker in

theorem modularRedLocHom_ne_zero_iff_of_ker_eq (x : LaurentSeries L)
    (h : x ∈ modularLocalized N A red) (h' : x ∈ modularLocalized N A red') :
    modularRedLocHom N A red ⟨x, h⟩ ≠ 0 ↔ modularRedLocHom N A red' ⟨x, h'⟩ ≠ 0 := by

  have hm := h
  rw [modularLocalized, mem_localizedAtKer] at hm
  obtain ⟨r, s, hs, hxs⟩ := hm
  have hs' : s ∉ redKer A red' (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    fun hs' => hs ((mem_redKer_iff_of_ker_eq red red' hker s).mpr hs')
  have spec : redLoc (⟨x, h⟩ : modularLocalized N A red) * redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) s
      = redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r :=
    redLoc_spec (A := A) (red := red) (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A) ⟨x, h⟩ hxs
  have spec' : redLoc (⟨x, h'⟩ : modularLocalized N A red') * redRes A red' (modularRing N A) (modularRing_le_integralCoeffs N A) s
      = redRes A red' (modularRing N A) (modularRing_le_integralCoeffs N A) r :=
    redLoc_spec (A := A) (red := red') (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A) ⟨x, h'⟩ hxs
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A) hs
  have hsne' := redRes_ne_zero_of_notMem (A := A) (red := red') (R := modularRing N A) (hR := modularRing_le_integralCoeffs N A) hs'

  have e1 : modularRedLocHom N A red ⟨x, h⟩ ≠ 0 ↔ r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) := by
    rw [notMem_redKer_iff, ← spec]
    show redLoc (⟨x, h⟩ : modularLocalized N A red) ≠ 0 ↔ _
    exact ⟨fun hne => mul_ne_zero hne hsne, fun hne h0 => hne (by rw [h0, zero_mul])⟩
  have e2 : modularRedLocHom N A red' ⟨x, h'⟩ ≠ 0 ↔ r ∉ redKer A red' (modularRing N A) (modularRing_le_integralCoeffs N A) := by
    rw [notMem_redKer_iff, ← spec']
    show redLoc (⟨x, h'⟩ : modularLocalized N A red') ≠ 0 ↔ _
    exact ⟨fun hne => mul_ne_zero hne hsne', fun hne h0 => hne (by rw [h0, zero_mul])⟩
  rw [e1, e2, not_iff_not]
  exact mem_redKer_iff_of_ker_eq red red' hker r

end Transport

end CharPReduction
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "placeSpecialization_exists_level_one_residueField PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar PlaceSpecialization.LevelOneProlongationPair.exists_isModel PlaceSpecialization.LevelOneProlongationPair CharPReduction.modularLocalized CharPReduction.modularRedLocHom PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_open "ModularCurve.NodeLocalized"
open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

theorem exists_smul_gaussUnit_residueField
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    [CharP (IsLocalRing.ResidueField ↥A) q]
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue ↥A)),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 := by

  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime q
  have hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q := ModularCurve.heckeAlphaBarIntegral_of_prime _ 1 q
  have hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q := ModularCurve.heckeBetaBarIntegral_of_prime _ 1 q
  obtain ⟨P⟩ := ModularCurve.placeSpecialization_exists_level_one_residueField q data hKr A hA hα hβ
  obtain ⟨R, -⟩ := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_isModel P

  obtain ⟨c, hc, hres⟩ := R.R₁.exists_smul_mem f hf
  have hc0 : c ≠ 0 := R.R₁.smul_const_ne_zero hc hres

  have hm : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue ↥A) :=
    (ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized R
      (c • f)).mp hc
  refine ⟨c, hc0, hm, ?_⟩

  obtain ⟨hc', heq⟩ := R.residue₁_eq_modularRedLocHom (c • f) hm
  intro h0
  apply hres
  have hι : (R.ι (R.R₁.residue ⟨c • f, hc'⟩) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = 0 := by
    rw [heq, h0]
  have hι' : R.ι (R.R₁.residue ⟨c • f, hc'⟩) = 0 := by
    first
    | exact_mod_cast hι
    | exact Subtype.ext hι
  have : R.R₁.residue ⟨c • f, hc'⟩ = 0 := (map_eq_zero_iff R.ι R.ι.injective).mp hι'
  exact this

theorem exists_smul_gaussUnit_card
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 := by

  have hq0 : red ((q : ℕ) : ↥A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hqm : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (hker _).mp hq0
  have hA : A.LiesOverPrime q := by
    have : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hqm
    have e : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by push_cast; rfl
    rw [e] at this
    exact this
  haveI : CharP (IsLocalRing.ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hA
  have hker' : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ red c = 0 := fun c => by
    rw [IsLocalRing.residue_eq_zero_iff, hker]
  obtain ⟨c, hc0, h₀, hu₀⟩ := exists_smul_gaussUnit_residueField hA f hf
  have h : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    (CharPReduction.mem_modularLocalized_iff_of_ker_eq (A := A.toSubring) (IsLocalRing.residue ↥A) red hker' _).mp h₀
  exact ⟨c, hc0, h, (CharPReduction.modularRedLocHom_ne_zero_iff_of_ker_eq (A := A.toSubring) (IsLocalRing.residue ↥A) red
    hker' _ h₀ h).mp hu₀⟩

end NodeLocalized
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0)
      (h : ((c • f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 :=
  ModularCurve.NodeLocalized.exists_smul_gaussUnit_card red hker f hf

end S_ModularCurve_NodeLocalized_exists_smul_gaussUnit
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_smul_gaussUnit (solution)
