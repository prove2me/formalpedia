-- Prove2me | solution 1 for ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_ofNat1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a7822e73-5dba-5077-bcb6-4436666b5f2e

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_NodeLocalized_modularRedLocHom_eq_zero_iff_mem_span_branchFst
import Theorems.Thm_ModularCurve_NodeLocalized_exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_NodeLocalized_exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728.ModularCurve.NodeLocalized"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.redRes CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom CharPReduction.redLocHom_apply CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem jqd_mem_full modularFunctionField_le_full jWidth frickeInvolutionBar modularFunctionFieldBar ssJSet NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve"

section Remint

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffMap_jqModC' (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

end Remint

section Bridges

private theorem coeffEmb_jq' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
  coeffMap_jqModC' (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coeffEmb_jqN' (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  have h := coeffMap_qExpand' (algebraMap ℚ (AlgebraicClosure ℚ)) N jq
  rw [jqNModC, ← coeffEmb_jq']
  exact h

end Bridges

namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint modularEvalAt isUnit_modularEvalAt coeffSubring redRestrict modularRedLocHom_eq_zero_iff_mem_span_branchFst exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint pointEval_eq_zero_of_modularEval_eq_zero isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring"
p2m_open "ModularCurve.NodeLocalized"

section Helpers

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] (red : A →+* k)

omit [CharP k q] in

private theorem ne_zero_of_modularRedLocHom_ne_zero {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0) :
    (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
  intro h0
  apply hgu
  have h : (⟨_, hg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 :=
    Subtype.ext h0
  rw [h, map_zero]

omit [CharP k q] in

private theorem exists_inv_mem_modularLocalized {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hgu : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0) :
    ∃ h : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩
        = (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩)⁻¹ := by
  have hgL : (g : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    ne_zero_of_modularRedLocHom_ne_zero red hg hgu
  have hinvL : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by
    norm_cast
  obtain ⟨r, s, hs, heq⟩ := id hg
  have hsne := CharPReduction.redRes_ne_zero_of_notMem (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hs
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red)
    (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
    (⟨_, hg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) heq
  have hrne : CharPReduction.redRes A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hgu hsne
  have hrk : r ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hrne
  have hmem : ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    refine ⟨s, r, hrk, ?_⟩
    rw [hinvL]
    calc ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ * r
        = ((g : LaurentSeries (AlgebraicClosure ℚ)))⁻¹
          * ((g : LaurentSeries (AlgebraicClosure ℚ)) * s) := by rw [heq]
      _ = s := inv_mul_cancel_left₀ hgL _
  refine ⟨hmem, ?_⟩
  have hone : (⟨_, hmem⟩ * ⟨_, hg⟩ :
      ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 := by
    apply Subtype.ext
    show ((g⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      * (g : LaurentSeries (AlgebraicClosure ℚ)) = 1
    rw [hinvL, inv_mul_cancel₀ hgL]
  have hmul := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hone
  rw [map_mul, map_one] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

end Helpers

section Legs

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {k : Type*} [Field k] [CharP k q] {red : A →+* k}
variable {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

private theorem modularEval_mem_bar (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ modularFunctionFieldBar (1 * q) := by
  have hj0 : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← coeffEmb_jq']
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))
  have hj1 : jqNModC (AlgebraicClosure ℚ) (1 * q) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← coeffEmb_jqN']
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp [modularEval, CharPReduction.constSeries]
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | mul_X p i h =>
    rw [map_mul]
    refine mul_mem h ?_
    fin_cases i
    · simpa [modularEval] using hj0
    · simpa [modularEval] using hj1

private theorem lift_leg {a : k}
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := by
  obtain ⟨r, t, ht, hf⟩ := f.2
  have hEt : modularEval (1 * q) (coeffSubring A K) t ≠ 0 := fun h0 =>
    ht (pointEval_eq_zero_of_modularEval_eq_zero red a K t h0)
  have hdiv : (f : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) r / modularEval (1 * q) (coeffSubring A K) t := by
    rw [eq_div_iff hEt]
    exact hf
  rw [hdiv]
  exact div_mem (modularEval_mem_bar r) (modularEval_mem_bar t)

private theorem modularEval_mem_modularRing (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) p ∈ CharPReduction.modularRing (1 * q) A.toSubring := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hc : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c)
        = CharPReduction.constSeries A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2.1⟩ := by
      simp [modularEval, CharPReduction.constSeries]
    rw [hc]
    exact CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring _
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | mul_X p i h =>
    rw [map_mul]
    refine mul_mem h ?_
    fin_cases i
    · simpa [modularEval] using CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring
    · simpa [modularEval] using CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring

private theorem modularEval_notMem_redKer [DecidableEq k] [FiniteDimensional ℚ K] {a : k}
    (ha2 : a ^ (q ^ 2) = a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    {t : MvPolynomial (Fin 2) ↥(coeffSubring A K)}
    (ht : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0) :
    (⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩ :
        ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉
      CharPReduction.redKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) := by
  intro hmem

  have hz : CharPReduction.modularRedLocHom (1 * q) A.toSubring red
      ⟨_, CharPReduction.subring_le_localizedAtKer A.toSubring red
        (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        (⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩ :
          ↥(CharPReduction.modularRing (1 * q) A.toSubring)).2⟩ = 0 := by
    show CharPReduction.redLocHom _ = 0
    rw [CharPReduction.redLocHom_apply]
    exact (CharPReduction.redLoc_coe (A := A.toSubring) (red := red)
      (R := CharPReduction.modularRing (1 * q) A.toSubring)
      (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) (coeffSubring A K) t, modularEval_mem_modularRing t⟩).trans
      (RingHom.mem_ker.mp hmem)

  have hspan := (ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red a ha2 K ϖ hϖ
    ⟨_, modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) t⟩
    _).mp hz

  obtain ⟨-, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hloc
  have hmax' : IsLocalRing.maximalIdeal
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) = _ := hmax
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (MvPolynomial.C x) q
  have hpoly : (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K))
      = (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)) - (MvPolynomial.X 0 - MvPolynomial.C x) * c := by
    rw [← hc, MvPolynomial.C_pow]
    ring
  have hle : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}
      ≤ IsLocalRing.maximalIdeal
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    rw [Ideal.span_le]
    rintro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have h1 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have h2 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have h3 : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
      rw [hmax']
      exact Ideal.subset_span (by simp)
    have hsplit : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
        = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
          - (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) * (⟨modularEval (1 * q) (coeffSubring A K) (c), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      apply Subtype.ext
      show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q)
        = modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))
          - modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x) * modularEval (1 * q) (coeffSubring A K) c
      rw [hpoly, map_sub, map_mul]
    rcases hy with rfl | rfl
    · exact h1
    · rw [hsplit]
      exact Ideal.sub_mem _ h3 (Ideal.mul_mem_right _ _ h2)

  haveI : Fact (RingHom.ker (modularEval (1 * q) (coeffSubring A K)) ≤
      RingHom.ker (pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q))) :=
    ⟨fun p hp => RingHom.mem_ker.mpr
      (pointEval_eq_zero_of_modularEval_eq_zero red a K p (RingHom.mem_ker.mp hp))⟩
  have hu := isUnit_modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) ht
  exact (IsLocalRing.mem_maximalIdeal _).mp (hle hspan) hu

omit [CharP k q] in

private theorem at_leg {a b : k}
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a b)) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalizedAtPoint (1 * q) A.toSubring red a b := by
  obtain ⟨r, t, ht, hf⟩ := f.2
  refine ⟨MvPolynomial.map (Subring.inclusion inf_le_left) r, MvPolynomial.map (Subring.inclusion inf_le_left) t,
    ?_, ?_⟩
  · simp only [pointEval, redRestrict, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map] at ht ⊢
    exact ht
  · simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map] at hf ⊢
    exact hf

private theorem mem_leg [DecidableEq k] [FiniteDimensional ℚ K] {a : k}
    (ha2 : a ^ (q ^ 2) = a) (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  obtain ⟨r, t, ht, hf⟩ := f.2
  exact ⟨⟨_, modularEval_mem_modularRing r⟩, ⟨_, modularEval_mem_modularRing t⟩,
    modularEval_notMem_redKer ha2 x hx ϖ hϖ ht, hf⟩

private theorem natCast_pow_char' (n : ℕ) : ((n : k) ^ q) = n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_pow (Fact.out : q.Prime).ne_zero]
  | succ n ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]

private theorem ofNat1728_pow_char : ((1728 : k) ^ q) = 1728 := by
  have h := natCast_pow_char' (k := k) (q := q) 1728
  exact_mod_cast h

private theorem ofNat1728_pow_char_sq : (1728 : k) ^ (q ^ 2) = 1728 := by
  rw [pow_two, pow_mul, ofNat1728_pow_char, ofNat1728_pow_char]

private theorem mem_leg₀ [DecidableEq k] [FiniteDimensional ℚ K] (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (f : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
  mem_leg ofNat1728_pow_char_sq 1728 (map_ofNat (redRestrict red K) 1728) ϖ hϖ f

private theorem conj1_leg [DecidableEq k] [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε) (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (heK1 : 1 ≤ eK) (e : ℕ) (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (e * eK) * w)
    (hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)) (hHF : (H' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hredH : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, mem_leg₀ ϖ hϖ H'⟩ ≠ 0) :
    ∃ hG₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • (⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁⟩ ≠ 0 := by

  obtain ⟨εu, hεu⟩ := hε
  set ε' : ↥(coeffSubring A K) := ((εu⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) with hε'
  have hεε' : ε * ε' = 1 := by
    rw [hε', ← hεu]
    exact εu.mul_inv

  set Gm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ with hGm
  set Hm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ with hHm
  have hwF : (w : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg w
  set wm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ with hwm
  obtain ⟨wu, hwu⟩ := hw
  set wi : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) :=
    ((wu⁻¹ : (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))ˣ) :
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) with hwi
  have hwwi : w * wi = 1 := by
    rw [hwi, ← hwu]
    exact wu.mul_inv
  have hwiF : (wi : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg wi

  have hconst : ∀ c : ↥(coeffSubring A K), algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    fun c => CharPReduction.subring_le_localizedAtKer A.toSubring red _ _
      (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2.1⟩)
  have hcε' : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [map_pow]
    exact pow_mem (hconst ε') e
  have hcε : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε : AlgebraicClosure ℚ) ^ e) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [map_pow]
    exact pow_mem (hconst ε) e
  have hπcε' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hcε'⟩ ≠ 0 := by
    have hone : (⟨_, hcε'⟩ * ⟨_, hcε⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 := by
      apply Subtype.ext
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε : AlgebraicClosure ℚ) ^ e) = 1
      rw [← map_mul, ← mul_pow, mul_comm]
      have h1 : ((ε : AlgebraicClosure ℚ) * (ε' : AlgebraicClosure ℚ)) = 1 := by
        have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hεε'
        simpa using h
      rw [h1, one_pow, map_one]
    have h := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hone
    rw [map_mul, map_one] at h
    exact left_ne_zero_of_mul_eq_one h

  have hwO : (w : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ w
  have hwiO : (wi : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ wi
  have hπw : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hwO⟩ ≠ 0 := by
    have hone : (⟨_, hwO⟩ * ⟨_, hwiO⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 1 := by
      apply Subtype.ext
      show (w : LaurentSeries (AlgebraicClosure ℚ)) * (wi : LaurentSeries (AlgebraicClosure ℚ)) = 1
      have h := congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) hwwi
      simpa using h
    have h := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hone
    rw [map_mul, map_one] at h
    exact left_ne_zero_of_mul_eq_one h

  have hHO : ((Hm : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ H'
  have hπH : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hHO⟩ ≠ 0 := hredH
  obtain ⟨hHiO, hπHi⟩ := exists_inv_mem_modularLocalized red hHO hπH
  have hπHi' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hHiO⟩ ≠ 0 := by
    rw [hπHi]
    exact inv_ne_zero hπH

  have hHL : (H' : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := ne_zero_of_modularRedLocHom_ne_zero red hHO hπH
  have hqL : (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqϖL : ((q : ℕ) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simpa using h
  have hGHL : (G' : LaurentSeries (AlgebraicClosure ℚ)) * (H' : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) * (w : LaurentSeries (AlgebraicClosure ℚ)) := by
    have h := congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) hGH
    simpa [modularEval, CharPReduction.constSeries, map_pow] using h
  have hεε'L : (ε : AlgebraicClosure ℚ) * (ε' : AlgebraicClosure ℚ) = 1 := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hεε'
    simpa using h
  have hT : ((((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • Gm : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ε' : AlgebraicClosure ℚ) ^ e) * (w : LaurentSeries (AlgebraicClosure ℚ)) * ((Hm⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hHinv : ((Hm⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((H' : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by
      rw [hHm]
      norm_cast
    rw [hHinv, IntermediateField.coe_smul, hGm, Algebra.smul_def, map_inv₀, map_pow, hqϖL, map_mul, map_pow, map_pow]
    change _ * (G' : LaurentSeries (AlgebraicClosure ℚ)) = _
    have hεL : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε : AlgebraicClosure ℚ) * algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε' : AlgebraicClosure ℚ) = 1 := by
      rw [← map_mul, hεε'L, map_one]
    have hϖL : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ)) ^ (e * eK) := map_pow _ _ _
    rw [hϖL] at hGHL
    have hεne : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hεL
    have hϖne : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply hqL
      rw [hqϖL]
      have : (ϖ : AlgebraicClosure ℚ) = 0 := (map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h0
      rw [this, zero_pow (by omega), zero_mul]
    have hEinv : (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε : AlgebraicClosure ℚ))⁻¹ = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ε' : AlgebraicClosure ℚ) :=
      inv_eq_of_mul_eq_one_right hεL
    rw [← hEinv, eq_mul_inv_iff_mul_eq₀ hHL, mul_assoc, hGHL, mul_pow, ← pow_mul, mul_comm eK e, mul_inv, inv_pow,
      mul_comm ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (ϖ : AlgebraicClosure ℚ)) ^ (e * eK))⁻¹, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖne)]

  have hG₁ : ((((((q : ℕ) : AlgebraicClosure ℚ) ^ e)⁻¹ • Gm : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hT]
    exact mul_mem (mul_mem hcε' hwO) hHiO
  have hπG₁ : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁⟩ ≠ 0 := by
    have hsplit : (⟨_, hG₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hcε'⟩ * ⟨_, hwO⟩ * ⟨_, hHiO⟩ := by
      apply Subtype.ext
      exact hT
    rw [hsplit, map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hπcε' hπw) hπHi'
  exact ⟨hG₁, hπG₁⟩

private theorem conj2_leg [DecidableEq k] [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K))
    (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (G' H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) (hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}
      = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}) :
    ∃ hG₂ : ((frickeInvolutionBar (1 * q) (⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₂⟩ ≠ 0 := by
  set Gm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ with hGm

  have hq0 : ((1728 : k) ^ q) = 1728 := ofNat1728_pow_char
  have ha2₀ : (1728 : k) ^ (q ^ 2) = 1728 := ofNat1728_pow_char_sq
  obtain ⟨σ, hσcoe, hσeval⟩ :=
    ModularCurve.NodeLocalized.exists_ringEquiv_modularLocalizedAtPoint_coe_eq_frickeInvolutionBar red (1728 : k) ha2₀ K

  have ha2' : ((1728 : k) ^ q) ^ (q ^ 2) = (1728 : k) ^ q := by rw [hq0, ha2₀]
  have hx' : redRestrict red K 1728 = (1728 : k) ^ q := by rw [hq0]; exact map_ofNat (redRestrict red K) 1728
  have hσG : ((σ G' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q) Gm : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := hσcoe G' hGF
  have hfrG : ((frickeInvolutionBar (1 * q) Gm : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [← hσG]
    exact mem_leg ha2' 1728 hx' ϖ hϖ (σ G')
  have hσGO : ((σ G' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    rw [hσG]
    exact hfrG
  have hredFrG : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hfrG⟩ ≠ 0 := by
    intro h0
    have h0' : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hσGO⟩ = 0 := by
      have hEq : (⟨_, hσGO⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hfrG⟩ := Subtype.ext hσG
      rw [hEq]
      exact h0
    have hmemσ := (ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red ((1728 : k) ^ q) ha2' K ϖ hϖ
      (σ G') hσGO).mp h0'

    have himg : Ideal.map (σ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) →+* ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q)))
        (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
        = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q))),
          (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q) _⟩ :
            ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) ((1728 : k) ^ q) (((1728 : k) ^ q) ^ q)))} := by
      rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
      have e1 := hσeval (MvPolynomial.C ϖ)
      have e2 := hσeval (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)
      have hrenC : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.C ϖ : MvPolynomial (Fin 2) ↥(coeffSubring A K))
          = MvPolynomial.C ϖ := MvPolynomial.rename_C _ _
      have hrenX : MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
            (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥(coeffSubring A K))
          = MvPolynomial.X 1 - MvPolynomial.X 0 ^ q := by
        simp [MvPolynomial.rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hrenC] at e1
      rw [hrenX] at e2
      simp only [RingHom.coe_coe]
      rw [show (σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))) = σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) (MvPolynomial.C ϖ)) from rfl,
        show (σ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
              ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))) = σ (modularEvalAt (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q)) from rfl,
        e1, e2]
      rfl
    rw [← himg] at hmemσ
    obtain ⟨g₀, hg₀, hg₀eq⟩ := (Ideal.mem_map_of_equiv σ _).mp hmemσ
    have hg₀G : g₀ = G' := σ.injective hg₀eq
    rw [hg₀G, ← hsp2] at hg₀
    exact hnm2 hg₀
  exact ⟨hfrG, hredFrG⟩

private theorem conj3_leg (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ϖ : ↥(coeffSubring A K)) (eK : ℕ) (ε : ↥(coeffSubring A K))
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK) (e : ℕ)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ), modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (e * eK) * w)
    (hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)) (hHF : (H' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q)) (hHL : (H' : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ : ↥(modularFunctionFieldBar (1 * q))) = 0 := by
  set Gm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩ with hGm
  set Hm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ with hHm
  have hwF : (w : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg w
  set wm : ↥(modularFunctionFieldBar (1 * q)) := ⟨(w : LaurentSeries (AlgebraicClosure ℚ)), hwF⟩ with hwm
  obtain ⟨wu, hwu⟩ := hw
  set wi : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) := ((wu⁻¹ : (↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))ˣ) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) with hwi
  have hwwi : w * wi = 1 := by
    rw [hwi, ← hwu]
    exact wu.mul_inv
  have hwiF : (wi : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg wi
  have hqL : (((q : ℕ) : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqϖL : ((q : ℕ) : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ eK * (ε : AlgebraicClosure ℚ) := by
    have h := congrArg (fun z : ↥(coeffSubring A K) => (z : AlgebraicClosure ℚ)) hqϖ
    simpa using h
  have hGHL : (G' : LaurentSeries (AlgebraicClosure ℚ)) * (H' : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) * (w : LaurentSeries (AlgebraicClosure ℚ)) := by
    have h := congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) hGH
    simpa [modularEval, CharPReduction.constSeries, map_pow] using h

  intro W hW
  obtain ⟨⟨x, hx0, hxord⟩, ⟨y, hy0, hyord⟩⟩ := hW

  have hint : ∀ g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)),
      ∀ hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q), (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
    intro g hgF
    have hgA : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalizedAtPoint (1 * q) A.toSubring red (red x) (red y) := by
      rw [hx0, hy0]
      exact at_leg g
    obtain ⟨c, hc⟩ := ModularCurve.NodeLocalized.exists_sub_algebraMap_mem_nonunits_of_mem_modularLocalizedAtPoint
      red hker W x y hxord hyord ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ hgA
    have hsub : (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
      (W.toValuationSubring.valuation_le_one_iff _).mp (W.toValuationSubring.mem_nonunits_iff.mp hc).le
    have h := add_mem hsub (W.algebraMap_mem' (c : AlgebraicClosure ℚ))
    rwa [sub_add_cancel] at h

  have hHm0 : Hm ≠ 0 := fun h0 => hHL (by rw [hHm] at h0; exact congrArg Subtype.val h0)
  have hwwi' : wm * (⟨(wi : LaurentSeries (AlgebraicClosure ℚ)), hwiF⟩ : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
    apply Subtype.ext
    show (w : LaurentSeries (AlgebraicClosure ℚ)) * (wi : LaurentSeries (AlgebraicClosure ℚ)) = 1
    have h := congrArg (fun z : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) hwwi
    simpa using h
  have hwm0 : wm ≠ 0 := left_ne_zero_of_mul_eq_one hwwi'
  have hwi0 : (⟨(wi : LaurentSeries (AlgebraicClosure ℚ)), hwiF⟩ : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := right_ne_zero_of_mul_eq_one hwwi'
  have hGHm : Gm * Hm = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) * wm := by
    apply Subtype.ext
    push_cast
    rw [← map_pow]
    exact hGHL
  have hϖ0 : (ϖ : AlgebraicClosure ℚ) ^ (e * eK) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    apply hqL
    rw [hqϖL, h0, zero_pow (by omega), zero_mul]
  have hcm0 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((ϖ : AlgebraicClosure ℚ) ^ (e * eK)) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hGm0 : Gm ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hGHm
    exact mul_ne_zero hcm0 hwm0 hGHm.symm

  have hG0 : 0 ≤ W.ord Gm := GaussReduction.ord_nonneg_of_mem_gen W (hint G' hGF) hGm0
  have hH0 : 0 ≤ W.ord Hm := GaussReduction.ord_nonneg_of_mem_gen W (hint H' hHF) hHm0
  have hw0 : 0 ≤ W.ord wm := GaussReduction.ord_nonneg_of_mem_gen W (hint w hwF) hwm0
  have hwi0' : 0 ≤ W.ord (⟨(wi : LaurentSeries (AlgebraicClosure ℚ)), hwiF⟩ : ↥(modularFunctionFieldBar (1 * q))) := GaussReduction.ord_nonneg_of_mem_gen W (hint wi hwiF) hwi0
  have hsum_w : W.ord wm + W.ord (⟨(wi : LaurentSeries (AlgebraicClosure ℚ)), hwiF⟩ : ↥(modularFunctionFieldBar (1 * q))) = 0 := by
    rw [← W.ord_mul hwm0 hwi0, hwwi', W.ord_one]
  have hsum_GH : W.ord Gm + W.ord Hm = W.ord wm := by
    rw [← W.ord_mul hGm0 hHm0, hGHm, W.ord_mul hcm0 hwm0, StandardAnnulus.ord_algebraMap_eq_zero W hϖ0, zero_add]
  omega

end Legs

end NodeLocalized
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (1728 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (jWidth (1728 : k) * eK) * w)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))}) :
    ∃ (Gf : ↥(modularFunctionFieldBar (1 * q))) (_ : (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)))
      (hG₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (1728 : k))⁻¹ • Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (hG₂ : ((frickeInvolutionBar (1 * q) Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₂⟩ ≠ 0 ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord Gf = 0 := by
  have _ := ha
  have _ := hq
  have _ := hpr1
  have _ := hpr2
  have hGF : (G' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg G'
  have hHF : (H' : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) := lift_leg H'

  have hredH : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, mem_leg₀ ϖ hϖ H'⟩ ≠ 0 := by
    intro h0
    have := (ModularCurve.NodeLocalized.modularRedLocHom_eq_zero_iff_mem_span_branchFst red (1728 : k)
      ModularCurve.NodeLocalized.ofNat1728_pow_char_sq K ϖ hϖ H' (mem_leg₀ ϖ hϖ H')).mp h0
    rw [← hsp1] at this
    exact hnm1 this
  have hHO : (((⟨(H' : LaurentSeries (AlgebraicClosure ℚ)), hHF⟩ : modularFunctionFieldBar (1 * q)) :
      modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := mem_leg₀ ϖ hϖ H'
  have hπH : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hHO⟩ ≠ 0 := hredH
  have hHL : (H' : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := ne_zero_of_modularRedLocHom_ne_zero red hHO hπH
  obtain ⟨hG₁, hπG₁⟩ := conj1_leg ϖ hϖ eK ε hε hqϖ heK1 (jWidth (1728 : k)) G' H' w hw hGH hGF hHF hredH
  obtain ⟨hG₂, hπG₂⟩ := conj2_leg ϖ hϖ G' H' hGF hsp2 hnm2
  exact ⟨⟨(G' : LaurentSeries (AlgebraicClosure ℚ)), hGF⟩, rfl, hG₁, hG₂, hπG₁, hπG₂,
    conj3_leg hker ϖ eK ε hqϖ heK1 (jWidth (1728 : k)) G' H' w hw hGH hGF hHF hHL⟩

end S_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728 (solution)
