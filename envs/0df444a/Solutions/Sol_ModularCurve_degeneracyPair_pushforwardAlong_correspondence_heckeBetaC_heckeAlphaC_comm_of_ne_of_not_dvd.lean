-- Prove2me | solution 1 for ModularCurve.degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/569441c4-2f86-5ff3-8159-f63f7e1e1ec3

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_jqModC_of_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_ModularCurve_jqModC_mem_adjoin_jqNModC_of_prime_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace R1LawsC3

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pushforwardAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong φ' hφ' D := by
  subst h
  rfl

end Congr

section Exchange

variable {K F₀ F₁ R₀ R₁ : Type*} [Field K] [Field F₀] [Field F₁] [Field R₀] [Field R₁]
  [Algebra K F₀] [Algebra K F₁] [Algebra K R₀] [Algebra K R₁]
  [HasPrincipalDivisors K R₀] [HasPrincipalDivisors K R₁]

theorem pushforwardAlong_correspondence_comm_of_exchange
    (φ : F₀ →ₐ[K] F₁) (ψ : R₀ →ₐ[K] R₁)
    (α₀ β₀ : F₀ →ₐ[K] R₀) (α₁ β₁ : F₁ →ₐ[K] R₁)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hα₀ : α₀.toRingHom.IsIntegral) (hβ₀ : β₀.toRingHom.IsIntegral)
    (hα₁ : α₁.toRingHom.IsIntegral) (hβ₁ : β₁.toRingHom.IsIntegral)
    (hα : ψ.comp α₀ = α₁.comp φ)
    (hex : ∀ D : Divisor K F₁,
      Divisor.pullbackAlong β₀ hβ₀ (Divisor.pushforwardAlong φ hφ D)
        = Divisor.pushforwardAlong ψ hψ (Divisor.pullbackAlong β₁ hβ₁ D))
    (D : Divisor K F₁) :
    Divisor.pushforwardAlong φ hφ (Divisor.correspondence β₁ α₁ hβ₁ hα₁ D)
      = Divisor.correspondence β₀ α₀ hβ₀ hα₀ (Divisor.pushforwardAlong φ hφ D) := by
  have hα₁φ : (α₁.comp φ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hφ hα₁
  have hψα₀ : (ψ.comp α₀).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hα₀ hψ
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    Divisor.pushforwardAlong_pushforwardAlong φ α₁ hφ hα₁ hα₁φ,
    pushforwardAlong_congr hα.symm hα₁φ hψα₀,
    ← Divisor.pushforwardAlong_pushforwardAlong α₀ ψ hα₀ hψ hψα₀, ← hex]

theorem pushforwardAlong_correspondence_comm_of_linearDisjoint
    (φ : F₀ →ₐ[K] F₁) (ψ : R₀ →ₐ[K] R₁)
    (α₀ β₀ : F₀ →ₐ[K] R₀) (α₁ β₁ : F₁ →ₐ[K] R₁)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hα₀ : α₀.toRingHom.IsIntegral) (hβ₀ : β₀.toRingHom.IsIntegral)
    (hα₁ : α₁.toRingHom.IsIntegral) (hβ₁ : β₁.toRingHom.IsIntegral)
    (hα : ψ.comp α₀ = α₁.comp φ) (hβ : ψ.comp β₀ = β₁.comp φ)
    (hfin : FiniteAlong K (β₁.comp φ)) (hsep : SeparableAlong K (β₁.comp φ))
    (hgen : Algebra.adjoin K (Set.range β₁ ∪ Set.range ψ) = ⊤)
    (hLD : finrankAlong K (β₁.comp φ) = finrankAlong K φ * finrankAlong K β₀)
    (D : Divisor K F₁) :
    Divisor.pushforwardAlong φ hφ (Divisor.correspondence β₁ α₁ hβ₁ hα₁ D)
      = Divisor.correspondence β₀ α₀ hβ₀ hα₀ (Divisor.pushforwardAlong φ hφ D) :=
  pushforwardAlong_correspondence_comm_of_exchange φ ψ α₀ β₀ α₁ β₁ hφ hψ hα₀ hβ₀ hα₁ hβ₁ hα
    (fun D => Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
      φ β₀ β₁ ψ hφ hβ₀ hβ₁ hψ hβ hfin hsep hgen hLD D) D

end Exchange

section Modular

open ModularCurve IntermediateField

variable (k : Type*) [Field k] (M s ℓ : ℕ) [NeZero M] [NeZero s] [NeZero ℓ] [NeZero (M * s)]

theorem qExpand_comm (a b : ℕ) [NeZero a] [NeZero b] (x : LaurentSeries k) :
    qExpand k a (qExpand k b x) = qExpand k b (qExpand k a x) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  haveI : NeZero (b * a) := ⟨Nat.mul_ne_zero (NeZero.ne b) (NeZero.ne a)⟩
  rw [qExpand_qExpand, qExpand_qExpand, qExpand_congr (Nat.mul_comm a b)]

theorem jqNModC_mul (a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] :
    jqNModC k (a * b) = qExpand k b (jqNModC k a) := by
  unfold jqNModC
  rw [qExpand_qExpand, qExpand_congr (Nat.mul_comm b a)]

variable {k M s} in

theorem le_of_pinned
    (φ₀ : modularFunctionFieldC k M →ₐ[k] modularFunctionFieldC k (M * s))
    (hφα : ∀ x, ((φ₀ x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x) :
    modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s) := by
  intro x hx
  have h : ((φ₀ ⟨x, hx⟩ : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x := hφα ⟨x, hx⟩
  rw [← h]
  exact (φ₀ ⟨x, hx⟩).2

variable {k M s} in

theorem map_le_of_pinned
    (φ₁ : modularFunctionFieldC k M →ₐ[k] modularFunctionFieldC k (M * s))
    (hφβ : ∀ x, ((φ₁ x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x) :
    (modularFunctionFieldC k M).map (qExpandAlgC k s) ≤ modularFunctionFieldC k (M * s) := by
  rintro _ ⟨x, hx, rfl⟩
  have h : ((φ₁ ⟨x, hx⟩ : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x :=
    hφβ ⟨x, hx⟩
  show qExpand k s x ∈ _
  rw [← h]
  exact (φ₁ ⟨x, hx⟩).2

variable {k M s} in

theorem roof_le (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s)) :
    charLDegeneracyRoof k M ℓ ≤ charLDegeneracyRoof k (M * s) ℓ := by
  have hC : modularFunctionFieldC k (M * s) ≤ charLDegeneracyRoof k (M * s) ℓ :=
    modularFunctionFieldC_le_charLDegeneracyRoof k (M * s) ℓ
  have hq := qExpand_image_le_charLDegeneracyRoof k (M * s) ℓ
  unfold charLDegeneracyRoof
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hC (jqModC_mem k (M * s))
  · exact hC (hle (jqNModC_mem k M))
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · refine hq ⟨jqNModC k M, hle (jqNModC_mem k M), ?_⟩
    show qExpand k ℓ (jqNModC k M) = jqNModC k (M * ℓ)
    rw [← jqNModC_mul]

variable {k M s} in

theorem roof_map_le (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s))
    (hqe : (modularFunctionFieldC k M).map (qExpandAlgC k s) ≤ modularFunctionFieldC k (M * s)) :
    (charLDegeneracyRoof k M ℓ).map (qExpandAlgC k s) ≤ charLDegeneracyRoof k (M * s) ℓ := by
  have hC : modularFunctionFieldC k (M * s) ≤ charLDegeneracyRoof k (M * s) ℓ :=
    modularFunctionFieldC_le_charLDegeneracyRoof k (M * s) ℓ
  have hq := qExpand_image_le_charLDegeneracyRoof k (M * s) ℓ
  have hjs : qExpand k s (jqModC k) ∈ modularFunctionFieldC k (M * s) :=
    hqe ⟨jqModC k, jqModC_mem k M, rfl⟩
  have hjMs : qExpand k s (jqNModC k M) ∈ modularFunctionFieldC k (M * s) :=
    hqe ⟨jqNModC k M, jqNModC_mem k M, rfl⟩
  unfold charLDegeneracyRoof
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [qExpandAlgC_apply]
  rcases hx with rfl | rfl | rfl | rfl
  · exact hC hjs
  · exact hC hjMs
  · refine hq ⟨qExpand k s (jqModC k), hjs, ?_⟩
    show qExpand k ℓ (qExpand k s (jqModC k)) = qExpand k s (jqNModC k ℓ)
    unfold jqNModC
    exact qExpand_comm k ℓ s _
  · refine hq ⟨qExpand k s (jqNModC k M), hjMs, ?_⟩
    show qExpand k ℓ (qExpand k s (jqNModC k M)) = qExpand k s (jqNModC k (M * ℓ))
    rw [jqNModC_mul k M ℓ]
    exact qExpand_comm k ℓ s _

variable {k M s ℓ} in

def roofIncl (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s)) :
    charLDegeneracyRoof k M ℓ →ₐ[k] charLDegeneracyRoof k (M * s) ℓ :=
  IntermediateField.inclusion (roof_le ℓ hle)

@[scoped simp]
theorem coe_roofIncl (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s))
    (x : charLDegeneracyRoof k M ℓ) : (roofIncl hle x : LaurentSeries k) = x :=
  IntermediateField.coe_inclusion _ x

variable {k M s ℓ} in

def roofSubst (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s))
    (hqe : (modularFunctionFieldC k M).map (qExpandAlgC k s) ≤ modularFunctionFieldC k (M * s)) :
    charLDegeneracyRoof k M ℓ →ₐ[k] charLDegeneracyRoof k (M * s) ℓ :=
  (IntermediateField.inclusion (roof_map_le ℓ hle hqe)).comp
    ((charLDegeneracyRoof k M ℓ).equivMap (qExpandAlgC k s)).toAlgHom

@[scoped simp]
theorem coe_roofSubst (hle : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * s))
    (hqe : (modularFunctionFieldC k M).map (qExpandAlgC k s) ≤ modularFunctionFieldC k (M * s))
    (x : charLDegeneracyRoof k M ℓ) :
    (roofSubst hle hqe x : LaurentSeries k) = qExpand k s x := by
  rfl

variable {k M s ℓ}

section Pair

variable (φ : Fin 2 → (modularFunctionFieldC k M →ₐ[k] modularFunctionFieldC k (M * s)))
  (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
  (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x)

def roofMap (i : Fin 2) : charLDegeneracyRoof k M ℓ →ₐ[k] charLDegeneracyRoof k (M * s) ℓ :=
  if i = 0 then roofIncl (le_of_pinned (φ 0) hφα)
  else roofSubst (le_of_pinned (φ 0) hφα) (map_le_of_pinned (φ 1) hφβ)

theorem roofMap_zero : roofMap (ℓ := ℓ) φ hφα hφβ 0 = roofIncl (le_of_pinned (φ 0) hφα) :=
  if_pos rfl

theorem roofMap_one : roofMap (ℓ := ℓ) φ hφα hφβ 1
    = roofSubst (le_of_pinned (φ 0) hφα) (map_le_of_pinned (φ 1) hφβ) :=
  if_neg (by decide)

theorem coe_roofMap_zero (x : charLDegeneracyRoof k M ℓ) :
    (roofMap (ℓ := ℓ) φ hφα hφβ 0 x : LaurentSeries k) = x := by
  rw [roofMap_zero]
  exact IntermediateField.coe_inclusion _ x

theorem coe_roofMap_one (x : charLDegeneracyRoof k M ℓ) :
    (roofMap (ℓ := ℓ) φ hφα hφβ 1 x : LaurentSeries k) = qExpand k s x := by
  rw [roofMap_one]
  rfl

theorem roofMap_comp_heckeAlphaC (i : Fin 2) :
    (roofMap (ℓ := ℓ) φ hφα hφβ i).comp (heckeAlphaC k M ℓ)
      = (heckeAlphaC k (M * s) ℓ).comp (φ i) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  fin_cases i
  · show ((roofMap φ hφα hφβ 0 (heckeAlphaC k M ℓ x) : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = (heckeAlphaC k (M * s) ℓ (φ 0 x) : LaurentSeries k)
    rw [coe_roofMap_zero, coe_heckeAlphaC, coe_heckeAlphaC, hφα]
  · show ((roofMap φ hφα hφβ 1 (heckeAlphaC k M ℓ x) : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = (heckeAlphaC k (M * s) ℓ (φ 1 x) : LaurentSeries k)
    rw [coe_roofMap_one, coe_heckeAlphaC, coe_heckeAlphaC, hφβ]

theorem roofMap_comp_heckeBetaC (i : Fin 2) :
    (roofMap (ℓ := ℓ) φ hφα hφβ i).comp (heckeBetaC k M ℓ)
      = (heckeBetaC k (M * s) ℓ).comp (φ i) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  fin_cases i
  · show ((roofMap φ hφα hφβ 0 (heckeBetaC k M ℓ x) : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = (heckeBetaC k (M * s) ℓ (φ 0 x) : LaurentSeries k)
    rw [coe_roofMap_zero, coe_heckeBetaC, coe_heckeBetaC, hφα]
  · show ((roofMap φ hφα hφβ 1 (heckeBetaC k M ℓ x) : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = (heckeBetaC k (M * s) ℓ (φ 1 x) : LaurentSeries k)
    rw [coe_roofMap_one, coe_heckeBetaC, coe_heckeBetaC, hφβ]
    exact qExpand_comm k s ℓ _

theorem roofMap_isIntegral (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (i : Fin 2) :
    (roofMap (ℓ := ℓ) φ hφα hφβ i).toRingHom.IsIntegral := by
  have h : ((roofMap (ℓ := ℓ) φ hφα hφβ i).comp (heckeAlphaC k M ℓ)).toRingHom.IsIntegral := by
    rw [roofMap_comp_heckeAlphaC]
    exact RingHom.IsIntegral.trans _ _ (hφ i) hα₁
  exact RingHom.IsIntegral.tower_top (heckeAlphaC k M ℓ).toRingHom _ h

theorem comm_of_hex
    [HasPrincipalDivisors k (charLDegeneracyRoof k (M * s) ℓ)]
    [HasPrincipalDivisors k (charLDegeneracyRoof k M ℓ)]
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ)
    (hα₀ : HeckeAlphaCIntegral k M ℓ) (hβ₀ : HeckeBetaCIntegral k M ℓ)
    (i : Fin 2)
    (hex : ∀ D : Divisor k (modularFunctionFieldC k (M * s)),
      Divisor.pullbackAlong (heckeBetaC k M ℓ) hβ₀ (Divisor.pushforwardAlong (φ i) (hφ i) D)
        = Divisor.pushforwardAlong (roofMap (ℓ := ℓ) φ hφα hφβ i)
            (roofMap_isIntegral φ hφα hφβ hφ hα₁ i)
            (Divisor.pullbackAlong (heckeBetaC k (M * s) ℓ) hβ₁ D))
    (D : Divisor k (modularFunctionFieldC k (M * s))) :
    Divisor.pushforwardAlong (φ i) (hφ i)
        (Divisor.correspondence (heckeBetaC k (M * s) ℓ) (heckeAlphaC k (M * s) ℓ) hβ₁ hα₁ D)
      = Divisor.correspondence (heckeBetaC k M ℓ) (heckeAlphaC k M ℓ) hβ₀ hα₀
          (Divisor.pushforwardAlong (φ i) (hφ i) D) :=
  pushforwardAlong_correspondence_comm_of_exchange (φ i) (roofMap (ℓ := ℓ) φ hφα hφβ i)
    (heckeAlphaC k M ℓ) (heckeBetaC k M ℓ) (heckeAlphaC k (M * s) ℓ) (heckeBetaC k (M * s) ℓ)
    (hφ i) (roofMap_isIntegral φ hφα hφβ hφ hα₁ i) hα₀ hβ₀ hα₁ hβ₁
    (roofMap_comp_heckeAlphaC φ hφα hφβ i) hex D

theorem comm_of_linearDisjoint
    [HasPrincipalDivisors k (charLDegeneracyRoof k (M * s) ℓ)]
    [HasPrincipalDivisors k (charLDegeneracyRoof k M ℓ)]
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ)
    (hα₀ : HeckeAlphaCIntegral k M ℓ) (hβ₀ : HeckeBetaCIntegral k M ℓ)
    (i : Fin 2)
    (hfin : FiniteAlong k ((heckeBetaC k (M * s) ℓ).comp (φ i)))
    (hsep : SeparableAlong k ((heckeBetaC k (M * s) ℓ).comp (φ i)))
    (hgen : Algebra.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
      ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ i)) = ⊤)
    (hLD : finrankAlong k (heckeBetaC k (M * s) ℓ) = finrankAlong k (heckeBetaC k M ℓ))
    (D : Divisor k (modularFunctionFieldC k (M * s))) :
    Divisor.pushforwardAlong (φ i) (hφ i)
        (Divisor.correspondence (heckeBetaC k (M * s) ℓ) (heckeAlphaC k (M * s) ℓ) hβ₁ hα₁ D)
      = Divisor.correspondence (heckeBetaC k M ℓ) (heckeAlphaC k M ℓ) hβ₀ hα₀
          (Divisor.pushforwardAlong (φ i) (hφ i) D) := by
  refine pushforwardAlong_correspondence_comm_of_linearDisjoint (φ i)
    (roofMap (ℓ := ℓ) φ hφα hφβ i)
    (heckeAlphaC k M ℓ) (heckeBetaC k M ℓ) (heckeAlphaC k (M * s) ℓ) (heckeBetaC k (M * s) ℓ)
    (hφ i) (roofMap_isIntegral φ hφα hφβ hφ hα₁ i) hα₀ hβ₀ hα₁ hβ₁
    (roofMap_comp_heckeAlphaC φ hφα hφβ i) (roofMap_comp_heckeBetaC φ hφα hφβ i)
    hfin hsep hgen ?_ D
  rw [finrankAlong_comp, hLD]

end Pair

end Modular

section SelfAdjoin

open IntermediateField

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem adjoin_preimage_eq_top (E : IntermediateField k L) (S : Set L)
    (hES : E ≤ adjoin k S) (hSE : S ⊆ E) :
    adjoin k ((↑) ⁻¹' S : Set E) = ⊤ := by
  have hE : E = adjoin k S := le_antisymm hES (adjoin_le_iff.mpr hSE)
  have hSr : S ⊆ Set.range (Subtype.val : E → L) := fun x hx => ⟨⟨x, hSE hx⟩, rfl⟩
  apply lift_injective E
  rw [lift_adjoin, lift_top, Set.image_preimage_eq_of_subset hSr]
  exact hE.symm

theorem mem_adjoin_preimage (E : IntermediateField k L) (S : Set L) (hSE : S ⊆ E)
    (x : E) (hx : (x : L) ∈ adjoin k S) :
    x ∈ adjoin k ((↑) ⁻¹' S : Set E) := by
  have hSr : S ⊆ Set.range (Subtype.val : E → L) := fun x hx => ⟨⟨x, hSE hx⟩, rfl⟩
  rw [← mem_lift x, lift_adjoin, Set.image_preimage_eq_of_subset hSr]
  exact hx

theorem finiteAlong_of_adjoin_finite {F : Type*} [Field F] [Algebra k F]
    (E : IntermediateField k L) (φ : F →ₐ[k] E) (hφ : φ.toRingHom.IsIntegral)
    (S : Set L) (hS : S.Finite) (hES : E ≤ adjoin k S) (hSE : S ⊆ E) :
    FiniteAlong k φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Algebra.IsAlgebraic F E := Algebra.IsIntegral.isAlgebraic
  set T : Subalgebra F E := Algebra.adjoin F ((↑) ⁻¹' S : Set E) with hT
  have hTfield : IsField T := Subalgebra.isField_of_algebraic T
  have hinv : ∀ x ∈ T.restrictScalars k, x⁻¹ ∈ T.restrictScalars k := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [inv_zero]; exact zero_mem _
    obtain ⟨y, hy⟩ := hTfield.mul_inv_cancel (a := ⟨x, hx⟩) (fun h => hx0 (congrArg Subtype.val h))
    have hxy : x * (y : E) = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hxy]
    exact y.2
  set IF : IntermediateField k E := (T.restrictScalars k).toIntermediateField hinv with hIF
  have hIFtop : IF = ⊤ := by
    apply top_le_iff.mp
    rw [← adjoin_preimage_eq_top E S hES hSE, adjoin_le_iff]
    intro x hx
    show x ∈ T
    exact Algebra.subset_adjoin hx
  have hTtop : T = ⊤ := by
    apply top_le_iff.mp
    intro x _
    have : x ∈ IF := by rw [hIFtop]; trivial
    exact this
  haveI : Algebra.FiniteType F E := by
    refine ⟨⟨(hS.preimage Subtype.val_injective.injOn).toFinset, ?_⟩⟩
    rw [Set.Finite.coe_toFinset]
    exact hTtop
  exact Algebra.IsIntegral.finite

theorem algebra_adjoin_eq_top_of_generators {C : Type*} [Field C] [Algebra k C]
    (E : IntermediateField k L) (α : C →ₐ[k] E) (hα : α.toRingHom.IsIntegral)
    (T : Set E) (S : Set L) (hES : E ≤ adjoin k S) (hSE : S ⊆ E)
    (hgen : ∀ x : E, (x : L) ∈ S → x ∈ adjoin k (Set.range α ∪ T)) :
    Algebra.adjoin k (Set.range α ∪ T) = ⊤ := by
  letI := algebraAlong α
  haveI := isScalarTower_along α
  haveI := isIntegral_along α hα
  haveI : Algebra.IsAlgebraic C E := Algebra.IsIntegral.isAlgebraic
  set Sub : Subalgebra k E := Algebra.adjoin k (Set.range α ∪ T) with hSub
  let SubC : Subalgebra C E :=
    { Sub with
      algebraMap_mem' := fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩) }
  have hfield : IsField SubC := Subalgebra.isField_of_algebraic SubC
  have hinv : ∀ x ∈ Sub, x⁻¹ ∈ Sub := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [inv_zero]; exact zero_mem _
    have hx' : x ∈ SubC := hx
    obtain ⟨y, hy⟩ := hfield.mul_inv_cancel (a := ⟨x, hx'⟩) (fun h => hx0 (congrArg Subtype.val h))
    have hxy : x * (y : E) = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hxy]
    exact y.2
  set IF : IntermediateField k E := Sub.toIntermediateField hinv with hIF
  have hle : adjoin k (Set.range α ∪ T) ≤ IF := by
    rw [adjoin_le_iff]
    intro x hx
    show x ∈ Sub
    exact Algebra.subset_adjoin hx
  have hIFtop : IF = ⊤ := by
    apply top_le_iff.mp
    rw [← adjoin_preimage_eq_top E S hES hSE, adjoin_le_iff]
    intro x hx
    exact hle (hgen x hx)
  apply top_le_iff.mp
  intro x _
  have : x ∈ IF := by rw [hIFtop]; trivial
  exact this

end SelfAdjoin

section Degrees

open ModularCurve IntermediateField

variable (k : Type*) [Field k]

theorem qExpandAlgHomC_eq_qExpandAlgC (n : ℕ) [NeZero n] : qExpandAlgHomC k n = qExpandAlgC k n := by
  apply AlgHom.ext
  intro x
  rw [qExpandAlgHomC_apply, qExpandAlgC_apply]

theorem finrankAlong_heckeBetaC_eq_relfinrank (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    finrankAlong k (heckeBetaC k N ℓ)
      = IntermediateField.relfinrank ((modularFunctionFieldC k N).map (qExpandAlgHomC k ℓ))
          (charLDegeneracyRoof k N ℓ) := by
  have h := AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (modularFunctionFieldC k N)
    (charLDegeneracyRoof k N ℓ) (heckeBetaC k N ℓ)
  refine h.trans ?_
  congr 1
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, (coe_heckeBetaC k N ℓ y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, coe_heckeBetaC k N ℓ ⟨y, hy⟩⟩

theorem dedekindPsi_ratio_eq {ℓ s N r r' : ℕ} (hℓ : ℓ.Prime) (hs : 0 < s) (hN : 0 < N)
    (hℓs : ¬ ℓ ∣ s)
    (h : r * dedekindPsi N = dedekindPsi (N * ℓ)) (h' : r' * dedekindPsi (N * s) = dedekindPsi (N * s * ℓ)) :
    r = r' := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨a, N₀, hN₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' ℓ hℓ.ne_one
  have hcopN₀ : Nat.Coprime (ℓ ^ a) N₀ :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hN₀))
  have hcopN₀' : Nat.Coprime (ℓ ^ (a + 1)) N₀ :=
    (Nat.Coprime.pow_left (a + 1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hN₀))
  have hN₀s : ¬ ℓ ∣ N₀ * s := fun hd => (hℓ.dvd_mul.mp hd).elim hN₀ hℓs
  have hcopN₀s : Nat.Coprime (ℓ ^ a) (N₀ * s) :=
    (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hN₀s))
  have hcopN₀s' : Nat.Coprime (ℓ ^ (a + 1)) (N₀ * s) :=
    (Nat.Coprime.pow_left (a + 1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hN₀s))
  have e1 : ℓ ^ a * N₀ * ℓ = ℓ ^ (a + 1) * N₀ := by ring
  have e2 : ℓ ^ a * N₀ * s = ℓ ^ a * (N₀ * s) := by ring
  have e3 : ℓ ^ a * N₀ * s * ℓ = ℓ ^ (a + 1) * (N₀ * s) := by ring
  rw [e1, dedekindPsi_mul_of_coprime _ _ hcopN₀, dedekindPsi_mul_of_coprime _ _ hcopN₀'] at h
  rw [e3, e2, dedekindPsi_mul_of_coprime _ _ hcopN₀s, dedekindPsi_mul_of_coprime _ _ hcopN₀s'] at h'
  have hψN₀ : 0 < dedekindPsi N₀ := dedekindPsi_pos _ (fun h0 => hN₀ (h0 ▸ dvd_zero ℓ))
  have hψN₀s : 0 < dedekindPsi (N₀ * s) :=
    dedekindPsi_pos _ (Nat.mul_ne_zero (fun h0 => hN₀ (h0 ▸ dvd_zero ℓ)) hs.ne')
  have hψa : 0 < dedekindPsi (ℓ ^ a) := dedekindPsi_pos _ (pow_ne_zero a hℓ.ne_zero)
  have hr : r * dedekindPsi (ℓ ^ a) = dedekindPsi (ℓ ^ (a + 1)) := by
    apply Nat.eq_of_mul_eq_mul_right hψN₀
    calc r * dedekindPsi (ℓ ^ a) * dedekindPsi N₀ = r * (dedekindPsi (ℓ ^ a) * dedekindPsi N₀) := by ring
      _ = dedekindPsi (ℓ ^ (a + 1)) * dedekindPsi N₀ := h
  have hr' : r' * dedekindPsi (ℓ ^ a) = dedekindPsi (ℓ ^ (a + 1)) := by
    apply Nat.eq_of_mul_eq_mul_right hψN₀s
    calc r' * dedekindPsi (ℓ ^ a) * dedekindPsi (N₀ * s)
        = r' * (dedekindPsi (ℓ ^ a) * dedekindPsi (N₀ * s)) := by ring
      _ = dedekindPsi (ℓ ^ (a + 1)) * dedekindPsi (N₀ * s) := h'
  exact Nat.eq_of_mul_eq_mul_right hψa (hr.trans hr'.symm)

theorem finrankAlong_heckeBetaC_mul_eq (M s ℓ p : ℕ) [NeZero M] [NeZero s] [NeZero ℓ]
    [NeZero (M * s)] [CharP k p] (hs : s.Prime) (hℓ : ℓ.Prime) (hℓs : ℓ ≠ s)
    (hp : ¬ p ∣ M * s * ℓ) :
    finrankAlong k (heckeBetaC k (M * s) ℓ) = finrankAlong k (heckeBetaC k M ℓ) := by
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  haveI : NeZero (M * s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * s)) (NeZero.ne ℓ)⟩
  have hpM : ¬ p ∣ M := fun h => hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h s) ℓ)
  have hpMs : ¬ p ∣ M * s := fun h => hp (dvd_mul_of_dvd_left h ℓ)
  have hpMℓ : ¬ p ∣ M * ℓ := fun h => hp (by
    rcases h with ⟨c, hc⟩
    exact ⟨c * s, by rw [mul_right_comm, hc]; ring⟩)
  have castMℓ : ((M * ℓ : ℕ) : k) ≠ 0 := fun h => hpMℓ ((CharP.cast_eq_zero_iff k p _).mp h)
  have castMsℓ : ((M * s * ℓ : ℕ) : k) ≠ 0 := fun h => hp ((CharP.cast_eq_zero_iff k p _).mp h)
  rw [finrankAlong_heckeBetaC_eq_relfinrank, finrankAlong_heckeBetaC_eq_relfinrank,
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p (M * s) hpMs,
    modularFunctionFieldC_eq_modularFunctionFieldFullC k p M hpM,
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k p (M * s) ℓ hp,
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k p M ℓ hpMℓ]
  have h := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k M ℓ castMℓ).2
  have h' := (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi k (M * s) ℓ castMsℓ).2
  exact (dedekindPsi_ratio_eq hℓ hs.pos (Nat.pos_of_ne_zero (NeZero.ne M))
    (fun hd => hℓs ((Nat.prime_dvd_prime_iff_eq hℓ hs).mp hd)) h h').symm

end Degrees

section Separability

open IntermediateField

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem isSeparable_of_le {A T : IntermediateField k L} (h : A ≤ T) {x : L}
    (hx : IsSeparable A x) : IsSeparable T x := by
  letI : Algebra A T := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  exact IsSeparable.tower_top T hx

theorem isSeparable_of_le' {A B : IntermediateField k L} (T : IntermediateField B L)
    (h : ∀ a : L, a ∈ A → a ∈ T) {x : L} (hx : IsSeparable A x) : IsSeparable T x := by
  letI : Algebra A T := RingHom.toAlgebra
    { toFun := fun a => ⟨a, h a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  exact IsSeparable.tower_top T hx

theorem isSeparable_of_mem' {B : IntermediateField k L} (T : IntermediateField B L) {x : L} (hx : x ∈ T) :
    IsSeparable T x :=
  isSeparable_algebraMap (⟨x, hx⟩ : T)

set_option maxHeartbeats 3200000 in

theorem separableAlong_inclusion_of_generators (B E : IntermediateField k L) (hBE : B ≤ E)
    (S₁ : Set L) (hS₁ : ∀ x ∈ S₁, IsSeparable B x)
    (S : Set L) (hES : E ≤ adjoin k S)
    (hS : ∀ x ∈ S, IsSeparable (adjoin B S₁) x) :
    SeparableAlong k (IntermediateField.inclusion hBE) := by
  haveI : Algebra.IsSeparable B (adjoin B S₁) :=
    (isSeparable_adjoin_iff_isSeparable B L).mpr hS₁
  haveI hE'sep : Algebra.IsSeparable (adjoin B S₁) (adjoin (adjoin B S₁) S) :=
    (isSeparable_adjoin_iff_isSeparable _ L).mpr hS
  have hle : adjoin k S ≤ ((adjoin (adjoin B S₁) S).restrictScalars B).restrictScalars k :=
    adjoin_le_iff.mpr (fun y hy => subset_adjoin (adjoin B S₁) S hy)
  have hsepL : ∀ x : L, x ∈ E → IsSeparable B x := by
    intro x hx
    have hx' : x ∈ adjoin (adjoin B S₁) S := by
      have h := hle (hES hx)
      rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_restrictScalars] at h
      exact h
    have h2 : IsSeparable (adjoin B S₁) x :=
      IntermediateField.isSeparable_of_mem_isSeparable (adjoin B S₁) L hx'
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable B h2
  letI := algebraAlong (IntermediateField.inclusion hBE)
  haveI := isScalarTower_along (IntermediateField.inclusion hBE)
  let f : E →ₐ[B] L :=
    { E.val.toRingHom with
      commutes' := fun _ => rfl }
  exact ⟨fun x => (isSeparable_map_iff f Subtype.val_injective).mp (hsepL x.1 x.2)⟩

theorem separableAlong_of_range_eq {F : Type*} [Field F] [Algebra k F]
    (B E : IntermediateField k L) (hBE : B ≤ E) (φ : F →ₐ[k] E)
    (hφB : ∀ a, (φ a : L) ∈ B) (hsurj : ∀ b : L, b ∈ B → ∃ a, (φ a : L) = b)
    (hsep : SeparableAlong k (IntermediateField.inclusion hBE)) : SeparableAlong k φ := by
  let g : F →+* B :=
    { toFun := fun a => ⟨(φ a : L), hφB a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hgval : ∀ a, ((g a : B) : L) = (φ a : L) := fun a => rfl
  have hg : Function.Bijective g := by
    constructor
    · intro a a' h
      have h1 : (φ a : L) = (φ a' : L) := by rw [← hgval, ← hgval, h]
      exact φ.toRingHom.injective (Subtype.ext h1)
    · intro b
      obtain ⟨a, ha⟩ := hsurj b b.2
      exact ⟨a, Subtype.ext ha⟩
  let e₁ : B ≃+* F := (RingEquiv.ofBijective g hg).symm
  letI i1 : Algebra B E := algebraAlong (IntermediateField.inclusion hBE)
  letI i2 : Algebra F E := algebraAlong φ
  have hsep' : @Algebra.IsSeparable B E _ _ i1 := hsep
  refine @Algebra.IsSeparable.of_equiv_equiv B E F E _ _ _ _ i1 i2 e₁ (RingEquiv.refl E) ?_ hsep'
  apply RingHom.ext
  intro b
  apply Subtype.ext
  show ((φ (e₁ b) : E) : L) = ((IntermediateField.inclusion hBE b : E) : L)
  rw [IntermediateField.coe_inclusion, ← hgval]
  have h1 : g (e₁ b) = b := (RingEquiv.ofBijective g hg).apply_symm_apply b
  rw [h1]

end Separability

section Igusa

open ModularCurve IntermediateField Polynomial

theorem eval₂_swapBivar {R : Type*} [CommRing R] (Φ : Polynomial (Polynomial ℤ)) (x y : R) :
    (swapBivar Φ).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) y) x
      = Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom R) x) y := by
  have key1 : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) y) x).comp swapInner
      = Polynomial.eval₂RingHom (Int.castRingHom R) x := by
    apply Polynomial.ringHom_ext
    · intro n
      simp [swapInner]
    · simp [swapInner]
  have key : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) y) x).comp swapBivar
      = Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom R) x) y := by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : swapBivar (Polynomial.C a) = swapInner a := by
        simp [swapBivar]
      rw [RingHom.comp_apply, h1]
      have h2 := congrFun (congrArg DFunLike.coe key1) a
      rw [RingHom.comp_apply] at h2
      rw [h2]
      simp
    · rw [RingHom.comp_apply, swapBivar_X]
      simp
  have := congrFun (congrArg DFunLike.coe key) Φ
  simpa using this

variable (k : Type*) [Field k]

theorem eval₂_phi_jN_jNs {s : ℕ} [NeZero s] (data : ModularPolynomialData s) (N : ℕ) [NeZero N] :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k N))
      (jqNModC k (N * s)) = 0 := by
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero data k N
  have h3 : (Polynomial.aeval (R := ℤ) (jqNModC k N)).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k N) := by
    apply Polynomial.ringHom_ext
    · intro m; simp
    · simp
  rw [← h3]
  exact h

theorem isSeparable_jqNModC_adjoin_jqNModC_mul (s : ℕ) [Fact s.Prime] (hs : (s : k) ≠ 0)
    (N : ℕ) [NeZero N] [NeZero (N * s)] :
    IsSeparable (IntermediateField.adjoin k ({jqNModC k (N * s)} : Set (LaurentSeries k))) (jqNModC k N) := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm s

  have hP : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqModC k))).Separable :=
    ModularPolynomialData.separable_map_jqModC_of_prime k data hs

  have hev : (qExpand k (N * s)).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqModC k))
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k (N * s)) := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · simp [jqNModC]
  have hQ : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k (N * s)))).Separable := by
    rw [← hev, ← Polynomial.map_map]
    exact hP.map

  have hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k))
      (jqNModC k (N * s)))).eval (jqNModC k N) = 0 := by
    rw [Polynomial.eval_map]
    have h1 := eval₂_swapBivar data.Φ (jqNModC k N) (jqNModC k (N * s))
    rw [swapBivar_eq_of_evalSymm hsymm] at h1
    rw [h1]
    exact eval₂_phi_jN_jNs k data N

  set T := IntermediateField.adjoin k ({jqNModC k (N * s)} : Set (LaurentSeries k)) with hT
  have hjs : jqNModC k (N * s) ∈ T := subset_adjoin k _ (Set.mem_singleton _)
  have hmapT : (algebraMap T (LaurentSeries k)).comp
      (Polynomial.eval₂RingHom (Int.castRingHom T) (⟨jqNModC k (N * s), hjs⟩ : T))
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k (N * s)) := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have hQT : ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom T) (⟨jqNModC k (N * s), hjs⟩ : T))).map
      (algebraMap T (LaurentSeries k)))
      = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqNModC k (N * s))) := by
    rw [Polynomial.map_map, hmapT]
  have hsepT : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom T) (⟨jqNModC k (N * s), hjs⟩ : T))).Separable := by
    rw [← Polynomial.separable_map (algebraMap T (LaurentSeries k)), hQT]
    exact hQ
  have haeval : Polynomial.aeval (jqNModC k N)
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom T) (⟨jqNModC k (N * s), hjs⟩ : T))) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hQT]
    exact hroot
  exact Polynomial.Separable.of_dvd hsepT (minpoly.dvd _ (jqNModC k N) haeval)

theorem jqNModC_congr {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    jqNModC k a = jqNModC k b := by
  subst h
  rfl

theorem isSeparable_jqModC_adjoin_jqNModC (s : ℕ) [Fact s.Prime] (hs : (s : k) ≠ 0) :
    IsSeparable (IntermediateField.adjoin k ({jqNModC k s} : Set (LaurentSeries k))) (jqModC k) := by
  haveI : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  haveI : NeZero (1 * s) := ⟨by rw [one_mul]; exact NeZero.ne s⟩
  have h := isSeparable_jqNModC_adjoin_jqNModC_mul k s hs 1
  rw [jqNModC_congr k (one_mul s), jqNModC_one] at h
  exact h

end Igusa

section GoodChar

open ModularCurve IntermediateField

variable {k : Type*} [Field k] {M s ℓ : ℕ} [NeZero M] [NeZero s] [NeZero ℓ] [NeZero (M * s)]

variable (φ : Fin 2 → (modularFunctionFieldC k M →ₐ[k] modularFunctionFieldC k (M * s)))

theorem finiteAlong_heckeBetaC_comp (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hℓ : ℓ.Prime) (i : Fin 2) :
    FiniteAlong k ((heckeBetaC k (M * s) ℓ).comp (φ i)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hfinφ : FiniteAlong k (φ i) := by
    refine finiteAlong_of_adjoin_finite (modularFunctionFieldC k (M * s)) (φ i) (hφ i)
      ({jqModC k, jqNModC k (M * s)} : Set (LaurentSeries k)) (Set.toFinite _) ?_ ?_
    · unfold modularFunctionFieldC; exact le_rfl
    · intro x hx
      rcases hx with rfl | rfl
      · exact jqModC_mem k (M * s)
      · exact jqNModC_mem k (M * s)
  exact AlgebraicCurve.finiteAlong_comp (φ i) (heckeBetaC k (M * s) ℓ) hfinφ
    (finiteAlong_heckeBetaC k (M * s) ℓ)

omit [NeZero M] in

theorem roof_le_adjoin_gens :
    charLDegeneracyRoof k (M * s) ℓ ≤ IntermediateField.adjoin k
      ({jqModC k, jqNModC k (M * s), jqNModC k ℓ, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k)) := by
  unfold charLDegeneracyRoof; exact le_rfl

omit [NeZero M] in
theorem gens_subset_roof :
    ({jqModC k, jqNModC k (M * s), jqNModC k ℓ, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k))
      ⊆ charLDegeneracyRoof k (M * s) ℓ := by
  unfold charLDegeneracyRoof; exact IntermediateField.subset_adjoin k _

theorem mem_adjoin_of_coe_qExpand (T : Set (charLDegeneracyRoof k (M * s) ℓ))
    (x : charLDegeneracyRoof k (M * s) ℓ) (y : modularFunctionFieldC k (M * s))
    (hx : (x : LaurentSeries k) = qExpand k ℓ (y : LaurentSeries k)) :
    x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ) ∪ T) := by
  refine IntermediateField.subset_adjoin k _ (Or.inl ⟨y, ?_⟩)
  apply Subtype.ext
  rw [coe_heckeBetaC]
  exact hx.symm

theorem mem_adjoin_of_coe_eq (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x) (i : Fin 2)
    (y : charLDegeneracyRoof k M ℓ) (x : charLDegeneracyRoof k (M * s) ℓ)
    (hx : (x : LaurentSeries k) = (roofMap (ℓ := ℓ) φ hφα hφβ i y : LaurentSeries k)) :
    x ∈ IntermediateField.adjoin k
      (Set.range (heckeBetaC k (M * s) ℓ) ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ i)) :=
  IntermediateField.subset_adjoin k _ (Or.inr ⟨y, Subtype.ext hx.symm⟩)

omit [NeZero s] [NeZero (M * s)] in
theorem jqNModC_mem_roof (N : ℕ) [NeZero N] : jqNModC k N ∈ charLDegeneracyRoof k N ℓ := by
  unfold charLDegeneracyRoof
  exact IntermediateField.subset_adjoin k _ (by simp)

omit [NeZero s] [NeZero (M * s)] in
theorem jqNModC_mul_mem_roof (N : ℕ) [NeZero N] [NeZero (N * ℓ)] :
    jqNModC k (N * ℓ) ∈ charLDegeneracyRoof k N ℓ := by
  unfold charLDegeneracyRoof
  exact IntermediateField.subset_adjoin k _ (by simp)

omit [NeZero s] [NeZero M] [NeZero (M * s)] in
theorem jqNModC_ell_mem_roof (N : ℕ) [NeZero N] : jqNModC k ℓ ∈ charLDegeneracyRoof k N ℓ := by
  unfold charLDegeneracyRoof
  exact IntermediateField.subset_adjoin k _ (by simp)

omit [NeZero s] [NeZero M] [NeZero (M * s)] in
theorem jqModC_mem_roof (N : ℕ) [NeZero N] : jqModC k ∈ charLDegeneracyRoof k N ℓ := by
  unfold charLDegeneracyRoof
  exact IntermediateField.subset_adjoin k _ (by simp)

theorem hgen_zero (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x)
    (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s * ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ) :
    Algebra.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
      ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 0)) = ⊤ := by
  haveI : NeZero (M * s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * s)) (NeZero.ne ℓ)⟩
  refine algebra_adjoin_eq_top_of_generators (charLDegeneracyRoof k (M * s) ℓ)
    (heckeBetaC k (M * s) ℓ) hβ₁ _ _ roof_le_adjoin_gens gens_subset_roof ?_

  have hj : ∀ x : charLDegeneracyRoof k (M * s) ℓ, (x : LaurentSeries k) = jqModC k →
      x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
        ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 0)) := fun x hx =>
    mem_adjoin_of_coe_eq φ hφα hφβ 0 ⟨jqModC k, jqModC_mem_roof M⟩ x (by rw [coe_roofMap_zero, hx])
  have hjMsℓ : ∀ x : charLDegeneracyRoof k (M * s) ℓ, (x : LaurentSeries k) = jqNModC k (M * s * ℓ) →
      x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
        ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 0)) := fun x hx =>
    mem_adjoin_of_coe_qExpand _ x ⟨jqNModC k (M * s), jqNModC_mem k (M * s)⟩
      (by rw [hx]; exact jqNModC_mul k (M * s) ℓ)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx | hx
  · exact hj x hx
  ·
    have hmem : (x : LaurentSeries k) ∈ IntermediateField.adjoin k
        ({jqModC k, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k)) := by
      have h := modularFunctionFieldC_eq_modularFunctionFieldFullC k p (M * s * ℓ) hp
      unfold modularFunctionFieldC at h
      rw [h, hx]
      exact jqModCd_mem_full k (M * s * ℓ) (dvd_mul_right (M * s) ℓ)
    have hSE : ({jqModC k, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k))
        ⊆ charLDegeneracyRoof k (M * s) ℓ := by
      intro y hy
      rcases hy with rfl | rfl
      · exact jqModC_mem_roof (M * s)
      · exact jqNModC_mul_mem_roof (M * s)
    have h2 := mem_adjoin_preimage (charLDegeneracyRoof k (M * s) ℓ) _ hSE x hmem
    refine (IntermediateField.adjoin_le_iff.mpr ?_) h2
    intro y hy
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · exact hj y hy
    · exact hjMsℓ y hy
  · exact mem_adjoin_of_coe_qExpand _ x ⟨jqModC k, jqModC_mem k (M * s)⟩ (by rw [hx]; rfl)
  · exact hjMsℓ x hx

theorem hgen_one (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x)
    (hs : s.Prime) (hℓ : ℓ.Prime) (hℓs : ℓ ≠ s) (hsℓ : ((s * ℓ : ℕ) : k) ≠ 0)
    (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ) :
    Algebra.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
      ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 1)) = ⊤ := by
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  haveI : NeZero (s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne s) (NeZero.ne ℓ)⟩
  haveI : NeZero (ℓ * s) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne s)⟩
  haveI : NeZero (M * s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * s)) (NeZero.ne ℓ)⟩
  refine algebra_adjoin_eq_top_of_generators (charLDegeneracyRoof k (M * s) ℓ)
    (heckeBetaC k (M * s) ℓ) hβ₁ _ _ roof_le_adjoin_gens gens_subset_roof ?_

  have hjs_coe : (roofMap (ℓ := ℓ) φ hφα hφβ 1 ⟨jqModC k, jqModC_mem_roof M⟩ : LaurentSeries k)
      = jqNModC k s := coe_roofMap_one φ hφα hφβ _
  have hjsℓ_coe : (roofMap (ℓ := ℓ) φ hφα hφβ 1 ⟨jqNModC k ℓ, jqNModC_ell_mem_roof M⟩ : LaurentSeries k)
      = jqNModC k (s * ℓ) := by
    rw [coe_roofMap_one, ← jqNModC_mul k ℓ s]
    exact jqNModC_congr k (Nat.mul_comm ℓ s)
  have hjs : ∀ x : charLDegeneracyRoof k (M * s) ℓ, (x : LaurentSeries k) = jqNModC k s →
      x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
        ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 1)) := fun x hx =>
    mem_adjoin_of_coe_eq φ hφα hφβ 1 _ x (hx.trans hjs_coe.symm)
  have hjℓ : ∀ x : charLDegeneracyRoof k (M * s) ℓ, (x : LaurentSeries k) = jqNModC k ℓ →
      x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
        ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 1)) := fun x hx =>
    mem_adjoin_of_coe_qExpand _ x ⟨jqModC k, jqModC_mem k (M * s)⟩ (by rw [hx]; rfl)
  have hjsℓ : ∀ x : charLDegeneracyRoof k (M * s) ℓ, (x : LaurentSeries k) = jqNModC k (s * ℓ) →
      x ∈ IntermediateField.adjoin k (Set.range (heckeBetaC k (M * s) ℓ)
        ∪ Set.range (roofMap (ℓ := ℓ) φ hφα hφβ 1)) := fun x hx =>
    mem_adjoin_of_coe_eq φ hφα hφβ 1 _ x (hx.trans hjsℓ_coe.symm)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx | hx
  ·
    have hgen := jqModC_mem_adjoin_jqNModC_of_prime_of_ne k s ℓ hs hℓ hℓs.symm hsℓ
    have hSE : ({jqNModC k s, jqNModC k ℓ, jqNModC k (s * ℓ)} : Set (LaurentSeries k))
        ⊆ charLDegeneracyRoof k (M * s) ℓ := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · rw [← hjs_coe]; exact Subtype.mem _
      · exact jqNModC_ell_mem_roof (M * s)
      · rw [← hjsℓ_coe]; exact Subtype.mem _
    have h2 := mem_adjoin_preimage (charLDegeneracyRoof k (M * s) ℓ) _ hSE x (hx ▸ hgen)
    refine (IntermediateField.adjoin_le_iff.mpr ?_) h2
    intro y hy
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy
    · exact hjs y hy
    · exact hjℓ y hy
    · exact hjsℓ y hy
  · refine mem_adjoin_of_coe_eq φ hφα hφβ 1 ⟨jqNModC k M, jqNModC_mem_roof M⟩ x ?_
    rw [coe_roofMap_one, hx]
    exact jqNModC_mul k M s
  · exact hjℓ x hx
  · refine mem_adjoin_of_coe_qExpand _ x ⟨jqNModC k (M * s), jqNModC_mem k (M * s)⟩ ?_
    rw [hx]
    exact jqNModC_mul k (M * s) ℓ

theorem isSeparable_gens (hMs : ((M * s : ℕ) : k) ≠ 0) (hℓ0 : ((ℓ : ℕ) : k) ≠ 0)
    (hMsℓ : ((M * s * ℓ : ℕ) : k) ≠ 0) :
    ∀ x ∈ ({jqModC k, jqNModC k (M * s), jqNModC k ℓ, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k)),
      IsSeparable (IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))) x := by
  haveI : NeZero (M * s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * s)) (NeZero.ne ℓ)⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact isSeparable_algebraMap
      (⟨jqModC k, IntermediateField.subset_adjoin k _ (Set.mem_singleton _)⟩ :
        IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k)))
  · exact isSeparable_jqNModC_of_natCast_ne_zero k (M * s) hMs
  · exact isSeparable_jqNModC_of_natCast_ne_zero k ℓ hℓ0
  · exact isSeparable_jqNModC_of_natCast_ne_zero k (M * s * ℓ) hMsℓ

theorem hsep_zero
    (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
    (hℓ : ℓ.Prime) (hMs : ((M * s : ℕ) : k) ≠ 0) (hℓ0 : ((ℓ : ℕ) : k) ≠ 0)
    (hMsℓ : ((M * s * ℓ : ℕ) : k) ≠ 0) :
    SeparableAlong k ((heckeBetaC k (M * s) ℓ).comp (φ 0)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  set B : IntermediateField k (LaurentSeries k) := (modularFunctionFieldC k M).map (qExpandAlgC k ℓ) with hB
  have hBE : B ≤ charLDegeneracyRoof k (M * s) ℓ := by
    rintro _ ⟨x, hx, rfl⟩
    exact qExpand_image_le_charLDegeneracyRoof k (M * s) ℓ ⟨x, le_of_pinned (φ 0) hφα hx, rfl⟩
  have hjℓB : jqNModC k ℓ ∈ B := ⟨jqModC k, jqModC_mem k M, rfl⟩
  have hS₁ : ∀ x ∈ ({jqModC k} : Set (LaurentSeries k)), IsSeparable B x := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine isSeparable_of_le ?_ (isSeparable_jqModC_adjoin_jqNModC k ℓ hℓ0)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjℓB)
  have hincl : SeparableAlong k (IntermediateField.inclusion hBE) := by
    refine separableAlong_inclusion_of_generators B _ hBE {jqModC k} hS₁ _ roof_le_adjoin_gens ?_
    intro x hx
    refine isSeparable_of_le' (IntermediateField.adjoin B ({jqModC k} : Set (LaurentSeries k))) ?_
      (isSeparable_gens hMs hℓ0 hMsℓ x hx)
    intro a ha
    have hle : IntermediateField.adjoin k ({jqModC k} : Set (LaurentSeries k))
        ≤ (IntermediateField.adjoin B ({jqModC k} : Set (LaurentSeries k))).restrictScalars k :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
        (IntermediateField.mem_adjoin_simple_self B (jqModC k)))
    exact hle ha
  have hval : ∀ a, (((heckeBetaC k (M * s) ℓ).comp (φ 0) a : charLDegeneracyRoof k (M * s) ℓ) :
      LaurentSeries k) = qExpand k ℓ (a : LaurentSeries k) := by
    intro a
    rw [AlgHom.comp_apply, coe_heckeBetaC, hφα]
  have h1 : ∀ a, (((heckeBetaC k (M * s) ℓ).comp (φ 0) a : charLDegeneracyRoof k (M * s) ℓ) :
      LaurentSeries k) ∈ B := fun a => ⟨a, a.2, (hval a).symm⟩
  have h2 : ∀ b : LaurentSeries k, b ∈ B →
      ∃ a, (((heckeBetaC k (M * s) ℓ).comp (φ 0) a : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = b := by
    rintro b ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, hval ⟨x, hx⟩⟩
  exact separableAlong_of_range_eq B _ hBE _ h1 h2 hincl

theorem hsep_one
    (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x)
    (hs : s.Prime) (hℓ : ℓ.Prime) (hs0 : ((s : ℕ) : k) ≠ 0) (hℓ0 : ((ℓ : ℕ) : k) ≠ 0) :
    SeparableAlong k ((heckeBetaC k (M * s) ℓ).comp (φ 1)) := by
  haveI : Fact s.Prime := ⟨hs⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero (ℓ * s) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne s)⟩
  haveI : NeZero (M * s * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne (M * s)) (NeZero.ne ℓ)⟩
  set B : IntermediateField k (LaurentSeries k) :=
    ((modularFunctionFieldC k M).map (qExpandAlgC k s)).map (qExpandAlgC k ℓ) with hB
  have hBE : B ≤ charLDegeneracyRoof k (M * s) ℓ := by
    rintro _ ⟨y, hy, rfl⟩
    exact qExpand_image_le_charLDegeneracyRoof k (M * s) ℓ ⟨y, map_le_of_pinned (φ 1) hφβ hy, rfl⟩

  have hjℓsB : jqNModC k (ℓ * s) ∈ B := by
    refine ⟨qExpand k s (jqModC k), ⟨jqModC k, jqModC_mem k M, rfl⟩, ?_⟩
    show qExpand k ℓ (qExpand k s (jqModC k)) = jqNModC k (ℓ * s)
    rw [qExpand_qExpand]
    rfl
  have hjMsℓB : jqNModC k (M * s * ℓ) ∈ B := by
    refine ⟨qExpand k s (jqNModC k M), ⟨jqNModC k M, jqNModC_mem k M, rfl⟩, ?_⟩
    show qExpand k ℓ (qExpand k s (jqNModC k M)) = jqNModC k (M * s * ℓ)
    rw [← jqNModC_mul k M s, ← jqNModC_mul k (M * s) ℓ]
  set T : IntermediateField B (LaurentSeries k) :=
    IntermediateField.adjoin B ({jqNModC k ℓ} : Set (LaurentSeries k)) with hT
  have hS₁ : ∀ x ∈ ({jqNModC k ℓ} : Set (LaurentSeries k)), IsSeparable B x := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine isSeparable_of_le ?_ (isSeparable_jqNModC_adjoin_jqNModC_mul k s hs0 ℓ)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjℓsB)
  have hBT : ∀ a : LaurentSeries k, a ∈ B → a ∈ T := fun a ha => T.algebraMap_mem ⟨a, ha⟩
  have hjℓT : jqNModC k ℓ ∈ T := IntermediateField.mem_adjoin_simple_self B (jqNModC k ℓ)
  have hS : ∀ x ∈ ({jqModC k, jqNModC k (M * s), jqNModC k ℓ, jqNModC k (M * s * ℓ)} : Set (LaurentSeries k)),
      IsSeparable T x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    ·
      refine isSeparable_of_le' T ?_ (isSeparable_jqModC_adjoin_jqNModC k ℓ hℓ0)
      intro a ha
      exact (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjℓT) :
        IntermediateField.adjoin k ({jqNModC k ℓ} : Set (LaurentSeries k)) ≤ T.restrictScalars k) ha
    ·
      refine isSeparable_of_le' T ?_ (isSeparable_jqNModC_adjoin_jqNModC_mul k ℓ hℓ0 (M * s))
      intro a ha
      exact (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hBT _ hjMsℓB)) :
        IntermediateField.adjoin k ({jqNModC k (M * s * ℓ)} : Set (LaurentSeries k)) ≤ T.restrictScalars k) ha
    · exact isSeparable_of_mem' T hjℓT
    · exact isSeparable_of_mem' T (hBT _ hjMsℓB)
  have hincl : SeparableAlong k (IntermediateField.inclusion hBE) :=
    separableAlong_inclusion_of_generators B _ hBE {jqNModC k ℓ} hS₁ _ roof_le_adjoin_gens hS
  have hval : ∀ a, (((heckeBetaC k (M * s) ℓ).comp (φ 1) a : charLDegeneracyRoof k (M * s) ℓ) :
      LaurentSeries k) = qExpand k ℓ (qExpand k s (a : LaurentSeries k)) := by
    intro a
    rw [AlgHom.comp_apply, coe_heckeBetaC, hφβ]
  have h1 : ∀ a, (((heckeBetaC k (M * s) ℓ).comp (φ 1) a : charLDegeneracyRoof k (M * s) ℓ) :
      LaurentSeries k) ∈ B := fun a => ⟨qExpand k s a, ⟨a, a.2, rfl⟩, (hval a).symm⟩
  have h2 : ∀ b : LaurentSeries k, b ∈ B →
      ∃ a, (((heckeBetaC k (M * s) ℓ).comp (φ 1) a : charLDegeneracyRoof k (M * s) ℓ) :
        LaurentSeries k) = b := by
    rintro b ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, hval ⟨x, hx⟩⟩
  exact separableAlong_of_range_eq B _ hBE _ h1 h2 hincl

theorem comm_of_not_dvd (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hφα : ∀ x, ((φ 0 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = x)
    (hφβ : ∀ x, ((φ 1 x : modularFunctionFieldC k (M * s)) : LaurentSeries k) = qExpand k s x)
    (p : ℕ) [CharP k p] (hs : s.Prime) (hℓ : ℓ.Prime) (hℓs : ℓ ≠ s)
    (hp : ¬ p ∣ M * s * ℓ)
    [HasPrincipalDivisors k (charLDegeneracyRoof k (M * s) ℓ)]
    [HasPrincipalDivisors k (charLDegeneracyRoof k M ℓ)]
    (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ)
    (hα₀ : HeckeAlphaCIntegral k M ℓ) (hβ₀ : HeckeBetaCIntegral k M ℓ)
    (i : Fin 2) (D : Divisor k (modularFunctionFieldC k (M * s))) :
    Divisor.pushforwardAlong (φ i) (hφ i)
        (Divisor.correspondence (heckeBetaC k (M * s) ℓ) (heckeAlphaC k (M * s) ℓ) hβ₁ hα₁ D)
      = Divisor.correspondence (heckeBetaC k M ℓ) (heckeAlphaC k M ℓ) hβ₀ hα₀
          (Divisor.pushforwardAlong (φ i) (hφ i) D) := by
  have hpMs : ¬ p ∣ M * s := fun h => hp (dvd_mul_of_dvd_left h ℓ)
  have hps : ¬ p ∣ s := fun h => hpMs (dvd_mul_of_dvd_right h M)
  have hpℓ : ¬ p ∣ ℓ := fun h => hp (dvd_mul_of_dvd_right h _)
  have hpsℓ : ¬ p ∣ s * ℓ := fun h => hp (by
    rcases h with ⟨c, hc⟩
    exact ⟨c * M, by nlinarith [hc]⟩)
  have cast_ne : ∀ n : ℕ, ¬ p ∣ n → ((n : ℕ) : k) ≠ 0 :=
    fun n hn h => hn ((CharP.cast_eq_zero_iff k p n).mp h)
  refine comm_of_linearDisjoint φ hφα hφβ hφ hα₁ hβ₁ hα₀ hβ₀ i
    (finiteAlong_heckeBetaC_comp φ hφ hℓ i) ?_ ?_
    (finrankAlong_heckeBetaC_mul_eq k M s ℓ p hs hℓ hℓs hp) D
  · fin_cases i
    · exact hsep_zero φ hφα hℓ (cast_ne _ hpMs) (cast_ne _ hpℓ) (cast_ne _ hp)
    · exact hsep_one φ hφβ hs hℓ (cast_ne _ hps) (cast_ne _ hpℓ)
  · fin_cases i
    · exact hgen_zero φ hφα hφβ p hp hβ₁
    · exact hgen_one φ hφα hφβ hs hℓ hℓs (cast_ne _ hpsℓ) hβ₁

end GoodChar

end R1LawsC3
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd.R1LawsC3"

end
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd.R1LawsC3"

open AlgebraicCurve ModularCurve in
theorem solution
    (M s ℓ : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) (hℓ : ℓ.Prime) (hℓs : ℓ ≠ s)
    {k : Type*} [Field k] (p : ℕ) [CharP k p] (hp : ¬ p ∣ M * s * ℓ) :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k (M * s) ℓ)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M ℓ)]
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x)
      (hα₁ : HeckeAlphaCIntegral k (M * s) ℓ) (hβ₁ : HeckeBetaCIntegral k (M * s) ℓ)
      (hα₀ : HeckeAlphaCIntegral k M ℓ) (hβ₀ : HeckeBetaCIntegral k M ℓ)
      (i : Fin 2) (D : Divisor k ↥(modularFunctionFieldC k (M * s))),
      Divisor.pushforwardAlong (φ i) (hφ i)
          (Divisor.correspondence (heckeBetaC k (M * s) ℓ) (heckeAlphaC k (M * s) ℓ) hβ₁ hα₁ D)
        = Divisor.correspondence (heckeBetaC k M ℓ) (heckeAlphaC k M ℓ) hβ₀ hα₀
            (Divisor.pushforwardAlong (φ i) (hφ i) D) := by
  intro _ _ φ hφ hφα hφβ hα₁ hβ₁ hα₀ hβ₀ i D
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact R1LawsC3.comm_of_not_dvd φ hφ hφα hφβ p hs hℓ hℓs hp hα₁ hβ₁ hα₀ hβ₀ i D

end S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd (solution)
