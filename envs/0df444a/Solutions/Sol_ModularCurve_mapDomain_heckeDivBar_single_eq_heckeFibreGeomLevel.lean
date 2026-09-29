-- Prove2me | solution 1 for ModularCurve.mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4f70a6af-2f55-58e7-9785-16c0a61575cf

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_towerSubstBar_finiteAlong
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open AlgebraicCurve ModularCurve Finset

namespace S09S3

local notation "𝕂" => AlgebraicClosure ℚ

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

theorem inertiaDegAlong_eq_one_of_deg_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.deg = 1) : w.inertiaDegAlong φ hφ = 1 := by
  have h := deg_restrictAlong_mul_inertiaDegAlong φ hφ w
  rw [hw] at h
  exact Nat.eq_one_of_mul_eq_one_left h

end Generic

section Level

variable (N ℓ : ℕ) [NeZero N] [hl : Fact ℓ.Prime]

theorem finiteAlong_beta : FiniteAlong 𝕂 (heckeBetaBar 𝕂 N ℓ) := by
  rw [heckeBetaBar_eq_towerSubstBar]
  exact towerSubstBar_finiteAlong 𝕂 ℓ dvd_rfl

theorem sum_ramificationIndexAlong_heckeBetaBar (hlN : ¬ ℓ ∣ N) (hβ : HeckeBetaBarIntegral 𝕂 N ℓ)
    [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (N * ℓ))]
    (hdeg1 : ∀ W : Place 𝕂 (modularFunctionFieldBar (N * ℓ)), W.deg = 1)
    (v : Place 𝕂 (modularFunctionFieldBar N)) :
    ∑ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v, (W.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) : ℤ) = ℓ + 1 := by
  have h := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong (heckeBetaBar 𝕂 N ℓ) hβ (finiteAlong_beta N ℓ)
    (separableAlong_of_charZero (heckeBetaBar 𝕂 N ℓ) hβ) v
  rw [finrankAlong_heckeBetaBar 𝕂 N ℓ, if_neg hlN] at h
  push_cast at h
  rw [← h]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [inertiaDegAlong_eq_one_of_deg_eq_one _ hβ W (hdeg1 W), Nat.cast_one, mul_one]

theorem mapDomain_heckeDivBar_single_of_deg_eq_one {k : Type*} [Field k] (hα : HeckeAlphaBarIntegral 𝕂 N ℓ)
    (hβ : HeckeBetaBarIntegral 𝕂 N ℓ) [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (N * ℓ))]
    (hdeg1 : ∀ W : Place 𝕂 (modularFunctionFieldBar (N * ℓ)), W.deg = 1)
    (sp : Place 𝕂 (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N))
    (v : Place 𝕂 (modularFunctionFieldBar N)) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1))
      = ∑ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v,
          Finsupp.single (sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα)) (W.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) : ℤ) := by
  rw [mapDomain_heckeDivBar_single hα hβ sp v 1]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [inertiaDegAlong_eq_one_of_deg_eq_one _ hα W (hdeg1 W), Nat.cast_one, mul_one, one_mul]

variable {k : Type*} [Field k] [CharP k ℓ] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

theorem mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel (hlN : ¬ ℓ ∣ N)
    (hα : HeckeAlphaBarIntegral 𝕂 N ℓ) (hβ : HeckeBetaBarIntegral 𝕂 N ℓ)
    [HasPrincipalDivisors 𝕂 (modularFunctionFieldBar (N * ℓ))]
    (hdeg1 : ∀ W : Place 𝕂 (modularFunctionFieldBar (N * ℓ)), W.deg = 1)
    (sp : Place 𝕂 (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N))
    (d1 : ∀ W : Place 𝕂 (modularFunctionFieldBar (N * ℓ)),
      sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα)
          = frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeBetaBar 𝕂 N ℓ) hβ)) ∨
        frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα))
          = sp (W.restrictAlong (heckeBetaBar 𝕂 N ℓ) hβ))
    (d2 : ∀ v : Place 𝕂 (modularFunctionFieldBar N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (sp v)) ≠ sp v →
        ∃ W₀ : Place 𝕂 (modularFunctionFieldBar (N * ℓ)), W₀.restrictAlong (heckeBetaBar 𝕂 N ℓ) hβ = v ∧
          sp (W₀.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = frobOnPlacesGeomLevel k N data hKr (sp v) ∧
          W₀.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) = 1 ∧
          ∀ W : Place 𝕂 (modularFunctionFieldBar (N * ℓ)), W.restrictAlong (heckeBetaBar 𝕂 N ℓ) hβ = v →
            sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = frobOnPlacesGeomLevel k N data hKr (sp v) → W = W₀)
    (v : Place 𝕂 (modularFunctionFieldBar N)) :
    Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1))
      = heckeFibreGeomLevel k N data hKr (Finsupp.single (sp v) 1) := by
  classical
  set x := sp v with hx
  set Fx := frobOnPlacesGeomLevel k N data hKr x with hFx
  set Vx := verOnPlacesGeomLevel k N data hKr x with hVx
  have hRHS : heckeFibreGeomLevel k N data hKr (Finsupp.single x 1)
      = Finsupp.single Fx 1 + Finsupp.single Vx (ℓ : ℤ) := by
    rw [heckeFibreGeomLevel, AddMonoidHom.add_apply,
      frobeniusPushforwardGeomLevel_single, frobeniusPullbackGeomLevel_single, one_mul]
  rw [hRHS, mapDomain_heckeDivBar_single_of_deg_eq_one N ℓ hα hβ hdeg1 sp v]

  have d1v : ∀ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v,
      sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx ∨
        frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα)) = x := by
    intro W hW
    have hWv := Place.mem_fiberAlong.mp hW
    rcases d1 W with h | h
    · left; rw [h, hWv]
    · right; rw [h, hWv]

  have hb : ∀ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v,
      frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα)) = x →
        sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Vx := by
    intro W _ h
    rw [hVx, ← h, verOnPlacesGeomLevel_frobOnPlacesGeomLevel]
  have hsum := sum_ramificationIndexAlong_heckeBetaBar N ℓ hlN hβ hdeg1 v
  by_cases hcol : frobOnPlacesGeomLevel k N data hKr Fx = x
  · have hVF : Vx = Fx := by
      rw [hVx, ← hcol, verOnPlacesGeomLevel_frobOnPlacesGeomLevel]
    have hall : ∀ W ∈ Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v,
        sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx := by
      intro W hW
      rcases d1v W hW with h | h
      · exact h
      · rw [hb W hW h, hVF]
    rw [Finset.sum_congr rfl (fun W hW => by rw [hall W hW]), ← Finsupp.single_finsetSum, hsum, hVF,
      ← Finsupp.single_add]
    congr 1
    ring
  ·
    obtain ⟨W₀, hW₀, hW₀a, hW₀e, huniq⟩ := d2 v hcol
    have hfilt : (Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v).filter
        (fun W => sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx) = {W₀} := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hW, hWa⟩; exact huniq W (Place.mem_fiberAlong.mp hW) hWa
      · rintro rfl; exact ⟨Place.mem_fiberAlong.mpr hW₀, hW₀a⟩
    have h2 : ∑ W ∈ (Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v).filter
        (fun W => sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx),
        (W.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) : ℤ) = 1 := by
      rw [hfilt, Finset.sum_singleton, hW₀e, Nat.cast_one]
    rw [← Finset.sum_filter_add_sum_filter_not (Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v)
      (fun W => sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx)]
    have ha : ∑ W ∈ (Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v).filter
        (fun W => sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx),
        Finsupp.single (sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα)) (W.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) : ℤ)
          = Finsupp.single Fx 1 := by
      rw [Finset.sum_congr rfl (fun W hW => by rw [(Finset.mem_filter.mp hW).2]), ← Finsupp.single_finsetSum, h2]
    have htot := Finset.sum_filter_add_sum_filter_not (Place.fiberAlong (heckeBetaBar 𝕂 N ℓ) hβ v)
      (fun W => sp (W.restrictAlong (heckeAlphaBar 𝕂 N ℓ) hα) = Fx)
      (fun W => (W.ramificationIndexAlong (heckeBetaBar 𝕂 N ℓ) : ℤ))
    rw [hsum, h2] at htot
    rw [ha]
    congr 1
    rw [Finset.sum_congr rfl (fun W hW => by
      obtain ⟨hW', hne⟩ := Finset.mem_filter.mp hW
      rcases d1v W hW' with h | h
      · exact absurd h hne
      · rw [hb W hW' h]), ← Finsupp.single_finsetSum]
    congr 1
    rw [add_comm] at htot
    exact add_right_cancel htot

end Level

end S09S3

theorem solution (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hlN : ¬ ℓ ∣ N) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] (hdeg1 : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), W.deg = 1) {k : Type*} [Field k] [CharP k ℓ] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data) (sp : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place k (modularFunctionFieldC k N)) (d1 : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα) = frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)) ∨ frobOnPlacesGeomLevel k N data hKr (sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα)) = sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ)) (d2 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (sp v)) ≠ sp v → ∃ W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v ∧ sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα) = frobOnPlacesGeomLevel k N data hKr (sp v) ∧ W₀.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = 1 ∧ ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)), W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v → sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα) = frobOnPlacesGeomLevel k N data hKr (sp v) → W = W₀) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : Finsupp.mapDomain sp (heckeDivBar hα hβ (Finsupp.single v 1)) = heckeFibreGeomLevel k N data hKr (Finsupp.single (sp v) 1) := by
  exact S09S3.mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel N ℓ data hKr hlN hα hβ hdeg1 sp d1 d2 v

end S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel
end P2MW
export P2MW.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeFibreGeomLevel (solution)
