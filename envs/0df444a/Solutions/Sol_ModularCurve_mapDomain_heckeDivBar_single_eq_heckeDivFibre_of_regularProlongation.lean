-- Prove2me | solution 1 for ModularCurve.mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fb69682a-a29b-5bbf-93ea-fd96eed4d759

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace HeckeCorrespondenceReduction

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem isRational_restrict_of_isRational [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) :
    (w.restrict F).IsRational := by
  intro y
  obtain ⟨k, hk⟩ := hw (algebraMap (w.restrict F).ResidueField w.ResidueField y)
  refine ⟨k, (algebraMap (w.restrict F).ResidueField w.ResidueField).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField k]
  exact hk

private theorem isRational_restrictAlong_of_isRational (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.IsRational) :
    (w.restrictAlong φ hφ).IsRational := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact isRational_restrict_of_isRational w hw

private theorem inertiaDegAlong_eq_one_of_isRational (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.IsRational)
    (hv : (w.restrictAlong φ hφ).IsRational) : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.inertiaDeg_eq_one_of_isRational w hw hv

private theorem inertiaDegAlong_eq_one_of_isRational' (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.IsRational) :
    w.inertiaDegAlong φ hφ = 1 :=
  inertiaDegAlong_eq_one_of_isRational φ hφ w hw (isRational_restrictAlong_of_isRational φ hφ w hw)

private theorem pushforwardAlong_eq_mapDomain (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hf : ∀ w : Place K F', w.inertiaDegAlong φ hφ = 1) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Finsupp.mapDomain (fun w => w.restrictAlong φ hφ) D := by
  refine Finsupp.induction_linear D ?_ (fun D₁ D₂ h₁ h₂ => ?_) (fun w n => ?_)
  · simp
  · rw [map_add, Finsupp.mapDomain_add, h₁, h₂]
  · rw [Divisor.pushforwardAlong_single, hf, Nat.cast_one, mul_one, Finsupp.mapDomain_single]

private theorem isRational_of_deg_eq_one (w : Place K F) (h : w.deg = 1) : w.IsRational :=
  ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp h).2

end Generic

private theorem isRational_bar (M : ℕ) [NeZero M]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : v.IsRational := by
  haveI := isCurveOver_modularFunctionFieldBar M
  haveI : Module.Finite (AlgebraicClosure ℚ) v.ResidueField := IsCurveOver.finiteResidue v
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ)
    (K := v.ResidueField)).2

end HeckeCorrespondenceReduction

open HeckeCorrespondenceReduction in

theorem solution
    (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (q : ℕ) [hq' : Fact q.Prime] [NeZero (N * q)]
    (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N q)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A (modularFunctionFieldBar (N * q))
      (charLDegeneracyRoof (ResidueField ↥A) N q))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q))
    (hr : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * q))) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hRα : ∀ f : R₁.integers,
      ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N q (R₁.residue f))
    (hRβ : ∀ f : R₁.integers,
      ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N q (R₁.residue f))
    (hdegα : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc (Finsupp.single (r₁ v) 1)))
    (hdegβ : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc (Finsupp.single (r₁ v) 1))) :
    ∀ v, Finsupp.mapDomain r₁ (heckeDivBar hαq hβq (Finsupp.single v 1))
      = heckeDivFibre (ResidueField ↥A) N q hβc hαc (Finsupp.single (r₁ v) 1) := by
  intro v
  obtain ⟨_, hpb, hra, _⟩ :=
    PlaceSpecialization.exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
      N A q hαq hβq hαc hβc hdeg1 R₁ r₁ hr₁ R r hr hRα hRβ hdegα hdegβ

  have hgen : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq = 1 :=
    fun W => inertiaDegAlong_eq_one_of_isRational (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq W
      (isRational_bar (N * q) W) (isRational_bar N _)
  have hfib : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q),
      Y.inertiaDegAlong (heckeAlphaC (ResidueField ↥A) N q) hαc = 1 :=
    fun Y => inertiaDegAlong_eq_one_of_isRational' (heckeAlphaC (ResidueField ↥A) N q) hαc Y
      (isRational_of_deg_eq_one Y (hdeg1 Y))

  have hfun : (r₁ ∘ fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq)
      = ((fun Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q) =>
          Y.restrictAlong (heckeAlphaC (ResidueField ↥A) N q) hαc) ∘ r) :=
    funext fun W => (hra W).symm
  calc Finsupp.mapDomain r₁ (heckeDivBar hαq hβq (Finsupp.single v 1))
      = Finsupp.mapDomain r₁ (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))) :=
        rfl
    _ = Finsupp.mapDomain r₁
          (Finsupp.mapDomain (fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
              W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq)
            (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))) :=
        congrArg (Finsupp.mapDomain r₁) (pushforwardAlong_eq_mapDomain _ hαq hgen _)
    _ = Finsupp.mapDomain (r₁ ∘ fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
            W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq)
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1)) :=
        Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          ((fun Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q) =>
              Y.restrictAlong (heckeAlphaC (ResidueField ↥A) N q) hαc) ∘ r)
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1)) :=
        congrArg (fun φ => Finsupp.mapDomain φ
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))) hfun
    _ = Finsupp.mapDomain
          (fun Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q) =>
            Y.restrictAlong (heckeAlphaC (ResidueField ↥A) N q) hαc)
          (Finsupp.mapDomain r
            (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))) :=
        Finsupp.mapDomain_comp
    _ = Divisor.pushforwardAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
          (Finsupp.mapDomain r
            (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))) :=
        (pushforwardAlong_eq_mapDomain _ hαc hfib _).symm
    _ = Divisor.pushforwardAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
          (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc (Finsupp.single (r₁ v) 1)) :=
        congrArg (Divisor.pushforwardAlong (heckeAlphaC (ResidueField ↥A) N q) hαc) (hpb v)
    _ = heckeDivFibre (ResidueField ↥A) N q hβc hαc (Finsupp.single (r₁ v) 1) := rfl

end S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
end P2MW
export P2MW.S_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation (solution)
