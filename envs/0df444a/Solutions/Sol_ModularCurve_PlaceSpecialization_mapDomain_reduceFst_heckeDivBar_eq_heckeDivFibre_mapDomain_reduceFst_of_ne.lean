-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/eaba68d5-fa58-5968-b8b9-2acf3af27480

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_heckeExchangeAt_of_primes_of_ne
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_eq_of_forall_single
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

noncomputable section

open AlgebraicCurve ModularCurve

namespace HeckeLevelChangeExchange

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem pushforwardAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong φ' hφ' D := by
  subst h
  rfl

private theorem pullbackAlong_congr [HasPrincipalDivisors K F'] {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong φ' hφ' D := by
  subst h
  rfl

private theorem inertiaDegAlong_eq_one_of_isRational (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hw : w.IsRational) (hv : (w.restrictAlong φ hφ).IsRational) :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.inertiaDeg_eq_one_of_isRational w hw hv

private theorem pushforwardAlong_eq_mapDomain (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hf : ∀ w : Place K F', w.inertiaDegAlong φ hφ = 1) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Finsupp.mapDomain (fun w => w.restrictAlong φ hφ) D := by
  refine Finsupp.induction_linear D ?_ (fun D₁ D₂ h₁ h₂ => ?_) (fun w n => ?_)
  · simp
  · rw [map_add, Finsupp.mapDomain_add, h₁, h₂]
  · rw [Divisor.pushforwardAlong_single, hf, Nat.cast_one, mul_one, Finsupp.mapDomain_single]

end Generic

private theorem isRational_bar (M : ℕ) [NeZero M]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : v.IsRational := by
  haveI := isCurveOver_modularFunctionFieldBar M
  haveI : Module.Finite (AlgebraicClosure ℚ) v.ResidueField := IsCurveOver.finiteResidue v
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ)
    (K := v.ResidueField)).2

private theorem inertiaDegAlong_bar_eq_one {M M' : ℕ} [NeZero M] [NeZero M']
    (φ : modularFunctionFieldBar M →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M')
    (hφ : φ.toRingHom.IsIntegral) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M')) :
    w.inertiaDegAlong φ hφ = 1 :=
  inertiaDegAlong_eq_one_of_isRational φ hφ w (isRational_bar M' w) (isRational_bar M _)

section Exchange

variable (N q ℓ : ℕ) [NeZero N] [NeZero q] [NeZero ℓ] [Fact q.Prime] [Fact ℓ.Prime] (hne : ℓ ≠ q)
  (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
  (hαN : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
  (hβN : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
  (hαNq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
  (hβNq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
  [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))]
  [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * ℓ))]

include hne in

private theorem pushforwardAlong_heckeDivBar
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (heckeDivBar hαNq hβNq E)
      = heckeDivBar hαN hβN
          (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq E) := by

  have hM : N * q * ℓ = N * ℓ * q := Nat.mul_right_comm N q ℓ
  have h1 : N * ℓ ∣ N * q * ℓ := (dvd_of_eq_roof N ℓ q (N * q * ℓ) hM).1
  have h2 : N * q * ℓ ∣ N * q * ℓ := (dvd_of_eq_roof N ℓ q (N * q * ℓ) hM).2
  have h0 : N ∣ N * q * ℓ := Dvd.dvd.mul_right (dvd_mul_right N q) ℓ
  have hu : (towerInclBar (AlgebraicClosure ℚ) h1).toRingHom.IsIntegral :=
    towerInclBar_isIntegral (AlgebraicClosure ℚ) h1
  have hu' : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ h2).toRingHom.IsIntegral :=
    towerSubstBar_isIntegral (AlgebraicClosure ℚ) ℓ h2
  have h0I : (towerInclBar (AlgebraicClosure ℚ) h0).toRingHom.IsIntegral :=
    towerInclBar_isIntegral (AlgebraicClosure ℚ) h0

  have hcompL : (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) = towerInclBar (AlgebraicClosure ℚ) h0 := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply, coe_heckeAlphaBar, coe_heckeAlphaBar, coe_towerInclBar]
  have hcompR : (towerInclBar (AlgebraicClosure ℚ) h1).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) = towerInclBar (AlgebraicClosure ℚ) h0 := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply, coe_towerInclBar, coe_heckeAlphaBar, coe_towerInclBar]
  have hsub : towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ h2
      = heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [coe_towerSubstBar, coe_heckeBetaBar]
  have hIL : ((heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N q)).toRingHom.IsIntegral := by
    rw [hcompL]; exact h0I
  have hIR : ((towerInclBar (AlgebraicClosure ℚ) h1).comp
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)).toRingHom.IsIntegral := by
    rw [hcompR]; exact h0I

  have hex : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ q (N * q * ℓ) hM :=
    heckeExchangeAt_of_primes_of_ne (AlgebraicClosure ℚ) N ℓ q (N * q * ℓ) Fact.out Fact.out hne hM
  have key := hex hβN hαq hu hu' E

  show Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq
      (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hαNq
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβNq E))
    = Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαN
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβN
          (Divisor.pushforwardAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq E))
  rw [key, Divisor.pushforwardAlong_pushforwardAlong _ _ hαq hαNq hIL,
    Divisor.pushforwardAlong_pushforwardAlong _ _ hαN hu hIR,
    pushforwardAlong_congr hcompL hIL h0I, pushforwardAlong_congr hcompR hIR h0I,
    pullbackAlong_congr hsub hu' hβNq]

include hne in

private theorem mapDomain_restrictAlong_heckeDivBar
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Finsupp.mapDomain (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq)
        (heckeDivBar hαNq hβNq E)
      = heckeDivBar hαN hβN
          (Finsupp.mapDomain
            (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq) E) := by
  rw [← pushforwardAlong_eq_mapDomain _ hαq (inertiaDegAlong_bar_eq_one _ hαq),
    ← pushforwardAlong_eq_mapDomain _ hαq (inertiaDegAlong_bar_eq_one _ hαq)]
  exact pushforwardAlong_heckeDivBar N q ℓ hne hαq hαN hβN hαNq hβNq E

end Exchange

end HeckeLevelChangeExchange

end

open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField A) N))
      (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
        ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f)),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          ∀ [Fact (ℓ : ℕ).Prime]
            (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
            (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ)
            (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))]
            [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
            (hdeg1 : ∀ Y : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ), Y.deg = 1)
            (Rℓ : RegularProlongation A (modularFunctionFieldBar (N * (ℓ : ℕ)))
              (charLDegeneracyRoof (ResidueField A) N ℓ))
            (rℓ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ)))
              → Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
            (hrℓ : ∀ f : Rℓ.integers, Rℓ.residue f ≠ 0 →
              ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * (ℓ : ℕ))),
                (∀ V, D V = V.ord (f : modularFunctionFieldBar (N * (ℓ : ℕ)))) →
              ∀ Q, Finsupp.mapDomain rℓ D Q = Q.ord (Rℓ.residue f))
            (hRα : ∀ f : R₁.integers,
              ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeAlphaC (ResidueField A) N ℓ (R₁.residue f))
            (hRβ : ∀ f : R₁.integers,
              ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N ℓ (f : modularFunctionFieldBar N) ∈ Rℓ.integers,
                Rℓ.residue ⟨_, h⟩ = heckeBetaC (ResidueField A) N ℓ (R₁.residue f))
            (hdegα : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hαℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeAlphaC (ResidueField A) N ℓ) hαc
                  (Finsupp.single (P.sp v) 1)))
            (hdegβ : ∀ v, Divisor.degree
                (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβℓ (Finsupp.single v 1))
              = Divisor.degree (Divisor.pullbackAlong (heckeBetaC (ResidueField A) N ℓ) hβc
                  (Finsupp.single (P.sp v) 1)))
          (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q * (ℓ : ℕ)))]
          (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          Finsupp.mapDomain P.reduceFst (heckeDivBar hαq hβq X) =
            heckeDivFibre (ResidueField A) N ℓ hβc hαc (Finsupp.mapDomain P.reduceFst X) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro data hKr hα hβ P R₁ hr₁ l hlq _instFℓ hαℓ hβℓ hαc hβc _hpdN _hpdNℓ _hpdRoof hdeg1 Rℓ rℓ hrℓ hRα hRβ hdegα
    hdegβ hαq hβq _hpdNqℓ X
  haveI : NeZero (l : ℕ) := ⟨l.2.ne_zero⟩

  have hsq : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Finsupp.mapDomain P.sp (heckeDivBar hαℓ hβℓ (Finsupp.single v 1)) =
        heckeDivFibre (ResidueField A) N (l : ℕ) hβc hαc (Finsupp.single (P.sp v) 1) :=
    fun v => ModularCurve.mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation N A (l : ℕ) hαℓ
      hβℓ hαc hβc hdeg1 R₁ P.sp hr₁ Rℓ rℓ hrℓ hRα hRβ hdegα hdegβ v

  have hsp : ∀ Y : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Finsupp.mapDomain P.sp (heckeDivBar hαℓ hβℓ Y) =
        heckeDivFibre (ResidueField A) N (l : ℕ) hβc hαc (Finsupp.mapDomain P.sp Y) :=
    fun Y => mapDomain_heckeDivBar_eq_of_forall_single hαℓ hβℓ P.sp
      (heckeDivFibre (ResidueField A) N (l : ℕ) hβc hαc) hsq Y

  have hcomp : ∀ Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      Finsupp.mapDomain P.reduceFst Z =
        Finsupp.mapDomain P.sp
          (Finsupp.mapDomain
            (fun V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
              V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) Z) :=
    fun Z => Finsupp.mapDomain_comp
      (f := fun V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
        V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
      (g := P.sp) (v := Z)
  exact (hcomp _).trans
    ((congrArg (fun Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) => Finsupp.mapDomain P.sp Z)
        (HeckeLevelChangeExchange.mapDomain_restrictAlong_heckeDivBar N q (l : ℕ) hlq hα hαℓ hβℓ hαq hβq X)).trans
      ((hsp _).trans (congrArg (fun Z => heckeDivFibre (ResidueField A) N (l : ℕ) hβc hαc Z) (hcomp X).symm)))

end S_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne (solution)
