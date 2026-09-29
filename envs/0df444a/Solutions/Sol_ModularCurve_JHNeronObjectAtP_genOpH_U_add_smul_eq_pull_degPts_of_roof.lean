-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.genOpH_U_add_smul_eq_pull_degPts_of_roof
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/7f79066e-4304-5db7-a54e-a6eb0c526982

import Mathlib
import Theorems.Thm_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_U_add_smul_eq_pull_degPts_of_roof
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hpN : ¬ p ∣ M / p) (hM : M = M / p * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S : Set ℕ)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))]

    (αH βH : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (hαq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((αH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβq : ∀ u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)), ((βH u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (αpull : Fin 2 → (JH (M / p) (ModularCurve.infSubgroup p M H hpM) →+ JH M H))

    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hpull1 : ∀ (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))))
        (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),
      (Dv : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) = Divisor.pullbackAlong βH hβint (Dw : Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))) →
        αpull 1 (Pic0.mk Dw) = Pic0.mk Dv)

    (hle : CohCarrier.GammaH M H ≤ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
    (pbar : (ZMod (M / p))ˣ) (hpbar : (pbar : ZMod (M / p)) = p)
    (hin : ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H p)
    (hβN : ModularCurve.HeckeBetaHDefined (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : ModularCurve.HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    (hfinα : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p))
    (hNα : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hfinα)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p)))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (hι : ι.toRingHom.IsIntegral)
    (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιβ : (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)).toRingHom.IsIntegral)
    (hFIιβ : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)) hιβ)
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))))
    (hWβ : ∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x)
    (hWα : ∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p
            ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pbar).symm x))

    (hιsurj : Function.Surjective (Pic0.pullbackAlongHom ι hι hFIι))
    (hιdegα : ∀ D : Divisor (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      Divisor.pushforwardAlong αH hαint (Divisor.pullbackAlong ι hι D) =
        Divisor.pushforwardAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hα D)
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθι : ∀ x₁ : Pic0 (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFIι x₁ =
        Pic0.pullbackAlongHom ι hι hFIι (SemilinearAut.ofAlgAut W.symm • x₁)) :
    ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) x + SemilinearAut.ofAlgAut θ • x = αpull 1 (O.degPts 0 x) := by
  classical

  have hαH : αH = ι.comp (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) := by
    apply AlgHom.ext; intro u; apply Subtype.ext
    rw [hαq u, AlgHom.comp_apply, hιcoe, ModularCurve.coe_heckeAlphaHBar]
  have hβH : βH = ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) := by
    apply AlgHom.ext; intro u; apply Subtype.ext
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    rw [hβq u, AlgHom.comp_apply, hιcoe, ModularCurve.coe_heckeBetaHBar _ _ _ hβN]
  subst hαH
  subst hβH

  intro x
  obtain ⟨x₁, rfl⟩ := hιsurj x
  rw [ModularCurve.genOpH_U, hθι x₁,
    ModularCurve.JH.heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
      (M / p) p hpN M hM (ModularCurve.infSubgroup p M H hpM) H hle pbar hpbar hin hβN ι hιcoe hα hfinα hNα hι hFIι hιβ hFIιβ W hWβ hWα x₁]

  obtain ⟨D₁, rfl⟩ := Pic0.mk_surjective x₁
  rw [Pic0.pushforwardAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk]
  rw [hdeg0 (Pic0.pullbackAlongDegZeroHom ι hι hFIι D₁)
        (Pic0.pushforwardAlongDegZero (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hα D₁) ?hw]
  case hw =>
    rw [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_pullbackAlongDegZeroHom, hιdegα]
  rw [hpull1 (Pic0.pushforwardAlongDegZero (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hα D₁)
        (Pic0.pullbackAlongDegZeroHom (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p)) hιβ hFIιβ
          (Pic0.pushforwardAlongDegZero (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p) hα D₁)) ?hv]
  case hv =>
    rw [Pic0.coe_pullbackAlongDegZeroHom]

end S_ModularCurve_JHNeronObjectAtP_genOpH_U_add_smul_eq_pull_degPts_of_roof
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_genOpH_U_add_smul_eq_pull_degPts_of_roof (solution)
