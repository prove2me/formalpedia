-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1192395e-5501-5ebe-9ef9-d264b1e6c9f7

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_chartAlgFin_int
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionField
import Theorems.Thm_ModularCurve_modularFunctionFieldFull_algHom_ext
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace OggALH

theorem gammaM_le_gamma0 (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    ΓM M H ≤ CongruenceSubgroup.Gamma0 p := by
  intro γ hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hγ
  rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
  have := congrArg (ZMod.castHom hpM (ZMod p)) h0
  rwa [map_intCast, map_zero] at this

theorem full_le (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H) := by
  rw [← modularFunctionFieldFullC_rat]
  exact (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans
    (qExpFunctionFieldC_mono ℚ (gammaM_le_gamma0 p M H hpM))

noncomputable def incl (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) :
    ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)) :=
  (RingHomClass.toRingHom (IntermediateField.inclusion hle)).toRatAlgHom

theorem coe_incl (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) (x : ↥(modularFunctionFieldFull p)) :
    ((incl p M H hle x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := by
  rw [incl, RingHom.toRatAlgHom_apply, RingHom.coe_coe, IntermediateField.coe_inclusion]

theorem incl_jFull (p M : ℕ) [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) :
    incl p M H hle (IgusaScheme.jFull p) = jAt (ΓM M H) hj := by
  apply Subtype.ext
  rw [coe_incl, IgusaScheme.coe_jFull, coe_jAt, jqModC_rat]

theorem incl_mem_chartAlgFin (p M : ℕ) [Fact p.Prime] [NeZero p] (H : Subgroup (ZMod M)ˣ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H))
    {a : ↥(modularFunctionFieldFull p)}
    (ha : a ∈ TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :
    incl p M H hle a ∈ chartAlgFin p (ΓM M H) hj := by
  classical
  set ι := incl p M H hle with hιdef
  let θℤ : ↥(modularFunctionFieldFull p) →ₐ[ℤ] ↥(qExpFunctionFieldC ℚ (ΓM M H)) := ι.toRingHom.toIntAlgHom
  have hmapadj : ∀ x ∈ Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)),
      ι x ∈ Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
    intro x hx
    have h1 : θℤ x ∈ (Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))).map θℤ :=
      Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at h1
    have h2 : Algebra.adjoin ℤ ({θℤ (IgusaScheme.jFull p)} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))) ≤
        (Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))).restrictScalars ℤ := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      show ι (IgusaScheme.jFull p) ∈ Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))
      rw [hιdef, incl_jFull p M H hj hle]
      exact Algebra.subset_adjoin rfl
    exact h2 h1
  let φ : ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))) →+*
      ↥(Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H)))) :=
    RingHom.codRestrict (ι.toRingHom.comp
      (Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p))).toSubring.subtype) _
      (fun x => hmapadj x x.2)
  have hcomp : (algebraMap ↥(Algebra.adjoin (R p) ({jAt (ΓM M H) hj} : Set ↥(qExpFunctionFieldC ℚ (ΓM M H))))
        ↥(qExpFunctionFieldC ℚ (ΓM M H))).comp φ =
      ι.toRingHom.comp (algebraMap ↥(Algebra.adjoin ℤ ({IgusaScheme.jFull p} : Set ↥(modularFunctionFieldFull p)))
        ↥(modularFunctionFieldFull p)) := by
    ext x
    rfl
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at ha ⊢
  exact ha.map_of_comp_eq φ ι.toRingHom hcomp

theorem sigma_comp_incl (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
        ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ))
    [NeZero p] (hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H)) (x : ↥(modularFunctionFieldFull p)) :
    σ (incl p M H hle x) = incl p M H hle (frickeInvolutionFull p x) := by
  classical
  have hp : p.Prime := Fact.out
  haveI hMp : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos).ne'⟩
  set ι := incl p M H hle with hιdef
  have hι : ∀ x : ↥(modularFunctionFieldFull p),
      ((ι x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := coe_incl p M H hle
  have hw : IsFrickeAutFull p (frickeInvolutionFull p) := isFrickeAutFull_frickeInvolutionFull_prime p

  obtain ⟨σ₀, h₀i, h₀ii⟩ := exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  have hσ₀ : ∀ x, σ x = σ₀ x := by
    have key := algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup p M H hpM hpM2 hHp (σ₀.trans σ.symm) (by
      intro f u hfu
      have e : σ₀ f = σ f := Subtype.ext (by rw [h₀i f u hfu, hσ f u hfu])
      rw [AlgEquiv.trans_apply, e, AlgEquiv.symm_apply_apply])
    intro x
    have hx : σ.symm (σ₀ x) = x := by
      have := congrArg (fun e : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)) => e x) key
      simpa using this
    calc σ x = σ (σ.symm (σ₀ x)) := by rw [hx]
      _ = σ₀ x := σ.apply_symm_apply _

  have hjN : (jq : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (ΓN p M H hpM) := by
    rw [← jqModC_rat]; exact qExpFunctionFieldC_mono ℚ le_top hj
  have h1N : qExpand ℚ 1 jq ∈ qExpFunctionFieldC ℚ (ΓN p M H hpM) := by
    rw [qExpand_one_apply]; exact hjN

  have e1 : ((ι ⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
      ((⟨qExpand ℚ 1 jq, h1N⟩ : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) :=
    (hι _).trans ((Subtype.coe_mk _ _).trans (Subtype.coe_mk _ _).symm)
  have hgen1 : σ (ι ⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩) =
      ι (frickeInvolutionFull p ⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩) := by
    apply Subtype.ext
    rw [hw 1 p (one_mul p) inferInstance inferInstance, hι,
      hσ (ι ⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩) ⟨qExpand ℚ 1 jq, h1N⟩ e1,
      Subtype.coe_mk, Subtype.coe_mk, qExpand_one_apply]

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    have : p * p ∣ p * (M / p) := mul_dvd_mul_left p h
    rwa [Nat.mul_div_cancel' hpM, ← pow_two] at this
  have hcop : Nat.Coprime p (M / p) := hp.coprime_iff_not_dvd.mpr hpN
  have hσjp : ((σ (ι ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
      LaurentSeries ℚ) = jq := by
    rw [hσ₀]
    have hfu : ((ι ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩ : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
        qExpand ℚ p ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) := by
      rw [hι, coe_jAt, jqModC_rat, Subtype.coe_mk]
    have h2 := h₀ii (ZMod.unitOfCoprime p hcop) (ZMod.coe_unitOfCoprime p hcop)
      (ι ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩) (jAt (ΓN p M H hpM) hj) hfu
    have hx : ((⟨coeffEmb (AlgebraicClosure ℚ) ((jAt (ΓN p M H hpM) hj : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jAt (ΓN p M H hpM) hj).2⟩ :
          ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) jq := by
      rw [Subtype.coe_mk, coe_jAt, jqModC_rat]
    rw [diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM)
      (ZMod.unitOfCoprime p hcop) _ jq (by rw [← jqModC_rat]; exact qExpFunctionFieldC_mono ℚ le_top hj) hx, hx] at h2
    exact (coeffEmb (AlgebraicClosure ℚ)).injective h2
  have hgenp : σ (ι ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩) =
      ι (frickeInvolutionFull p ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩) := by
    apply Subtype.ext
    rw [hσjp, hw p 1 (mul_one p) inferInstance inferInstance, hι, Subtype.coe_mk, qExpand_one_apply]

  have key : (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) →ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H))).comp ι =
      ι.comp (frickeInvolutionFull p : ↥(modularFunctionFieldFull p) →ₐ[ℚ] ↥(modularFunctionFieldFull p)) := by
    apply modularFunctionFieldFull_algHom_ext
    intro d _ hd
    rcases (Nat.dvd_prime hp).mp hd with hd1 | hdp
    · subst hd1
      exact hgen1
    · have hpd := hdp.symm
      subst hpd
      exact hgenp
  exact DFunLike.congr_fun key x

end OggALH

open OggALH in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
        ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) :
    ∃ v w : ↥(chartAlgFin p (ΓM M H) hj),
      (((v : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∧
      (((w : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹ ∧
      v * w = algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12) ∧
      σ ((v : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((w : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H) := full_le p M H hpM
  set ι := incl p M H hle with hιdef
  have hι : ∀ x : ↥(modularFunctionFieldFull p),
      ((ι x : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := coe_incl p M H hle

  have hmem : modularUnitSeries p ∈ modularFunctionFieldFull p :=
    modularFunctionField_le_full p (modularUnitSeries_mem_modularFunctionField p)
  obtain ⟨hint, hint'⟩ := modularUnitSeries_mem_chartAlgFin_int p hmem
  set uF : ↥(modularFunctionFieldFull p) := ⟨modularUnitSeries p, hmem⟩ with huF_def
  have huF : (uF : LaurentSeries ℚ) = modularUnitSeries p := by rw [huF_def, Subtype.coe_mk]
  have hne0 : uF ≠ 0 := fun h => modularUnitSeries_ne_zero p (by rw [← huF, h, ZeroMemClass.coe_zero])

  have hσu : σ (ι uF) = ι (frickeInvolutionFull p uF) := sigma_comp_incl p M H hpM hpM2 hHp hj σ hσ hle uF
  have hwu : ((frickeInvolutionFull p uF : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹ := by
    rw [huF_def, coe_frickeInvolutionFull_modularUnitSeries p hmem, ← HahnSeries.C_mul_eq_smul, map_pow, map_natCast]
  have hwu' : frickeInvolutionFull p uF = (p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹ := by
    apply Subtype.ext
    rw [hwu]
    push_cast
    rw [huF]
  refine ⟨⟨ι uF, incl_mem_chartAlgFin p M H hj hle hint⟩,
    ⟨ι ((p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹), incl_mem_chartAlgFin p M H hj hle hint'⟩, ?_, ?_, ?_, ?_⟩
  · show ((ι uF : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = _
    rw [hι, huF]
  · show ((ι ((p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) :
        LaurentSeries ℚ) = _
    rw [← hwu', hι, hwu]
  · apply Subtype.ext
    rw [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
    show ι uF * ι ((p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹) = _
    rw [← map_mul, mul_left_comm, mul_inv_cancel₀ hne0, mul_one, map_pow, map_natCast, map_pow, map_natCast]
  · show σ (ι uF) = ι ((p : ↥(modularFunctionFieldFull p)) ^ 12 * uF⁻¹)
    rw [hσu, hwu']

end S_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH (solution)
