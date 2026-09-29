-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/addf9188-1389-5138-9f09-0a8ae1b668c9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_AlgebraicGeometry_Scheme_span_singleton_le_span_singleton_of_forall_germ_eq_mul
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_isInvertible_ideal_eq_span_of_locallyPrincipalDatum
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

namespace TwistAsm

structure Frame where
  p : ℕ
  M : ℕ
  [inst1 : Fact p.Prime]
  [inst2 : NeZero M]
  H : Subgroup (ZMod M)ˣ
  hpM : p ∣ M
  hpM2 : ¬ p ^ 2 ∣ M
  hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H
  [inst3 : NeZero (M / p)]
  hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))
  𝔛 : XHDRModelAtP p M H hpM hj

  A : ValuationSubring (AlgebraicClosure ℚ)
  hA : A.LiesOverPrime p
  [inst4 : CharP (ResidueField ↥A) p]
  [inst5 : IsAlgClosed (ResidueField ↥A)]
  ρ : R p →+* ↥A
  hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)

  pb : (ZMod (M / p))ˣ
  hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p))
  δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
  hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v

  SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
  hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p

  θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)
  α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)
  hα : α.IsIntegral
  hβ : (θ.toAlgHom.comp α).IsIntegral
  Psp : JHPlaceSpecialization p M H hpM A
  Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ

  hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y
  hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))
  hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ
  hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ

  hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)
  hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)
  e : ↥SS → ℕ
  he : ∀ s, 0 < e s
  An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H)
  hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
  k : ℕ
  hk : ∀ s : ↥SS, e s ∣ k

  gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
  hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _
  hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A
  bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
  hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _
  hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))

  [inst6 : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
  eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H)
  heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a))

  hloc : ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0)

attribute [scoped instance] Frame.inst1 Frame.inst2 Frame.inst3 Frame.inst4 Frame.inst5 Frame.inst6

theorem germ_eq_mul_of_map_eq {X : Scheme.{0}} {U W : X.Opens} (hWU : W ≤ U) (y : ↥X) (hyW : y ∈ W)
    (t c : Γ(X, U)) (t₀ : Γ(X, W)) (ht : X.presheaf.map (homOfLE hWU).op t = X.presheaf.map (homOfLE hWU).op c * t₀) :
    (X.presheaf.germ U y (hWU hyW)).hom t = (X.presheaf.germ U y (hWU hyW)).hom c * (X.presheaf.germ W y hyW).hom t₀ := by
  have e1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWU) y hyW t
  have e2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWU) y hyW c
  change (X.presheaf.germ W y hyW).hom ((X.presheaf.map (homOfLE hWU).op) t) = _ at e1
  change (X.presheaf.germ W y hyW).hom ((X.presheaf.map (homOfLE hWU).op) c) = _ at e2
  rw [← e1, ← e2, ht, map_mul]

namespace Frame

variable (F : Frame)

abbrev XA : Scheme.{0} := pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))

noncomputable abbrev CRpt (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : ↥F.XA :=
  F.bc.base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base n)

def Sinf : Set ↥F.XA := Set.range (F.𝔛.comp F.A F.hA F.ρ F.hρ 0 ≫ F.bc).base
def Szero : Set ↥F.XA := Set.range (F.𝔛.comp F.A F.hA F.ρ F.hρ 1 ≫ F.bc).base
def CR : Set ↥F.XA := Set.range F.CRpt

noncomputable abbrev nodeOf (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : ↥F.SS :=
  ⟨(F.𝔛.placeOn0 F.A F.hA F.ρ F.hρ n, F.𝔛.placeOn1 F.A F.hA F.ρ F.hρ n), (F.hSS _).mpr (F.𝔛.nodePair_mem F.A F.hA F.ρ F.hρ n)⟩

noncomputable def Uloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : F.XA.Opens :=
  (F.hloc (F.nodeOf n) n rfl rfl).choose

theorem CRpt_mem_Uloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : F.CRpt n ∈ F.Uloc n :=
  (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose

theorem nonempty_Uloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ F.Uloc n)) :=
  (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose_spec.choose

noncomputable def tloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : Γ(F.XA, F.Uloc n) :=
  (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose_spec.choose_spec.choose

theorem bc_eq : F.bc = bcMap (ΓM F.M F.H) F.hj F.ρ (IsLocalRing.residue ↥F.A) rfl := by
  apply pullback.hom_ext
  · rw [F.hbc₁, bcMap_fst]
  · rw [F.hbc₂, bcMap_snd]

scoped instance isClosedImmersion_bc : IsClosedImmersion F.bc := by
  rw [F.bc_eq]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hcomp : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A)) ≫ Spec.map (CommRingCat.ofHom F.ρ) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥F.A).comp F.ρ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let e : pullback (pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A))) ≅
      fibre (Γ := ΓM F.M F.H) (hj := F.hj) ((IsLocalRing.residue ↥F.A).comp F.ρ) :=
    pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl hcomp
  have he : bcMap (ΓM F.M F.H) F.hj F.ρ (IsLocalRing.residue ↥F.A) rfl = e.inv ≫ pullback.fst _ _ := by
    rw [Iso.eq_inv_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst]
      simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
    · rw [Category.assoc, bcMap_snd]
      simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd_assoc, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
  rw [he]
  infer_instance

theorem isClosed_Sinf : IsClosed F.Sinf := by
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 0
  exact (F.𝔛.comp F.A F.hA F.ρ F.hρ 0 ≫ F.bc).isClosedEmbedding.isClosed_range

theorem isClosed_Szero : IsClosed F.Szero := by
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 1
  exact (F.𝔛.comp F.A F.hA F.ρ F.hρ 1 ≫ F.bc).isClosedEmbedding.isClosed_range

theorem isClosed_range_bc : IsClosed (Set.range F.bc.base) := F.bc.isClosedEmbedding.isClosed_range

theorem finite_ssPlaces : (ssPlacesQExp (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p).Finite := by
  have hinj : Function.Injective (fun y : ↥(ssPlacesQExp (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p) =>
      (⟨(qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p y.1, y.1), (F.hSS _).mpr (frob_mk_mem_ssNodePairsQExp y.2)⟩ : ↥F.SS)) := by
    intro y y' h
    exact Subtype.ext (congrArg (fun s : ↥F.SS => s.1.2) h)
  haveI : Finite ↥(ssPlacesQExp (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p) := Finite.of_injective _ hinj
  exact Set.toFinite _

scoped instance finite_crossings : Finite ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)) := by
  haveI := F.finite_ssPlaces.to_subtype
  exact Finite.of_equiv _ (F.𝔛.nodeEquiv F.A F.hA F.ρ F.hρ).symm

theorem finite_CR : F.CR.Finite := Set.finite_range _

theorem isClosed_CRpt (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    IsClosed ({F.CRpt n} : Set ↥F.XA) := by
  obtain ⟨-, ⟨hcl, -⟩⟩ := F.𝔛.node_pin F.A F.hA F.ρ F.hρ n

  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 0
  have h1 : IsClosed ({(pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n} : Set _) := by
    have e : (F.𝔛.efib F.A F.hA F.ρ F.hρ).base ((inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base
        ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n)) =
        (pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
    rw [← e, ← Set.image_singleton]
    exact (F.𝔛.efib F.A F.hA F.ρ F.hρ).homeomorph.isClosedMap _ hcl
  have h2 := ((F.𝔛.comp F.A F.hA F.ρ F.hρ 0 ≫ F.bc).isClosedEmbedding.isClosedMap _ h1)
  rw [Set.image_singleton] at h2
  exact h2

theorem isClosed_CR : IsClosed F.CR := by
  rw [CR, Set.range_eq_iUnion]
  exact isClosed_iUnion_of_finite (fun n => F.isClosed_CRpt n)

theorem exists_affine_mem_le (z : ↥F.XA) (O : F.XA.Opens) (hz : z ∈ O) :
    ∃ V : F.XA.affineOpens, z ∈ (V : F.XA.Opens) ∧ (V : F.XA.Opens) ≤ O := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ := F.XA.isBasis_affineOpens.exists_subset_of_mem_open hz O.2
  exact ⟨⟨V, hV⟩, hzV, hle⟩

theorem isClosed_CR_ne (z : ↥F.XA) : IsClosed (⋃ n' : {n' // F.CRpt n' ≠ z}, ({F.CRpt n'.1} : Set ↥F.XA)) :=
  isClosed_iUnion_of_finite (fun n' => F.isClosed_CRpt n'.1)

open Classical in

def Oof (z : ↥F.XA) : F.XA.Opens :=
  if hz : z ∈ F.CR then F.Uloc hz.choose ⊓ ⟨(⋃ n' : {n' // F.CRpt n' ≠ z}, ({F.CRpt n'.1} : Set ↥F.XA))ᶜ, (F.isClosed_CR_ne z).isOpen_compl⟩
  else if z ∈ F.Sinf then ⟨(F.Szero ∪ F.CR)ᶜ, (F.isClosed_Szero.union F.isClosed_CR).isOpen_compl⟩
  else ⟨F.Sinfᶜ, F.isClosed_Sinf.isOpen_compl⟩

theorem mem_CR_of_mem_Sinf_of_mem_Szero (z : ↥F.XA) (h0 : z ∈ F.Sinf) (h1 : z ∈ F.Szero) : z ∈ F.CR := by
  obtain ⟨a, rfl⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have hab : (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base a = (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base b := by
    apply F.bc.isClosedEmbedding.injective
    change (F.𝔛.comp F.A F.hA F.ρ F.hρ 0 ≫ F.bc).base a = (F.𝔛.comp F.A F.hA F.ρ F.hρ 1 ≫ F.bc).base b
    exact hb.symm
  obtain ⟨n, hn, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨n, ?_⟩
  change F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n)) = (F.𝔛.comp F.A F.hA F.ρ F.hρ 0 ≫ F.bc).base a
  rw [hn]
  rfl

open Classical in
theorem mem_Oof (z : ↥F.XA) : z ∈ F.Oof z := by
  unfold Oof
  split_ifs with hz h0
  · refine ⟨?_, ?_⟩
    · have := F.CRpt_mem_Uloc hz.choose
      rwa [hz.choose_spec] at this
    · change z ∈ (⋃ n' : {n' // F.CRpt n' ≠ z}, ({F.CRpt n'.1} : Set ↥F.XA))ᶜ
      rw [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      intro n' h
      exact n'.2 (Set.mem_singleton_iff.mp h).symm
  · change z ∈ (F.Szero ∪ F.CR)ᶜ
    intro h
    rcases h with h1 | h1
    · exact hz (F.mem_CR_of_mem_Sinf_of_mem_Szero z h0 h1)
    · exact hz h1
  · exact h0

def Uof (z : ↥F.XA) : F.XA.affineOpens := (F.exists_affine_mem_le z (F.Oof z) (F.mem_Oof z)).choose

theorem mem_Uof (z : ↥F.XA) : z ∈ (F.Uof z : F.XA.Opens) := (F.exists_affine_mem_le z (F.Oof z) (F.mem_Oof z)).choose_spec.1

theorem Uof_le_Oof (z : ↥F.XA) : (F.Uof z : F.XA.Opens) ≤ F.Oof z := (F.exists_affine_mem_le z (F.Oof z) (F.mem_Oof z)).choose_spec.2

open Classical in
theorem Uof_le_Uloc (z : ↥F.XA) (hz : z ∈ F.CR) : (F.Uof z : F.XA.Opens) ≤ F.Uloc hz.choose := by
  have h := F.Uof_le_Oof z
  unfold Oof at h
  rw [dif_pos hz] at h
  exact h.trans inf_le_left

open Classical in

def gof (z : ↥F.XA) : Γ(F.XA, (F.Uof z : F.XA.Opens)) :=
  if hz : z ∈ F.CR then F.XA.presheaf.map (homOfLE (F.Uof_le_Uloc z hz)).op (F.tloc hz.choose)
  else if z ∈ F.Sinf then ((F.p : ℕ) : Γ(F.XA, (F.Uof z : F.XA.Opens))) ^ F.k
  else 1

theorem iSup_Uof : ⨆ z, (F.Uof z : F.XA.Opens) = ⊤ :=
  top_le_iff.mp fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, F.mem_Uof z⟩

open Classical in
theorem Uof_inf (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∈ F.Sinf) (y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    y ∉ F.Szero ∧ y ∉ F.CR := by
  have h := F.Uof_le_Oof z hy
  unfold Oof at h
  rw [dif_neg hz, if_pos h0] at h
  change y ∈ (F.Szero ∪ F.CR)ᶜ at h
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at h
  exact h

open Classical in
theorem Uof_other (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∉ F.Sinf) (y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    y ∉ F.Sinf := by
  have h := F.Uof_le_Oof z hy
  unfold Oof at h
  rw [dif_neg hz, if_neg h0] at h
  exact h

open Classical in
theorem Uof_crossing_only (z : ↥F.XA) (hz : z ∈ F.CR) (n' : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (hn' : F.CRpt n' ∈ (F.Uof z : F.XA.Opens)) : F.CRpt n' = z := by
  have h := F.Uof_le_Oof z hn'
  unfold Oof at h
  rw [dif_pos hz] at h
  have h2 := h.2
  change F.CRpt n' ∈ (⋃ m : {m // F.CRpt m ≠ z}, ({F.CRpt m.1} : Set ↥F.XA))ᶜ at h2
  by_contra hne
  exact h2 (Set.mem_iUnion.mpr ⟨⟨n', hne⟩, rfl⟩)

open Classical in
theorem gof_crossing (z : ↥F.XA) (hz : z ∈ F.CR) :
    F.gof z = F.XA.presheaf.map (homOfLE (F.Uof_le_Uloc z hz)).op (F.tloc hz.choose) := by
  unfold gof; rw [dif_pos hz]

open Classical in
theorem gof_inf (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∈ F.Sinf) :
    F.gof z = ((F.p : ℕ) : Γ(F.XA, (F.Uof z : F.XA.Opens))) ^ F.k := by
  unfold gof; rw [dif_neg hz, if_pos h0]

open Classical in
theorem gof_other (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∉ F.Sinf) : F.gof z = 1 := by
  unfold gof; rw [dif_neg hz, if_neg h0]

theorem CRpt_choose (z : ↥F.XA) (hz : z ∈ F.CR) : F.CRpt hz.choose = z := hz.choose_spec

abbrev reading (U : F.XA.Opens) [Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U))] (a : Γ(F.XA, U)) : ↥(xHFunctionFieldBar F.M F.H) :=
  F.𝔛.Meta.ffEquiv.symm (F.𝔛.Meta.C.germToFunctionField (F.gA ⁻¹ᵁ U) ((F.gA.app U).hom a))

structure Gaps where
  unit_of_ord_zero : ∀ (U : F.XA.Opens) (x : closedPoints F.𝔛.Meta.C) (hx : F.gA.base x.1 ∈ U) (a : Γ(F.XA, U)),
    (letI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U)) := ⟨⟨x.1, hx⟩⟩; (F.𝔛.Meta.placeOfPoint x).ord (F.reading U a) = 0) →
    (letI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U)) := ⟨⟨x.1, hx⟩⟩; F.reading U a ≠ 0) →
    IsUnit ((F.XA.presheaf.germ U (F.gA.base x.1) hx).hom a)
  gen_or_special : ∀ y : ↥F.XA, y ∈ Set.range F.gA.base ∨ y ∈ Set.range F.bc.base
  exists_closedPoint_notMem : ∀ (T : Finset (Place (ResidueField ↥F.A) (JHNeronObjectAtP.Fbar F.p F.M F.H F.hpM (ResidueField ↥F.A)))),
    ∃ Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ∉ T
  mem_closedPoints_or_eq_genericPoint : ∀ q : ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C, q ∈ closedPoints _ ∨ q = genericPoint _

  gA_genericPoint : F.gA.base (genericPoint F.𝔛.Meta.C) = genericPoint ↥F.XA

  meta_mem_closedPoints_or_eq_genericPoint : ∀ x : ↥F.𝔛.Meta.C, x ∈ closedPoints _ ∨ x = genericPoint _

theorem exists_closedPoint_mem (O : (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C.Opens) [hO : Nonempty (Scheme.Opens.toScheme O)] :
    ∃ Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C, Q.1 ∈ O := by
  haveI : JacobsonSpace ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C := LocallyOfFiniteType.jacobsonSpace (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).toBase
  obtain ⟨⟨q, hq⟩⟩ := hO
  have hcl := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C) O.2.isLocallyClosed
  have hne : ((O : Set ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C) ∩ closedPoints _).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h' : O.carrier ∩ closedPoints ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C = ∅ := h
    rw [h', closure_empty] at hcl
    have : q ∈ closure O.carrier := subset_closure hq
    rw [← hcl] at this
    exact this
  obtain ⟨x, hxO, hxcl⟩ := hne
  exact ⟨⟨x, hxcl⟩, hxO⟩

theorem isUnit_germ_p_of_mem_range_gA (U : F.XA.Opens) (y : ↥F.XA) (hy : y ∈ U) (hgen : y ∈ Set.range F.gA.base) :
    IsUnit ((F.XA.presheaf.germ U y hy).hom ((F.p : ℕ) : Γ(F.XA, U))) := by
  obtain ⟨x, rfl⟩ := hgen
  rw [← isUnit_map_iff (F.gA.stalkMap x).hom, Scheme.Hom.germ_stalkMap_apply, map_natCast]

  have hp : IsUnit ((F.p : ℕ) : Γ(F.𝔛.Meta.C, F.gA ⁻¹ᵁ U)) := by
    have h0 : ((F.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : F.p.Prime).ne_zero
    have := (isUnit_iff_ne_zero.mpr h0).map ((F.𝔛.Meta.toBase.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv.hom)
    rw [map_natCast] at this
    have := this.map (F.𝔛.Meta.C.presheaf.map (homOfLE (le_top : F.gA ⁻¹ᵁ U ≤ ⊤)).op).hom
    rwa [map_natCast] at this
  have h2 := hp.map (F.𝔛.Meta.C.presheaf.germ (F.gA ⁻¹ᵁ U) x hy).hom
  rw [map_natCast] at h2
  rw [map_natCast]
  exact h2

theorem tloc_firstBranch (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hQ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ F.Uloc n)
    (hne : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ≠ F.CRpt n) :
    ∃ (W : F.XA.Opens) (hWU : W ≤ F.Uloc n) (hQW : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ W)
      (t₀ : Γ(F.XA, W)), F.XA.presheaf.map (homOfLE hWU).op (F.tloc n) = ((F.p : ℕ) : Γ(F.XA, W)) ^ F.k * t₀ ∧
        IsUnit ((F.XA.presheaf.germ W _ hQW).hom t₀) := by
  obtain ⟨-, -, hv0, -⟩ := (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose_spec.choose_spec.choose_spec
  exact hv0 Q hQ hne

theorem isUnit_germ_tloc_secondBranch (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hQ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∈ F.Uloc n)
    (hne : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ≠ F.CRpt n) :
    IsUnit ((F.XA.presheaf.germ (F.Uloc n) _ hQ).hom (F.tloc n)) := by
  obtain ⟨-, hv1, -, -⟩ := (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose_spec.choose_spec.choose_spec
  exact hv1 Q hQ hne

theorem ord_reading_tloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (x : closedPoints F.𝔛.Meta.C) (hx : F.gA.base x.1 ∈ F.Uloc n) :
    letI := F.nonempty_Uloc n
    (F.𝔛.Meta.placeOfPoint x).ord (F.reading (F.Uloc n) (F.tloc n)) = 0 := by
  obtain ⟨-, -, -, hhor⟩ := (F.hloc (F.nodeOf n) n rfl rfl).choose_spec.choose_spec.choose_spec.choose_spec
  exact hhor x hx

scoped instance isClosedImmersion_pullback_fst_comp :
    IsClosedImmersion (pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)) := by
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 1
  infer_instance

theorem CRpt_injective : Function.Injective F.CRpt := by
  intro n n' h
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 0
  have h1 := F.bc.isClosedEmbedding.injective h
  have h2 := (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).isClosedEmbedding.injective h1
  exact (pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).isClosedEmbedding.injective h2

theorem choose_eq_of_CRpt (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) (h : F.CRpt n ∈ F.CR) :
    h.choose = n := F.CRpt_injective (h.choose_spec)

def Assoc {y : ↥F.XA} (a b : F.XA.presheaf.stalk y) : Prop := ∃ u : F.XA.presheaf.stalk y, IsUnit u ∧ a = u * b

theorem Assoc.refl {y : ↥F.XA} (a : F.XA.presheaf.stalk y) : F.Assoc a a := ⟨1, isUnit_one, (one_mul a).symm⟩

theorem Assoc.symm {y : ↥F.XA} {a b : F.XA.presheaf.stalk y} (h : F.Assoc a b) : F.Assoc b a := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  exact ⟨v, IsUnit.of_mul_eq_one _ hv, by rw [← mul_assoc, hv, one_mul]⟩

theorem Assoc.trans {y : ↥F.XA} {a b c : F.XA.presheaf.stalk y} (h : F.Assoc a b) (h' : F.Assoc b c) : F.Assoc a c := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨v, hv, rfl⟩ := h'
  exact ⟨u * v, hu.mul hv, by rw [mul_assoc]⟩

theorem Assoc.of_isUnit {y : ↥F.XA} {a b : F.XA.presheaf.stalk y} (ha : IsUnit a) (hb : IsUnit b) : F.Assoc a b := by
  obtain ⟨v, hv⟩ := hb.exists_left_inv
  refine ⟨a * v, ha.mul ?_, by rw [mul_assoc, hv, mul_one]⟩
  exact IsUnit.of_mul_eq_one _ hv

theorem assoc_tloc_firstBranch (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hQ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ F.Uloc n)
    (hne : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ≠ F.CRpt n) :
    F.Assoc ((F.XA.presheaf.germ (F.Uloc n) _ hQ).hom (F.tloc n))
      ((F.XA.presheaf.germ (F.Uloc n) _ hQ).hom (((F.p : ℕ) : Γ(F.XA, F.Uloc n)) ^ F.k)) := by
  obtain ⟨W, hWU, hQW, t₀, ht, hunit⟩ := F.tloc_firstBranch n Q hQ hne
  refine ⟨(F.XA.presheaf.germ W _ hQW).hom t₀, hunit, ?_⟩
  rw [mul_comm]
  apply germ_eq_mul_of_map_eq hWU _ hQW
  rw [map_pow, map_natCast]
  exact ht

theorem assoc_tloc_secondBranch (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hQ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∈ F.Uloc n)
    (hne : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ≠ F.CRpt n) :
    F.Assoc ((F.XA.presheaf.germ (F.Uloc n) _ hQ).hom (F.tloc n)) 1 :=
  Assoc.of_isUnit F (F.isUnit_germ_tloc_secondBranch n Q hQ hne) isUnit_one

abbrev etaBranch (i : Fin 2) : ↥F.XA :=
  F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base (genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C))

theorem etaBranch_specializes (i : Fin 2) (q : ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C) :
    F.etaBranch i ⤳ F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base q) :=
  ((genericPoint_specializes q).map (F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base.hom.continuous).map
    F.bc.base.hom.continuous

theorem genericPoint_not_mem_closedPoints (G : F.Gaps) : genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C ∉ closedPoints _ := by
  intro hη
  obtain ⟨Q, hQ⟩ := G.exists_closedPoint_notMem {(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint ⟨_, hη⟩}
  have hne : Q.1 ≠ genericPoint _ := by
    intro h
    apply hQ
    rw [Finset.mem_singleton]
    congr 1
    exact Subtype.ext h

  have hcl : closure ({genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C} : Set _) = {genericPoint _} :=
    (show IsClosed ({genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C} : Set _) from hη).closure_eq
  have : Q.1 ∈ closure ({genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C} : Set _) := (genericPoint_specializes Q.1).mem_closure
  rw [hcl, Set.mem_singleton_iff] at this
  exact hne this

theorem exists_closedPoint_branch_mem (G : F.Gaps) (i : Fin 2) (O : F.XA.Opens) (hO : F.etaBranch i ∈ O) (z : ↥F.XA) (hz : IsClosed ({z} : Set ↥F.XA))
    (hηz : F.etaBranch i ≠ z) :
    ∃ Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C,
      F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base Q.1) ∈ O ∧
      F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base Q.1) ≠ z := by
  let m := (F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i) ≫ F.bc
  let O' : (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C.Opens := m ⁻¹ᵁ O ⊓ ⟨(m.base ⁻¹' {z})ᶜ, (hz.preimage m.base.hom.continuous).isOpen_compl⟩
  haveI : Nonempty (Scheme.Opens.toScheme O') := ⟨⟨genericPoint _, hO, hηz⟩⟩
  obtain ⟨Q, hQ1, hQ2⟩ := F.exists_closedPoint_mem O'
  exact ⟨Q, hQ1, hQ2⟩

theorem etaBranch_ne_CRpt (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    F.etaBranch 0 ≠ F.CRpt n := by
  intro h
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 0
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have h1 := F.bc.isClosedEmbedding.injective h
  change (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base (genericPoint _)) =
    (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n) at h1
  have h2 := (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).isClosedEmbedding.injective h1
  obtain ⟨-, ⟨hcl, -⟩⟩ := F.𝔛.node_pin F.A F.hA F.ρ F.hρ n
  apply F.genericPoint_not_mem_closedPoints G
  have e : (inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base (genericPoint _)) = genericPoint _ := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  rw [← e, h2]
  exact hcl

theorem etaBranch_one_ne_CRpt (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    F.etaBranch 1 ≠ F.CRpt n := by
  intro h
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 1
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ

  have hc : F.CRpt n = F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n)) := by
    change F.bc.base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base n) =
      F.bc.base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base n)
    rw [pullback.condition]
  rw [hc] at h
  have h1 := F.bc.isClosedEmbedding.injective h
  change (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base (genericPoint _)) =
    (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n) at h1
  have h2 := (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).isClosedEmbedding.injective h1
  obtain ⟨⟨hcl, -⟩, -⟩ := F.𝔛.node_pin F.A F.hA F.ρ F.hρ n
  apply F.genericPoint_not_mem_closedPoints G
  have e : (inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base (genericPoint _)) = genericPoint _ := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  rw [← e, h2]
  exact hcl

theorem isUnit_germ_of_specializes' {U : F.XA.Opens} {x y : ↥F.XA} (h : x ⤳ y) (hy : y ∈ U) (s : Γ(F.XA, U))
    (hu : IsUnit ((F.XA.presheaf.germ U y hy).hom s)) : IsUnit ((F.XA.presheaf.germ U x (h.mem_open U.2 hy)).hom s) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes_apply F.XA.presheaf hy h s
  have := hu.map (F.XA.presheaf.stalkSpecializes h).hom
  rw [e] at this
  exact this

theorem assoc_tloc_etaFirst (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (h : F.etaBranch 0 ∈ F.Uloc n) :
    F.Assoc ((F.XA.presheaf.germ (F.Uloc n) _ h).hom (F.tloc n))
      ((F.XA.presheaf.germ (F.Uloc n) _ h).hom (((F.p : ℕ) : Γ(F.XA, F.Uloc n)) ^ F.k)) := by
  obtain ⟨Q, hQO, hQne⟩ := F.exists_closedPoint_branch_mem G 0 (F.Uloc n) h (F.CRpt n) (F.isClosed_CRpt n) (F.etaBranch_ne_CRpt G n)
  obtain ⟨W, hWU, hQW, t₀, ht, hunit⟩ := F.tloc_firstBranch n Q hQO hQne
  have hηW : F.etaBranch 0 ∈ W := (F.etaBranch_specializes 0 Q.1).mem_open W.2 hQW
  refine ⟨(F.XA.presheaf.germ W _ hηW).hom t₀, F.isUnit_germ_of_specializes' (F.etaBranch_specializes 0 Q.1) hQW t₀ hunit, ?_⟩
  rw [mul_comm]
  apply germ_eq_mul_of_map_eq hWU _ hηW
  rw [map_pow, map_natCast]
  exact ht

theorem assoc_tloc_etaSecond (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (h : F.etaBranch 1 ∈ F.Uloc n) :
    F.Assoc ((F.XA.presheaf.germ (F.Uloc n) _ h).hom (F.tloc n)) 1 := by
  obtain ⟨Q, hQO, hQne⟩ := F.exists_closedPoint_branch_mem G 1 (F.Uloc n) h (F.CRpt n) (F.isClosed_CRpt n) (F.etaBranch_one_ne_CRpt G n)
  have hu := F.isUnit_germ_tloc_secondBranch n Q hQO hQne
  exact Assoc.of_isUnit F (F.isUnit_germ_of_specializes' (F.etaBranch_specializes 1 Q.1) hQO _ hu) isUnit_one

theorem CRpt_eq_second (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    F.CRpt n = F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n)) := by
  change F.bc.base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base n) =
    F.bc.base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base n)
  rw [pullback.condition]

theorem etaBranch_one_mem_Uloc (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) :
    F.etaBranch 1 ∈ F.Uloc n := by
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have hmem := F.CRpt_mem_Uloc n
  rw [F.CRpt_eq_second n] at hmem
  have e : (F.𝔛.efib F.A F.hA F.ρ F.hρ).base ((inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base
      ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n)) =
      (pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hs := F.etaBranch_specializes 1 ((inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n))
  change F.etaBranch 1 ⤳ F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base _)) at hs
  rw [e] at hs
  exact hs.mem_open (F.Uloc n).2 hmem

theorem tloc_ne_zero (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) : F.tloc n ≠ 0 := by
  intro h0
  obtain ⟨u, hu, hEq⟩ := F.assoc_tloc_etaSecond G n (F.etaBranch_one_mem_Uloc n)
  rw [h0, map_zero, mul_one] at hEq
  rw [← hEq] at hu
  exact not_isUnit_zero hu

theorem reading_ne_zero (G : F.Gaps) (U : F.XA.Opens) [Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U))] (a : Γ(F.XA, U)) (ha : a ≠ 0) :
    F.reading U a ≠ 0 := by
  intro h
  have h1 : (F.𝔛.Meta.C.germToFunctionField (F.gA ⁻¹ᵁ U)) ((F.gA.app U).hom a) = 0 := by
    have := congrArg F.𝔛.Meta.ffEquiv h
    simpa using this

  have hmem : genericPoint F.𝔛.Meta.C ∈ F.gA ⁻¹ᵁ U := (‹Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U))›.elim fun x => (genericPoint_specializes x.1).mem_open (F.gA ⁻¹ᵁ U).2 x.2)
  have h2 : (F.𝔛.Meta.C.presheaf.germ (F.gA ⁻¹ᵁ U) (genericPoint _) hmem).hom ((F.gA.app U).hom a) = 0 := h1
  rw [← Scheme.Hom.germ_stalkMap_apply] at h2

  have key : ∀ (y : ↥F.XA) (hy : y = genericPoint ↥F.XA) (hyU : y ∈ U) (φ : F.XA.presheaf.stalk y →+* F.𝔛.Meta.C.functionField),
      φ ((F.XA.presheaf.germ U y hyU).hom a) = 0 → False := by
    rintro y rfl hyU φ hφ
    have hinj : Function.Injective φ := φ.injective
    have : (F.XA.presheaf.germ U (genericPoint ↥F.XA) hyU).hom a = 0 := hinj (by rw [hφ, map_zero])
    exact ha (germ_injective_of_isIntegral _ _ hyU (by rw [this, map_zero]))
  exact key _ G.gA_genericPoint hmem (F.gA.stalkMap (genericPoint _)).hom h2

theorem isUnit_germ_tloc_genericFibre (G : F.Gaps) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
    (x : closedPoints F.𝔛.Meta.C) (hx : F.gA.base x.1 ∈ F.Uloc n) :
    IsUnit ((F.XA.presheaf.germ (F.Uloc n) _ hx).hom (F.tloc n)) := by
  apply G.unit_of_ord_zero (F.Uloc n) x hx (F.tloc n)
  · have := F.ord_reading_tloc n x hx
    convert this using 2
  · haveI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ F.Uloc n)) := ⟨⟨x.1, hx⟩⟩
    have := F.reading_ne_zero G (F.Uloc n) (F.tloc n) (F.tloc_ne_zero G n)
    convert this using 2

theorem isUnit_germ_genericPoint (U : F.XA.Opens) (h : genericPoint ↥F.XA ∈ U) (a : Γ(F.XA, U)) (ha : a ≠ 0) :
    IsUnit ((F.XA.presheaf.germ U (genericPoint ↥F.XA) h).hom a) := by
  rw [isUnit_iff_ne_zero]
  intro h0
  exact ha (germ_injective_of_isIntegral _ _ h (by rw [h0, map_zero]))

theorem CR_subset_Sinf : F.CR ⊆ F.Sinf := by
  rintro _ ⟨n, rfl⟩
  exact ⟨(pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n, rfl⟩

theorem range_bc_subset (y : ↥F.XA) (hy : y ∈ Set.range F.bc.base) : y ∈ F.Sinf ∨ y ∈ F.Szero := by
  obtain ⟨w, rfl⟩ := hy
  rcases F.𝔛.comp_jointly_surjective F.A F.hA F.ρ F.hρ w with ⟨a, ha⟩ | ⟨a, ha⟩
  · left; exact ⟨a, by change F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base a) = _; rw [ha]⟩
  · right; exact ⟨a, by change F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base a) = _; rw [ha]⟩

theorem branch_cases (G : F.Gaps) (i : Fin 2) (y : ↥F.XA) (hy : y ∈ Set.range (F.𝔛.comp F.A F.hA F.ρ F.hρ i ≫ F.bc).base) :
    (∃ Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C, y = F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base Q.1)) ∨
      y = F.etaBranch i := by
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  obtain ⟨q, rfl⟩ := hy
  have e : (F.𝔛.efib F.A F.hA F.ρ F.hρ).base ((inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base q) = q := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rcases G.mem_closedPoints_or_eq_genericPoint ((inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base q) with hcl | hgen
  · left
    refine ⟨⟨_, hcl⟩, ?_⟩
    change F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ i).base q) = F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ i).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base _))
    rw [e]
  · right
    change F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ i).base q) = F.bc.base ((F.𝔛.comp F.A F.hA F.ρ F.hρ i).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base _))
    rw [← hgen, e]

theorem mem_Uloc_of_CRpt_eq (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) (y : ↥F.XA)
    (h : F.CRpt n = y) : y ∈ F.Uloc n := h ▸ F.CRpt_mem_Uloc n

open Classical in

def stdGerm (y : ↥F.XA) : F.XA.presheaf.stalk y :=
  if hC : y ∈ F.CR then (F.XA.presheaf.germ (F.Uloc hC.choose) y (F.mem_Uloc_of_CRpt_eq hC.choose y hC.choose_spec)).hom (F.tloc hC.choose)
  else if y ∈ F.Sinf then ((F.p : ℕ) : F.XA.presheaf.stalk y) ^ F.k
  else 1

open Classical in
theorem stdGerm_inf (y : ↥F.XA) (hC : y ∉ F.CR) (h0 : y ∈ F.Sinf) : F.stdGerm y = ((F.p : ℕ) : F.XA.presheaf.stalk y) ^ F.k := by
  unfold stdGerm; rw [dif_neg hC, if_pos h0]

open Classical in
theorem stdGerm_other (y : ↥F.XA) (hC : y ∉ F.CR) (h0 : y ∉ F.Sinf) : F.stdGerm y = 1 := by
  unfold stdGerm; rw [dif_neg hC, if_neg h0]

theorem germ_res_eq {U V : F.XA.Opens} (h : V ≤ U) (y : ↥F.XA) (hy : y ∈ V) (s : Γ(F.XA, U)) :
    (F.XA.presheaf.germ V y hy).hom ((F.XA.presheaf.map (homOfLE h).op).hom s) = (F.XA.presheaf.germ U y (h hy)).hom s :=
  TopCat.Presheaf.germ_res_apply F.XA.presheaf (homOfLE h) y hy s

theorem assoc_gof_inf (G : F.Gaps) (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∈ F.Sinf) (y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    F.Assoc ((F.XA.presheaf.germ (F.Uof z) y hy).hom (F.gof z)) (F.stdGerm y) := by
  obtain ⟨hy0, hyC⟩ := F.Uof_inf z hz h0 y hy
  rw [F.gof_inf z hz h0, map_pow, map_natCast]
  by_cases hyinf : y ∈ F.Sinf
  · rw [F.stdGerm_inf y hyC hyinf]
    exact Assoc.refl F _
  · rw [F.stdGerm_other y hyC hyinf]
    have hgen : y ∈ Set.range F.gA.base := by
      rcases G.gen_or_special y with h | h
      · exact h
      · rcases F.range_bc_subset y h with h' | h'
        · exact absurd h' hyinf
        · exact absurd h' hy0
    have hu := F.isUnit_germ_p_of_mem_range_gA (F.Uof z) y hy hgen
    rw [map_natCast] at hu
    exact Assoc.of_isUnit F (hu.pow _) isUnit_one

theorem assoc_gof_other (z : ↥F.XA) (hz : z ∉ F.CR) (h0 : z ∉ F.Sinf) (y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    F.Assoc ((F.XA.presheaf.germ (F.Uof z) y hy).hom (F.gof z)) (F.stdGerm y) := by
  have hy0 := F.Uof_other z hz h0 y hy
  have hyC : y ∉ F.CR := fun h => hy0 (F.CR_subset_Sinf h)
  rw [F.gof_other z hz h0, map_one, F.stdGerm_other y hyC hy0]
  exact Assoc.refl F _

open Classical in

theorem assoc_gof_crossing (G : F.Gaps) (z : ↥F.XA) (hz : z ∈ F.CR) (y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    F.Assoc ((F.XA.presheaf.germ (F.Uof z) y hy).hom (F.gof z)) (F.stdGerm y) := by
  have hyU : y ∈ F.Uloc hz.choose := F.Uof_le_Uloc z hz hy
  rw [F.gof_crossing z hz, F.germ_res_eq]
  by_cases hyC : y ∈ F.CR
  ·
    obtain ⟨n', rfl⟩ := hyC
    have hzy : F.CRpt n' = z := F.Uof_crossing_only z hz n' hy
    subst hzy
    unfold stdGerm
    rw [dif_pos ⟨n', rfl⟩]
    exact Assoc.refl F _
  · by_cases hy0 : y ∈ F.Sinf
    · rw [F.stdGerm_inf y hyC hy0]
      rcases F.branch_cases G 0 y hy0 with ⟨Q, hQ⟩ | hgen
      · subst hQ
        have hne : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ≠ F.CRpt hz.choose :=
          fun h => hyC (h ▸ ⟨hz.choose, rfl⟩)
        have := F.assoc_tloc_firstBranch hz.choose Q hyU hne
        rwa [map_pow, map_natCast] at this
      · subst hgen
        have := F.assoc_tloc_etaFirst G hz.choose hyU
        rwa [map_pow, map_natCast] at this
    · rw [F.stdGerm_other y hyC hy0]
      rcases G.gen_or_special y with hgen | hbc
      · obtain ⟨x, hx⟩ := hgen
        subst hx
        rcases G.meta_mem_closedPoints_or_eq_genericPoint x with hcl | hgx
        · exact Assoc.of_isUnit F (F.isUnit_germ_tloc_genericFibre G hz.choose ⟨x, hcl⟩ hyU) isUnit_one
        · have hyeq : F.gA.base x = genericPoint ↥F.XA := by rw [hgx]; exact G.gA_genericPoint
          have key : ∀ (y' : ↥F.XA) (hy' : y' ∈ F.Uloc hz.choose), y' = genericPoint ↥F.XA →
              IsUnit ((F.XA.presheaf.germ (F.Uloc hz.choose) y' hy').hom (F.tloc hz.choose)) := by
            rintro _ hy' rfl
            exact F.isUnit_germ_genericPoint _ hy' _ (F.tloc_ne_zero G hz.choose)
          exact Assoc.of_isUnit F (key _ hyU hyeq) isUnit_one
      · rcases F.range_bc_subset y hbc with h' | h'
        · exact absurd h' hy0
        · rcases F.branch_cases G 1 y h' with ⟨Q, hQ⟩ | hgen
          · subst hQ
            exact F.assoc_tloc_secondBranch hz.choose Q hyU (fun h => hyC (h ▸ ⟨hz.choose, rfl⟩))
          · subst hgen
            exact F.assoc_tloc_etaSecond G hz.choose hyU

open Classical in

theorem assoc_gof_stdGerm (G : F.Gaps) (z y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) :
    F.Assoc ((F.XA.presheaf.germ (F.Uof z) y hy).hom (F.gof z)) (F.stdGerm y) := by
  by_cases hz : z ∈ F.CR
  · exact F.assoc_gof_crossing G z hz y hy
  · by_cases h0 : z ∈ F.Sinf
    · exact F.assoc_gof_inf G z hz h0 y hy
    · exact F.assoc_gof_other z hz h0 y hy

theorem assoc_gof_gof (G : F.Gaps) (z z' y : ↥F.XA) (hy : y ∈ (F.Uof z : F.XA.Opens)) (hy' : y ∈ (F.Uof z' : F.XA.Opens)) :
    F.Assoc ((F.XA.presheaf.germ (F.Uof z) y hy).hom (F.gof z)) ((F.XA.presheaf.germ (F.Uof z') y hy').hom (F.gof z')) :=
  Assoc.trans F (F.assoc_gof_stdGerm G z y hy) (Assoc.symm F (F.assoc_gof_stdGerm G z' y hy'))

theorem isUnit_stdGerm_genericPoint (G : F.Gaps) (hC : genericPoint ↥F.XA ∉ F.CR) : IsUnit (F.stdGerm (genericPoint ↥F.XA)) := by
  classical
  by_cases h0 : genericPoint ↥F.XA ∈ F.Sinf
  · rw [F.stdGerm_inf _ hC h0]
    have hgen : genericPoint ↥F.XA ∈ Set.range F.gA.base := ⟨_, G.gA_genericPoint⟩
    have := F.isUnit_germ_p_of_mem_range_gA ⊤ _ trivial hgen
    rw [map_natCast] at this
    exact this.pow _
  · rw [F.stdGerm_other _ hC h0]
    exact isUnit_one

theorem genericPoint_not_mem_CR (G : F.Gaps) : genericPoint ↥F.XA ∉ F.CR := by
  rintro ⟨n, hn⟩

  have hcl := F.isClosed_CRpt n
  rw [hn] at hcl
  have : F.etaBranch 0 ∈ closure ({genericPoint ↥F.XA} : Set ↥F.XA) := (genericPoint_specializes (F.etaBranch 0)).mem_closure
  rw [hcl.closure_eq, Set.mem_singleton_iff] at this
  exact F.etaBranch_ne_CRpt G n (this.trans hn.symm)

theorem hg_datum (G : F.Gaps) (z : ↥F.XA) (W : F.XA.affineOpens) (h : (W : F.XA.Opens) ≤ F.Uof z) :
    (F.XA.presheaf.map (homOfLE h).op).hom (F.gof z) ∈ nonZeroDivisors Γ(F.XA, W) := by
  by_cases hW : Nonempty (W : F.XA.Opens)
  · haveI := hW
    apply mem_nonZeroDivisors_of_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := hW
    have hη : genericPoint ↥F.XA ∈ (W : F.XA.Opens) := (genericPoint_specializes w).mem_open (W : F.XA.Opens).2 hw
    intro h0
    obtain ⟨u, hu, e⟩ := F.assoc_gof_stdGerm G z (genericPoint ↥F.XA) (h hη)
    have hunit : IsUnit ((F.XA.presheaf.germ (F.Uof z) (genericPoint ↥F.XA) (h hη)).hom (F.gof z)) := by
      rw [e]; exact hu.mul (F.isUnit_stdGerm_genericPoint G (F.genericPoint_not_mem_CR G))
    rw [← F.germ_res_eq h _ hη, h0, map_zero] at hunit
    exact not_isUnit_zero hunit
  · have hbot : (W : F.XA.Opens) = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    have hsub : Subsingleton Γ(F.XA, (W : F.XA.Opens)) := CommRingCat.subsingleton_of_isTerminal (F.XA.sheaf.isTerminalOfEqEmpty hbot)
    rw [hsub.elim ((F.XA.presheaf.map (homOfLE h).op).hom (F.gof z)) 1]
    exact one_mem _

theorem hcomp_datum (G : F.Gaps) (z z' : ↥F.XA) (W : F.XA.affineOpens)
    (hi : (W : F.XA.Opens) ≤ F.Uof z) (hj : (W : F.XA.Opens) ≤ F.Uof z') :
    Ideal.span {(F.XA.presheaf.map (homOfLE hi).op).hom (F.gof z)} = Ideal.span {(F.XA.presheaf.map (homOfLE hj).op).hom (F.gof z')} := by
  have key : ∀ (z z' : ↥F.XA) (hi : (W : F.XA.Opens) ≤ F.Uof z) (hj : (W : F.XA.Opens) ≤ F.Uof z'),
      Ideal.span {(F.XA.presheaf.map (homOfLE hi).op).hom (F.gof z)} ≤ Ideal.span {(F.XA.presheaf.map (homOfLE hj).op).hom (F.gof z')} := by
    intro z z' hi hj
    apply AlgebraicGeometry.Scheme.span_singleton_le_span_singleton_of_forall_germ_eq_mul W
    · intro V hV
      have := F.hg_datum G z' V (hV.trans hj)
      have e : (F.XA.presheaf.map (homOfLE (hV.trans hj)).op).hom (F.gof z') =
          (F.XA.presheaf.map (homOfLE hV).op).hom ((F.XA.presheaf.map (homOfLE hj).op).hom (F.gof z')) := by
        change _ = (F.XA.presheaf.map (homOfLE hj).op ≫ F.XA.presheaf.map (homOfLE hV).op).hom (F.gof z')
        rw [← F.XA.presheaf.map_comp]; rfl
      rwa [e] at this
    · intro x hx
      obtain ⟨u, -, e⟩ := F.assoc_gof_gof G z z' x (hi hx) (hj hx)
      refine ⟨u, ?_⟩
      change (F.XA.presheaf.germ W x hx).hom ((F.XA.presheaf.map (homOfLE hi).op).hom (F.gof z)) =
        u * (F.XA.presheaf.germ W x hx).hom ((F.XA.presheaf.map (homOfLE hj).op).hom (F.gof z'))
      rw [F.germ_res_eq hi x hx, F.germ_res_eq hj x hx]
      exact e
  exact le_antisymm (key z z' hi hj) (key z' z hj hi)

structure D4Out where

  I : F.XA.IdealSheafData
  hI : I.IsInvertible

  ideal_eq : ∀ (z : ↥F.XA) (W : F.XA.affineOpens) (h : (W : F.XA.Opens) ≤ F.Uof z),
    I.ideal W = Ideal.span {(F.XA.presheaf.map (homOfLE h).op).hom (F.gof z)}

  hinv : Scheme.Modules.IsInvertible I.module
  φ : ∀ V : F.XA.Opens, Γ(I.module, V) →+ (F.XA.functionField : Type)
  hnat : ∀ (V V' : F.XA.Opens) (h : V' ≤ V), Nonempty V' → ∀ m : Γ(I.module, V), φ V' (I.module.presheaf.map (homOfLE h).op m) = φ V m
  hsmul : ∀ (V : F.XA.Opens) [Nonempty V] (a : Γ(F.XA, V)) (m : Γ(I.module, V)), φ V (a • m) = algebraMap Γ(F.XA, V) F.XA.functionField a * φ V m
  hinj : ∀ V : F.XA.Opens, Nonempty V → Function.Injective (φ V)
  hframe : ∀ (W : F.XA.affineOpens) (hW : Nonempty (W : F.XA.Opens)) (g : Γ(F.XA, W)), g ∈ nonZeroDivisors Γ(F.XA, W) → I.ideal W = Ideal.span {g} →
    ∃ m : Γ(I.module, (W : F.XA.Opens)), Scheme.Modules.IsFrameOn m W ∧ φ W m = (letI := hW; F.XA.germToFunctionField (W : F.XA.Opens) g)

  hg : ∀ (z : ↥F.XA) (W : F.XA.affineOpens) (h : (W : F.XA.Opens) ≤ F.Uof z),
    (F.XA.presheaf.map (homOfLE h).op).hom (F.gof z) ∈ nonZeroDivisors Γ(F.XA, W)

section D5

variable {F}

omit F in
theorem D5.map_homOfLE_refl {X : Scheme.{0}} {U : X.Opens} (s : Γ(X, U)) : (X.presheaf.map (homOfLE (le_refl U)).op).hom s = s := by
  have : (homOfLE (le_refl U)).op = 𝟙 (Opposite.op U) := rfl
  rw [this, CategoryTheory.Functor.map_id]; rfl

omit F in

theorem D5.ne_zero_of_isFrameOn {X : Scheme.{0}} [IsIntegral X] {M : X.Modules} {U : X.Opens} [hU : Nonempty (Scheme.Opens.toScheme U)]
    {m : Γ(M, U)} (h : Scheme.Modules.IsFrameOn m U) : m ≠ 0 := by
  intro hm
  have hb := (h (le_refl U) le_rfl).1 (a₁ := (1 : Γ(X, U))) (a₂ := (0 : Γ(X, U)))
    (by simp only [hm, map_zero, smul_zero])
  exact one_ne_zero hb

omit F in

theorem D5.ord_algebraMap_eq_zero {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) {a : K} (ha : a ≠ 0) :
    v.ord (algebraMap K L a) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K L a, v.algebraMap_mem' a⟩, ⟨algebraMap K L (a⁻¹), v.algebraMap_mem' (a⁻¹)⟩,
      Subtype.ext (by show algebraMap K L a * algebraMap K L (a⁻¹) = 1; rw [← map_mul, mul_inv_cancel₀ ha, map_one]),
      Subtype.ext (by show algebraMap K L (a⁻¹) * algebraMap K L a = 1; rw [← map_mul, inv_mul_cancel₀ ha, map_one])⟩
  exact v.ord_coe_unit u

variable (F) (D : F.D4Out)

theorem D5.exists_datumFrame (z : ↥F.XA) :
    ∃ m : Γ(D.I.module, (F.Uof z : F.XA.Opens)), Scheme.Modules.IsFrameOn m (F.Uof z) ∧
      D.φ (F.Uof z) m = (letI : Nonempty (Scheme.Opens.toScheme (F.Uof z : F.XA.Opens)) := ⟨⟨z, F.mem_Uof z⟩⟩;
        F.XA.germToFunctionField (F.Uof z : F.XA.Opens) (F.gof z)) := by
  obtain ⟨m, hm, hφ⟩ := D.hframe (F.Uof z) ⟨⟨z, F.mem_Uof z⟩⟩ _ (D.hg z (F.Uof z) le_rfl) (D.ideal_eq z (F.Uof z) le_rfl)
  refine ⟨m, hm, ?_⟩
  rw [hφ, D5.map_homOfLE_refl]

theorem D5.not_mem_CR_comp0 (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hnn : ∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1) :
    F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∉ F.CR := by
  rintro ⟨n, hn⟩
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 0
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ

  have h1 : (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n) =
      (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base Q.1) := F.bc.isClosedEmbedding.injective hn
  have h2 := (F.𝔛.comp F.A F.hA F.ρ F.hρ 0).isClosedEmbedding.injective h1
  obtain ⟨-, ⟨hcl0, hpin0⟩⟩ := F.𝔛.node_pin F.A F.hA F.ρ F.hρ n
  have hQ : Q = ⟨_, hcl0⟩ := by
    apply Subtype.ext
    show Q.1 = (inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base _
    rw [h2, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  apply hnn (F.nodeOf n).1 (F.nodeOf n).2
  show (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q = F.𝔛.placeOn0 F.A F.hA F.ρ F.hρ n
  rw [hQ, hpin0]

theorem D5.not_mem_CR_comp1 (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hnn : ∀ s ∈ F.SS, qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) ≠ s.1) :
    F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∉ F.CR := by
  rintro ⟨n, hn⟩
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ 1
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have hn' : F.bc.base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base n) =
      F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) := by
    rw [← hn]; show _ = F.CRpt n; unfold Frame.CRpt; rw [pullback.condition]
  have h1 : (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((pullback.snd (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)).base n) =
      (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base ((F.𝔛.efib F.A F.hA F.ρ F.hρ).base Q.1) := F.bc.isClosedEmbedding.injective hn'
  have h2 := (F.𝔛.comp F.A F.hA F.ρ F.hρ 1).isClosedEmbedding.injective h1
  obtain ⟨⟨hcl1, hpin1⟩, -⟩ := F.𝔛.node_pin F.A F.hA F.ρ F.hρ n
  have hQ : Q = ⟨_, hcl1⟩ := by
    apply Subtype.ext
    show Q.1 = (inv (F.𝔛.efib F.A F.hA F.ρ F.hρ)).base _
    rw [h2, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  apply hnn (F.nodeOf n).1 (F.nodeOf n).2
  show qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) = F.𝔛.placeOn0 F.A F.hA F.ρ F.hρ n
  rw [hQ, hpin1]

theorem D5.clause_fixed' : (∀ (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C),
          JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ (qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q)) →
          (∀ s ∈ F.SS, qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens) (_ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(D.I.module, U))
            (g : ↥(xHFunctionFieldBar F.M F.H)) (_ : g = F.eK (D.φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar F.M F.H), F.Psp.reduceFst F.α F.hα V = qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) →
              F.Psp.reduceSnd (F.θ.toAlgHom.comp F.α) F.hβ F.δ V = (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q → V.ord g = 0)) := by
  intro Q hfix hnn
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have hzCR := D5.not_mem_CR_comp1 F Q hnn
  have hz0 : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∈ F.Szero := ⟨(F.𝔛.efib F.A F.hA F.ρ F.hρ).base Q.1, rfl⟩
  have hzinf : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∉ F.Sinf :=
    fun h => hzCR (F.mem_CR_of_mem_Sinf_of_mem_Szero _ h hz0)
  obtain ⟨m, hm, hφ⟩ := D5.exists_datumFrame F D (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1))
  rw [F.gof_other _ hzCR hzinf] at hφ
  haveI : Nonempty (Scheme.Opens.toScheme (F.Uof (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1)) : F.XA.Opens)) :=
    ⟨⟨_, F.mem_Uof _⟩⟩
  refine ⟨_, F.mem_Uof _, inferInstance, m, _, rfl, hm, fun V _ _ => ?_⟩
  rw [hφ, map_one, map_one, Place.ord_one]

end D5

section D5b

variable (D : F.D4Out)

theorem D5.clause_fixed : (∀ (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C),
          JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) →
          (∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens) (_ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(D.I.module, U))
            (g : ↥(xHFunctionFieldBar F.M F.H)) (_ : g = F.eK (D.φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar F.M F.H), F.Psp.reduceFst F.α F.hα V = (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ F.Rpd.R₁.integers), F.Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q).ord (F.Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar F.p F.M F.H F.hpM (ResidueField ↥F.A)) = 0)) := by
  intro Q hfix hnn
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have hzCR := D5.not_mem_CR_comp0 F Q hnn
  have hzinf : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ F.Sinf := ⟨(F.𝔛.efib F.A F.hA F.ρ F.hρ).base Q.1, rfl⟩
  obtain ⟨m, hm, hφ⟩ := D5.exists_datumFrame F D (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1))
  rw [F.gof_inf _ hzCR hzinf] at hφ
  haveI : Nonempty (Scheme.Opens.toScheme (F.Uof (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1)) : F.XA.Opens)) :=
    ⟨⟨_, F.mem_Uof _⟩⟩
  have hp0 : ((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : F.p.Prime).ne_zero)

  have hg : F.eK (D.φ _ m) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar F.M F.H) (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k) := by
    rw [hφ, map_pow, map_natCast, map_pow, map_natCast, map_pow, map_natCast]

  have hcg : (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹ • F.eK (D.φ _ m) = 1 := by
    rw [hg, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hc : (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹ • F.eK (D.φ _ m) ∈ F.Rpd.R₁.integers := by rw [hcg]; exact one_mem _
  have e1 : (⟨_, hc⟩ : F.Rpd.R₁.integers) = 1 := Subtype.ext hcg
  refine ⟨_, F.mem_Uof _, inferInstance, m, _, rfl, hm, fun V _ => ?_, (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹, hc, ?_, ?_⟩
  · rw [hg]; exact D5.ord_algebraMap_eq_zero V hp0
  · rw [e1, map_one]; exact one_ne_zero
  · rw [e1, map_one, Place.ord_one]

end D5b

section D5c

variable (D : F.D4Out)

omit F in

theorem D5.exists_isUnit_reading_mul_of_isFrameOn {L : Type*} [Field L]
    {X : Scheme.{0}} [IsIntegral X] (𝓛 : X.Modules)
    (φ : ∀ U : X.Opens, Γ(𝓛, U) →+ (X.functionField : Type))
    (hφres : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m)
    (hφlin : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(𝓛, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (eK : X.functionField ≃+* L) (x₀ : X)
    (U : X.Opens) (hxU : x₀ ∈ U) (m : Γ(𝓛, U)) (g : L) (hg : g = eK (φ U m)) (hmU : Scheme.Modules.IsFrameOn m U)
    (V : X.Opens) (hxV : x₀ ∈ V) (σ : Γ(𝓛, V)) (hσV : Scheme.Modules.IsFrameOn σ V) (f : L) (hf : f = eK (φ V σ)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme (U ⊓ V))) (u : Γ(X, U ⊓ V)), IsUnit u ∧
      f = eK (algebraMap Γ(X, U ⊓ V) X.functionField u) * g := by
  haveI hW : Nonempty (Scheme.Opens.toScheme (U ⊓ V)) := ⟨⟨x₀, show x₀ ∈ U ⊓ V from ⟨hxU, hxV⟩⟩⟩
  obtain ⟨u, hu⟩ := (hmU (inf_le_left : U ⊓ V ≤ U) inf_le_left).2 (𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ)
  obtain ⟨u', hu'⟩ := (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).2 (𝓛.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op m)
  have hunit : IsUnit u := by
    refine isUnit_iff_exists_inv.mpr ⟨u', (hσV (inf_le_right : U ⊓ V ≤ V) inf_le_right).1 ?_⟩
    show (u * u') • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ =
      (1 : Γ(X, U ⊓ V)) • 𝓛.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op σ
    rw [mul_smul, one_smul]
    simp only [] at hu hu'
    rw [hu', hu]
  refine ⟨hW, u, hunit, ?_⟩
  rw [hf, hg, ← map_mul, ← hφres V (U ⊓ V) inf_le_right hW σ, ← hφres U (U ⊓ V) inf_le_left hW m]
  simp only [] at hu
  rw [← hu, hφlin]

theorem D5.gA_not_mem_range_bc (x : ↥F.𝔛.Meta.C) : F.gA.base x ∉ Set.range F.bc.base := by
  rintro ⟨y, hy⟩

  have h1 : (F.bc ≫ pullback.snd _ _).base y = (F.gA ≫ pullback.snd _ _).base x := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
  rw [F.hbc₂, F.hgA₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h1

  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥F.A)).hom := by
    rw [CommRingCat.hom_ofHom]; infer_instance
  have hl : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A))).base
      ((pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥F.A).comp F.ρ)))).base y) =
      IsLocalRing.closedPoint ↥F.A := by
    rw [Subsingleton.elim ((pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥F.A).comp F.ρ)))).base y)
      (IsLocalRing.closedPoint (ResidueField ↥F.A)), Spec_closedPoint]
  have hr : ((barPt F.A).base (F.𝔛.Meta.toBase.base x)).asIdeal = ⊥ := by
    show Ideal.comap (CommRingCat.ofHom F.A.subtype).hom (F.𝔛.Meta.toBase.base x).asIdeal = ⊥
    have : (F.𝔛.Meta.toBase.base x).asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime (AlgebraicClosure ℚ) _ _ (F.𝔛.Meta.toBase.base x).isPrime
    rw [this, CommRingCat.hom_ofHom]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  rw [hl] at h1
  have hmax : IsLocalRing.maximalIdeal ↥F.A = ⊥ := by
    have := congrArg PrimeSpectrum.asIdeal h1
    rw [hr] at this
    exact this

  obtain ⟨hpA, hpmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp F.hA
  rw [hmax, Ideal.mem_bot] at hpmax
  have : ((F.p : ℕ) : AlgebraicClosure ℚ) = 0 := congrArg Subtype.val hpmax
  exact (Fact.out : F.p.Prime).ne_zero (by exact_mod_cast this)

theorem D5.clause_generic : (∀ (x : closedPoints F.𝔛.Meta.C) (U : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens), F.gA.base x.1 ∈ U → ∀ (m : Γ(D.I.module, U)) (g : ↥(xHFunctionFieldBar F.M F.H)), g = F.eK (D.φ U m) →
          Scheme.Modules.IsFrameOn m U → (F.𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          F.Psp.IsStrictFst F.α (F.θ.toAlgHom.comp F.α) F.hα F.hβ F.δ (F.𝔛.Meta.placeOfPoint x) ∨ F.Psp.IsStrictSnd F.α (F.θ.toAlgHom.comp F.α) F.hα F.hβ F.δ (F.𝔛.Meta.placeOfPoint x)) := by
  intro x U hxU m g hg hmU hord
  exfalso
  apply hord

  have hzbc := D5.gA_not_mem_range_bc F x.1
  have hzCR : F.gA.base x.1 ∉ F.CR := fun ⟨n, hn⟩ => hzbc ⟨_, hn⟩
  have hzinf : F.gA.base x.1 ∉ F.Sinf := fun ⟨y, hy⟩ => hzbc ⟨_, hy⟩
  obtain ⟨m₁, hm₁, hφ₁⟩ := D5.exists_datumFrame F D (F.gA.base x.1)
  rw [F.gof_other _ hzCR hzinf, map_one] at hφ₁

  obtain ⟨hne, u, hu, hgu⟩ := D5.exists_isUnit_reading_mul_of_isFrameOn D.I.module D.φ D.hnat D.hsmul F.eK (F.gA.base x.1)
    (F.Uof (F.gA.base x.1)) (F.mem_Uof _) m₁ 1 (by rw [hφ₁, map_one]) hm₁ U hxU m hmU g hg
  rw [mul_one] at hgu

  haveI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ ((F.Uof (F.gA.base x.1) : F.XA.Opens) ⊓ U))) :=
    ⟨⟨x.1, show F.gA.base x.1 ∈ (F.Uof (F.gA.base x.1) : F.XA.Opens) ⊓ U from ⟨F.mem_Uof _, hxU⟩⟩⟩
  rw [hgu]
  erw [F.heK]
  exact CurveModel.ord_placeOfPoint_ffEquiv_symm_germToFunctionField_eq_zero_of_isUnit F.𝔛.Meta
    (F.gA ⁻¹ᵁ ((F.Uof (F.gA.base x.1) : F.XA.Opens) ⊓ U)) x
    (show F.gA.base x.1 ∈ (F.Uof (F.gA.base x.1) : F.XA.Opens) ⊓ U from ⟨F.mem_Uof _, hxU⟩) _ (hu.map _)

end D5c

section D5d

variable (D : F.D4Out)

omit F in

theorem D5.germToFunctionField_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (h : U ≤ V)
    [hU : Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme V)] (t : Γ(X, V)) :
    X.germToFunctionField U ((X.presheaf.map (homOfLE h).op).hom t) = X.germToFunctionField V t :=
  TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) _ _ t

theorem D5.clause_node : (∀ (s : ↥F.SS) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1)))
      (_ : F.𝔛.placeOn0 F.A F.hA F.ρ F.hρ n = s.1.1) (_ : F.𝔛.placeOn1 F.A F.hA F.ρ F.hρ n = s.1.2),
          ∃ (U : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens) (_ : F.bc.base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(D.I.module, U))
            (g : ↥(xHFunctionFieldBar F.M F.H)) (_ : g = F.eK (D.φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (F.An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (F.An s).param) ^ (-((F.k / F.e s : ℕ) : ℤ)) ∈ F.A, IsUnit (⟨_, h⟩ : ↥F.A))) := by
  intro s n hn0 hn1
  have hz : F.CRpt n ∈ F.CR := ⟨n, rfl⟩
  have hch : hz.choose = n := F.choose_eq_of_CRpt n hz
  have hns : F.nodeOf hz.choose = s := by
    rw [hch]
    exact Subtype.ext (Prod.ext hn0 hn1)

  obtain ⟨m, hm, hφ⟩ := D5.exists_datumFrame F D (F.CRpt n)
  rw [F.gof_crossing _ hz] at hφ
  haveI : Nonempty (Scheme.Opens.toScheme (F.Uof (F.CRpt n) : F.XA.Opens)) := ⟨⟨_, F.mem_Uof _⟩⟩
  haveI : Nonempty (Scheme.Opens.toScheme (F.Uloc hz.choose)) := ⟨⟨_, F.CRpt_mem_Uloc _⟩⟩
  haveI := F.nonempty_Uloc hz.choose

  have hgr : F.eK (D.φ _ m) = F.reading (F.Uloc hz.choose) (F.tloc hz.choose) := by
    rw [hφ]
    erw [D5.germToFunctionField_map (F.Uof_le_Uloc (F.CRpt n) hz) (F.tloc hz.choose)]
    exact F.heK (F.Uloc hz.choose) (F.tloc hz.choose)

  have hg0 : F.eK (D.φ _ m) ≠ 0 := by
    intro h
    apply D5.ne_zero_of_isFrameOn hm
    apply D.hinj _ ⟨⟨_, F.mem_Uof _⟩⟩
    rw [map_zero]
    exact (map_eq_zero_iff _ F.eK.injective).mp h
  refine ⟨_, F.mem_Uof _, inferInstance, m, _, rfl, hm, hg0, ?_⟩

  rw [hgr, ← hns]
  exact (F.hloc (F.nodeOf hz.choose) hz.choose rfl rfl).choose_spec.choose_spec.choose_spec.choose_spec.1

end D5d

section D5e

variable (D : F.D4Out)

namespace D5
omit F in

private theorem _root_.TwistAsm.Frame.D5.mem_of_pow_mem {K : Type*} [Field K] (O : ValuationSubring K) {x : K} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ O) : x ∈ O := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact O.zero_mem
  rcases O.mem_or_inv_mem x with hm | hinv
  · exact hm
  have e : x = x ^ n * (x⁻¹) ^ (n - 1) := by
    rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ hx), ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
  rw [e]
  exact mul_mem h (pow_mem hinv _)

end D5
p2m_export "TwistAsm.Frame" "D5.mem_of_pow_mem"
omit F in

theorem D5.qExpFrobeniusPlaceModL_injective (K : Type) [Field K] (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] :
    Function.Injective (qExpFrobeniusPlaceModL K Γ ℓ) := by
  intro w w' h
  apply Place.ext
  ext x
  obtain ⟨y, hy⟩ := exists_qExpFrobeniusModL_eq_pow K Γ ℓ x
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have key : ∀ v : Place K ↥(qExpFunctionFieldC K Γ),
      x ∈ v.toValuationSubring ↔ y ∈ (qExpFrobeniusPlaceModL K Γ ℓ v).toValuationSubring := by
    intro v
    rw [mem_qExpFrobeniusPlaceModL_iff, hy]
    exact ⟨fun hx => pow_mem hx ℓ, fun hx => D5.mem_of_pow_mem _ hℓ hx⟩
  rw [key, key, h]

theorem D5.isClosed_bc_comp (i : Fin 2) (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C) :
    IsClosed ({F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i).base Q.1)} : Set ↥F.XA) := by
  haveI := F.𝔛.comp_isClosedImmersion F.A F.hA F.ρ F.hρ i
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have h := ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ i) ≫ F.bc).isClosedEmbedding.isClosedMap _ Q.2
  rwa [Set.image_singleton] at h

theorem D5.exists_frame_inf (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)
    (hnn : ∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1) :
    ∃ (m : Γ(D.I.module, (F.Uof (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1)) : F.XA.Opens))),
      Scheme.Modules.IsFrameOn m (F.Uof (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1))) ∧
      ∃ hc : (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹ • F.eK (D.φ _ m) ∈ F.Rpd.R₁.integers,
        F.Rpd.R₁.residue ⟨_, hc⟩ ≠ 0 := by
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ
  have hzCR := D5.not_mem_CR_comp0 F Q hnn
  have hzinf : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ F.Sinf := ⟨(F.𝔛.efib F.A F.hA F.ρ F.hρ).base Q.1, rfl⟩
  obtain ⟨m, hm, hφ⟩ := D5.exists_datumFrame F D (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1))
  rw [F.gof_inf _ hzCR hzinf] at hφ
  have hp0 : ((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : F.p.Prime).ne_zero)
  have hg : F.eK (D.φ _ m) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar F.M F.H) (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k) := by
    rw [hφ, map_pow, map_natCast, map_pow, map_natCast, map_pow, map_natCast]
  have hcg : (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹ • F.eK (D.φ _ m) = 1 := by
    rw [hg, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hc : (((F.p : ℕ) : AlgebraicClosure ℚ) ^ F.k)⁻¹ • F.eK (D.φ _ m) ∈ F.Rpd.R₁.integers := by rw [hcg]; exact one_mem _
  refine ⟨m, hm, hc, ?_⟩
  rw [show (⟨_, hc⟩ : F.Rpd.R₁.integers) = 1 from Subtype.ext hcg, map_one]
  exact one_ne_zero

theorem D5.clause_affineBase (G : F.Gaps) : (∃ Uaff : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥F.SS) (n : ↥(pullback (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1))) (_ : F.𝔛.placeOn0 F.A F.hA F.ρ F.hρ n = s.1.1) (_ : F.𝔛.placeOn1 F.A F.hA F.ρ F.hρ n = s.1.2), F.bc.base ((pullback.fst (F.𝔛.comp F.A F.hA F.ρ F.hρ 0) (F.𝔛.comp F.A F.hA F.ρ F.hρ 1) ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C),
            JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) →
          (∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1) → F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C),
            JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ (qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q)) →
          (∀ s ∈ F.SS, qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) ≠ s.1) → F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C) (U : (pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).Opens) (_ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ U) (_ : F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(D.I.module, U)) (g : ↥(xHFunctionFieldBar F.M F.H)) (_ : g = F.eK (D.φ U m)),
              (∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ F.Rpd.R₁.integers), F.Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) := by
  classical
  haveI := F.𝔛.efib_iso F.A F.hA F.ρ F.hρ

  obtain ⟨Q₀, hQ₀⟩ := G.exists_closedPoint_notMem (F.SS.image Prod.fst)
  have hnn₀ : ∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q₀ ≠ s.1 :=
    fun s hs h => hQ₀ (Finset.mem_image.mpr ⟨s, hs, h.symm⟩)

  have hFixFin := ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift F.p F.M F.H F.hpM F.hpM2 F.A F.hA F.pb F.hpb F.δ F.hδ
  have hinjP := (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint_bijective.1
  have hφinjP := D5.qExpFrobeniusPlaceModL_injective (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p

  let T : Set ↥F.XA :=
    ((F.CR ∪
      (fun Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C => F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q.1)) ''
        {Q | JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) ∧
          ∀ s ∈ F.SS, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ≠ s.1}) ∪
      (fun Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C => F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 1).base Q.1)) ''
        {Q | JHPlaceSpecialization.Fixed (p := F.p) (M := F.M) (H := F.H) (hpM := F.hpM) (A := F.A) F.δ
            (qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q)) ∧
          ∀ s ∈ F.SS, qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q) ≠ s.1}) ∪
      {F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q₀.1)}
  have hTfin : T.Finite := by
    refine ((F.finite_CR.union (Set.Finite.image _ ?_)).union (Set.Finite.image _ ?_)).union (Set.finite_singleton _)
    · exact (hFixFin.preimage (fun _ _ _ _ h => hinjP h)).subset fun Q hQ => hQ.1
    · exact (hFixFin.preimage (f := fun Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C =>
          qExpFrobeniusPlaceModL (ResidueField ↥F.A) (ΓN F.p F.M F.H F.hpM) F.p ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q))
        (fun _ _ _ _ h => hinjP (hφinjP h))).subset fun Q hQ => hQ.1
  have hTcl : ∀ t ∈ T, IsClosed ({t} : Set ↥F.XA) := by
    rintro t (((⟨n, rfl⟩ | ⟨Q, -, rfl⟩) | ⟨Q, -, rfl⟩) | ht)
    · exact F.isClosed_CRpt n
    · exact D5.isClosed_bc_comp F 0 Q
    · exact D5.isClosed_bc_comp F 1 Q
    · rw [Set.mem_singleton_iff.mp ht]; exact D5.isClosed_bc_comp F 0 Q₀

  haveI : Infinite (ResidueField ↥F.A) := inferInstance
  obtain ⟨Uaff, hUaff, hTU⟩ := TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
    (jAt (ΓM F.M F.H) F.hj) F.ρ T hTfin hTcl

  obtain ⟨m₀, hm₀, hc₀, hres₀⟩ := D5.exists_frame_inf F D Q₀ hnn₀
  haveI : Nonempty (Scheme.Opens.toScheme (F.Uof (F.bc.base ((F.𝔛.efib F.A F.hA F.ρ F.hρ ≫ F.𝔛.comp F.A F.hA F.ρ F.hρ 0).base Q₀.1)) : F.XA.Opens)) :=
    ⟨⟨_, F.mem_Uof _⟩⟩
  refine ⟨Uaff, hUaff, fun s n _ _ => hTU (Or.inl (Or.inl (Or.inl ⟨n, rfl⟩))),
    fun Q hf hn => hTU (Or.inl (Or.inl (Or.inr ⟨Q, ⟨hf, hn⟩, rfl⟩))),
    fun Q hf hn => hTU (Or.inl (Or.inr ⟨Q, ⟨hf, hn⟩, rfl⟩)),
    Q₀, _, F.mem_Uof _, hTU (Or.inr rfl), inferInstance, m₀, _, rfl, hnn₀, hm₀, _, hc₀, hres₀⟩

end D5e

theorem nonempty_D4Out (G : F.Gaps) : Nonempty F.D4Out := by
  obtain ⟨I, hI, hideal⟩ := AlgebraicGeometry.Scheme.IdealSheafData.exists_isInvertible_ideal_eq_span_of_locallyPrincipalDatum
    F.Uof F.iSup_Uof F.gof (fun z W h => F.hg_datum G z W h) (fun z z' W hi hj => F.hcomp_datum G z z' W hi hj)
  obtain ⟨hinv, φ, hnat, hsmul, hinj, hframe⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isInvertible_module_and_exists_presentation_isFrameOn I hI
  exact ⟨⟨I, hI, hideal, hinv, φ, hnat, (fun V _ a m => hsmul V a m), hinj, hframe, fun z W h => F.hg_datum G z W h⟩⟩

section Gaps1

theorem gaps_IG : IsIntegral F.XA ∧ (∀ W : F.XA.Opens, Nonempty (Scheme.Opens.toScheme W) → Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ W))) ∧
    IsOpenImmersion F.gA :=
  ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
    F.p F.M F.hpM F.H F.A F.hA F.hj F.𝔛 F.ρ F.hρ F.gA F.hgA₁ F.hgA₂

theorem gaps_gA_genericPoint : F.gA.base (genericPoint F.𝔛.Meta.C) = genericPoint ↥F.XA := by
  haveI := F.gaps_IG.2.2
  exact genericPoint_eq_of_isOpenImmersion F.gA

theorem gaps_unit_of_ord_zero (U : F.XA.Opens) (x : closedPoints F.𝔛.Meta.C) (hx : F.gA.base x.1 ∈ U) (a : Γ(F.XA, U))
    (hord : letI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U)) := ⟨⟨x.1, hx⟩⟩; (F.𝔛.Meta.placeOfPoint x).ord (F.reading U a) = 0)
    (hne : letI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U)) := ⟨⟨x.1, hx⟩⟩; F.reading U a ≠ 0) :
    IsUnit ((F.XA.presheaf.germ U (F.gA.base x.1) hx).hom a) := by
  haveI : Nonempty (Scheme.Opens.toScheme (F.gA ⁻¹ᵁ U)) := ⟨⟨x.1, hx⟩⟩

  rw [← isUnit_map_iff (F.gA.stalkMap x.1).hom, Scheme.Hom.germ_stalkMap_apply]

  set ψ : F.𝔛.Meta.C.presheaf.stalk x.1 →+* ↥(xHFunctionFieldBar F.M F.H) :=
    (F.𝔛.Meta.ffEquiv.symm : F.𝔛.Meta.C.functionField ≃+* ↥(xHFunctionFieldBar F.M F.H)).toRingHom.comp
      (algebraMap (F.𝔛.Meta.C.presheaf.stalk x.1) F.𝔛.Meta.C.functionField) with hψ
  have hψinj : Function.Injective ψ :=
    F.𝔛.Meta.ffEquiv.symm.injective.comp (IsFractionRing.injective (F.𝔛.Meta.C.presheaf.stalk x.1) F.𝔛.Meta.C.functionField)
  have hrange := F.𝔛.Meta.range_stalk_eq x

  have hread : ψ ((F.𝔛.Meta.C.presheaf.germ (F.gA ⁻¹ᵁ U) x.1 hx).hom ((F.gA.app U).hom a)) = F.reading U a := by
    show F.𝔛.Meta.ffEquiv.symm (algebraMap _ _ _) = F.𝔛.Meta.ffEquiv.symm _
    congr 1
    show (F.𝔛.Meta.C.presheaf.stalkSpecializes _).hom _ = _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (F.𝔛.Meta.placeOfPoint x).toValuationSubring
  obtain ⟨u, hu⟩ := (F.𝔛.Meta.placeOfPoint x).exists_unit_mul_zpow hne hπ
  rw [hord, zpow_zero, mul_one] at hu

  have hinv : ((↑(u⁻¹) : (F.𝔛.Meta.placeOfPoint x).toValuationSubring) : ↥(xHFunctionFieldBar F.M F.H)) ∈ ψ.range := by
    rw [hrange]; exact (↑(u⁻¹) : (F.𝔛.Meta.placeOfPoint x).toValuationSubring).2
  obtain ⟨t, ht⟩ := hinv
  refine isUnit_iff_exists_inv.mpr ⟨t, hψinj ?_⟩
  rw [map_mul, map_one, hread, ht, hu, ← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]

end Gaps1

section Gaps2

theorem range_bc_eq : Set.range F.bc.base =
    (pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).base ⁻¹' {IsLocalRing.closedPoint ↥F.A} := by
  rw [F.bc_eq]
  have hcomp : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A)) ≫ Spec.map (CommRingCat.ofHom F.ρ) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥F.A).comp F.ρ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let e : pullback (pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥F.A))) ≅
      fibre (Γ := ΓM F.M F.H) (hj := F.hj) ((IsLocalRing.residue ↥F.A).comp F.ρ) :=
    pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl hcomp
  have he : bcMap (ΓM F.M F.H) F.hj F.ρ (IsLocalRing.residue ↥F.A) rfl = e.inv ≫ pullback.fst _ _ := by
    rw [Iso.eq_inv_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst]
      simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
    · rw [Category.assoc, bcMap_snd]
      simp only [e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd_assoc, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
  have hsurj : Function.Surjective e.inv.base := fun z => ⟨e.hom.base z, by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl⟩
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp]
  erw [Scheme.Pullback.range_fst]
  congr 1
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥F.A)).hom := by rw [CommRingCat.hom_ofHom]; infer_instance
  ext z
  simp only [Set.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint (ResidueField ↥F.A))]
    exact Spec_closedPoint
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint _, Spec_closedPoint⟩

theorem range_gA_eq : Set.range F.gA.base =
    {y | ((pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).base y).asIdeal = ⊥} := by
  haveI := F.𝔛.eeta_iso
  let prA : pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom (algebraMap (R F.p) (AlgebraicClosure ℚ)))) ⟶ F.XA :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom F.A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, F.hρ])
  have hgA : F.gA = F.𝔛.eeta ≫ prA := by
    apply pullback.hom_ext
    · rw [F.hgA₁, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [F.hgA₂, Category.assoc, pullback.lift_snd, ← Category.assoc, F.𝔛.heeta]
  have hcomp : Spec.map (CommRingCat.ofHom F.A.subtype) ≫ Spec.map (CommRingCat.ofHom F.ρ) =
      Spec.map (CommRingCat.ofHom (algebraMap (R F.p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, F.hρ]
  let e : pullback (pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))) (Spec.map (CommRingCat.ofHom F.A.subtype)) ≅
      pullback (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom (algebraMap (R F.p) (AlgebraicClosure ℚ)))) :=
    pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl hcomp
  have he : prA = e.inv ≫ pullback.fst _ _ := by
    rw [Iso.eq_inv_comp]
    apply pullback.hom_ext
    · simp only [prA, e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
    · simp only [prA, e, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd_assoc, pullback.lift_snd, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
  have hsurj : Function.Surjective e.inv.base := fun z => ⟨e.hom.base z, by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl⟩
  have hsurj' : Function.Surjective F.𝔛.eeta.base := fun z => ⟨(inv F.𝔛.eeta).base z, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [hgA, he, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj'.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp, hsurj.range_comp]
  erw [Scheme.Pullback.range_fst]
  ext y
  simp only [Set.mem_preimage, Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw]
    show Ideal.comap (CommRingCat.ofHom F.A.subtype).hom w.asIdeal = ⊥
    rw [@Ideal.eq_bot_of_prime (AlgebraicClosure ℚ) _ _ w.isPrime, CommRingCat.hom_ofHom]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective
  · intro hy
    refine ⟨IsLocalRing.closedPoint (AlgebraicClosure ℚ), PrimeSpectrum.ext ?_⟩
    show Ideal.comap (CommRingCat.ofHom F.A.subtype).hom (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).asIdeal = _
    rw [@Ideal.eq_bot_of_prime (AlgebraicClosure ℚ) _ _ (IsLocalRing.closedPoint (AlgebraicClosure ℚ)).isPrime, hy, CommRingCat.hom_ofHom]
    exact Ideal.comap_bot_of_injective _ Subtype.val_injective

theorem gaps_gen_or_special (hrank : ∀ q : PrimeSpectrum ↥F.A, q.asIdeal = ⊥ ∨ q = IsLocalRing.closedPoint ↥F.A) (y : ↥F.XA) :
    y ∈ Set.range F.gA.base ∨ y ∈ Set.range F.bc.base := by
  rcases hrank ((pullback.snd (toBase F.p (ΓM F.M F.H) F.hj) (Spec.map (CommRingCat.ofHom F.ρ))).base y) with h | h
  · left; rw [F.range_gA_eq]; exact h
  · right; rw [F.range_bc_eq]; exact h

end Gaps2

section Gaps3

theorem gaps_exists_pow_mem_span_natCast_of_mem_maximalIdeal (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (m : ↥A) (hm : m ∈ maximalIdeal ↥A) :
    ∃ k : ℕ, m ^ k ∈ Ideal.span {((p : ℕ) : ↥A)} := by
  classical
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(m : AlgebraicClosure ℚ)} with hL
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (m : AlgebraicClosure ℚ)).isIntegral)
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥L (AlgebraicClosure ℚ))) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hp.out hA
  set AL := A.comap (algebraMap ↥L (AlgebraicClosure ℚ)) with hAL
  have hmL : (m : AlgebraicClosure ℚ) ∈ L := IntermediateField.mem_adjoin_simple_self ℚ _
  set mL : ↥AL := ⟨⟨(m : AlgebraicClosure ℚ), hmL⟩, by show algebraMap ↥L (AlgebraicClosure ℚ) ⟨m, hmL⟩ ∈ A; exact m.2⟩ with hmLdef
  set pL : ↥AL := ⟨((p : ℕ) : ↥L), by show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) ∈ A; rw [map_natCast]; exact natCast_mem A p⟩ with hpLdef
  let ι : ↥AL →+* ↥A :=
    { toFun := fun x => ⟨algebraMap ↥L (AlgebraicClosure ℚ) x.1, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hιm : ι mL = m := Subtype.ext rfl
  have hιp : ι pL = ((p : ℕ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) = ((p : ↥A) : AlgebraicClosure ℚ)
    rw [map_natCast]; rfl
  have hp0 : pL ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥AL => ((x.1 : ↥L) : AlgebraicClosure ℚ)) h
    simp only [hpLdef] at this
    exact (Nat.cast_ne_zero.mpr hp.out.ne_zero : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0) (by simpa using this)
  have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    have hc : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
    rw [← hc]
    exact hmem
  have key : ∀ x : ↥AL, ι x ∈ maximalIdeal ↥A → x ∈ maximalIdeal ↥AL := fun x hx => by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map ι)
  have hpnu : pL ∈ maximalIdeal ↥AL := key pL (by rw [hιp]; exact hpA)
  have hmnu : mL ∈ maximalIdeal ↥AL := key mL (by rw [hιm]; exact hm)
  have hrad : mL ∈ (Ideal.span {pL}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJne : J ≠ ⊥ := fun h => hp0 (by
      have : pL ∈ J := hJ (Ideal.subset_span rfl)
      rw [h] at this
      exact (Submodule.mem_bot _).mp this)
    have hJmax : J = maximalIdeal ↥AL := IsLocalRing.eq_maximalIdeal (hJp.isMaximal hJne)
    rw [hJmax]; exact hmnu
  obtain ⟨k, hk⟩ := hrad
  refine ⟨k, ?_⟩
  have := Ideal.mem_map_of_mem ι hk
  rw [Ideal.map_span, Set.image_singleton, hιp, map_pow, hιm] at this
  exact this

theorem gaps_natCast_mem_of_prime_of_ne_bot (p : ℕ) [hp : Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (q : Ideal ↥A) [hq : q.IsPrime] (y : ↥A) (hy : y ∈ q) (hy0 : y ≠ 0) : ((p : ℕ) : ↥A) ∈ q := by
  classical
  set L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {(y : AlgebraicClosure ℚ)} with hL
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : FiniteDimensional ℚ ↥L :=
    IntermediateField.adjoin.finiteDimensional ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : AlgebraicClosure ℚ)).isIntegral)
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥L (AlgebraicClosure ℚ))) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime L A hp.out hA
  set AL := A.comap (algebraMap ↥L (AlgebraicClosure ℚ)) with hAL
  have hyL : (y : AlgebraicClosure ℚ) ∈ L := IntermediateField.mem_adjoin_simple_self ℚ _
  set yL : ↥AL := ⟨⟨(y : AlgebraicClosure ℚ), hyL⟩, by show algebraMap ↥L (AlgebraicClosure ℚ) ⟨y, hyL⟩ ∈ A; exact y.2⟩ with hyLdef
  set pL : ↥AL := ⟨((p : ℕ) : ↥L), by show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) ∈ A; rw [map_natCast]; exact natCast_mem A p⟩ with hpLdef
  let ι : ↥AL →+* ↥A :=
    { toFun := fun x => ⟨algebraMap ↥L (AlgebraicClosure ℚ) x.1, x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hιy : ι yL = y := Subtype.ext rfl
  have hιp : ι pL = ((p : ℕ) : ↥A) := by
    apply Subtype.ext
    show algebraMap ↥L (AlgebraicClosure ℚ) (p : ↥L) = ((p : ↥A) : AlgebraicClosure ℚ)
    rw [map_natCast]; rfl
  have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    obtain ⟨h, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).mp hA
    have hc : (⟨(p : AlgebraicClosure ℚ), h⟩ : ↥A) = ((p : ℕ) : ↥A) := Subtype.ext (by simp)
    rw [← hc]
    exact hmem
  have key : ∀ x : ↥AL, ι x ∈ maximalIdeal ↥A → x ∈ maximalIdeal ↥AL := fun x hx => by
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map ι)
  have hpnu : pL ∈ maximalIdeal ↥AL := key pL (by rw [hιp]; exact hpA)

  have hy0L : yL ≠ 0 := by
    intro h
    apply hy0
    rw [← hιy, h, map_zero]
  have hqL : (q.comap ι) = maximalIdeal ↥AL := by
    refine IsLocalRing.eq_maximalIdeal ((Ideal.comap_isPrime ι q).isMaximal ?_)
    intro h
    have : yL ∈ q.comap ι := by show ι yL ∈ q; rw [hιy]; exact hy
    rw [h] at this
    exact hy0L ((Submodule.mem_bot _).mp this)
  have : pL ∈ q.comap ι := by rw [hqL]; exact hpnu
  rw [← hιp]
  exact this

theorem gaps_prime_eq_bot_or_eq_maximalIdeal (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (q : Ideal ↥A) [hq : q.IsPrime] : q = ⊥ ∨ q = maximalIdeal ↥A := by
  classical
  by_cases h : q = ⊥
  · exact Or.inl h
  right
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hp : ((p : ℕ) : ↥A) ∈ q := gaps_natCast_mem_of_prime_of_ne_bot p A hA q y hy hy0
  refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) fun m hm => ?_
  obtain ⟨k, hk⟩ := gaps_exists_pow_mem_span_natCast_of_mem_maximalIdeal p A hA m hm
  exact hq.mem_of_pow_mem k ((Ideal.span_singleton_le_iff_mem _).mpr hp hk)

theorem gaps_gen_or_special' (y : ↥F.XA) : y ∈ Set.range F.gA.base ∨ y ∈ Set.range F.bc.base := by
  apply F.gaps_gen_or_special
  intro q
  rcases gaps_prime_eq_bot_or_eq_maximalIdeal F.p F.A F.hA q.asIdeal with h | h
  · exact Or.inl h
  · exact Or.inr (PrimeSpectrum.ext h)

theorem gaps_mem_closedPoints_or_eq_genericPoint {k : Type} [Field k] {L : Type} [Field L] [Algebra k L]
    (Mc : CurveModel k L) (x : ↥Mc.C) : x ∈ closedPoints ↥Mc.C ∨ x = genericPoint ↥Mc.C := by
  have h := (CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap k Mc.toBase Mc (𝟙 _)
    (Category.id_comp _) (by rw [Scheme.Hom.stalkMap_id]; exact IsIso.id _)).2 x
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem gaps_exists_closedPoint_notMem (T : Finset (Place (ResidueField ↥F.A) (JHNeronObjectAtP.Fbar F.p F.M F.H F.hpM (ResidueField ↥F.A)))) :
    ∃ Q : closedPoints (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C, (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint Q ∉ T := by
  by_contra h
  push Not at h
  have hinf := AlgebraicCurve.infinite_setOf_isClosed_singleton (F.𝔛.Mfib F.A F.hA F.ρ F.hρ).toBase
  have hinj : Function.Injective (fun Q : ↥{x : ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C | IsClosed ({x} : Set ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)} =>
      (⟨(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint ⟨Q.1, Q.2⟩, h ⟨Q.1, Q.2⟩⟩ : ↥T)) :=
    fun Q Q' e => Subtype.ext (congrArg Subtype.val ((F.𝔛.Mfib F.A F.hA F.ρ F.hρ).placeOfPoint_bijective.1 (congrArg Subtype.val e)))
  haveI : Finite ↥{x : ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C | IsClosed ({x} : Set ↥(F.𝔛.Mfib F.A F.hA F.ρ F.hρ).C)} := Finite.of_injective _ hinj
  exact hinf (Set.toFinite _)

end Gaps3

noncomputable def gapsOf : F.Gaps where
  unit_of_ord_zero := F.gaps_unit_of_ord_zero
  gen_or_special := F.gaps_gen_or_special'
  exists_closedPoint_notMem := F.gaps_exists_closedPoint_notMem
  mem_closedPoints_or_eq_genericPoint := gaps_mem_closedPoints_or_eq_genericPoint (F.𝔛.Mfib F.A F.hA F.ρ F.hρ)
  gA_genericPoint := F.gaps_gA_genericPoint
  meta_mem_closedPoints_or_eq_genericPoint := gaps_mem_closedPoints_or_eq_genericPoint F.𝔛.Meta

end Frame
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.TwistAsm.Frame"

end TwistAsm
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.TwistAsm.Frame P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.TwistAsm"

open TwistAsm in

theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))

    (hloc : ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0))
    (G : TwistAsm.Frame.Gaps (TwistAsm.Frame.mk p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK hloc)) :
    ∃ (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible 𝓛)
        (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type)),

        (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
        (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) ∧

        (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)) ∧

        (∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2), bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
              (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens), gA.base x.1 ∈ U → ∀ (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)), g = eK (φ U m) →
          Scheme.Modules.IsFrameOn m U → (𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x)) := by
  let F : TwistAsm.Frame := TwistAsm.Frame.mk p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK hloc
  obtain ⟨D⟩ := F.nonempty_D4Out G
  exact ⟨D.I.module, D.hinv, D.φ, D.hnat, D.hsmul, D.hinj, TwistAsm.Frame.D5.clause_node F D, TwistAsm.Frame.D5.clause_fixed F D,
    TwistAsm.Frame.D5.clause_fixed' F D, TwistAsm.Frame.D5.clause_affineBase F D G, TwistAsm.Frame.D5.clause_generic F D⟩

open TwistAsm in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hAn : ∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))))
    (k : ℕ) (hk : ∀ s : ↥SS, e s ∣ k)

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))

    [IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]
    (eK : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(xHFunctionFieldBar M H))
    (heK : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))] [Nonempty (Scheme.Opens.toScheme U)] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),
      eK ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) = 𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a)))

    (hloc : ∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
      ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U)
        (_ : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (t : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)),

        (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0 ∧
            ∃ h : P.evalAt (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) → IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ U _ hQ).hom t)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (hQ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U),
          bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ≠ bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) →
          ∃ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hWU : W ≤ U) (hQW : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ W) (t₀ : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)),
            (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.map (homOfLE hWU).op t = ((p : ℕ) : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), W)) ^ k * t₀ ∧
            IsUnit (((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).presheaf.germ W _ hQW).hom t₀)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C), gA.base x.1 ∈ U → (𝔛.Meta.placeOfPoint x).ord (𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom t))) = 0))
    :
    ∃ (𝓛 : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible 𝓛)
        (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ(𝓛, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type)),

        (∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(𝓛, U), φ V (𝓛.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U)) (m : Γ(𝓛, U)),
          φ U (a • m) = algebraMap Γ(pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m) ∧
        (∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U)) ∧

        (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
      (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2),
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧ g ≠ 0 ∧ (∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord (g) = 0 ∧
            ∃ h : P.evalAt (g) * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0) ∧
            (∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0 ∧
              ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q).ord (Rpd.R₁.residue ⟨c • g, hc⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0)) ∧

        (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
          JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) →
          ∃ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ U) (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U))
            (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
            Scheme.Modules.IsFrameOn m U ∧
            (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
              Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q → V.ord g = 0)) ∧

        (∃ Uaff : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, IsAffineOpen Uaff ∧
          (∀ (s : ↥SS) (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) (_ : 𝔛.placeOn0 A hA ρ hρ n = s.1.1) (_ : 𝔛.placeOn1 A hA ρ hρ n = s.1.2), bc.base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) →
          (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff) ∧
          (∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C),
            JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q)) →
          (∀ s ∈ SS, qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q) ≠ s.1) → bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base Q.1) ∈ Uaff) ∧
          (∃ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ U) (_ : bc.base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Q.1) ∈ Uaff)
            (_ : Nonempty (Scheme.Opens.toScheme U)) (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)) (_ : g = eK (φ U m)),
              (∀ s ∈ SS, (𝔛.Mfib A hA ρ hρ).placeOfPoint Q ≠ s.1) ∧ Scheme.Modules.IsFrameOn m U ∧
              ∃ (c : AlgebraicClosure ℚ) (hc : c • g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨c • g, hc⟩ ≠ 0)) ∧

        (∀ (x : closedPoints 𝔛.Meta.C) (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens), gA.base x.1 ∈ U → ∀ (m : Γ(𝓛, U)) (g : ↥(xHFunctionFieldBar M H)), g = eK (φ U m) →
          Scheme.Modules.IsFrameOn m U → (𝔛.Meta.placeOfPoint x).ord g ≠ 0 →
          Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ (𝔛.Meta.placeOfPoint x)) :=
  main p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK hloc (TwistAsm.Frame.gapsOf (TwistAsm.Frame.mk p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' e he An hAn k hk gA hgA₁ hgA₂ bc hbc₁ hbc₂ eK heK hloc))

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.TwistAsm.Frame P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width.TwistAsm"

end S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_isInvertible_presentation_frames_slopeLaw_fixed_base_strict_of_dvd_width (solution)
