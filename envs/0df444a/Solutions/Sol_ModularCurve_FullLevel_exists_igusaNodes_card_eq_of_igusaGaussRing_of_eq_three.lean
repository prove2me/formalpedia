-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/261897d3-5246-5151-a980-15dcd926306e

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_IgusaFunctionField
import Theorems.Thm_ModularCurve_FullLevel_xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_algEquiv_residue_eq_of_integers_eq
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff
import Theorems.Thm_ModularCurve_FullLevel_existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IgNodes

open scoped ArithmeticFunction.sigma

theorem isIntegral_inclusion_of_relfinrank_pos {κ Ω : Type*} [Field κ] [Field Ω] [Algebra κ Ω]
    {K₀ E : IntermediateField κ Ω} (hle : K₀ ≤ E) (hrel : 0 < IntermediateField.relfinrank K₀ E) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  have hfin : Module.Finite ↥K₀ ↥(IntermediateField.extendScalars hle) := by
    apply Module.finite_of_finrank_pos
    rwa [← IntermediateField.relfinrank_eq_finrank_of_le hle]
  haveI := hfin
  haveI : Algebra.IsIntegral ↥K₀ ↥(IntermediateField.extendScalars hle) := Algebra.IsIntegral.of_finite _ _
  intro x
  have hx : IsIntegral ↥K₀ (⟨(x : Ω), x.2⟩ : ↥(IntermediateField.extendScalars hle)) :=
    Algebra.IsIntegral.isIntegral _
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p, hp, ?_⟩
  apply Subtype.val_injective
  have e1 := congrArg Subtype.val hpx
  change ((IntermediateField.extendScalars hle).val.toRingHom)
      (Polynomial.eval₂ (algebraMap ↥K₀ ↥(IntermediateField.extendScalars hle)) ⟨(x : Ω), x.2⟩ p) = 0 at e1
  change (E.val.toRingHom) (Polynomial.eval₂ (IntermediateField.inclusion hle).toRingHom x p) = 0
  rw [Polynomial.hom_eval₂] at e1 ⊢
  exact e1

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_le_isIntegral (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
      (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  have heq := ModularCurve.FullLevel.xHFunctionFieldC_levelH_eq_modularFunctionFieldC_of_eq_three q hq3 M' hqM' A hA
  have hle : modularFunctionFieldC (ResidueField A) M' ≤ xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M') :=
    heq.symm.le
  refine ⟨hle, RingHom.isIntegral_of_surjective _ ?_⟩
  intro x
  exact ⟨⟨(x : LaurentSeries (ResidueField A)), heq ▸ x.2⟩, Subtype.ext rfl⟩

end IgNodes

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))
    :
    ∃ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) := by
  classical

  obtain ⟨R', hR'O, hR'res⟩ :=
    ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_coe_residue_eq_coe_residue_of_eq_three
      q hq3 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O

  have hRR' : ∀ f : fieldBar q M', f ∈ R'.integers ↔ f ∈ R.integers := by
    intro f; rw [hR'O, hR]
  obtain ⟨τ, hτ⟩ := AlgebraicCurve.RegularProlongation.exists_algEquiv_residue_eq_of_integers_eq R' R hRR'

  obtain ⟨hleC, hint⟩ := IgNodes.exists_le_isIntegral q hq3 M' hqM' A hA
  set j₀ : ↥(modularFunctionFieldC (ResidueField A) M') →ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := IntermediateField.inclusion hleC with hj₀
  set jA : ↥(modularFunctionFieldC (ResidueField A) M') →ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := τ.toAlgHom.comp j₀ with hjA
  have hjA_int : jA.toRingHom.IsIntegral := by
    have h1 : (τ : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))).toRingHom.IsIntegral :=
      RingHom.isIntegral_of_surjective _ τ.surjective
    have : jA.toRingHom = (τ : ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) →ₐ[ResidueField A] ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))).toRingHom.comp j₀.toRingHom := by
      rw [hjA]; rfl
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hint h1

  have hcompat : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
        R.residue ⟨_, hC⟩ = jA.toRingHom (R₀.residue ⟨f, hf⟩) := by
    intro f hf
    obtain ⟨hC', hres'⟩ := hR'res f hf
    refine ⟨(hRR' _).mp hC', ?_⟩
    rw [← hτ _ hC']
    show τ (R'.residue ⟨_, hC'⟩) = τ (j₀ (R₀.residue ⟨f, hf⟩))
    congr 1
    apply Subtype.ext

    rw [hj₀]
    exact hres'

  obtain ⟨hPT1, hPT2, hPT3⟩ := AlgebraicCurve.Place.restrictAlong_congrEquiv_and_existsUnique_iff
    j₀ hint jA hjA_int τ.toRingEquiv (fun a => by simpa using τ.commutes a) (fun x => rfl)
  have huniq : ∀ s : ↥W, ∃! Q : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q.restrictAlong jA hjA_int = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) := by
    intro s
    have hs : (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∈ ssPlaces q M' (ResidueField A) := (hW _).mp s.2
    exact (hPT3 _).mp
      (ModularCurve.FullLevel.existsUnique_place_restrictAlong_eq_of_mem_ssPlaces_of_eq_three q hq3 M' hqM' A hA hleC hint _ hs)

  have hbridge : ∀ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (Q : Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
      Q.restrictAlong jA hjA_int = s ↔
        ∀ g : modularFunctionFieldC (ResidueField A) M', g ∈ s.toValuationSubring ↔ jA.toRingHom g ∈ Q.toValuationSubring := by
    intro s Q
    constructor
    · rintro rfl g
      exact Iff.rfl
    · intro h
      apply AlgebraicCurve.Place.ext
      ext g
      exact (h g).symm
  let node : ↥W → Place (ResidueField A) ↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) := fun s => (huniq s).choose
  have hnode : ∀ s : ↥W, (node s).restrictAlong jA hjA_int = s := fun s => (huniq s).choose_spec.1
  have hnode_inj : Function.Injective node := by
    intro s s' h
    apply Subtype.ext
    rw [← hnode s, ← hnode s', h]
  refine ⟨Finset.univ.image node, ?_, ⟨jA.toRingHom, hcompat, ?_⟩⟩
  · rw [Finset.card_image_of_injective _ hnode_inj, Finset.card_univ, Fintype.card_coe]
  · intro Q
    rw [Finset.mem_image]
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨s, (hbridge _ _).mp (hnode s)⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, Finset.mem_univ _, ?_⟩
      exact ((huniq s).unique (hnode s) ((hbridge _ _).mpr hs)).symm ▸ rfl

end S_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_igusaNodes_card_eq_of_igusaGaussRing_of_eq_three (solution)
