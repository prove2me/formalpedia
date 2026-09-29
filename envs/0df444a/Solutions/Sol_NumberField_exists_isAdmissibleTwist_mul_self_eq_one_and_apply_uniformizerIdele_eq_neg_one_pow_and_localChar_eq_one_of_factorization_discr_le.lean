-- Prove2me | solution 1 for NumberField.exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9d110e0b-a306-5c16-b5d2-542c0e091920

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank
import Theorems.Thm_NumberField_discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Theorems.Thm_LanglandsTunnell_Converse_isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar
import Theorems.Thm_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
import Theorems.Thm_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
import Theorems.Thm_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex"
p2m_attr_erase "instance" "ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add ArtinL.Abelian.coeff_zero IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

noncomputable section

namespace C5Sign

private theorem isAdmissibleTwist_one (E : Type) [Field E] [NumberField E] :
    IsAdmissibleTwist E (1 : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) := by
  refine ⟨fun u => rfl, continuous_const, fun x => ?_⟩
  simp

private theorem isAdmissibleTwist_of_isFiniteOrderHeckeChar (E : Type) [Field E] [NumberField E]
    (ψ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hψ : HeckeCharacter.IsFiniteOrderHeckeChar E ψ) :
    IsAdmissibleTwist E ψ := by
  have h := LanglandsTunnell.Converse.isAdmissibleTwist_mul_comp_idelicNorm_of_isFiniteOrderHeckeChar E E ψ hψ 1
    (isAdmissibleTwist_one E)
  have e : ψ * (1 : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ).comp (M4aHerbrand.GenuineDescent.genuineBaseChange E E).idelicNorm = ψ := by
    ext x
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.one_apply, mul_one]
  rw [e] at h
  exact h

private theorem isUnramifiedCharAt_and_apply_eq_of_eulerCoeff_ne_zero (E : Type) [Field E] [NumberField E]
    (ψ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E))
    (h : LanglandsTunnell.CubicLambda.eulerCoeff E ψ v ≠ 0) :
    IsUnramifiedCharAt ψ v ∧
      ((ψ (uniformizerIdele E v) : ℂˣ) : ℂ) = LanglandsTunnell.CubicLambda.eulerCoeff E ψ v := by
  classical
  unfold LanglandsTunnell.CubicLambda.eulerCoeff at h ⊢
  by_cases hu : IsUnramifiedCharAt ψ v
  · exact ⟨hu, by rw [if_pos hu]⟩
  · exact absurd (if_neg hu) h

private theorem mul_self_eq_one_of_sq_eq_one {G : Type*} [Group G] (ω : G →* ℂˣ) (h : ω ^ 2 = 1)
    (x : G) : ω x * ω x = 1 := by
  have := congrArg (fun f : G →* ℂˣ => f x) h
  simpa [pow_two] using this

section Galois

variable (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]

omit [IsGalois E L] in

private theorem exists_under_eq (v : HeightOneSpectrum (𝓞 E)) :
    ∃ Q : HeightOneSpectrum (𝓞 L), Q.under (𝓞 E) = v := by
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQm (RingOfIntegers.not_isField L)
  refine ⟨⟨Q, hQm.isPrime, hQ0⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hQo.over.symm

private theorem exists_isArithFrobAt (Q : HeightOneSpectrum (𝓞 L)) :
    ∃ σ : L ≃ₐ[E] L, IsArithFrobAt (𝓞 E) σ Q.asIdeal :=
  ⟨arithFrobAt (𝓞 E) (L ≃ₐ[E] L) Q.asIdeal, IsArithFrobAt.arithFrobAt (𝓞 E) (L ≃ₐ[E] L) Q.asIdeal⟩

private theorem ramificationIdx_eq_one_of_intermediateField (F : IntermediateField E L)
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 := by

  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) w.asIdeal
  haveI := hQo
  haveI : Q.IsPrime := hQm.isPrime
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩
  haveI : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q w.asIdeal v.asIdeal

  have hQv : v.asIdeal.ramificationIdx' Q = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal Q v.ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[E] L)]
    exact hv
  have h1 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 L))).not.mpr w.ne_bot
  have h2 : Ideal.map (algebraMap (𝓞 E) (𝓞 L)) v.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L))).not.mpr v.ne_bot
  have h3 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal ≤ Q :=
    Ideal.map_le_of_le_comap (le_of_eq hQo.over)
  have htower := Ideal.ramificationIdx_algebra_tower (p := v.asIdeal) (P := w.asIdeal) (Q := Q) h1 h2 h3
  rw [hQv] at htower
  exact (Nat.eq_one_of_mul_eq_one_right htower.symm)

private theorem isGalois_fixedField (N : Subgroup (L ≃ₐ[E] L)) [N.Normal] :
    IsGalois E (IntermediateField.fixedField N) :=
  IsGalois.of_fixedField_normal_subgroup N

end Galois

section Core

variable (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
  (K : Type) [Field K] [NumberField K] [Algebra K L] [IsScalarTower ℚ K L]

open scoped Classical in
private theorem core :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧ (∀ x, ω x * ω x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 →
        IsUnramifiedCharAt ω v ∧
          ((ω (uniformizerIdele ℚ v) : ℂˣ) : ℂ) =
            (-1) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v))) ∧
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ), 1 ≤ m →
        (discr K).natAbs.factorization (Ideal.absNorm v.asIdeal) ≤ m →
          ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v m, localChar ω v u = 1 := by

  obtain ⟨hF2, hbridge⟩ :=
    NumberField.finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt ℚ L K
  set H : Subgroup (L ≃ₐ[ℚ] L) := (IsScalarTower.toAlgHom ℚ K L).fieldRange.fixingSubgroup with hH
  set ε : (L ≃ₐ[ℚ] L) →* ℤˣ :=
    (Equiv.Perm.sign : Equiv.Perm ((L ≃ₐ[ℚ] L) ⧸ H) →* ℤˣ).comp
      (MulAction.toPermHom (L ≃ₐ[ℚ] L) ((L ≃ₐ[ℚ] L) ⧸ H)) with hε
  set F : IntermediateField ℚ L := IntermediateField.fixedField ε.ker with hFdef

  have hsign : ∀ v : HeightOneSpectrum (𝓞 ℚ), Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 →
      ∃ (Q : HeightOneSpectrum (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.under (𝓞 ℚ) = v ∧ IsArithFrobAt (𝓞 ℚ) σ Q.asIdeal ∧
        ((ε σ : ℤˣ) : ℤ) = (-1) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v)) := by
    intro v hv
    obtain ⟨Q, hQ⟩ := exists_under_eq ℚ L v
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt ℚ L Q
    refine ⟨Q, σ, hQ, hσ, Eq.trans ?_
      (NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt ℚ L K v hv Q hQ
        σ hσ)⟩
    rfl
  by_cases htriv : ∀ σ : L ≃ₐ[ℚ] L, ε σ = 1
  ·
    refine ⟨1, isAdmissibleTwist_one ℚ, fun x => by simp, fun v hv => ⟨fun t _ _ => rfl, ?_⟩, fun v m _ _ u _ => rfl⟩
    obtain ⟨Q, σ, hQ, hσ, hval⟩ := hsign v hv
    rw [htriv σ, Units.val_one] at hval
    have h1 : ((-1 : ℂ) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v))) = 1 := by
      exact_mod_cast hval.symm
    rw [h1]
    rfl
  ·
    push Not at htriv
    obtain ⟨σ₀, hσ₀⟩ := htriv

    have hidx : Module.finrank ℚ F = ε.ker.index := by
      have h1 : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ F L
      have h2 : Module.finrank F L = Nat.card ε.ker := IntermediateField.finrank_fixedField_eq_card ε.ker
      have h3 : Nat.card (L ≃ₐ[ℚ] L) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
      have h4 : ε.ker.index * Nat.card ε.ker = Nat.card (L ≃ₐ[ℚ] L) := Subgroup.index_mul_card ε.ker
      have hpos : 0 < Nat.card ε.ker := Nat.card_pos
      have : Module.finrank ℚ F * Nat.card ε.ker = ε.ker.index * Nat.card ε.ker := by
        rw [← h2, h1, ← h3, ← h4, h2]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    have hne1 : ε.ker.index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one, MonoidHom.ker_eq_top_iff] at h
      exact hσ₀ (by rw [h]; rfl)
    have hF : Module.finrank ℚ F = 2 := by
      have hle : Module.finrank ℚ F ≤ 2 := hF2
      have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
      rw [hidx] at hle hpos ⊢
      omega
    haveI : IsGalois ℚ F := isGalois_fixedField ℚ L ε.ker
    have hprime : (Module.finrank ℚ F).Prime := by rw [hF]; exact Nat.prime_two
    obtain ⟨ψ, hψfin, hψ2, hψeuler, hψloc⟩ :=
      LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_localChar_eq_one_of_factorization_discr_le_of_isGalois_rat_of_prime_finrank
        F hprime
    rw [hF] at hψ2

    have hdvd : discr F ∣ discr K :=
      NumberField.discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr L K
    have hfac : ∀ p : ℕ, (discr F).natAbs.factorization p ≤ (discr K).natAbs.factorization p := by
      have h := (Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F))
        (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))).mpr (Int.natAbs_dvd_natAbs.mpr hdvd)
      exact fun p => h p
    refine ⟨ψ, isAdmissibleTwist_of_isFiniteOrderHeckeChar ℚ ψ hψfin, mul_self_eq_one_of_sq_eq_one ψ hψ2,
      fun v hv => ?_, fun v m hm hd u hu => hψloc v m hm ((hfac _).trans hd) u hu⟩
    obtain ⟨Q, σ, hQ, hσ, hval⟩ := hsign v hv
    obtain ⟨w, hw⟩ := exists_under_eq ℚ F v
    have he : v.asIdeal.ramificationIdx' w.asIdeal = 1 := ramificationIdx_eq_one_of_intermediateField ℚ L F v hv w hw
    have hroot := (hψeuler v w hw).1 he
    have hwmem : w ∈ primeFibre ℚ F v := hw
    obtain ⟨hb1, hb2⟩ := hbridge v hv Q hQ σ hσ w hwmem

    have hc : LanglandsTunnell.CubicLambda.eulerCoeff ℚ ψ v =
        (-1) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v)) := by
      rcases Int.units_eq_one_or (ε σ) with h1 | h1
      · have hf : v.asIdeal.inertiaDeg' w.asIdeal = 1 := hb1.mpr h1
        have hroot1 : IsPrimitiveRoot (LanglandsTunnell.CubicLambda.eulerCoeff ℚ ψ v) 1 := by
          convert hroot using 1
          exact hf.symm
        rw [IsPrimitiveRoot.one_right_iff] at hroot1
        rw [h1, Units.val_one] at hval
        rw [hroot1]
        exact_mod_cast hval
      · have hf : v.asIdeal.inertiaDeg' w.asIdeal = 2 := hb2.mpr h1
        have hroot2 : IsPrimitiveRoot (LanglandsTunnell.CubicLambda.eulerCoeff ℚ ψ v) 2 := by
          convert hroot using 1
          exact hf.symm
        rw [h1, Units.val_neg, Units.val_one] at hval
        rw [hroot2.eq_neg_one_of_two_right]
        exact_mod_cast hval
    have hc0 : LanglandsTunnell.CubicLambda.eulerCoeff ℚ ψ v ≠ 0 := by
      rw [hc]
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    obtain ⟨hunr, hψv⟩ := isUnramifiedCharAt_and_apply_eq_of_eulerCoeff_ne_zero ℚ ψ v hc0
    exact ⟨hunr, hψv.trans hc⟩

end Core

private theorem exists_galoisClosure (K : Type) [Field K] [NumberField K] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsScalarTower ℚ K L ∧ IsGalois ℚ L ∧ IsNormalClosure ℚ K L := by
  haveI : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  haveI : Normal ℚ (AlgebraicClosure K) := IsAlgClosure.normal ℚ (AlgebraicClosure K)
  haveI : Nonempty (K →ₐ[ℚ] AlgebraicClosure K) := ⟨IsScalarTower.toAlgHom ℚ K (AlgebraicClosure K)⟩
  haveI : FiniteDimensional ℚ (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) :=
    normalClosure.is_finiteDimensional ℚ K (AlgebraicClosure K)
  haveI : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := NumberField.mk
  haveI : Normal ℚ (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) :=
    normalClosure.normal ℚ K (AlgebraicClosure K)
  haveI : IsGalois ℚ (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := IsGalois.mk
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, isNormalClosure_normalClosure ℚ K (AlgebraicClosure K)⟩

end C5Sign

open C5Sign LanglandsTunnell.TateLocal HeckeCharacter in

theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ ω ∧ (∀ x, ω x * ω x = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsRamifiedIn K v →
        IsUnramifiedCharAt ω v ∧
          ((ω (uniformizerIdele ℚ v) : ℂˣ) : ℂ) = (-1) ^ (Module.finrank ℚ K + Nat.card (primeFibre ℚ K v))) ∧
      ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ), 1 ≤ m →
        (discr K).natAbs.factorization (Ideal.absNorm v.asIdeal) ≤ m →
          ∀ u ∈ higherUnitsAt ℚ v m, localChar ω v u = 1 := by
  obtain ⟨L, _, _, _, hST, hG, hNC⟩ := C5Sign.exists_galoisClosure K
  haveI := hST
  haveI := hG
  haveI := hNC
  obtain ⟨ω, hω, hω2, hval, hloc⟩ := C5Sign.core L K
  refine ⟨ω, hω, hω2, fun v hv => hval v ?_, hloc⟩

  refine NumberField.ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one ℚ K L v ?_
  intro w hw
  by_contra h
  exact hv ⟨w, hw, h⟩

end

end S_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le
end P2MW
export P2MW.S_NumberField_exists_isAdmissibleTwist_mul_self_eq_one_and_apply_uniformizerIdele_eq_neg_one_pow_and_localChar_eq_one_of_factorization_discr_le (solution)
