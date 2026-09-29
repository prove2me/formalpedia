-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c983f4a4-9aa9-5291-9b20-be60890124eb

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineBeta
import Definitions.Def_HeckeCharacter_FiniteOrder
import Theorems.Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_Converse_hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3.LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda"

private theorem exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (n : ℕ)
    (hn : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n, χ u = 1) :
    ∃ a ≤ n, LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ a := by
  classical
  have hex : ∃ m : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v m, χ u = 1 := ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hn, ?_⟩
  unfold LanglandsTunnell.TateLocal.HasConductorExponentAt
  refine ⟨Nat.find_spec hex, ?_⟩
  intro m hm
  have hnot : ¬ ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v m, χ u = 1 := Nat.find_min hex hm
  by_contra hcon
  exact hnot fun u hu => Classical.byContradiction fun hne => hcon ⟨u, hu, hne⟩

private theorem exists_hasConductorExponentAt_mul_le_max
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ₁ χ₂ : (v.adicCompletion K)ˣ →* ℂˣ) (a₁ a₂ : ℕ)
    (h₁ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₁ a₁)
    (h₂ : LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ₂ a₂) :
    ∃ a ≤ max a₁ a₂, LanglandsTunnell.TateLocal.HasConductorExponentAt K v (χ₁ * χ₂) a := by
  refine exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt K v (χ₁ * χ₂)
    (max a₁ a₂) ?_
  intro u hu
  rw [MonoidHom.mul_apply,
    h₁.1 u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone K v (le_max_left a₁ a₂) hu),
    h₂.1 u (LanglandsTunnell.TateLocal.higherUnitsAt_antitone K v (le_max_right a₁ a₂) hu), mul_one]

private theorem exists_hasConductorExponentAt_finset_prod_le_sum
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ι : Type} (s : Finset ι) (χ : ι → (v.adicCompletion K)ˣ →* ℂˣ) (a : ι → ℕ)
    (h : ∀ i ∈ s, LanglandsTunnell.TateLocal.HasConductorExponentAt K v (χ i) (a i)) :
    ∃ c ≤ ∑ i ∈ s, a i, LanglandsTunnell.TateLocal.HasConductorExponentAt K v (∏ i ∈ s, χ i) c := by
  refine exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt K v (∏ i ∈ s, χ i)
    (∑ i ∈ s, a i) ?_
  intro u hu
  rw [MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one fun i hi => (h i hi).1 u ?_
  exact LanglandsTunnell.TateLocal.higherUnitsAt_antitone K v
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hi) hu

private theorem exists_hasConductorExponentAt_comp_le
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : Type) [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (χ : (w.adicCompletion L)ˣ →* ℂˣ) (f : (v.adicCompletion K)ˣ →* (w.adicCompletion L)ˣ) (a : ℕ)
    (hf : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v a, f u ∈ LanglandsTunnell.TateLocal.higherUnitsAt L w a)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt L w χ a) :
    ∃ b ≤ a, LanglandsTunnell.TateLocal.HasConductorExponentAt K v (χ.comp f) b := by
  refine exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt K v (χ.comp f) a ?_
  intro u hu
  rw [MonoidHom.comp_apply]
  exact hχ.1 (f u) (hf u hu)

private theorem eq_one_of_forall_norm_pow_sub_one_lt_half (z : ℂ)
    (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hre : ∀ j : ℕ, (1 : ℝ) / 2 ≤ (z ^ j).re := by
    intro j
    have h1 : |(z ^ j - 1).re| ≤ ‖z ^ j - 1‖ := Complex.abs_re_le_norm _
    have h2 : (z ^ j - 1).re = (z ^ j).re - 1 := by simp
    rw [h2] at h1
    have h3 := h j
    have h4 := (abs_le.mp h1).1
    linarith
  have hsum : (k : ℝ) / 2 ≤ ‖∑ j ∈ Finset.range k, z ^ j‖ := by
    calc (k : ℝ) / 2 = ∑ _j ∈ Finset.range k, (1 : ℝ) / 2 := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.range k, (z ^ j).re := Finset.sum_le_sum fun j _ => hre j
      _ = (∑ j ∈ Finset.range k, z ^ j).re := by rw [Complex.re_sum]
      _ ≤ ‖∑ j ∈ Finset.range k, z ^ j‖ := Complex.re_le_norm _
  have hk' : 1 < (k : ℝ) * ‖z - 1‖ := by
    rw [div_lt_iff₀ hd] at hk
    exact hk
  have hnorm : ‖z ^ k - 1‖ = ‖∑ j ∈ Finset.range k, z ^ j‖ * ‖z - 1‖ := by
    rw [← geom_sum_mul, norm_mul]
  have hbig : (k : ℝ) / 2 * ‖z - 1‖ ≤ ‖z ^ k - 1‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
  have hk2 : 1 / 2 < (k : ℝ) / 2 * ‖z - 1‖ := by linarith
  linarith [h k]

private theorem mul_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) {u u' : (v.adicCompletion K)ˣ} (hu : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n)
    (hu' : u' ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n) :
    u * u' ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n := by
  obtain ⟨hval, hball⟩ := hu
  obtain ⟨hval', hball'⟩ := hu'
  refine ⟨by rw [Units.val_mul, map_mul, hval, hval', one_mul], ?_⟩
  rcases hball with hn | hle
  · exact Or.inl hn
  rcases hball' with hn | hle'
  · exact Or.inl hn
  right
  have hsplit : ((u * u' : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
      (u : v.adicCompletion K) * ((u' : v.adicCompletion K) - 1) + ((u : v.adicCompletion K) - 1) := by
    rw [Units.val_mul]; ring
  rw [hsplit]
  refine (Valued.v.map_add _ _).trans (max_le ?_ hle)
  rw [map_mul, hval, one_mul]
  exact hle'

private theorem pow_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (n : ℕ) {u : (v.adicCompletion K)ˣ} (hu : u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n) (k : ℕ) :
    u ^ k ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n := by
  induction k with
  | zero => simpa using LanglandsTunnell.TateLocal.one_mem_higherUnitsAt K v n
  | succ k ih => rw [pow_succ]; exact mul_mem_higherUnitsAt K v n ih hu

private theorem exists_nat_setOf_valued_sub_le_subset_of_mem_nhds
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {x : v.adicCompletion K} {s : Set (v.adicCompletion K)} (hs : s ∈ nhds x) :
    ∃ n : ℕ, {y : v.adicCompletion K | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} ⊆ s := by
  have h₁ := Valued.mem_nhds.mp hs
  obtain ⟨γ, hγ⟩ := h₁
  have h₂ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective _ γ.1
  obtain ⟨t, ht⟩ := h₂
  have htne : Valued.v t ≠ 0 := by
    intro h0
    apply γ.ne_zero
    rw [← ht]
    exact MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff.mpr h0
  have h₃ : ∃ L : ℤ, WithZero.exp L = Valued.v t := ⟨WithZero.log (Valued.v t), WithZero.exp_log htne⟩
  obtain ⟨L, hL⟩ := h₃
  refine ⟨(-L).toNat + 1, fun y hy => hγ ?_⟩
  rw [Set.mem_setOf_eq, ← ht, ← Valuation.restrict_def, Valuation.restrict_lt_iff]
  have hyle : Valued.v (y - x) ≤ WithZero.exp (-(((-L).toNat + 1 : ℕ) : ℤ)) := hy
  refine lt_of_le_of_lt hyle ?_
  rw [← hL, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-L)
  omega

private theorem exists_higherUnitsAt_subset_of_mem_nhds_one
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {s : Set (v.adicCompletion K)ˣ} (hs : s ∈ nhds (1 : (v.adicCompletion K)ˣ)) :
    ∃ n : ℕ, LanglandsTunnell.TateLocal.higherUnitsAt K v n ⊆ s := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hs
  obtain ⟨t, ht, hts⟩ := hs
  rw [Units.embedProduct_apply, inv_one, Units.val_one, mem_nhds_prod_iff] at ht
  obtain ⟨A, hA, B, hB, hAB⟩ := ht
  have hB' : (fun y : v.adicCompletion K => MulOpposite.op y) ⁻¹' B ∈ nhds (1 : v.adicCompletion K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hB)
  obtain ⟨n₁, hn₁⟩ := exists_nat_setOf_valued_sub_le_subset_of_mem_nhds K v hA
  obtain ⟨n₂, hn₂⟩ := exists_nat_setOf_valued_sub_le_subset_of_mem_nhds K v hB'
  refine ⟨max n₁ n₂ + 1, fun u hu => hts ?_⟩
  obtain ⟨hval, hball⟩ := hu
  have hle : Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-((max n₁ n₂ + 1 : ℕ) : ℤ)) := by
    rcases hball with h0 | h
    · omega
    · exact h
  have hinv : Valued.v (((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) =
      Valued.v ((u : v.adicCompletion K) - 1) := by
    have hu0 : (u : v.adicCompletion K) ≠ 0 := u.ne_zero
    have hsplit : ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        ((u : v.adicCompletion K))⁻¹ * (1 - (u : v.adicCompletion K)) := by
      rw [Units.val_inv_eq_inv_val]; field_simp
    rw [hsplit, map_mul, map_inv₀, hval, inv_one, one_mul, Valuation.map_sub_swap]
  have hmono : ∀ m : ℕ, m ≤ max n₁ n₂ + 1 →
      WithZero.exp (-((max n₁ n₂ + 1 : ℕ) : ℤ)) ≤ WithZero.exp (-(m : ℤ)) := by
    intro m hm
    rw [WithZero.exp_le_exp]
    omega
  show Units.embedProduct _ u ∈ t
  rw [Units.embedProduct_apply]
  refine hAB ⟨hn₁ ?_, hn₂ ?_⟩
  · exact hle.trans (hmono n₁ (by omega))
  · show Valued.v (((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n₂ : ℤ))
    rw [hinv]
    exact hle.trans (hmono n₂ (by omega))

private theorem exists_forall_mem_higherUnitsAt_apply_eq_one_of_continuous
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ n : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v n, χ u = 1 := by
  have hD : (fun z : ℂˣ => (z : ℂ)) ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (1 : ℂˣ) :=
    (Metric.isOpen_ball.preimage Units.continuous_val).mem_nhds (by simp)
  have hpre : χ ⁻¹' ((fun z : ℂˣ => (z : ℂ)) ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (1 : (v.adicCompletion K)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨n, hn⟩ := exists_higherUnitsAt_subset_of_mem_nhds_one K v hpre
  refine ⟨n, fun u hu => ?_⟩
  have hpow : ∀ k : ℕ, ‖((χ u : ℂˣ) : ℂ) ^ k - 1‖ < 1 / 2 := by
    intro k
    have hk := hn (pow_mem_higherUnitsAt K v n hu k)
    simp only [Set.mem_preimage, map_pow, Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at hk
    exact hk
  exact Units.val_eq_one.mp (eq_one_of_forall_norm_pow_sub_one_lt_half _ hpow)

private theorem exists_hasConductorExponentAt_of_continuous
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ a : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt K v χ a := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_forall_mem_higherUnitsAt_apply_eq_one_of_continuous K v χ hχ
  have hex : ∃ m : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v m, χ u = 1 := ⟨n, hn⟩
  refine ⟨Nat.find hex, ?_⟩
  unfold LanglandsTunnell.TateLocal.HasConductorExponentAt
  refine ⟨Nat.find_spec hex, fun m hm => ?_⟩
  have hnot : ¬ ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v m, χ u = 1 := Nat.find_min hex hm
  by_contra hcon
  exact hnot fun u hu => Classical.byContradiction fun hne => hcon ⟨u, hu, hne⟩

private theorem exists_finset_levels_forall_mem_of_mem_nhds_one (K : Type) [Field K] [NumberField K]
    {s : Set (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)}
    (hs : s ∈ nhds (1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)) :
    ∃ (I : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
      (n : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ),
      ∀ y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K,
        (∀ v, Valued.v (y v) ≤ (1 : WithZero (Multiplicative ℤ))) →
        (∀ v ∈ I, Valued.v (y v - 1) ≤ WithZero.exp (-(n v : ℤ))) → y ∈ s := by
  classical
  have hopen : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    fun v => Valued.isOpen_valuationSubring _
  set one' : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    fun v => ⟨1, one_mem (v.adicCompletionIntegers K)⟩ with hone'
  have h1 : (1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K) =
      RestrictedProduct.structureMap (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        v.adicCompletion K) (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite one' :=
    IsDedekindDomain.FiniteAdeleRing.ext (h := fun _ => rfl)
  rw [h1] at hs

  have hs' : s ∈ nhds (RestrictedProduct.structureMap
      (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite one') := hs
  have hmap := RestrictedProduct.nhds_eq_map_structureMap hopen one'
  rw [hmap] at hs'
  have hs'' := Filter.mem_map.mp hs'
  rw [nhds_pi] at hs''
  obtain ⟨I, hIfin, t, ht, hIt⟩ := Filter.mem_pi.mp hs''
  have hb : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), ∃ m : ℕ,
      ∀ z : (v.adicCompletionIntegers K : Set (v.adicCompletion K)),
        Valued.v ((z : v.adicCompletion K) - 1) ≤ WithZero.exp (-(m : ℤ)) → z ∈ t v := by
    intro v
    obtain ⟨U, hU, hUt⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
    obtain ⟨m, hm⟩ := exists_nat_setOf_valued_sub_le_subset_of_mem_nhds K v hU
    exact ⟨m, fun z hz => hUt (hm hz)⟩
  choose n hn using hb
  refine ⟨hIfin.toFinset, n, fun y hint hcong => ?_⟩
  have hmem : ∀ v, y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun v =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hint v)
  have hy : y = RestrictedProduct.structureMap
      (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) => v.adicCompletion K)
      (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite (fun v => ⟨y v, hmem v⟩) :=
    IsDedekindDomain.FiniteAdeleRing.ext (h := fun _ => rfl)
  rw [hy]
  exact hIt fun v hv => hn v _ (hcong v (hIfin.mem_toFinset.mpr hv))

private theorem le_idealMultiplicity_finset_prod_pow (K : Type) [Field K] [NumberField K]
    (I : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (n : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
    {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : v ∈ I) :
    n v ≤ HeckeCharacter.idealMultiplicity K v (∏ w ∈ I, w.asIdeal ^ n w) := by
  have hne : (∏ w ∈ I, w.asIdeal ^ n w) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (by rw [Submodule.zero_eq_bot]; exact w.ne_bot)
  unfold HeckeCharacter.idealMultiplicity
  refine (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hne)
    (Associates.irreducible_mk.mpr v.irreducible)).mp ?_
  rw [← Associates.mk_pow]
  exact Associates.mk_le_mk_of_dvd (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ n w) hv)

private def IsCongruentIdele (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K))
    (u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) : Prop :=
  (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 = 1 ∧
    ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Valued.v ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v) = 1 ∧
      Valued.v ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity K v 𝔣 : ℤ))

private theorem IsCongruentIdele.mul (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K)) {u u' : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ}
    (hu : IsCongruentIdele K 𝔣 u)
    (hu' : IsCongruentIdele K 𝔣 u') :
    IsCongruentIdele K 𝔣 (u * u') := by
  obtain ⟨harch, hfin⟩ := hu
  obtain ⟨harch', hfin'⟩ := hu'
  have earch : ((u * u' : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
      NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 =
      (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 *
        (u' : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 := rfl
  refine ⟨by rw [earch, harch, harch', one_mul], fun v => ?_⟩
  obtain ⟨hval, hle⟩ := hfin v
  obtain ⟨hval', hle'⟩ := hfin' v
  have hcomp : ((u * u' : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
      NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v =
      (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v *
        (u' : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v := rfl
  rw [hcomp]
  refine ⟨by rw [map_mul, hval, hval', one_mul], ?_⟩
  have hsplit : (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v *
      (u' : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v - 1 =
      (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v *
          ((u' : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v - 1) +
        ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v - 1) := by ring
  rw [hsplit]
  refine (Valued.v.map_add _ _).trans (max_le ?_ hle)
  rw [map_mul, hval, one_mul]
  exact hle'

private theorem IsCongruentIdele.one (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K)) :
    IsCongruentIdele K 𝔣
      (1 : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) := by
  refine ⟨rfl, fun v => ?_⟩
  have hone : ((1 : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
      NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v = 1 := rfl
  rw [hone, map_one, sub_self, map_zero]
  exact ⟨rfl, zero_le'⟩

private theorem IsCongruentIdele.pow (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K)) {u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ}
    (hu : IsCongruentIdele K 𝔣 u) (k : ℕ) :
    IsCongruentIdele K 𝔣 (u ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact IsCongruentIdele.one K 𝔣
  | succ k ih => rw [pow_succ]; exact IsCongruentIdele.mul K 𝔣 ih hu

private theorem IsCongruentIdele.inv (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K)) {u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ}
    (hu : IsCongruentIdele K 𝔣 u) :
    IsCongruentIdele K 𝔣 u⁻¹ := by
  obtain ⟨harch, hfin⟩ := hu
  have hmul : (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K) *
      ((u⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
        NumberField.AdeleRing (NumberField.RingOfIntegers K) K) = 1 := Units.mul_inv u
  refine ⟨?_, fun v => ?_⟩
  · have h1 : (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 *
        ((u⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
          NumberField.AdeleRing (NumberField.RingOfIntegers K) K).1 = 1 := congrArg Prod.fst hmul
    rw [harch, one_mul] at h1
    exact h1
  · obtain ⟨hval, hle⟩ := hfin v
    have h2 : (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v *
        ((u⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
          NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v = 1 :=
      congrArg (fun x : NumberField.AdeleRing (NumberField.RingOfIntegers K) K => x.2 v) hmul
    have hinv : ((u⁻¹ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :
        NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v =
        ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v)⁻¹ :=
      eq_inv_of_mul_eq_one_right h2
    have hu0 : (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v ≠ 0 := by
      intro h0; rw [h0, map_zero] at hval; exact zero_ne_one hval
    rw [hinv, map_inv₀, hval, inv_one]
    refine ⟨rfl, ?_⟩
    have hsplit : ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v)⁻¹ - 1 =
        ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v)⁻¹ *
          (1 - (u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v) := by
      field_simp
    rw [hsplit, map_mul, map_inv₀, hval, inv_one, one_mul, Valuation.map_sub_swap]
    exact hle

private theorem exists_admitsModulus_of_continuous (K : Type) [Field K] [NumberField K]
    (χ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ 𝔣 : Ideal (NumberField.RingOfIntegers K), HeckeCharacter.AdmitsModulus K χ 𝔣 := by
  classical
  have hD : (fun z : ℂˣ => (z : ℂ)) ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (1 : ℂˣ) :=
    (Metric.isOpen_ball.preimage Units.continuous_val).mem_nhds (by simp)
  have hpre : χ ⁻¹' ((fun z : ℂˣ => (z : ℂ)) ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (1 : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ) :=
    hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hpre
  obtain ⟨t, ht, hts⟩ := hpre
  rw [Units.embedProduct_apply, inv_one, Units.val_one, mem_nhds_prod_iff] at ht
  obtain ⟨A, hA, B, hB, hAB⟩ := ht
  have hB' : (fun y : NumberField.AdeleRing (NumberField.RingOfIntegers K) K => MulOpposite.op y) ⁻¹' B ∈
      nhds (1 : NumberField.AdeleRing (NumberField.RingOfIntegers K) K) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hB)

  have key : ∀ W : Set (NumberField.AdeleRing (NumberField.RingOfIntegers K) K),
      W ∈ nhds (1 : NumberField.AdeleRing (NumberField.RingOfIntegers K) K) →
      ∃ (I : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (n : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ),
        ∀ x : NumberField.AdeleRing (NumberField.RingOfIntegers K) K, x.1 = 1 →
          (∀ v, Valued.v (x.2 v) = (1 : WithZero (Multiplicative ℤ))) →
          (∀ v ∈ I, Valued.v (x.2 v - 1) ≤ WithZero.exp (-(n v : ℤ))) → x ∈ W := by
    intro W hW
    have hW' : W ∈ nhds ((1 : NumberField.InfiniteAdeleRing K),
        (1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers K) K)) := hW
    obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.mp hW'
    obtain ⟨I, n, hIn⟩ := exists_finset_levels_forall_mem_of_mem_nhds_one K hW₂
    refine ⟨I, n, fun x hx1 hxv hxc => hW ⟨?_, hIn x.2 (fun v => (hxv v).le) hxc⟩⟩
    rw [hx1]
    exact mem_of_mem_nhds hW₁
  obtain ⟨I₁, n₁, h₁⟩ := key A hA
  obtain ⟨I₂, n₂, h₂⟩ := key _ hB'
  set n : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ := fun v => max (n₁ v) (n₂ v) with hn
  set 𝔣 : Ideal (NumberField.RingOfIntegers K) := ∏ w ∈ I₁ ∪ I₂, w.asIdeal ^ n w with h𝔣

  have hlevel : ∀ (u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ),
      IsCongruentIdele K 𝔣 u →
      ∀ (J : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (m : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ),
        J ⊆ I₁ ∪ I₂ → (∀ v, m v ≤ n v) → ∀ v ∈ J,
          Valued.v ((u : NumberField.AdeleRing (NumberField.RingOfIntegers K) K).2 v - 1) ≤
            WithZero.exp (-(m v : ℤ)) := by
    intro u hu J m hJ hm v hv
    refine ((hu.2 v).2).trans ?_
    rw [WithZero.exp_le_exp]
    have hmult := le_idealMultiplicity_finset_prod_pow K (I₁ ∪ I₂) n (hJ hv)
    rw [← h𝔣] at hmult
    have := hm v
    omega
  have hin : ∀ u : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ,
      IsCongruentIdele K 𝔣 u → (χ u : ℂ) ∈ Metric.ball (1 : ℂ) (1 / 2) := by
    intro u hu
    have huinv := IsCongruentIdele.inv K 𝔣 hu
    have hmem : u ∈ χ ⁻¹' ((fun z : ℂˣ => (z : ℂ)) ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) := by
      apply hts
      show Units.embedProduct _ u ∈ t
      rw [Units.embedProduct_apply]
      refine hAB ⟨h₁ _ hu.1 (fun v => (hu.2 v).1) ?_, h₂ _ huinv.1 (fun v => (huinv.2 v).1) ?_⟩
      · exact hlevel u hu I₁ n₁ Finset.subset_union_left (fun v => le_max_left _ _)
      · exact hlevel u⁻¹ huinv I₂ n₂ Finset.subset_union_right (fun v => le_max_right _ _)
    exact hmem
  refine ⟨𝔣, fun u harch hfin => ?_⟩
  have hu : IsCongruentIdele K 𝔣 u := ⟨harch, hfin⟩
  have hpow : ∀ k : ℕ, ‖((χ u : ℂˣ) : ℂ) ^ k - 1‖ < 1 / 2 := by
    intro k
    have hk := hin (u ^ k) (IsCongruentIdele.pow K 𝔣 hu k)
    rw [map_pow, Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at hk
    exact hk
  exact Units.val_eq_one.mp (eq_one_of_forall_norm_pow_sub_one_lt_half _ hpow)

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.higherUnitsAt TateLocal.one_mem_higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "inducedCoeff IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt finite_setOf_isBadPlace_of_continuous exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three"
namespace CentralConductor
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

@[reducible] private noncomputable def instFintypeExtension (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 ℚ)) : Fintype (v.Extension (𝓞 K)) :=
  Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) v

attribute [local instance] instFintypeExtension

section AlgebraUnique

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem algebra_ringOfIntegers_rat_ext (S : Type) [CommRing S] (P Q : Algebra (𝓞 ℚ) S) : P = Q := by
  refine Algebra.algebra_ext P Q fun r => ?_
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective r
  exact RingHom.congr_fun
    (RingHom.ext_int ((@algebraMap (𝓞 ℚ) S _ _ P).comp Rat.ringOfIntegersEquiv.symm.toRingHom)
      ((@algebraMap (𝓞 ℚ) S _ _ Q).comp Rat.ringOfIntegersEquiv.symm.toRingHom)) n

end AlgebraUnique

section TrivialTwist

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem isUnramifiedCharAt_one (𝔓 : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) 𝔓 :=
  fun _ _ _ => rfl

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem isAdmissibleTwist_one : Converse.IsAdmissibleTwist K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :=
  ⟨fun _ => rfl, (continuous_const : Continuous fun _ : (AdeleRing (𝓞 K) K)ˣ => (1 : ℂˣ)),
    fun _ => by simp⟩

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem inducedCoeff_one :
    inducedCoeff K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) = fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ) :=
  funext fun 𝔓 => by simp [inducedCoeff, isUnramifiedCharAt_one K 𝔓]

variable [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem not_isTwistRamifiedAbove_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ¬ IsTwistRamifiedAbove K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v :=
  fun ⟨𝔓, _, h⟩ => h (isUnramifiedCharAt_one K 𝔓)

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem isBadPlace_one_iff (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsBadPlace K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v ↔ IsRamifiedIn K v :=
  ⟨fun h => h.elim id fun h' => (not_isTwistRamifiedAbove_one K v h').elim, Or.inl⟩

end TrivialTwist

section Fibre

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem primeFibre_eq_range (v : HeightOneSpectrum (𝓞 ℚ)) :
    RankinSelberg.primeFibre ℚ K v =
      Set.range (fun w : v.Extension (𝓞 K) => (w.1 : HeightOneSpectrum (𝓞 K))) := by
  ext 𝔓
  constructor
  · exact fun h => ⟨⟨𝔓, h⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact w.2

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem val_injective_extension (v : HeightOneSpectrum (𝓞 ℚ)) :
    Function.Injective (fun w : v.Extension (𝓞 K) => (w.1 : HeightOneSpectrum (𝓞 K))) :=
  fun _ _ h => Subtype.ext h

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem finprod_mem_primeFibre_eq (v : HeightOneSpectrum (𝓞 ℚ)) {M : Type*} [CommMonoid M]
    (g : HeightOneSpectrum (𝓞 K) → M) :
    ∏ᶠ 𝔓 ∈ RankinSelberg.primeFibre ℚ K v, g 𝔓 = ∏ w : v.Extension (𝓞 K), g w.1 := by
  rw [primeFibre_eq_range, finprod_mem_range (val_injective_extension K v), finprod_eq_prod_of_fintype]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem finsum_mem_primeFibre_eq (v : HeightOneSpectrum (𝓞 ℚ)) {M : Type*} [AddCommMonoid M]
    (g : HeightOneSpectrum (𝓞 K) → M) :
    ∑ᶠ 𝔓 ∈ RankinSelberg.primeFibre ℚ K v, g 𝔓 = ∑ w : v.Extension (𝓞 K), g w.1 := by
  rw [primeFibre_eq_range, finsum_mem_range (val_injective_extension K v), finsum_eq_sum_of_fintype]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem sum_inertiaDeg_eq_three (hdeg : Module.finrank ℚ K = 3) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ IsRamifiedIn K v) :
    ∑ w : v.Extension (𝓞 K), v.asIdeal.inertiaDeg' w.1.asIdeal = 3 := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  have h := Ideal.sum_ramification_inertia_extensions (𝓞 ℚ) ℚ K (𝓞 K) v
  rw [hdeg] at h
  have he : ∀ w : v.Extension (𝓞 K), Ideal.ramificationIdx' v.asIdeal w.1.asIdeal = 1 := fun w => by
    by_contra hne
    exact hv ⟨w.1, w.2, hne⟩
  simpa [he] using h

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem one_le_inertiaDeg (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)) :
    1 ≤ v.asIdeal.inertiaDeg' w.1.asIdeal := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)
  haveI := v.isMaximal
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  exact Ideal.inertiaDeg'_pos v.asIdeal w.1.asIdeal

end Fibre

section ThirdCoefficient

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem coeff_prod_eq_prod_coeff {ι : Type*} (s : Finset ι) (q : ι → ℂ[X]) (d : ι → ℕ)
    (hq : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hq' : ∀ i ∈ s, (q i).natDegree ≤ d i := fun i hi => hq i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons,
      coeff_mul_add_eq_of_natDegree_le (hq a (Finset.mem_cons_self a s))
        ((natDegree_prod_le _ _).trans (Finset.sum_le_sum hq')), ih hq']

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem natDegree_inducedFactor_le {R : Type*} [CommRing R] (a : R) (d : ℕ) :
    (C 1 - C a * X ^ d).natDegree ≤ d :=
  (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_C_mul_X_pow_le a d))

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem coeff_inducedFactor {R : Type*} [CommRing R] (a : R) {d : ℕ} (hd : 1 ≤ d) :
    (C 1 - C a * X ^ d).coeff d = -a := by
  have hd' : d ≠ 0 := by omega
  simp [coeff_one, coeff_C_mul, coeff_X_pow, hd']

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem inducedE3_eq_neg_prod (hdeg : Module.finrank ℚ K = 3) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    RankinSelberg.inducedE3 ℚ c v = -∏ w : v.Extension (𝓞 K), (-(c w.1)) := by
  have hf : ∀ w : v.Extension (𝓞 K),
      (w.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.1.asIdeal = v.asIdeal.inertiaDeg' w.1.asIdeal :=
    fun w => by rw [w.2]
  have hsum : ∑ w : v.Extension (𝓞 K), (w.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.1.asIdeal = 3 := by
    rw [Finset.sum_congr rfl fun w _ => hf w]
    exact sum_inertiaDeg_eq_three K hdeg v hv
  simp only [RankinSelberg.inducedE3, RankinSelberg.inducedEulerPoly, finprod_mem_primeFibre_eq]
  rw [← hsum, coeff_prod_eq_prod_coeff Finset.univ
    (fun w : v.Extension (𝓞 K) => RankinSelberg.inducedFactor ℚ c w.1)
    (fun w => (w.1.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.1.asIdeal)
    (fun w _ => natDegree_inducedFactor_le _ _)]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  exact coeff_inducedFactor (c w.1) (by rw [hf]; exact one_le_inertiaDeg K v w)

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem inducedE3_eq_inducedE3_one_mul_prod (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    RankinSelberg.inducedE3 ℚ c v =
      RankinSelberg.inducedE3 ℚ (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) v *
        ∏ w : v.Extension (𝓞 K), c w.1 := by
  rw [inducedE3_eq_neg_prod K hdeg c v hv,
    inducedE3_eq_neg_prod K hdeg (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) v hv,
    neg_mul, ← Finset.prod_mul_distrib]
  congr 2
  exact funext fun w => by ring

end ThirdCoefficient

section LocalMaps

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private noncomputable def localMap (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)) :
    v.adicCompletion ℚ →+* w.1.adicCompletion K :=
  (Extension.adicCompletionSemialgHom ℚ K w).toRingHom

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem localMap_apply (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)) (x : v.adicCompletion ℚ) :
    localMap K v w x = Extension.adicCompletionSemialgHom ℚ K w x := rfl

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem valued_localMap (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K)) (x : v.adicCompletion ℚ) :
    Valued.v (localMap K v w x) =
      Valued.v x ^ (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal :=
  Extension.valued_adicCompletionSemialgHom ℚ K w x

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem map_mem_higherUnitsAt (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))
    (he : (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal = 1) (n : ℕ)
    (u : (v.adicCompletion ℚ)ˣ) (hu : u ∈ TateLocal.higherUnitsAt ℚ v n) :
    Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) u ∈
      TateLocal.higherUnitsAt K w.1 n := by
  obtain ⟨hval, hball⟩ := hu
  refine ⟨?_, ?_⟩
  · show Valued.v (localMap K v w (u : v.adicCompletion ℚ)) = 1
    rw [valued_localMap, he, pow_one, hval]
  · rcases hball with h0 | hle
    · exact Or.inl h0
    · right
      show Valued.v (localMap K v w (u : v.adicCompletion ℚ) - 1) ≤ _
      rw [← map_one (localMap K v w), ← map_sub, valued_localMap, he, pow_one]
      exact hle

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem localChar_map_uniformizerUnit (v : HeightOneSpectrum (𝓞 ℚ)) (w : v.Extension (𝓞 K))
    (he : (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsUnramifiedCharAt μ w.1) :
    localChar μ w.1 (Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K)
      (uniformizerUnit ℚ v)) = localChar μ w.1 (uniformizerUnit K w.1) := by
  set t := Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K)
    (uniformizerUnit ℚ v) with ht
  have hvt : Valued.v (t : w.1.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (localMap K v w (uniformizerUnit ℚ v : v.adicCompletion ℚ)) = _
    rw [valued_localMap, he, pow_one, valued_uniformizerUnit]
  have hq : Valued.v ((t * (uniformizerUnit K w.1)⁻¹ : (w.1.adicCompletion K)ˣ) : w.1.adicCompletion K)
      = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hvt, valued_uniformizerUnit,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h1 : localChar μ w.1 (t * (uniformizerUnit K w.1)⁻¹) = 1 := by
    refine hμ _ ?_ ?_
    · exact (mem_adicCompletionIntegers ..).2 hq.le
    · refine (mem_adicCompletionIntegers ..).2 ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, hq, inv_one]
  calc localChar μ w.1 t = localChar μ w.1 (t * (uniformizerUnit K w.1)⁻¹ * uniformizerUnit K w.1) := by
        rw [inv_mul_cancel_right]
    _ = localChar μ w.1 (uniformizerUnit K w.1) := by rw [map_mul, h1, one_mul]

end LocalMaps

section Conorm

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private noncomputable def evalAt (u : HeightOneSpectrum (𝓞 K)) : FiniteAdeleRing (𝓞 K) K →* u.adicCompletion K where
  toFun x := x u
  map_one' := RestrictedProduct.one_apply _ u
  map_mul' x y := RestrictedProduct.mul_apply _ x y u

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in
private theorem evalAt_apply (u : HeightOneSpectrum (𝓞 K)) (x : FiniteAdeleRing (𝓞 K) K) : evalAt K u x = x u := rfl

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem finiteConorm_localUnit (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K) : FiniteAdeleRing (𝓞 ℚ) ℚ →* FiniteAdeleRing (𝓞 K) K)
        (localUnit (𝓞 ℚ) ℚ v t) =
      ∏ w : v.Extension (𝓞 K), localUnit (𝓞 K) K w.1
        (Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) t) := by
  classical
  refine Units.ext (RestrictedProduct.ext (h := fun u => ?_))
  rw [Units.coe_prod]

  change _ = evalAt K u _
  rw [map_prod]
  simp only [evalAt_apply]

  change Extension.adicCompletionSemialgHom ℚ K (⟨u, rfl⟩ : (u.under (𝓞 ℚ)).Extension (𝓞 K))
      (((localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) (u.under (𝓞 ℚ))) = _
  by_cases hu : u.under (𝓞 ℚ) = v
  · subst hu
    rw [localUnit_apply_self, Finset.prod_eq_single ⟨u, rfl⟩]
    · simp only [Subtype.coe_mk, localUnit_apply_self, Units.coe_map, MonoidHom.coe_coe]
      rfl
    · intro w _ hw
      rw [localUnit_apply_of_ne]
      exact fun h => hw (Subtype.ext h.symm)
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [localUnit_apply_of_ne]
    · rw [map_one]
      symm
      refine Finset.prod_eq_one fun w _ => ?_
      rw [localUnit_apply_of_ne]
      exact fun h => hu (h ▸ w.2)
    · exact hu

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem genuineβ_finIncl (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    M4aHerbrand.Bridge.genuineβ ℚ K (finIncl (𝓞 ℚ) ℚ x) =
      finIncl (𝓞 K) K (M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K) x) :=
  Prod.ext (by rw [M4aHerbrand.Bridge.genuineβ_fst, finIncl_apply_fst, finIncl_apply_fst, map_one])
    (by rw [M4aHerbrand.Bridge.genuineβ_snd, finIncl_apply_snd, finIncl_apply_snd])

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem apply_genuineβ_localUnit (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (t : (v.adicCompletion ℚ)ˣ) :
    μ (Units.map (M4aHerbrand.Bridge.genuineβ ℚ K : AdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 K) K)
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t))) =
      ∏ w : v.Extension (𝓞 K), localChar μ w.1
        (Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) t) := by
  have h : Units.map (M4aHerbrand.Bridge.genuineβ ℚ K : AdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 K) K)
      (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) =
      Units.map (finIncl (𝓞 K) K) (Units.map
        (M4aHerbrand.Bridge.finiteConorm (𝓞 ℚ) ℚ K (𝓞 K) : FiniteAdeleRing (𝓞 ℚ) ℚ →* FiniteAdeleRing (𝓞 K) K)
        (localUnit (𝓞 ℚ) ℚ v t)) :=
    Units.ext (genuineβ_finIncl K _)
  rw [h, finiteConorm_localUnit K v t, map_prod, map_prod]
  rfl

end Conorm

section LocalTriviality

variable (K : Type) [Field K] [NumberField K]

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel Polynomial in

private theorem localChar_map_eq_one_of_mem_higherUnitsAt_inducedLevelAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hexp : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ∃ a : ℕ, TateLocal.HasConductorExponentAt K 𝔓 (localChar μ 𝔓) a)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) (u : (v.adicCompletion ℚ)ˣ)
    (hu : u ∈ TateLocal.higherUnitsAt ℚ v (inducedLevelAt K μ v)) (w : v.Extension (𝓞 K)) :
    localChar μ w.1 (Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) u) = 1 := by
  obtain ⟨a, ha⟩ := hexp w.1
  have he : (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    rw [w.2]
    by_contra hne
    exact hv ⟨w.1, w.2, hne⟩
  have hmem : Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) u ∈
      TateLocal.higherUnitsAt K w.1 (inducedLevelAt K μ v) :=
    map_mem_higherUnitsAt K v w he _ u hu
  have hca : TateLocal.conductorExponentAt K w.1 (localChar μ w.1) = a :=
    TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K w.1 ha
  have hfs := finsum_mem_primeFibre_eq K v
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal.inertiaDeg' 𝔓.asIdeal * TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓))
  have hlevel : a ≤ inducedLevelAt K μ v := by
    unfold inducedLevelAt
    rw [hfs]
    calc a = 1 * a := (one_mul a).symm
      _ ≤ v.asIdeal.inertiaDeg' w.1.asIdeal * TateLocal.conductorExponentAt K w.1 (localChar μ w.1) := by
          rw [hca]; exact Nat.mul_le_mul (one_le_inertiaDeg K v w) le_rfl
      _ ≤ ∑ w' : v.Extension (𝓞 K),
            v.asIdeal.inertiaDeg' w'.1.asIdeal * TateLocal.conductorExponentAt K w'.1 (localChar μ w'.1) :=
          Finset.single_le_sum
            (f := fun w' : v.Extension (𝓞 K) =>
              v.asIdeal.inertiaDeg' w'.1.asIdeal * TateLocal.conductorExponentAt K w'.1 (localChar μ w'.1))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  exact ha.1 _ (TateLocal.higherUnitsAt_antitone K w.1 hlevel hmem)

end LocalTriviality

end LanglandsTunnell.CubicInduction.CentralConductor

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "Converse.IsAdmissibleTwist TateLocal.higherUnitsAt TateLocal.one_mem_higherUnitsAt TateLocal.higherUnitsAt_antitone TateLocal.HasConductorExponentAt TateLocal.conductorExponentAt TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt RankinSelberg.primeFibre RankinSelberg.inducedFactor RankinSelberg.inducedEulerPoly RankinSelberg.inducedE3"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "inducedCoeff IsRamifiedIn IsTwistRamifiedAbove IsBadPlace inducedLevelAt finite_setOf_isBadPlace_of_continuous exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three"
namespace CentralConductor
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

attribute [local instance] instFintypeExtension

private noncomputable def baseChangeIdele (K : Type) [Field K] [NumberField K] :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (M4aHerbrand.Bridge.genuineβ ℚ K : AdeleRing (𝓞 ℚ) ℚ →* AdeleRing (𝓞 K) K)

private theorem continuous_baseChangeIdele (K : Type) [Field K] [NumberField K] :
    Continuous (baseChangeIdele K) :=
  Continuous.units_map _ (M4aHerbrand.Bridge.continuous_genuineβ ℚ K)

private theorem baseChangeIdele_algebraMap (K : Type) [Field K] [NumberField K] (e : ℚˣ) :
    baseChangeIdele K (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) e) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Units.map (algebraMap ℚ K : ℚ →* K) e) :=
  Units.ext (M4aHerbrand.Bridge.genuineβ_compat ℚ K (e : ℚ))

private theorem apply_baseChangeIdele_localUnit (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    μ (baseChangeIdele K (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v t))) =
      ∏ w : v.Extension (𝓞 K), localChar μ w.1
        (Units.map (localMap K v w : v.adicCompletion ℚ →* w.1.adicCompletion K) t) :=
  apply_genuineβ_localUnit K μ v t

end LanglandsTunnell.CubicInduction.CentralConductor

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : IsAdmissibleTwist ℚ ω)
    (hωp : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
      IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) a := by
  classical

  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    CentralConductor.algebra_ringOfIntegers_rat_ext (𝓞 K) _ _

  obtain ⟨ω₁, hω₁, hω₁p, -⟩ := exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three K hdeg 1
    (CentralConductor.isAdmissibleTwist_one K)

  set ν : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := ω * (μ.comp (CentralConductor.baseChangeIdele K))⁻¹ with hν
  have hνapply : ∀ x, ν x = ω x * (μ (CentralConductor.baseChangeIdele K x))⁻¹ := fun x => rfl
  have hνicc : AutomorphicForm.IsIdeleClassChar (𝓞 ℚ) ℚ ν := fun e => by
    rw [hνapply, hω.1 e, CentralConductor.baseChangeIdele_algebraMap, hμ.1, inv_one, one_mul]
  have hνc : Continuous ν := by
    show Continuous fun x => ω x * (μ (CentralConductor.baseChangeIdele K x))⁻¹
    exact hω.2.1.mul ((hμ.2.1.comp (CentralConductor.continuous_baseChangeIdele K)).inv)
  obtain ⟨𝔣ν, hmodν⟩ := exists_admitsModulus_of_continuous ℚ ν hνc
  obtain ⟨𝔣₁, hmod₁⟩ := exists_admitsModulus_of_continuous ℚ ω₁ hω₁.2.1

  have hfin := finite_setOf_isBadPlace_of_continuous K μ hμ.2.1
  have hS : ∀ p ∉ hfin.toFinset,
      ν (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
          (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (AdelicLevel.uniformizerUnit ℚ p))) =
        ω₁ (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
          (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (AdelicLevel.uniformizerUnit ℚ p))) := by
    intro p hp
    have hgood : ¬ IsBadPlace K μ p := fun h => hp (hfin.mem_toFinset.2 h)
    have hunr : ¬ IsRamifiedIn K p := fun h => hgood (Or.inl h)
    have hunrw : ∀ w : p.Extension (𝓞 K), IsUnramifiedCharAt μ w.1 := fun w => by
      by_contra h
      exact hgood (Or.inr ⟨w.1, w.2, h⟩)
    have hew : ∀ w : p.Extension (𝓞 K), (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal = 1 :=
      fun w => by
        rw [w.2]
        by_contra h
        exact hunr ⟨w.1, w.2, h⟩
    obtain ⟨hωu, hωe⟩ := hωp p hgood
    obtain ⟨hω₁u, hω₁e⟩ := hω₁p p fun h => hunr ((CentralConductor.isBadPlace_one_iff K p).1 h)
    rw [eulerCoeff, if_pos hωu] at hωe
    rw [eulerCoeff, if_pos hω₁u, CentralConductor.inducedCoeff_one] at hω₁e
    have hval : ((ω (AutomorphicForm.uniformizerIdele ℚ p) : ℂˣ) : ℂ) =
        ((ω₁ (AutomorphicForm.uniformizerIdele ℚ p) : ℂˣ) : ℂ) *
          ((μ (CentralConductor.baseChangeIdele K (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ)
            (AdelicLevel.localUnit (𝓞 ℚ) ℚ p (AdelicLevel.uniformizerUnit ℚ p)))) : ℂˣ) : ℂ) := by
      rw [hωe, hω₁e, CentralConductor.inducedE3_eq_inducedE3_one_mul_prod K hdeg (inducedCoeff K μ) p hunr,
        CentralConductor.apply_baseChangeIdele_localUnit K μ p (AdelicLevel.uniformizerUnit ℚ p), Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [CentralConductor.localChar_map_uniformizerUnit K p w (hew w) μ (hunrw w), inducedCoeff,
        if_pos (hunrw w)]
      rfl
    rw [hνapply, mul_inv_eq_iff_eq_mul]
    exact Units.ext (by rw [Units.val_mul]; exact hval)

  have hνω₁ : ν = ω₁ :=
    HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq ℚ ν ω₁ hνicc hω₁.1 hνc hω₁.2.1 𝔣ν 𝔣₁
      hmodν hmod₁ hfin.toFinset hS
  have hωx : ∀ x, ω x = ω₁ x * μ (CentralConductor.baseChangeIdele K x) := fun x => by
    have h := hνapply x
    rw [hνω₁] at h
    exact mul_inv_eq_iff_eq_mul.1 h.symm

  have hexp : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ∃ a : ℕ,
      LanglandsTunnell.TateLocal.HasConductorExponentAt K 𝔓 (localChar μ 𝔓) a :=
    fun 𝔓 => exists_hasConductorExponentAt_of_continuous K 𝔓 _
      (continuous_localChar μ hμ.2.1 𝔓)

  refine exists_hasConductorExponentAt_le_of_forall_mem_higherUnitsAt ℚ v
    (localChar ω v) (inducedLevelAt K μ v) fun u hu => ?_
  have hω₁v : localChar ω₁ v u = 1 :=
    (hasConductorExponentAt_localChar_zero_of_isUnramifiedCharAt ℚ ω₁ v
      (hω₁p v fun h => hv ((CentralConductor.isBadPlace_one_iff K v).1 h)).1).1 u
      (LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ v (Nat.zero_le _) hu)
  show ω (Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v u)) = 1
  rw [hωx, CentralConductor.apply_baseChangeIdele_localUnit K μ v u]
  change localChar ω₁ v u * _ = 1
  rw [hω₁v, one_mul]
  exact Finset.prod_eq_one fun w _ =>
    CentralConductor.localChar_map_eq_one_of_mem_higherUnitsAt_inducedLevelAt K μ hexp v hv u hu w

end S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_le_inducedLevelAt_of_eulerCoeff_eq_inducedE3 (solution)
