-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f0342d95-2f49-53e9-9152-77ebdbfdf3f8

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal UnramifiedWhittaker
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace CENTCOND

theorem subsingleton_algebra_ringOfIntegers_rat (A : Type) [Ring A] :
    Subsingleton (Algebra (𝓞 ℚ) A) := by
  refine ⟨fun P Q => Algebra.algebra_ext P Q fun r => ?_⟩
  have key : ∀ f g : 𝓞 ℚ →+* A, f = g := by
    intro f g
    refine RingHom.ext fun x => ?_
    have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) :=
      Rat.ringOfIntegersEquiv.injective (by rw [map_intCast, Int.cast_id])
    rw [hx, map_intCast, map_intCast]
  exact RingHom.congr_fun (key (@algebraMap (𝓞 ℚ) A _ _ P) (@algebraMap (𝓞 ℚ) A _ _ Q)) r

theorem continuous_centralChar_of_form_ne_zero
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hF : X.form ≠ 0) :
    Continuous ⇑X.centralChar := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, X.form g ≠ 0 := Function.ne_iff.mp hF
  have hsc : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀ := by
    have hdiag : Continuous fun a : AdeleRing (𝓞 ℚ) ℚ => Matrix.diagonal fun _ : Fin 3 => a :=
      (continuous_pi fun _ : Fin 3 => continuous_id).matrix_diagonal
    have hs : Continuous ((Matrix.scalar (Fin 3)).toMonoidHom :
        AdeleRing (𝓞 ℚ) ℚ → Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
      hdiag.congr fun a => (Matrix.scalar_apply a).symm
    have h1 : Continuous (centralScalarGL 3 (𝓞 ℚ) ℚ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → AdelicGL 3 (𝓞 ℚ) ℚ) :=
      Continuous.units_map _ hs
    exact h1.mul continuous_const
  have hval : Continuous fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z : ℂˣ) : ℂ) := by
    have heq : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((X.centralChar z : ℂˣ) : ℂ)) =
        fun z => X.form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g₀) / X.form g₀ := by
      funext z
      rw [hX.central z g₀, mul_div_cancel_right₀ _ hg₀]
    rw [heq]
    exact (hcont.comp hsc).div_const _
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have hinv : (fun z : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (((X.centralChar z)⁻¹ : ℂˣ) : ℂ)) =
      fun z => ((X.centralChar z⁻¹ : ℂˣ) : ℂ) := by
    funext z
    rw [map_inv]
  rw [hinv]
  exact hval.comp continuous_inv

theorem le_of_hasConductorExponentAt_of_forall (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (b L : ℕ) (hb : HasConductorExponentAt F v χ b)
    (hL : ∀ u ∈ higherUnitsAt F v L, χ u = 1) : b ≤ L := by
  by_contra h
  obtain ⟨u, hu, hne⟩ := hb.2 L (Nat.lt_of_not_le h)
  exact hne (hL u hu)

end CENTCOND

open CENTCOND in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v} X)
    (hcont : Continuous X.form) (hF : X.form ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hKv : ¬ IsRamifiedIn K v) :
    ∃ a ≤ inducedLevelAt K μ v,
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (NumberField.TateGlobal.localChar X.centralChar v) a := by
  classical
  haveI := subsingleton_algebra_ringOfIntegers_rat (𝓞 K)
  obtain rfl : ‹Algebra (𝓞 ℚ) (𝓞 K)› = NumberField.inst_ringOfIntegersAlgebra ℚ K := Subsingleton.elim _ _
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 ℚ) (𝓞 K)

  obtain ⟨η, hη0, -, hωeq⟩ :=
    LanglandsTunnell.CubicInduction.exists_localChar_centralChar_eq_finprod_mul_of_not_isRamifiedIn_of_isCubicInductionDataOn
      K hdeg ψ μ hμ pins X hX hcont hF v hKv

  obtain ⟨b, hb⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous ℚ v
    (localChar X.centralChar v)
    (NumberField.TateGlobal.continuous_localChar X.centralChar
      (continuous_centralChar_of_form_ne_zero K ψ μ pins X hX hcont hF) v)
  refine ⟨b, ?_, hb⟩
  apply le_of_hasConductorExponentAt_of_forall ℚ v _ b _ hb
  intro u hu

  have hunit : ∀ w : v.Extension (𝓞 K),
      localChar μ w.1 (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom u) = 1 := by
    intro w
    have hw : w.1 ∈ primeFibre ℚ K v := w.2

    obtain ⟨a, ha⟩ := LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous K w.1 (localChar μ w.1)
      (NumberField.TateGlobal.continuous_localChar μ hμ.2.1 w.1)
    have haL : a ≤ inducedLevelAt K μ v := by
      have hfin : (primeFibre ℚ K v).Finite := by
        have hfin' : (Ideal.primesOver v.asIdeal (𝓞 K)).Finite := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
        refine (hfin'.preimage (f := fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.asIdeal)
          (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
        intro 𝔓 h𝔓
        rw [mem_primeFibre] at h𝔓
        refine ⟨𝔓.isPrime, ⟨?_⟩⟩
        rw [← h𝔓]
        rfl
      haveI : w.1.asIdeal.LiesOver v.asIdeal :=
        ⟨(congrArg HeightOneSpectrum.asIdeal ((mem_primeFibre ℚ v w.1).mp hw)).symm⟩
      have hf : 1 ≤ v.asIdeal.inertiaDeg' w.1.asIdeal := Ideal.inertiaDeg'_pos _ _
      unfold inducedLevelAt
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
      calc a = 1 * a := (one_mul a).symm
        _ ≤ v.asIdeal.inertiaDeg' w.1.asIdeal * LanglandsTunnell.TateLocal.conductorExponentAt K w.1 (localChar μ w.1) := by
          rw [LanglandsTunnell.TateLocal.conductorExponentAt_eq_of_hasConductorExponentAt K w.1 ha]
          exact Nat.mul_le_mul_right a hf
        _ ≤ ∑ 𝔓 ∈ hfin.toFinset, v.asIdeal.inertiaDeg' 𝔓.asIdeal *
              LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓) :=
          Finset.single_le_sum (f := fun 𝔓 => v.asIdeal.inertiaDeg' 𝔓.asIdeal *
              LanglandsTunnell.TateLocal.conductorExponentAt K 𝔓 (localChar μ 𝔓)) (fun _ _ => Nat.zero_le _)
            (hfin.mem_toFinset.mpr hw)

    apply ha.1
    have hmono := LanglandsTunnell.TateLocal.higherUnitsAt_antitone K w.1 haL
    apply hmono
    obtain ⟨hu1, hu2⟩ := (LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff ℚ v).mp hu
    have he : (w.1.under (𝓞 ℚ)).asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
      rw [(mem_primeFibre ℚ v w.1).mp hw]
      by_contra hne
      exact hKv ⟨w.1, hw, hne⟩
    have hval : ∀ x : v.adicCompletion ℚ,
        Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) x) = Valued.v x := by
      intro x
      change Valued.v (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom ℚ K w x) = Valued.v x
      rw [IsDedekindDomain.HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom ℚ K w x, he, pow_one]
    refine (LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff K w.1).mpr ⟨?_, ?_⟩
    · change Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) (u : v.adicCompletion ℚ)) = 1
      rw [hval, hu1]
    · rcases hu2 with h0 | hle
      · exact Or.inl h0
      · right
        change Valued.v (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K) (u : v.adicCompletion ℚ) - 1) ≤ _
        rw [← map_one (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)), ← map_sub, hval]
        exact hle
  have hηu : η u = 1 := by
    apply hη0.1
    exact LanglandsTunnell.TateLocal.higherUnitsAt_antitone ℚ v (Nat.zero_le _) hu
  apply Units.ext
  rw [hωeq u, finprod_eq_one_of_forall_eq_one (fun w => by rw [hunit w, Units.val_one]), hηu, Units.val_one, one_mul]

end S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_hasConductorExponentAt_localChar_centralChar_le_inducedLevelAt_of_isCubicInductionDataOn (solution)
