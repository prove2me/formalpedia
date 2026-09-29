-- Prove2me | solution 1 for LanglandsTunnell.CubicLambda.exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/269f24de-9daf-5fec-aac8-f12eef1b87ec

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Frobenius
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.OrderOfElement
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Theorems.Thm_P2M_Dup_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen"
p2m_attr_erase "simp" "complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

section ReciprocityBlock

open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse AutomorphicForm
open scoped IsMulCommutative

section OnePlace

variable (L : Type) [Field L] [NumberField L]

private noncomputable def resolvent_locIdele (𝔮 : HeightOneSpectrum (𝓞 L)) (s : (𝔮.adicCompletion L)ˣ) :
    (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L 𝔮 s)

private theorem resolvent_uniformizerIdele_eq (𝔮 : HeightOneSpectrum (𝓞 L)) :
    uniformizerIdele L 𝔮 = resolvent_locIdele L 𝔮 (uniformizerUnit L 𝔮) := rfl

private theorem resolvent_localChar_eq (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 L))
    (t : (𝔮.adicCompletion L)ˣ) : localChar θ 𝔮 t = θ (resolvent_locIdele L 𝔮 t) := rfl

private theorem resolvent_isAdjuster_locIdele (𝔣 : Ideal (𝓞 L)) (𝔮 : HeightOneSpectrum (𝓞 L))
    (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) (s : (𝔮.adicCompletion L)ˣ) :
    IsAdjuster L 𝔣 (resolvent_locIdele L 𝔮 s) 1 := by
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · have hne : v ≠ 𝔮 := fun h => h𝔮 (h ▸ hv)
    simp only [map_one, inv_one, mul_one]
    show Valued.v (((localUnit (𝓞 L) L 𝔮 s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) = 1 ∧
      Valued.v (((localUnit (𝓞 L) L 𝔮 s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))
    rw [localUnit_apply_of_ne (𝓞 L) L 𝔮 s hne, sub_self, map_one, map_zero]
    exact ⟨rfl, zero_le'⟩
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one L τ rfl

private theorem resolvent_placeOrd_locIdele_of_ne (𝔮 : HeightOneSpectrum (𝓞 L)) (s : (𝔮.adicCompletion L)ˣ)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ 𝔮) :
    placeOrd L (projFin L (resolvent_locIdele L 𝔮 s)) w = 0 := by
  show -WithZero.log (Valued.v (((localUnit (𝓞 L) L 𝔮 s : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    FiniteAdeleRing (𝓞 L) L) w)) = 0
  rw [localUnit_apply_of_ne (𝓞 L) L 𝔮 s hw, map_one, WithZero.log_one, neg_zero]

private theorem resolvent_placeOrd_locIdele_self (𝔮 : HeightOneSpectrum (𝓞 L)) (s : (𝔮.adicCompletion L)ˣ) :
    placeOrd L (projFin L (resolvent_locIdele L 𝔮 s)) 𝔮 = -WithZero.log (Valued.v (s : 𝔮.adicCompletion L)) := by
  show -WithZero.log (Valued.v (((localUnit (𝓞 L) L 𝔮 s : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    FiniteAdeleRing (𝓞 L) L) 𝔮)) = _
  rw [localUnit_apply_self (𝓞 L) L 𝔮 s]

private theorem resolvent_valued_eq_one (𝔮 : HeightOneSpectrum (𝓞 L)) (t : (𝔮.adicCompletion L)ˣ)
    (ht : (t : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L)
    (ht' : ((t⁻¹ : (𝔮.adicCompletion L)ˣ) : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L) :
    Valued.v (t : 𝔮.adicCompletion L) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht ht'
  have hmul : Valued.v (t : 𝔮.adicCompletion L) * Valued.v ((t⁻¹ : (𝔮.adicCompletion L)ˣ) : 𝔮.adicCompletion L)
      = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine le_antisymm ht ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (t : 𝔮.adicCompletion L) *
          Valued.v ((t⁻¹ : (𝔮.adicCompletion L)ˣ) : 𝔮.adicCompletion L) := hmul.symm
    _ ≤ Valued.v (t : 𝔮.adicCompletion L) * 1 := mul_le_mul_right ht' _
    _ = Valued.v (t : 𝔮.adicCompletion L) := mul_one _

end OnePlace

section Frobenius

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]
  [IsMulCommutative (E ≃ₐ[L] E)]

private theorem resolvent_map_locIdele (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) (s : (𝔮.adicCompletion L)ˣ) :
    r (resolvent_locIdele L 𝔮 s) = artinFrob L E 𝔮 ^ (-WithZero.log (Valued.v (s : 𝔮.adicCompletion L))) := by
  rw [hiv _ (resolvent_isAdjuster_locIdele L 𝔣 𝔮 h𝔮 s),
    finprod_eq_single
      (fun v : HeightOneSpectrum (𝓞 L) => artinFrob L E v ^ placeOrd L (projFin L (resolvent_locIdele L 𝔮 s)) v)
      𝔮 (fun w hw => by
        show artinFrob L E w ^ placeOrd L (projFin L (resolvent_locIdele L 𝔮 s)) w = 1
        rw [resolvent_placeOrd_locIdele_of_ne L 𝔮 s hw, zpow_zero]),
    resolvent_placeOrd_locIdele_self]

private theorem resolvent_map_locIdele_eq_one (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) (t : (𝔮.adicCompletion L)ˣ)
    (ht : Valued.v (t : 𝔮.adicCompletion L) = 1) :
    r (resolvent_locIdele L 𝔮 t) = 1 := by
  rw [resolvent_map_locIdele L E r 𝔣 hiv 𝔮 h𝔮 t, ht, WithZero.log_one, neg_zero, zpow_zero]

private theorem resolvent_map_uniformizerIdele (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) :
    r (uniformizerIdele L 𝔮) = artinFrob L E 𝔮 := by
  rw [resolvent_uniformizerIdele_eq, resolvent_map_locIdele L E r 𝔣 hiv 𝔮 h𝔮, valued_uniformizerUnit,
    WithZero.log_exp, neg_neg, zpow_one]

private theorem resolvent_isUnramifiedCharAt (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) :
    IsUnramifiedCharAt (ψ.comp r) 𝔮 := by
  intro t ht ht'
  rw [resolvent_localChar_eq, MonoidHom.comp_apply,
    resolvent_map_locIdele_eq_one L E r 𝔣 hiv 𝔮 h𝔮 t (resolvent_valued_eq_one L 𝔮 t ht ht'), map_one]

private theorem resolvent_eulerCoeff_eq (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) :
    LanglandsTunnell.CubicLambda.eulerCoeff L (ψ.comp r) 𝔮 = ((ψ (artinFrob L E 𝔮) : ℂˣ) : ℂ) := by
  rw [LanglandsTunnell.CubicLambda.eulerCoeff, if_pos (resolvent_isUnramifiedCharAt L E r 𝔣 hiv ψ 𝔮 h𝔮),
    MonoidHom.comp_apply, resolvent_map_uniformizerIdele L E r 𝔣 hiv 𝔮 h𝔮]

end Frobenius

section Archimedean

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]
  [IsMulCommutative (E ≃ₐ[L] E)]

private theorem resolvent_archSign_mul_self (u : InfinitePlace L) (x : (u.Completion)ˣ) (τ : L →+* ℝ) :
    archSign L τ (archUnitHom u (x * x)) := by
  classical
  show (0 : ℝ) < NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf L τ)
    (Function.update (1 : InfiniteAdeleRing L) u ((x * x : (u.Completion)ˣ) : u.Completion) (placeOf L τ))
  by_cases h : placeOf L τ = u
  · subst h
    rw [Function.update_self, Units.val_mul, map_mul]
    exact mul_self_pos.mpr ((RingEquiv.map_ne_zero_iff _).mpr x.ne_zero)
  · rw [Function.update_of_ne h, show ((1 : InfiniteAdeleRing L) (placeOf L τ)) = 1 from rfl, map_one]
    exact zero_lt_one

private theorem resolvent_isAdjuster_arch_mul_self (𝔣 : Ideal (𝓞 L)) (u : InfinitePlace L) (x : (u.Completion)ˣ) :
    IsAdjuster L 𝔣 (archUnitHom u (x * x)) 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    show Valued.v ((1 : FiniteAdeleRing (𝓞 L) L) v) = 1 ∧
      Valued.v ((1 : FiniteAdeleRing (𝓞 L) L) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ))
    rw [fad_one_apply, sub_self, map_one, map_zero]
    exact ⟨rfl, zero_le'⟩
  · simp only [map_one, inv_one, mul_one]
    exact resolvent_archSign_mul_self L u x τ

private theorem resolvent_placeOrd_arch (u : InfinitePlace L) (y : (u.Completion)ˣ) (v : HeightOneSpectrum (𝓞 L)) :
    placeOrd L (projFin L (archUnitHom u y)) v = 0 := by
  show -WithZero.log (Valued.v ((1 : FiniteAdeleRing (𝓞 L) L) v)) = 0
  rw [fad_one_apply, map_one, WithZero.log_one, neg_zero]

private theorem resolvent_eq_one_of_sq_of_cube {G : Type*} [Group G] (g : G) (h2 : g ^ 2 = 1) (h3 : g ^ 3 = 1) :
    g = 1 := by
  have h : g ^ 3 = g ^ 2 * g := pow_succ g 2
  rw [h2, one_mul, h3] at h
  exact h.symm

private theorem resolvent_map_arch_eq_one (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (hexp : ∀ g : E ≃ₐ[L] E, g ^ 3 = 1) (u : InfinitePlace L) (x : (u.Completion)ˣ) :
    r (archUnitHom u x) = 1 := by
  refine resolvent_eq_one_of_sq_of_cube _ ?_ (hexp _)
  rw [pow_two, ← map_mul, ← map_mul, hiv _ (resolvent_isAdjuster_arch_mul_self L 𝔣 u x)]
  exact finprod_eq_one_of_forall_eq_one fun v => by rw [resolvent_placeOrd_arch, zpow_zero]

private theorem resolvent_isArchCompAt (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (hexp : ∀ g : E ≃ₐ[L] E, g ^ 3 = 1) (ψ : (E ≃ₐ[L] E) →* ℂˣ) (u : InfinitePlace L) :
    IsArchCompAt L (ψ.comp r) u 0 0 := by
  intro x
  rw [mul_zero, Complex.cpow_zero, zpow_zero, mul_one]
  show (((ψ.comp r) (archUnitHom u x) : ℂˣ) : ℂ) = 1
  rw [MonoidHom.comp_apply, resolvent_map_arch_eq_one L E r 𝔣 hiv hexp u x, map_one, Units.val_one]

private theorem resolvent_isArchCompAt_zmod (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (hexp : ∀ g : E ≃ₐ[L] E, g ^ 3 = 1) (ψ : (E ≃ₐ[L] E) →* ℂˣ) (u : InfinitePlace L) :
    IsArchCompAt L (ψ.comp r) u 0 (((0 : ZMod 2)).val : ℤ) := by
  rw [ZMod.val_zero, Nat.cast_zero]
  exact resolvent_isArchCompAt L E r 𝔣 hiv hexp ψ u

end Archimedean

section CharacterPlain

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]

private theorem resolvent_isIdeleClassChar (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E))
    (hi : M4aHerbrand.principalIdeles (𝓞 L) L ≤ r.ker) (ψ : (E ≃ₐ[L] E) →* ℂˣ) :
    IsIdeleClassChar (𝓞 L) L (ψ.comp r) := by
  intro a
  have h : Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a ∈ r.ker :=
    hi (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  rw [MonoidHom.mem_ker] at h
  rw [MonoidHom.comp_apply]
  exact (congrArg ψ h).trans (map_one ψ)

private theorem resolvent_isOfFinOrder (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E))
    (hexp : ∀ g : E ≃ₐ[L] E, g ^ 3 = 1) (ψ : (E ≃ₐ[L] E) →* ℂˣ) : IsOfFinOrder (ψ.comp r) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, MonoidHom.ext fun a => by
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, hexp, map_one, MonoidHom.one_apply]⟩

end CharacterPlain

section Character

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]
  [IsMulCommutative (E ≃ₐ[L] E)]

private theorem resolvent_unitIdeles_le_ker (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v) :
    unitIdeles L 𝔣 ≤ r.ker := by
  intro a ha
  obtain ⟨hunit, hcong, hsign⟩ := ha
  have hadj : IsAdjuster L 𝔣 a 1 := by
    refine ⟨fun v hv => ?_, fun τ => ?_⟩
    · simp only [map_one, inv_one, mul_one]
      exact ⟨hunit v, hcong v hv⟩
    · simp only [map_one, inv_one, mul_one]
      exact hsign τ
  rw [MonoidHom.mem_ker, hiv a hadj]
  exact finprod_eq_one_of_forall_eq_one fun v => by
    rw [(placeOrd_eq_zero_iff L (projFin L a) v).mpr (hunit v), zpow_zero]

private theorem resolvent_continuous_of_nhds (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (S : Set (AdeleRing (𝓞 L) L)ˣ)
    (hS : S ∈ nhds (1 : (AdeleRing (𝓞 L) L)ˣ)) (hθ : ∀ a ∈ S, θ a = 1) : Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  rw [ContinuousAt, map_one]
  exact tendsto_const_nhds.congr' (Filter.mem_of_superset hS fun a ha => (hθ a ha).symm)

private theorem resolvent_continuous (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (hnhds : ((unitIdeles L 𝔣 : Subgroup (AdeleRing (𝓞 L) L)ˣ) : Set (AdeleRing (𝓞 L) L)ˣ) ∈
      nhds (1 : (AdeleRing (𝓞 L) L)ˣ))
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) : Continuous (ψ.comp r) :=
  resolvent_continuous_of_nhds L (ψ.comp r) _ hnhds fun a ha => by
    have h : a ∈ r.ker := resolvent_unitIdeles_le_ker L E r 𝔣 hiv ha
    rw [MonoidHom.mem_ker] at h
    rw [MonoidHom.comp_apply, h, map_one]

end Character

section Psi

private theorem resolvent_exists_injective_char {G : Type*} [Group G] (p : ℕ) (hp : p.Prime)
    (hG : Nat.card G = p) : ∃ ψ : G →* ℂˣ, Function.Injective ψ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hζu : IsPrimitiveRoot (hζ.isUnit hp.ne_zero).unit p := hζ.isUnit_unit hp.ne_zero
  have hcard : Nat.card (Subgroup.zpowers (hζ.isUnit hp.ne_zero).unit) = p := by
    rw [Nat.card_zpowers, ← hζu.eq_orderOf]
  let e : G ≃* Subgroup.zpowers (hζ.isUnit hp.ne_zero).unit := mulEquivOfPrimeCardEq hG hcard
  exact ⟨(Subgroup.zpowers (hζ.isUnit hp.ne_zero).unit).subtype.comp e.toMonoidHom,
    fun a b h => e.injective (Subtype.ext h)⟩

end Psi

section Transfer

variable {G H : Type*} [Group G] [Group H]

private theorem resolvent_orderOf_map_eq (r₀ r₁ : G →* H) (hker : r₀.ker = r₁.ker) (x : G) :
    orderOf (r₀ x) = orderOf (r₁ x) :=
  orderOf_eq_orderOf_iff.mpr fun n => by
    rw [← map_pow, ← map_pow, ← MonoidHom.mem_ker, ← MonoidHom.mem_ker, hker]

private theorem resolvent_map_eq_one_of_ker_eq (r₀ r₁ : G →* H) (hker : r₀.ker = r₁.ker) {x : G}
    (hx : r₁ x = 1) : r₀ x = 1 := by
  rw [← MonoidHom.mem_ker, hker, MonoidHom.mem_ker]
  exact hx

private theorem resolvent_map_eq_inv_of_ker_eq (r₀ r₁ : G →* H) (hker : r₀.ker = r₁.ker) {x y : G}
    (hxy : r₁ y = (r₁ x)⁻¹) : r₀ y = (r₀ x)⁻¹ := by
  have h : r₀ (y * x) = 1 := by
    refine resolvent_map_eq_one_of_ker_eq r₀ r₁ hker ?_
    rw [map_mul, hxy, inv_mul_cancel]
  rw [map_mul] at h
  exact eq_inv_of_mul_eq_one_left h

private theorem resolvent_isPrimitiveRoot (ψ : G →* ℂˣ) (hψ : Function.Injective ψ) (g : G) :
    IsPrimitiveRoot ((ψ g : ℂˣ) : ℂ) (orderOf g) := by
  rw [← orderOf_injective ψ hψ g]
  exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.orderOf (ψ g))

end Transfer

section UnitIdelesNhds

variable (L : Type) [Field L] [NumberField L]

private theorem resolvent_isOpen_realPos :
    IsOpen {u : (AdeleRing (𝓞 L) L)ˣ | ∀ w : {w : InfinitePlace L // w.IsReal},
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((u : AdeleRing (𝓞 L) L).1 w.1)} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun w => ?_
  have hc : Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((u : AdeleRing (𝓞 L) L).1 w.1) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
      ((NumberField.AdelicLevel.continuous_archEval L w.1).comp
        ((NumberField.AdelicLevel.continuous_adeleArch (𝓞 L) L).comp Units.continuous_val))
  exact isOpen_lt continuous_const hc

private theorem resolvent_valued_eq_one_of_integral (u : (AdeleRing (𝓞 L) L)ˣ)
    (hint : (u : AdeleRing (𝓞 L) L).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L)
    (hinv : ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
      ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L)
    (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1 := by
  have hx := NumberField.AdelicLevel.valued_apply_le_one hint v
  have hy := NumberField.AdelicLevel.valued_apply_le_one hinv v
  have hmul : (u : AdeleRing (𝓞 L) L).2 v * ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v = 1 :=
    congrArg (fun x : AdeleRing (𝓞 L) L => x.2 v) u.mul_inv
  have hvmul : Valued.v ((u : AdeleRing (𝓞 L) L).2 v)
      * Valued.v (((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm hx ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((u : AdeleRing (𝓞 L) L).2 v)
          * Valued.v (((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 v) := hvmul.symm
    _ ≤ Valued.v ((u : AdeleRing (𝓞 L) L).2 v) * 1 := mul_le_mul_right hy _
    _ = Valued.v ((u : AdeleRing (𝓞 L) L).2 v) := mul_one _

private theorem resolvent_unitIdeles_mem_nhds (𝔣 : Ideal (𝓞 L)) (h𝔣 : 𝔣 ≠ ⊥) :
    ((unitIdeles L 𝔣 : Subgroup (AdeleRing (𝓞 L) L)ˣ) : Set (AdeleRing (𝓞 L) L)ˣ) ∈
      nhds (1 : (AdeleRing (𝓞 L) L)ˣ) := by
  let U : Set (AdeleRing (𝓞 L) L)ˣ :=
    {u | ∀ w : {w : InfinitePlace L // w.IsReal},
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((u : AdeleRing (𝓞 L) L).1 w.1)} ∩
      ({u | (u : AdeleRing (𝓞 L) L).2 - 1 ∈ NumberField.AdelicLevel.idealBall (𝓞 L) L 𝔣} ∩
        {u | ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
          ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L})
  have hopen : IsOpen U := by
    refine (resolvent_isOpen_realPos L).inter (IsOpen.inter ?_ ?_)
    · have hc : Continuous fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L).2 - 1 :=
        ((NumberField.AdelicLevel.continuous_adeleFin (𝓞 L) L).comp Units.continuous_val).sub
          continuous_const
      exact (NumberField.AdelicLevel.isOpen_idealBall (𝓞 L) L h𝔣).preimage hc
    · have hc : Continuous fun u : (AdeleRing (𝓞 L) L)ˣ =>
          ((u⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 :=
        (NumberField.AdelicLevel.continuous_adeleFin (𝓞 L) L).comp Units.continuous_coe_inv
      exact (NumberField.AdelicLevel.isOpen_integralFiniteAdeles (𝓞 L) L).preimage hc
  have hone : (1 : (AdeleRing (𝓞 L) L)ˣ) ∈ U := by
    refine ⟨fun w => ?_, ?_, ?_⟩
    · rw [show ((1 : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 w.1 = 1 from rfl, map_one]
      exact one_pos
    · show ((1 : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 - 1 ∈ NumberField.AdelicLevel.idealBall (𝓞 L) L 𝔣
      rw [show ((1 : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1 from rfl, sub_self]
      exact NumberField.AdelicLevel.zero_mem_idealBall 𝔣
    · show (((1 : (AdeleRing (𝓞 L) L)ˣ)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
        ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L
      rw [show (((1 : (AdeleRing (𝓞 L) L)ˣ)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 = 1 from rfl]
      exact NumberField.AdelicLevel.one_mem_integralFiniteAdeles
  have hsub : U ⊆ ((unitIdeles L 𝔣 : Subgroup (AdeleRing (𝓞 L) L)ˣ) : Set (AdeleRing (𝓞 L) L)ˣ) := by
    rintro u ⟨hpos, hball, hinv⟩
    have hint : (u : AdeleRing (𝓞 L) L).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
      have h := NumberField.AdelicLevel.add_mem_integralFiniteAdeles
        (NumberField.AdelicLevel.idealBall_subset_integralFiniteAdeles 𝔣 hball)
        (NumberField.AdelicLevel.one_mem_integralFiniteAdeles (R := 𝓞 L) (K := L))
      rwa [sub_add_cancel] at h
    have hunit : ∀ v : HeightOneSpectrum (𝓞 L),
        Valued.v (((projFin L u : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v) = 1 :=
      fun v => resolvent_valued_eq_one_of_integral L u hint hinv v
    have hcong : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ 𝔣 →
        Valued.v (((projFin L u : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) v - 1)
          ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by
      intro v _
      have h := hball v
      rw [NumberField.AdelicLevel.coe_sub_apply, NumberField.AdelicLevel.coe_one_apply,
        NumberField.AdelicLevel.idealBound_of_ne_bot h𝔣] at h
      exact h
    have hsign : ∀ τ : L →+* ℝ, archSign L τ u := by
      intro τ
      show 0 < archRealProjTau L τ u
      unfold archRealProjTau
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
      exact hpos ⟨placeOf L τ, isReal_placeOf L τ⟩
    exact And.intro hunit (And.intro hcong hsign)
  exact Filter.mem_of_superset (hopen.mem_nhds hone) hsub

end UnitIdelesNhds

section Wrappers

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]
  [IsMulCommutative (E ≃ₐ[L] E)]

private theorem resolvent_isPrimitiveRoot_eulerCoeff (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) (hψ : Function.Injective ψ) (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) :
    IsPrimitiveRoot (LanglandsTunnell.CubicLambda.eulerCoeff L (ψ.comp r) 𝔮) (orderOf (artinFrob L E 𝔮)) := by
  rw [resolvent_eulerCoeff_eq L E r 𝔣 hiv ψ 𝔮 h𝔮]
  exact resolvent_isPrimitiveRoot ψ hψ (artinFrob L E 𝔮)

private theorem resolvent_eulerCoeff_eq_inv (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E)) (𝔣 : Ideal (𝓞 L))
    (hiv : ∀ u : (AdeleRing (𝓞 L) L)ˣ, IsAdjuster L 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 L), artinFrob L E v ^ placeOrd L (projFin L u) v)
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)) (h𝔮 : ¬ 𝔮.asIdeal ∣ 𝔣) (h𝔮' : ¬ 𝔮'.asIdeal ∣ 𝔣)
    (hF : artinFrob L E 𝔮' = (artinFrob L E 𝔮)⁻¹) :
    LanglandsTunnell.CubicLambda.eulerCoeff L (ψ.comp r) 𝔮'
      = (LanglandsTunnell.CubicLambda.eulerCoeff L (ψ.comp r) 𝔮)⁻¹ := by
  rw [resolvent_eulerCoeff_eq L E r 𝔣 hiv ψ 𝔮 h𝔮, resolvent_eulerCoeff_eq L E r 𝔣 hiv ψ 𝔮' h𝔮', hF, map_inv,
    Units.val_inv_eq_inv_val]

end Wrappers

private theorem resolvent_eq_inv_of_eq_zero {a b : ℂ} (ha : a = 0) (hb : b = 0) : b = a⁻¹ := by
  rw [ha, hb, inv_zero]

private theorem resolvent_isFiniteOrderHeckeChar (L : Type) [Field L] [NumberField L]
    (θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (h₁ : IsIdeleClassChar (𝓞 L) L θ) (h₂ : Continuous θ) (h₃ : IsOfFinOrder θ) :
    IsFiniteOrderHeckeChar L θ :=
  ⟨h₁, h₂, h₃⟩

section Ramified

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E]

private theorem resolvent_eulerCoeff_eq_zero (r : (AdeleRing (𝓞 L) L)ˣ →* (E ≃ₐ[L] E))
    (hker : r.ker = M4aHerbrand.principalIdeles (𝓞 L) L ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange L E).idelicNorm.range)
    (ψ : (E ≃ₐ[L] E) →* ℂˣ) (hψ : Function.Injective ψ) (𝔮 : HeightOneSpectrum (𝓞 L)) (t : (𝔮.adicCompletion L)ˣ)
    (ht : (t : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L)
    (ht' : ((t⁻¹ : (𝔮.adicCompletion L)ˣ) : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L)
    (hnot : resolvent_locIdele L 𝔮 t ∉ M4aHerbrand.principalIdeles (𝓞 L) L ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange L E).idelicNorm.range) :
    LanglandsTunnell.CubicLambda.eulerCoeff L (ψ.comp r) 𝔮 = 0 := by
  rw [LanglandsTunnell.CubicLambda.eulerCoeff, if_neg]
  intro hunr
  have h1 := hunr t ht ht'
  rw [resolvent_localChar_eq, MonoidHom.comp_apply] at h1
  have h2 : r (resolvent_locIdele L 𝔮 t) = 1 := hψ (h1.trans (map_one ψ).symm)
  refine hnot ?_
  rw [← hker]
  exact MonoidHom.mem_ker.mpr h2

end Ramified

end ReciprocityBlock

section FrobeniusOrderBlock

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section FrobeniusOrder

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]

omit [NumberField E] [IsGalois L E] in
private theorem resolvent_under_primeAbove_isMaximal (𝔮 : HeightOneSpectrum (𝓞 L)) :
    ((primeAbove L E 𝔮).under (𝓞 L)).IsMaximal := by
  rw [under_primeAbove]
  exact 𝔮.isPrime.isMaximal 𝔮.ne_bot

omit [NumberField E] [IsGalois L E] in
private theorem resolvent_finite_quotient_under (𝔮 : HeightOneSpectrum (𝓞 L)) :
    Finite (𝓞 L ⧸ (primeAbove L E 𝔮).under (𝓞 L)) := by
  rw [under_primeAbove]
  exact Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot

private theorem resolvent_orderOf_artinFrob_eq_finrank (𝔮 : HeightOneSpectrum (𝓞 L))
    (hP : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥) :
    orderOf (artinFrob L E 𝔮)
      = Module.finrank (𝓞 L ⧸ (primeAbove L E 𝔮).under (𝓞 L)) (𝓞 E ⧸ primeAbove L E 𝔮) := by
  haveI := resolvent_under_primeAbove_isMaximal L E 𝔮
  haveI := resolvent_finite_quotient_under L E 𝔮
  haveI := Fintype.ofFinite (𝓞 L ⧸ (primeAbove L E 𝔮).under (𝓞 L))
  exact ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot hP
    ⟨artinFrob L E 𝔮, (isArithFrobAt_artinFrob L E 𝔮).mem_stabilizer⟩ (isArithFrobAt_artinFrob L E 𝔮)

end FrobeniusOrder

end FrobeniusOrderBlock

section RamificationDictionary

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]

attribute [local instance] Ideal.Quotient.field

private theorem cubic_inertia_primeAbove_eq_bot_iff (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : Ideal (𝓞 E))
    [𝔔.IsMaximal] (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥ ↔ 𝔮.asIdeal.ramificationIdx' 𝔔 = 1 := by
  haveI : 𝔔.LiesOver 𝔮.asIdeal := ⟨h𝔔.symm⟩
  haveI : Finite (𝓞 L ⧸ 𝔮.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot
  rw [Subgroup.eq_bot_iff_card,
    Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[L] E) 𝔮.asIdeal (primeAbove L E 𝔮),
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮.asIdeal 𝔔 (E ≃ₐ[L] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal 𝔔 𝔮.ne_bot]

private theorem cubic_inertia_primeAbove_ne_bot_iff (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : Ideal (𝓞 E))
    [𝔔.IsMaximal] (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) ≠ ⊥ ↔ 𝔮.asIdeal.ramificationIdx' 𝔔 ≠ 1 :=
  (cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 𝔔 h𝔔).not

private theorem cubic_inertia_eq_bot_iff_of_under_eq (𝔮 : HeightOneSpectrum (𝓞 L)) (Q 𝔔 : Ideal (𝓞 E))
    [Q.IsMaximal] [𝔔.IsMaximal] (hQ : Q.under (𝓞 L) = 𝔮.asIdeal) (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    Q.inertia (E ≃ₐ[L] E) = ⊥ ↔ 𝔮.asIdeal.ramificationIdx' 𝔔 = 1 := by
  haveI : Q.LiesOver 𝔮.asIdeal := ⟨hQ.symm⟩
  haveI : 𝔔.LiesOver 𝔮.asIdeal := ⟨h𝔔.symm⟩
  haveI : Finite (𝓞 L ⧸ 𝔮.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot
  rw [Subgroup.eq_bot_iff_card,
    Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[L] E) 𝔮.asIdeal Q,
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮.asIdeal 𝔔 (E ≃ₐ[L] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal 𝔔 𝔮.ne_bot]

private theorem cubic_ramificationIdx_ne_one_of_exists_inertia_ne_bot (𝔮 : HeightOneSpectrum (𝓞 L))
    (hex : ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧ Q.LiesOver 𝔮.asIdeal ∧ Q.inertia (E ≃ₐ[L] E) ≠ ⊥)
    (𝔔 : Ideal (𝓞 E)) [𝔔.IsMaximal] (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    𝔮.asIdeal.ramificationIdx' 𝔔 ≠ 1 := by
  obtain ⟨Q, hQp, hQl, hQi⟩ := hex
  haveI : Q.LiesOver 𝔮.asIdeal := hQl
  haveI : Q.IsMaximal := hQp.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔮.ne_bot Q)
  intro h1
  exact hQi ((cubic_inertia_eq_bot_iff_of_under_eq L E 𝔮 Q 𝔔 (Ideal.over_def Q 𝔮.asIdeal).symm h𝔔).mpr h1)

private theorem cubic_ramificationIdx_primeAbove_eq (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : Ideal (𝓞 E))
    [𝔔.IsMaximal] (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    𝔮.asIdeal.ramificationIdx' (primeAbove L E 𝔮) = 𝔮.asIdeal.ramificationIdx' 𝔔 := by
  haveI : 𝔔.LiesOver 𝔮.asIdeal := ⟨h𝔔.symm⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal (primeAbove L E 𝔮) 𝔮.ne_bot,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal 𝔔 𝔮.ne_bot]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup 𝔮.asIdeal (primeAbove L E 𝔮) 𝔔 (E ≃ₐ[L] E)

private theorem cubic_inertiaDeg_primeAbove_eq (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : Ideal (𝓞 E))
    [𝔔.IsMaximal] (h𝔔 : 𝔔.under (𝓞 L) = 𝔮.asIdeal) :
    𝔮.asIdeal.inertiaDeg' (primeAbove L E 𝔮) = 𝔮.asIdeal.inertiaDeg' 𝔔 := by
  haveI : 𝔔.LiesOver 𝔮.asIdeal := ⟨h𝔔.symm⟩
  rw [Ideal.inertiaDeg'_eq_inertiaDeg (p := 𝔮.asIdeal) (q := primeAbove L E 𝔮),
    Ideal.inertiaDeg'_eq_inertiaDeg (p := 𝔮.asIdeal) (q := 𝔔)]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔮.asIdeal (primeAbove L E 𝔮) 𝔔 (E ≃ₐ[L] E)

omit [NumberField E] [IsGalois L E] in

private theorem cubic_inertiaDeg_primeAbove_eq_finrank (𝔮 : HeightOneSpectrum (𝓞 L)) :
    𝔮.asIdeal.inertiaDeg' (primeAbove L E 𝔮) =
      Module.finrank (𝓞 L ⧸ (primeAbove L E 𝔮).under (𝓞 L)) (𝓞 E ⧸ primeAbove L E 𝔮) := by
  rw [← Ideal.inertiaDeg_algebraMap ((primeAbove L E 𝔮).under (𝓞 L)) (primeAbove L E 𝔮),
    under_primeAbove L E 𝔮]

omit [NumberField E] [IsGalois L E] in

private theorem cubic_exists_admissibleModulus_dvd_not_dvd (𝔣₀ : Ideal (𝓞 L)) (h₀ : IsAdmissibleModulus L E 𝔣₀)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥) :
    ∃ 𝔣 : Ideal (𝓞 L), IsAdmissibleModulus L E 𝔣 ∧ 𝔣 ∣ 𝔣₀ ∧ ¬ 𝔮.asIdeal ∣ 𝔣 := by
  unfold IsAdmissibleModulus at h₀ ⊢
  obtain ⟨hne, hram⟩ := h₀
  have hne0 : 𝔣₀ ≠ 0 := hne
  obtain ⟨n, 𝔣, hndvd, hfac⟩ := WfDvdMonoid.max_power_factor' hne0 𝔮.prime.not_unit
  refine ⟨𝔣, ⟨?_, ?_⟩, Dvd.intro_left _ hfac.symm, hndvd⟩
  · rintro rfl
    exact hne (by rw [hfac, Ideal.mul_bot])
  · intro v hv
    have hvq : v ≠ 𝔮 := by
      rintro rfl
      exact hv h𝔮
    have hnd : ¬ v.asIdeal ∣ 𝔮.asIdeal ^ n := fun hd => by
      have hle : 𝔮.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd (v.prime.dvd_of_dvd_pow hd)
      exact hvq (HeightOneSpectrum.ext (𝔮.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)
    have hv₀ := hram v hv
    rw [hfac] at hv₀
    exact v.prime.pow_dvd_of_dvd_mul_left _ hnd hv₀

end RamificationDictionary

section ModulusSupport

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]

private theorem cubic_not_dvd_of_inertia_eq_bot (𝔣 : Ideal (𝓞 L))
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ 𝔣 →
      ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧ Q.inertia (E ≃ₐ[L] E) ≠ ⊥)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (hunr : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥) :
    ¬ 𝔮.asIdeal ∣ 𝔣 := fun hdvd =>
  cubic_ramificationIdx_ne_one_of_exists_inertia_ne_bot L E 𝔮 (hsupp 𝔮 hdvd) (primeAbove L E 𝔮)
    (under_primeAbove L E 𝔮)
    ((cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 (primeAbove L E 𝔮) (under_primeAbove L E 𝔮)).mp hunr)

end ModulusSupport

section PrimeDegreeCharacter

open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin
open NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse AutomorphicForm
open scoped IsMulCommutative

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]

private theorem primeDegree_aut_order : Nat.card (F ≃ₐ[E] F) = Module.finrank E F := by
  rw [IsGalois.card_aut_eq_finrank]

private theorem primeDegree_isMulCommutative_aut (hℓ : (Module.finrank E F).Prime) :
    IsMulCommutative (F ≃ₐ[E] F) := by
  haveI : Fact (Module.finrank E F).Prime := ⟨hℓ⟩
  haveI : IsCyclic (F ≃ₐ[E] F) := isCyclic_of_prime_card (primeDegree_aut_order E F)
  infer_instance

private theorem primeDegree_aut_pow (σ : F ≃ₐ[E] F) : σ ^ Module.finrank E F = 1 := by
  rw [← primeDegree_aut_order E F]
  exact pow_card_eq_one'

private theorem primeDegree_comp_pow (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F)) (ψ : (F ≃ₐ[E] F) →* ℂˣ) :
    (ψ.comp r) ^ Module.finrank E F = 1 :=
  MonoidHom.ext fun a => by
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, primeDegree_aut_pow, map_one, MonoidHom.one_apply]

private theorem primeDegree_isOfFinOrder (hℓ : (Module.finrank E F).Prime) (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (ψ : (F ≃ₐ[E] F) →* ℂˣ) : IsOfFinOrder (ψ.comp r) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨Module.finrank E F, hℓ.pos, primeDegree_comp_pow E F r ψ⟩

end PrimeDegreeCharacter

open IsDedekindDomain NumberField HeckeCharacter
open LanglandsTunnell.P2.Artin NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.Converse AutomorphicForm
open scoped IsMulCommutative

open M4aHerbrand M4aHerbrand.GenuineDescent

open LanglandsTunnell.CubicLambda in

theorem solution
    (E : Type) [Field E] [NumberField E] (F : Type) [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)] (hℓ : (Module.finrank E F).Prime) :
    ∃ ψ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsFiniteOrderHeckeChar E ψ ∧ ψ ^ Module.finrank E F = 1 ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 E)) (𝔔 : HeightOneSpectrum (𝓞 F)), 𝔔.under (𝓞 E) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff E ψ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff E ψ 𝔮 = 0)) ∧
      ∃ (𝔣 : Ideal (𝓞 E)) (_ : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
        (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F)) (χ : (F ≃ₐ[E] F) →* ℂˣ),
        principalIdeles (𝓞 E) E ≤ r.ker ∧
        r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range ∧
        Function.Surjective r ∧
        (∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
          r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v) ∧
        Function.Injective χ ∧ ψ = χ.comp r := by
  obtain ⟨ψ, hψ⟩ := resolvent_exists_injective_char (Module.finrank E F) hℓ (primeDegree_aut_order E F)
  obtain ⟨𝔣₀, hadm₀, hsupp₀⟩ := LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported E F
  obtain ⟨𝔣, -, hsub, hadm⟩ :=
    LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F 𝔣₀ hadm₀.1
      (fun v hv => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _)) (hadm₀.2 v hv)) (Module.finrank E F)
  have hsupp : ∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣 →
      ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧ Q.inertia (F ≃ₐ[E] F) ≠ ⊥ :=
    fun v hv => hsupp₀ v (hsub v hv)
  obtain ⟨r, hi, hker, hsurj, hiv⟩ :=
    exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E F 𝔣 hadm
  refine ⟨ψ.comp r, resolvent_isFiniteOrderHeckeChar E _ (resolvent_isIdeleClassChar E F r hi ψ)
    (resolvent_continuous E F r 𝔣 hiv (resolvent_unitIdeles_mem_nhds E 𝔣 hadm.1) ψ)
    (primeDegree_isOfFinOrder E F hℓ r ψ), primeDegree_comp_pow E F r ψ, ?_,
    𝔣, hadm, r, ψ, hi, hker, hsurj, hiv, hψ, rfl⟩
  intro 𝔮 𝔔 h𝔔
  have h𝔔' : 𝔔.asIdeal.under (𝓞 E) = 𝔮.asIdeal := congrArg HeightOneSpectrum.asIdeal h𝔔
  haveI := 𝔔.isMaximal
  refine ⟨fun he => ?_, fun hne => ?_⟩
  · have hunr : (primeAbove E F 𝔮).inertia (F ≃ₐ[E] F) = ⊥ :=
      (cubic_inertia_primeAbove_eq_bot_iff E F 𝔮 𝔔.asIdeal h𝔔').mpr he
    have hord : orderOf (artinFrob E F 𝔮) = 𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal :=
      (resolvent_orderOf_artinFrob_eq_finrank E F 𝔮 hunr).trans
        ((cubic_inertiaDeg_primeAbove_eq_finrank E F 𝔮).symm.trans
          (cubic_inertiaDeg_primeAbove_eq E F 𝔮 𝔔.asIdeal h𝔔'))
    rw [← hord]
    exact resolvent_isPrimitiveRoot_eulerCoeff E F r 𝔣 hiv ψ hψ 𝔮 (cubic_not_dvd_of_inertia_eq_bot E F 𝔣 hsupp 𝔮 hunr)
  · have hram : (primeAbove E F 𝔮).inertia (F ≃ₐ[E] F) ≠ ⊥ :=
      (cubic_inertia_primeAbove_ne_bot_iff E F 𝔮 𝔔.asIdeal h𝔔').mpr hne
    obtain ⟨t, ht, ht', hnot⟩ :=
      exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot E F hℓ 𝔮 hram
    exact resolvent_eulerCoeff_eq_zero E F r hker ψ hψ 𝔮 t ht ht' hnot

end S_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank
end P2MW
export P2MW.S_LanglandsTunnell_CubicLambda_exists_isFiniteOrderHeckeChar_eulerCoeff_and_eq_comp_idelicArtinMap_of_isGalois_of_prime_finrank (solution)
