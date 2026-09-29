-- Prove2me | solution 1 for LanglandsTunnell.CubicLambda.exists_resolventChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/dca7bfc7-1ccf-5c01-a304-80896dcd730d

import Definitions.Def_LanglandsTunnell_CubicLambda
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported
import Theorems.Thm_P2M_Dup_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
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
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicLambda_exists_resolventChar
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

section GroupCoreBlock

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

section GroupCore

variable {G : Type*} [Group G]

private theorem resolvent_comm_of_orderOf_three (hG : Nat.card G = 6) (s τ : G) (hs : orderOf s = 3)
    (hτ : τ ∉ Subgroup.zpowers s) (hcomm : τ * s = s * τ) (a b : G) : a * b = b * a := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact Nat.succ_ne_zero 5)
  have hsC : s ∈ Subgroup.centralizer ({s} : Set G) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hzle : Subgroup.zpowers s ≤ Subgroup.centralizer ({s} : Set G) := Subgroup.zpowers_le.mpr hsC
  have hτC : τ ∈ Subgroup.centralizer ({s} : Set G) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm.symm
  have hle6 : Nat.card (Subgroup.centralizer ({s} : Set G)) ≤ 6 := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({s} : Set G))
    rw [hG] at h
    exact Nat.le_of_dvd (by norm_num) h
  have h3dvd : 3 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
    have h := Subgroup.card_dvd_of_le hzle
    rwa [Nat.card_zpowers, hs] at h
  have hne3 : Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 3 := fun h3 => by
    have heq : Subgroup.zpowers s = Subgroup.centralizer ({s} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzle (le_of_eq (by rw [Nat.card_zpowers, hs, h3]))
    exact hτ (by rw [heq]; exact hτC)
  have hpos : 0 < Nat.card (Subgroup.centralizer ({s} : Set G)) := Nat.card_pos
  have hC6 : Nat.card (Subgroup.centralizer ({s} : Set G)) = 6 := by
    obtain ⟨m, hm⟩ := h3dvd
    omega
  have hCtop : Subgroup.centralizer ({s} : Set G) = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (le_of_eq (by rw [Subgroup.card_top, hG, hC6]))
  have hcentral : ∀ g : G, g * s = s * g := fun g => by
    have hg : g ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [hCtop]
      exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg s (Set.mem_singleton s)).symm
  haveI hnormal : (Subgroup.zpowers s).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g s := hcentral g
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact hn⟩
  have hcenter : Subgroup.zpowers s ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hcentral)
  have hindex : (Subgroup.zpowers s).index = 2 := by
    have h := (Subgroup.zpowers s).index_mul_card
    rw [Nat.card_zpowers, hs, hG] at h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (G ⧸ Subgroup.zpowers s) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, hindex])
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.zpowers s))
    (by rw [QuotientGroup.ker_mk']; exact hcenter) a b

private theorem resolvent_eq_inv_of_conj {N : Type*} [Group N] (ι : N →* G) (hι : Function.Injective ι)
    (hN : Nat.card N = 3) (hG : Nat.card G = 6) (τ : G) (hτ : τ ∉ ι.range) (g g' : N)
    (hconj : ι g' = τ * ι g * τ⁻¹) (hnc : (∀ a b : G, a * b = b * a) → False) : g' = g⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hg : g = 1
  · subst hg
    have h1 : ι g' = ι 1 := by rw [hconj, map_one, mul_one, mul_inv_cancel]
    rw [hι h1, inv_one]
  · have hord : orderOf g = 3 := orderOf_eq_prime (by rw [← hN]; exact pow_card_eq_one') hg
    haveI : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; exact Nat.succ_ne_zero 2)
    have htop : Subgroup.zpowers g = ⊤ :=
      Subgroup.eq_of_le_of_card_ge le_top (le_of_eq (by rw [Subgroup.card_top, hN, Nat.card_zpowers, hord]))
    have hmem : g' ∈ Subgroup.zpowers g := by
      rw [htop]
      exact Subgroup.mem_top g'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← zpow_mod_orderOf, hord] at hk
    simp only [Nat.cast_ofNat] at hk
    have hk3 : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk
      have h : ι g = 1 := conj_eq_one_iff.mp (by rw [← hconj, ← hk, map_one])
      exact hg (hι (h.trans (map_one ι).symm))
    · exfalso
      rw [h1, zpow_one] at hk
      subst hk
      have hcomm : τ * ι g = ι g * τ := mul_inv_eq_iff_eq_mul.mp hconj.symm
      have hτz : τ ∉ Subgroup.zpowers (ι g) := fun h =>
        hτ (Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨g, rfl⟩) h)
      exact hnc (resolvent_comm_of_orderOf_three hG (ι g) τ (by rw [orderOf_injective ι hι g, hord]) hτz hcomm)
    · rw [h2, zpow_ofNat] at hk
      rw [← hk]
      have h3 : g ^ 3 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one g
      exact eq_inv_of_mul_eq_one_left ((pow_succ g 2).symm.trans h3)

end GroupCore

section NonNormal

private theorem resolvent_not_comm_of_not_normal (K E : Type*) [Field K] [CharZero K] [Field E] [CharZero E]
    [IsGalois ℚ E] (ιK : K →+* E) (hKn : ¬ Normal ℚ K) (hcomm : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) :
    False := by
  haveI : IsAbelianGalois ℚ E := { is_comm := ⟨hcomm⟩ }
  haveI : IsAbelianGalois ℚ K := IsAbelianGalois.of_algHom ιK.toRatAlgHom
  exact hKn inferInstance

end NonNormal

section ResidueCard

private theorem resolvent_natCard_quotient_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsMaximal] [Finite (R ⧸ p)] (P : Ideal S) [P.LiesOver p] [Finite (S ⧸ P)]
    (hf : p.inertiaDeg' P = 1) :
    Nat.card (S ⧸ P) = Nat.card (R ⧸ p) := by
  rw [Module.natCard_eq_pow_finrank (K := R ⧸ p) (V := S ⧸ P), ← Ideal.inertiaDeg_algebraMap, hf, pow_one]

end ResidueCard

section FrobeniusTransfer

private theorem resolvent_isArithFrobAt_of_card_eq {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R S] [Algebra R' S] {G G' : Type*} [Group G] [Group G'] [MulSemiringAction G S] [SMulCommClass G R S]
    [MulSemiringAction G' S] [SMulCommClass G' R' S] (σ : G) (σ' : G') (hact : ∀ x : S, σ' • x = σ • x)
    (Q : Ideal S) (hcard : Nat.card (R' ⧸ Q.under R') = Nat.card (R ⧸ Q.under R))
    (h : IsArithFrobAt R σ Q) : IsArithFrobAt R' σ' Q := by
  intro x
  show σ' • x - x ^ Nat.card (R' ⧸ Q.under R') ∈ Q
  rw [hact, hcard]
  exact h x

end FrobeniusTransfer

section FrobeniusInversion

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsScalarTower ℚ L E]

private def resolvent_restrictHom : (E ≃ₐ[L] E) →* (E ≃ₐ[ℚ] E) where
  toFun σ := σ.restrictScalars ℚ
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

private theorem resolvent_restrictHom_injective : Function.Injective (resolvent_restrictHom L E) :=
  fun _ _ h => AlgEquiv.restrictScalars_injective ℚ h

private theorem resolvent_restrictHom_smul (ρ : E ≃ₐ[L] E) (x : 𝓞 E) :
    resolvent_restrictHom L E ρ • x = ρ • x := rfl

private theorem resolvent_restrictHom_smul_ideal (ρ : E ≃ₐ[L] E) (I : Ideal (𝓞 E)) :
    resolvent_restrictHom L E ρ • I = ρ • I := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    resolvent_restrictHom_smul]

variable [IsGalois L E] [IsGalois ℚ E]

private theorem resolvent_artinFrob_eq_inv (K : Type) [Field K] [NumberField K] (ιK : K →+* E)
    (hKn : ¬ Normal ℚ K) (hE6 : Nat.card (E ≃ₐ[ℚ] E) = 6) (hN3 : Nat.card (E ≃ₐ[L] E) = 3)
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)) (h : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal)
    (h' : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal) (hne : 𝔮 ≠ 𝔮') (hf : p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1)
    (hf' : p.asIdeal.inertiaDeg' 𝔮'.asIdeal = 1) (hG' : (primeAbove L E 𝔮').inertia (E ≃ₐ[ℚ] E) = ⊥) :
    artinFrob L E 𝔮' = (artinFrob L E 𝔮)⁻¹ := by
  haveI := p.isMaximal
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨h.symm⟩
  haveI : 𝔮'.asIdeal.LiesOver p.asIdeal := ⟨h'.symm⟩
  haveI : (primeAbove L E 𝔮).LiesOver p.asIdeal := Ideal.LiesOver.trans (primeAbove L E 𝔮) 𝔮.asIdeal p.asIdeal
  haveI : (primeAbove L E 𝔮').LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (primeAbove L E 𝔮') 𝔮'.asIdeal p.asIdeal
  haveI : Finite (𝓞 ℚ ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ p.ne_bot
  haveI : Finite (𝓞 L ⧸ 𝔮.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot
  haveI : Finite (𝓞 L ⧸ 𝔮'.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮'.ne_bot
  have hover : p.asIdeal = (primeAbove L E 𝔮).under (𝓞 ℚ) := Ideal.LiesOver.over
  have hover' : p.asIdeal = (primeAbove L E 𝔮').under (𝓞 ℚ) := Ideal.LiesOver.over
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := 𝓞 ℚ) (B := 𝓞 E) (G := E ≃ₐ[ℚ] E)
    (primeAbove L E 𝔮) (primeAbove L E 𝔮') (hover.symm.trans hover')
  have hcard : Nat.card (𝓞 ℚ ⧸ (primeAbove L E 𝔮).under (𝓞 ℚ)) = Nat.card (𝓞 L ⧸ (primeAbove L E 𝔮).under (𝓞 L)) := by
    rw [← hover, under_primeAbove]
    exact (resolvent_natCard_quotient_eq p.asIdeal 𝔮.asIdeal hf).symm
  have hcard' : Nat.card (𝓞 ℚ ⧸ (primeAbove L E 𝔮').under (𝓞 ℚ)) =
      Nat.card (𝓞 L ⧸ (primeAbove L E 𝔮').under (𝓞 L)) := by
    rw [← hover', under_primeAbove]
    exact (resolvent_natCard_quotient_eq p.asIdeal 𝔮'.asIdeal hf').symm
  have hFq : IsArithFrobAt (𝓞 ℚ) (resolvent_restrictHom L E (artinFrob L E 𝔮)) (primeAbove L E 𝔮) :=
    resolvent_isArithFrobAt_of_card_eq _ _ (resolvent_restrictHom_smul L E _) _ hcard (isArithFrobAt_artinFrob L E 𝔮)
  have hFq' : IsArithFrobAt (𝓞 ℚ) (resolvent_restrictHom L E (artinFrob L E 𝔮')) (primeAbove L E 𝔮') :=
    resolvent_isArithFrobAt_of_card_eq _ _ (resolvent_restrictHom_smul L E _) _ hcard'
      (isArithFrobAt_artinFrob L E 𝔮')
  have hconjF : IsArithFrobAt (𝓞 ℚ) (τ * resolvent_restrictHom L E (artinFrob L E 𝔮) * τ⁻¹) (primeAbove L E 𝔮') := by
    rw [hτ]
    exact hFq.conj τ
  have hmem := hconjF.mul_inv_mem_inertia hFq'
  rw [hG', Subgroup.mem_bot, mul_inv_eq_one] at hmem
  have hτnot : τ ∉ (resolvent_restrictHom L E).range := by
    intro hr
    obtain ⟨ρ, hρ⟩ := MonoidHom.mem_range.mp hr
    have h1 : (primeAbove L E 𝔮').under (𝓞 L) = (primeAbove L E 𝔮).under (𝓞 L) := by
      rw [hτ, ← hρ, resolvent_restrictHom_smul_ideal, Ideal.under_smul]
    rw [under_primeAbove, under_primeAbove] at h1
    exact hne (HeightOneSpectrum.ext h1).symm
  exact resolvent_eq_inv_of_conj (resolvent_restrictHom L E) (resolvent_restrictHom_injective L E) hN3 hE6 τ hτnot
    (artinFrob L E 𝔮) (artinFrob L E 𝔮') hmem.symm (resolvent_not_comm_of_not_normal K E ιK hKn)

end FrobeniusInversion

end GroupCoreBlock

section CubicBlock

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

noncomputable section

section Lift

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E]

private theorem cubic_injective_of_ringOfIntegers (f : 𝓞 L →+* 𝓞 E) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  haveI : Finite (𝓞 L ⧸ RingHom.ker f) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hcast : ((Nat.card (𝓞 L ⧸ RingHom.ker f) : ℕ) : 𝓞 L ⧸ RingHom.ker f) = 0 := by
    rw [← nsmul_one]
    exact card_nsmul_eq_zero'
  rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker f)), Ideal.Quotient.eq_zero_iff_mem,
    RingHom.mem_ker, map_natCast] at hcast
  exact (Nat.card_pos (α := 𝓞 L ⧸ RingHom.ker f)).ne' (Nat.cast_eq_zero.mp hcast)

variable [Algebra (𝓞 L) (𝓞 E)]

private theorem cubic_injective_coe_comp_algebraMap :
    Function.Injective ((algebraMap (𝓞 E) E).comp (algebraMap (𝓞 L) (𝓞 E))) := by
  rw [RingHom.coe_comp]
  exact RingOfIntegers.coe_injective.comp (cubic_injective_of_ringOfIntegers L E _)

private def cubic_liftToFields : L →+* E :=
  IsFractionRing.lift (cubic_injective_coe_comp_algebraMap L E)

private theorem cubic_liftToFields_coe (x : 𝓞 L) :
    cubic_liftToFields L E (algebraMap (𝓞 L) L x) = algebraMap (𝓞 E) E (algebraMap (𝓞 L) (𝓞 E) x) :=
  IsFractionRing.lift_algebraMap (cubic_injective_coe_comp_algebraMap L E) x

end Lift

section Transport

variable (L E : Type) [Field L] [Field E]

private theorem cubic_algebra_eq_of_forall_coe (i₁ i₂ : Algebra (𝓞 L) (𝓞 E))
    (h : ∀ x : 𝓞 L,
      algebraMap (𝓞 E) E (letI := i₁; algebraMap (𝓞 L) (𝓞 E) x) =
        algebraMap (𝓞 E) E (letI := i₂; algebraMap (𝓞 L) (𝓞 E) x)) :
    i₁ = i₂ :=
  Algebra.algebra_ext i₁ i₂ fun x => RingOfIntegers.coe_injective (h x)

section OfLift

variable [NumberField L] [NumberField E]

private theorem cubic_algebra_eq_ofLift [i : Algebra (𝓞 L) (𝓞 E)] :
    i = (letI : Algebra L E := (cubic_liftToFields L E).toAlgebra; inst_ringOfIntegersAlgebra L E) := by
  refine cubic_algebra_eq_of_forall_coe L E i _ fun x => ?_
  exact (cubic_liftToFields_coe L E x).symm.trans rfl

end OfLift

private theorem cubic_under_eq_of_algebra_eq (i₁ i₂ : Algebra (𝓞 L) (𝓞 E)) (h : i₁ = i₂) (Q : Ideal (𝓞 E)) :
    (letI := i₁; Q.under (𝓞 L)) = (letI := i₂; Q.under (𝓞 L)) := by
  subst h
  rfl

private theorem cubic_ramificationIdx_eq_of_algebra_eq (i₁ i₂ : Algebra (𝓞 L) (𝓞 E)) (h : i₁ = i₂)
    (p : Ideal (𝓞 L)) (Q : Ideal (𝓞 E)) :
    (letI := i₁; p.ramificationIdx' Q) = (letI := i₂; p.ramificationIdx' Q) := by
  subst h
  rfl

private theorem cubic_inertiaDeg_eq_of_algebra_eq (i₁ i₂ : Algebra (𝓞 L) (𝓞 E)) (h : i₁ = i₂)
    (p : Ideal (𝓞 L)) (Q : Ideal (𝓞 E)) :
    (letI := i₁; p.inertiaDeg' Q) = (letI := i₂; p.inertiaDeg' Q) := by
  subst h
  rfl

end Transport

section RatBase

private theorem cubic_ringHom_ringOfIntegers_rat_ext {S : Type*} [Ring S] (f g : 𝓞 ℚ →+* S) : f = g := by
  have h : f.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) =
      g.comp (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) :=
    Subsingleton.elim _ _
  ext x
  have hx : x = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) :=
    (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm
  rw [hx]
  exact RingHom.congr_fun h _

private theorem cubic_algebra_ringOfIntegers_rat_eq (X : Type) [Field X] [NumberField X]
    (i : Algebra (𝓞 ℚ) (𝓞 X)) : i = inst_ringOfIntegersAlgebra ℚ X :=
  Algebra.algebra_ext i (inst_ringOfIntegersAlgebra ℚ X) fun r =>
    RingHom.congr_fun
      (cubic_ringHom_ringOfIntegers_rat_ext (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ i)
        (@algebraMap (𝓞 ℚ) (𝓞 X) _ _ (inst_ringOfIntegersAlgebra ℚ X))) r

end RatBase

section GaloisLayer

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E]

private theorem cubic_isGalois_of_isGalois_rat [IsGalois ℚ E] : IsGalois L E :=
  IsGalois.tower_top_of_isGalois ℚ L E

private theorem cubic_finrank_eq_three (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6) :
    Module.finrank L E = 3 := by
  have h : Module.finrank ℚ L * Module.finrank L E = Module.finrank ℚ E := by
    rw [Module.finrank_mul_finrank]
  rw [hL, hE] at h
  omega

variable [IsGalois L E]

private theorem cubic_natCard_aut_eq_three (h3 : Module.finrank L E = 3) : Nat.card (E ≃ₐ[L] E) = 3 := by
  rw [IsGalois.card_aut_eq_finrank, h3]

private theorem cubic_isMulCommutative_aut (h3 : Module.finrank L E = 3) : IsMulCommutative (E ≃ₐ[L] E) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic (E ≃ₐ[L] E) := isCyclic_of_prime_card (cubic_natCard_aut_eq_three L E h3)
  infer_instance

private theorem cubic_aut_pow_three (h3 : Module.finrank L E = 3) (σ : E ≃ₐ[L] E) : σ ^ (3 ^ 1) = 1 := by
  rw [pow_one, ← cubic_natCard_aut_eq_three L E h3]
  exact pow_card_eq_one'

end GaloisLayer

section Ramification

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
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal 𝔔 𝔮.ne_bot]

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
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal 𝔔 𝔮.ne_bot]

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
  rw [Ideal.inertiaDeg'_eq_inertiaDeg 𝔮.asIdeal (primeAbove L E 𝔮), Ideal.inertiaDeg'_eq_inertiaDeg 𝔮.asIdeal 𝔔]
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

end Ramification

section SplitPrime

variable (L : Type) [Field L] [NumberField L]

private theorem cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne (hL : Module.finrank ℚ L = 2)
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L))
    (h : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal) (h' : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal) (hne : 𝔮 ≠ 𝔮') :
    p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧ p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 := by
  classical
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨h.symm⟩
  haveI : 𝔮'.asIdeal.LiesOver p.asIdeal := ⟨h'.symm⟩
  have hsum := Ideal.sum_ramification_inertia (S := 𝓞 L) ℚ L p.ne_bot
  rw [hL] at hsum
  have hmem : 𝔮.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)).mpr ⟨𝔮.isPrime, inferInstance⟩
  have hmem' : 𝔮'.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 L)).mpr ⟨𝔮'.isPrime, inferInstance⟩
  have hne' : 𝔮.asIdeal ≠ 𝔮'.asIdeal := fun hh => hne (HeightOneSpectrum.ext hh)
  have hsub : ({𝔮.asIdeal, 𝔮'.asIdeal} : Finset (Ideal (𝓞 L))) ⊆
      IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 L) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]; exact hmem
    · rw [Finset.mem_singleton.mp hx]; exact hmem'
  have hle := Finset.sum_le_sum_of_subset
    (f := fun P : Ideal (𝓞 L) => p.asIdeal.ramificationIdx' P * p.asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', hsum] at hle
  have he : p.asIdeal.ramificationIdx' 𝔮.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔮.asIdeal p.ne_bot
  have hf : 0 < p.asIdeal.inertiaDeg' 𝔮.asIdeal := Ideal.inertiaDeg'_pos p.asIdeal 𝔮.asIdeal
  have he' : p.asIdeal.ramificationIdx' 𝔮'.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver 𝔮'.asIdeal p.ne_bot
  have hf' : 0 < p.asIdeal.inertiaDeg' 𝔮'.asIdeal := Ideal.inertiaDeg'_pos p.asIdeal 𝔮'.asIdeal
  have hpos : 0 < p.asIdeal.ramificationIdx' 𝔮.asIdeal * p.asIdeal.inertiaDeg' 𝔮.asIdeal :=
    mul_pos (Nat.pos_of_ne_zero he) hf
  have hpos' : 0 < p.asIdeal.ramificationIdx' 𝔮'.asIdeal * p.asIdeal.inertiaDeg' 𝔮'.asIdeal :=
    mul_pos (Nat.pos_of_ne_zero he') hf'
  have h1 : p.asIdeal.ramificationIdx' 𝔮.asIdeal * p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 := by omega
  exact ⟨Nat.eq_one_of_mul_eq_one_right h1, Nat.eq_one_of_mul_eq_one_left h1⟩

end SplitPrime

section RamifiedTransfer

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois ℚ E]

private theorem cubic_natCard_aut_rat_eq_six (hE : Module.finrank ℚ E = 6) : Nat.card (E ≃ₐ[ℚ] E) = 6 := by
  rw [IsGalois.card_aut_eq_finrank, hE]

private theorem cubic_ramificationIdx_primeAbove_eq_of_ne (hL : Module.finrank ℚ L = 2)
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L))
    (h : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal) (h' : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal) (hne : 𝔮 ≠ 𝔮') :
    𝔮.asIdeal.ramificationIdx' (primeAbove L E 𝔮) = 𝔮'.asIdeal.ramificationIdx' (primeAbove L E 𝔮') := by
  haveI : IsGalois L E := cubic_isGalois_of_isGalois_rat L E
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨h.symm⟩
  haveI : 𝔮'.asIdeal.LiesOver p.asIdeal := ⟨h'.symm⟩
  haveI : (primeAbove L E 𝔮).LiesOver p.asIdeal := Ideal.LiesOver.trans (primeAbove L E 𝔮) 𝔮.asIdeal p.asIdeal
  haveI : (primeAbove L E 𝔮').LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (primeAbove L E 𝔮') 𝔮'.asIdeal p.asIdeal
  obtain ⟨he, -⟩ := cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne L hL p 𝔮 𝔮' h h' hne
  obtain ⟨he', -⟩ := cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne L hL p 𝔮' 𝔮 h' h hne.symm
  have t := Ideal.ramificationIdx_algebra_tower' p.asIdeal 𝔮.asIdeal (primeAbove L E 𝔮)
  have t' := Ideal.ramificationIdx_algebra_tower' p.asIdeal 𝔮'.asIdeal (primeAbove L E 𝔮')
  have hg := Ideal.ramificationIdx_eq_of_isGaloisGroup p.asIdeal (primeAbove L E 𝔮) (primeAbove L E 𝔮')
    (E ≃ₐ[ℚ] E)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal (primeAbove L E 𝔮) p.ne_bot,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal (primeAbove L E 𝔮') p.ne_bot] at hg
  rw [he] at t
  rw [he'] at t'
  omega

private theorem cubic_inertia_primeAbove_eq_bot_iff_of_ne (hL : Module.finrank ℚ L = 2)
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L))
    (h : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal) (h' : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal) (hne : 𝔮 ≠ 𝔮') :
    (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥ ↔ (primeAbove L E 𝔮').inertia (E ≃ₐ[L] E) = ⊥ := by
  haveI : IsGalois L E := cubic_isGalois_of_isGalois_rat L E
  rw [cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 (primeAbove L E 𝔮) (under_primeAbove L E 𝔮),
    cubic_inertia_primeAbove_eq_bot_iff L E 𝔮' (primeAbove L E 𝔮') (under_primeAbove L E 𝔮'),
    cubic_ramificationIdx_primeAbove_eq_of_ne L E hL p 𝔮 𝔮' h h' hne]

private theorem cubic_inertia_primeAbove_rat_eq_bot_of_ne (hL : Module.finrank ℚ L = 2)
    (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L))
    (h : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal) (h' : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal) (hne : 𝔮 ≠ 𝔮')
    (hunr : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥) :
    (primeAbove L E 𝔮).inertia (E ≃ₐ[ℚ] E) = ⊥ := by
  haveI : IsGalois L E := cubic_isGalois_of_isGalois_rat L E
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨h.symm⟩
  haveI : (primeAbove L E 𝔮).LiesOver p.asIdeal := Ideal.LiesOver.trans (primeAbove L E 𝔮) 𝔮.asIdeal p.asIdeal
  have hQ : (primeAbove L E 𝔮).under (𝓞 ℚ) = p.asIdeal := (Ideal.over_def (primeAbove L E 𝔮) p.asIdeal).symm
  rw [cubic_inertia_eq_bot_iff_of_under_eq ℚ E p (primeAbove L E 𝔮) (primeAbove L E 𝔮) hQ hQ]
  have hL1 := (cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 (primeAbove L E 𝔮) (under_primeAbove L E 𝔮)).mp hunr
  obtain ⟨he, -⟩ := cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne L hL p 𝔮 𝔮' h h' hne
  have t := Ideal.ramificationIdx_algebra_tower' p.asIdeal 𝔮.asIdeal (primeAbove L E 𝔮)
  rw [he, hL1] at t
  omega

end RamifiedTransfer

section MergeGlue

variable (L E : Type) [Field L] [NumberField L] [Field E] [NumberField E] [Algebra L E] [IsGalois L E]

private theorem cubic_aut_pow_three' (h3 : Module.finrank L E = 3) (σ : E ≃ₐ[L] E) : σ ^ 3 = 1 := by
  rw [← cubic_natCard_aut_eq_three L E h3]
  exact pow_card_eq_one'

private theorem cubic_not_dvd_of_inertia_eq_bot (𝔣 : Ideal (𝓞 L))
    (hsupp : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ 𝔣 →
      ∃ Q : Ideal (𝓞 E), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧ Q.inertia (E ≃ₐ[L] E) ≠ ⊥)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (hunr : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥) :
    ¬ 𝔮.asIdeal ∣ 𝔣 := fun hdvd =>
  cubic_ramificationIdx_ne_one_of_exists_inertia_ne_bot L E 𝔮 (hsupp 𝔮 hdvd) (primeAbove L E 𝔮)
    (under_primeAbove L E 𝔮)
    ((cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 (primeAbove L E 𝔮) (under_primeAbove L E 𝔮)).mp hunr)

private theorem cubic_inertia_eq_bot_iff_inertia_eq_bot (𝔮 : HeightOneSpectrum (𝓞 L)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hQ : Q.under (𝓞 L) = 𝔮.asIdeal) (hQ' : Q'.under (𝓞 L) = 𝔮.asIdeal) :
    Q.inertia (E ≃ₐ[L] E) = ⊥ ↔ Q'.inertia (E ≃ₐ[L] E) = ⊥ :=
  (cubic_inertia_eq_bot_iff_of_under_eq L E 𝔮 Q Q hQ hQ).trans
    (cubic_inertia_eq_bot_iff_of_under_eq L E 𝔮 Q' Q hQ' hQ).symm

end MergeGlue

end

end CubicBlock

section Main

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open NumberField.InfinitePlace HeckeCharacter LanglandsTunnell.Converse LanglandsTunnell.CubicLambda

private theorem resolvent_main (K L E : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field E] [NumberField E] [Algebra L E] [IsGalois ℚ E] (ιK : K →+* E) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (hd : ∀ 𝔮 : HeightOneSpectrum (𝓞 L), (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) ≠ ⊥ →
      ∃ t : (𝔮.adicCompletion L)ˣ, (t : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L ∧
        ((t⁻¹ : (𝔮.adicCompletion L)ˣ) : 𝔮.adicCompletion L) ∈ 𝔮.adicCompletionIntegers L ∧
        Units.map (NumberField.AdelicLevel.finIncl (𝓞 L) L) (NumberField.AdelicLevel.localUnit (𝓞 L) L 𝔮 t) ∉
          M4aHerbrand.principalIdeles (𝓞 L) L ⊔
            (M4aHerbrand.GenuineDescent.genuineBaseChange L E).idelicNorm.range) :
    ∃ θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, IsFiniteOrderHeckeChar L θ ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : Ideal (𝓞 E)) [𝔔.IsMaximal], 𝔔.under (𝓞 L) = 𝔮.asIdeal →
        (𝔮.asIdeal.ramificationIdx' 𝔔 = 1 →
          IsPrimitiveRoot (eulerCoeff L θ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔 ≠ 1 → eulerCoeff L θ 𝔮 = 0)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)),
        𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal → 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal → 𝔮 ≠ 𝔮' →
          eulerCoeff L θ 𝔮' = (eulerCoeff L θ 𝔮)⁻¹) ∧
      (∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ)) ∧
      (∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0) := by
  haveI : IsGalois L E := cubic_isGalois_of_isGalois_rat L E
  have h3 : Module.finrank L E = 3 := cubic_finrank_eq_three L E hL hE
  haveI : IsMulCommutative (E ≃ₐ[L] E) := cubic_isMulCommutative_aut L E h3
  have hexp : ∀ g : E ≃ₐ[L] E, g ^ 3 = 1 := cubic_aut_pow_three' L E h3
  obtain ⟨ψ, hψ⟩ := resolvent_exists_injective_char 3 Nat.prime_three (cubic_natCard_aut_eq_three L E h3)
  obtain ⟨𝔣₀, hadm, hsupp⟩ := LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported L E
  obtain ⟨r, hi, hker, -, hiv⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_dvd_twentyFour L E 3 1
      Nat.prime_three (cubic_aut_pow_three L E h3) 𝔣₀ hadm (by decide) (by rw [h3]; decide)
  have hzero : ∀ 𝔮 : HeightOneSpectrum (𝓞 L), (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) ≠ ⊥ →
      eulerCoeff L (ψ.comp r) 𝔮 = 0 := fun 𝔮 hram => by
    obtain ⟨t, ht, ht', hnot⟩ := hd 𝔮 hram
    exact resolvent_eulerCoeff_eq_zero L E r hker ψ hψ 𝔮 t ht ht' hnot
  refine ⟨ψ.comp r, resolvent_isFiniteOrderHeckeChar L _ (resolvent_isIdeleClassChar L E r hi ψ)
    (resolvent_continuous L E r 𝔣₀ hiv (resolvent_unitIdeles_mem_nhds L 𝔣₀ hadm.1) ψ)
    (resolvent_isOfFinOrder L E r hexp ψ), ?_, ?_, fun u _ => resolvent_isArchCompAt_zmod L E r 𝔣₀ hiv hexp ψ u,
    fun u _ => resolvent_isArchCompAt L E r 𝔣₀ hiv hexp ψ u⟩
  · intro 𝔮 𝔔 _ h𝔔
    refine ⟨fun he => ?_, fun hne => hzero 𝔮 fun hbot =>
      hne ((cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 𝔔 h𝔔).mp hbot)⟩
    have hunr : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥ := (cubic_inertia_primeAbove_eq_bot_iff L E 𝔮 𝔔 h𝔔).mpr he
    have hord : orderOf (artinFrob L E 𝔮) = 𝔮.asIdeal.inertiaDeg' 𝔔 :=
      (resolvent_orderOf_artinFrob_eq_finrank L E 𝔮 hunr).trans
        ((cubic_inertiaDeg_primeAbove_eq_finrank L E 𝔮).symm.trans (cubic_inertiaDeg_primeAbove_eq L E 𝔮 𝔔 h𝔔))
    rw [← hord]
    exact resolvent_isPrimitiveRoot_eulerCoeff L E r 𝔣₀ hiv ψ hψ 𝔮
      (cubic_not_dvd_of_inertia_eq_bot L E 𝔣₀ hsupp 𝔮 hunr)
  · intro p 𝔮 𝔮' h h' hne
    by_cases hunr : (primeAbove L E 𝔮).inertia (E ≃ₐ[L] E) = ⊥
    · have hunr' : (primeAbove L E 𝔮').inertia (E ≃ₐ[L] E) = ⊥ :=
        (cubic_inertia_primeAbove_eq_bot_iff_of_ne L E hL p 𝔮 𝔮' h h' hne).mp hunr
      have hf : p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 :=
        (cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne L hL p 𝔮 𝔮' h h' hne).2
      have hf' : p.asIdeal.inertiaDeg' 𝔮'.asIdeal = 1 :=
        (cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne L hL p 𝔮' 𝔮 h' h hne.symm).2
      have hG' : (primeAbove L E 𝔮').inertia (E ≃ₐ[ℚ] E) = ⊥ :=
        cubic_inertia_primeAbove_rat_eq_bot_of_ne L E hL p 𝔮' 𝔮 h' h hne.symm hunr'
      exact resolvent_eulerCoeff_eq_inv L E r 𝔣₀ hiv ψ 𝔮 𝔮' (cubic_not_dvd_of_inertia_eq_bot L E 𝔣₀ hsupp 𝔮 hunr)
        (cubic_not_dvd_of_inertia_eq_bot L E 𝔣₀ hsupp 𝔮' hunr')
        (resolvent_artinFrob_eq_inv L E K ιK hKn (cubic_natCard_aut_rat_eq_six E hE)
          (cubic_natCard_aut_eq_three L E h3)
          p 𝔮 𝔮' h h' hne hf hf' hG')
    · have hunr' : (primeAbove L E 𝔮').inertia (E ≃ₐ[L] E) ≠ ⊥ := fun hb =>
        hunr ((cubic_inertia_primeAbove_eq_bot_iff_of_ne L E hL p 𝔮 𝔮' h h' hne).mpr hb)
      exact resolvent_eq_inv_of_eq_zero (hzero 𝔮 hunr) (hzero 𝔮' hunr')

end Main

#print axioms resolvent_locIdele
#print axioms resolvent_uniformizerIdele_eq
#print axioms resolvent_localChar_eq
#print axioms resolvent_isAdjuster_locIdele
#print axioms resolvent_placeOrd_locIdele_of_ne
#print axioms resolvent_placeOrd_locIdele_self
#print axioms resolvent_valued_eq_one
#print axioms resolvent_map_locIdele
#print axioms resolvent_map_locIdele_eq_one
#print axioms resolvent_map_uniformizerIdele
#print axioms resolvent_isUnramifiedCharAt
#print axioms resolvent_eulerCoeff_eq
#print axioms resolvent_archSign_mul_self
#print axioms resolvent_isAdjuster_arch_mul_self
#print axioms resolvent_placeOrd_arch
#print axioms resolvent_eq_one_of_sq_of_cube
#print axioms resolvent_map_arch_eq_one
#print axioms resolvent_isArchCompAt
#print axioms resolvent_isArchCompAt_zmod
#print axioms resolvent_isIdeleClassChar
#print axioms resolvent_isOfFinOrder
#print axioms resolvent_unitIdeles_le_ker
#print axioms resolvent_continuous_of_nhds
#print axioms resolvent_continuous
#print axioms resolvent_exists_injective_char
#print axioms resolvent_orderOf_map_eq
#print axioms resolvent_map_eq_one_of_ker_eq
#print axioms resolvent_map_eq_inv_of_ker_eq
#print axioms resolvent_isPrimitiveRoot
#print axioms resolvent_isOpen_realPos
#print axioms resolvent_valued_eq_one_of_integral
#print axioms resolvent_unitIdeles_mem_nhds
#print axioms resolvent_isPrimitiveRoot_eulerCoeff
#print axioms resolvent_eulerCoeff_eq_inv
#print axioms resolvent_eq_inv_of_eq_zero
#print axioms resolvent_isFiniteOrderHeckeChar
#print axioms resolvent_eulerCoeff_eq_zero
#print axioms resolvent_under_primeAbove_isMaximal
#print axioms resolvent_finite_quotient_under
#print axioms resolvent_orderOf_artinFrob_eq_finrank
#print axioms resolvent_comm_of_orderOf_three
#print axioms resolvent_eq_inv_of_conj
#print axioms resolvent_not_comm_of_not_normal
#print axioms resolvent_natCard_quotient_eq
#print axioms resolvent_isArithFrobAt_of_card_eq
#print axioms resolvent_restrictHom
#print axioms resolvent_restrictHom_injective
#print axioms resolvent_restrictHom_smul
#print axioms resolvent_restrictHom_smul_ideal
#print axioms resolvent_artinFrob_eq_inv
#print axioms cubic_injective_of_ringOfIntegers
#print axioms cubic_injective_coe_comp_algebraMap
#print axioms cubic_liftToFields
#print axioms cubic_liftToFields_coe
#print axioms cubic_algebra_eq_of_forall_coe
#print axioms cubic_algebra_eq_ofLift
#print axioms cubic_under_eq_of_algebra_eq
#print axioms cubic_ramificationIdx_eq_of_algebra_eq
#print axioms cubic_inertiaDeg_eq_of_algebra_eq
#print axioms cubic_ringHom_ringOfIntegers_rat_ext
#print axioms cubic_algebra_ringOfIntegers_rat_eq
#print axioms cubic_isGalois_of_isGalois_rat
#print axioms cubic_finrank_eq_three
#print axioms cubic_natCard_aut_eq_three
#print axioms cubic_isMulCommutative_aut
#print axioms cubic_aut_pow_three
#print axioms cubic_inertia_primeAbove_eq_bot_iff
#print axioms cubic_inertia_primeAbove_ne_bot_iff
#print axioms cubic_inertia_eq_bot_iff_of_under_eq
#print axioms cubic_ramificationIdx_ne_one_of_exists_inertia_ne_bot
#print axioms cubic_ramificationIdx_primeAbove_eq
#print axioms cubic_inertiaDeg_primeAbove_eq
#print axioms cubic_inertiaDeg_primeAbove_eq_finrank
#print axioms cubic_exists_admissibleModulus_dvd_not_dvd
#print axioms cubic_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ne
#print axioms cubic_natCard_aut_rat_eq_six
#print axioms cubic_ramificationIdx_primeAbove_eq_of_ne
#print axioms cubic_inertia_primeAbove_eq_bot_iff_of_ne
#print axioms cubic_inertia_primeAbove_rat_eq_bot_of_ne
#print axioms cubic_aut_pow_three'
#print axioms cubic_not_dvd_of_inertia_eq_bot
#print axioms cubic_inertia_eq_bot_iff_inertia_eq_bot
#print axioms resolvent_main

section ResolventExists

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open NumberField.InfinitePlace HeckeCharacter LanglandsTunnell.Converse LanglandsTunnell.CubicLambda

private theorem resolvent_exists_of_localUnits
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (hloc : ∀ (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M] [IsGalois F M],
      (Module.finrank F M).Prime → ∀ v : HeightOneSpectrum (𝓞 F),
        (LanglandsTunnell.P2.Artin.primeAbove F M v).inertia (M ≃ₐ[F] M) ≠ ⊥ →
          ∃ t : (v.adicCompletion F)ˣ, (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
            ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
            Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F) (NumberField.AdelicLevel.localUnit (𝓞 F) F v t) ∉
              M4aHerbrand.principalIdeles (𝓞 F) F ⊔
                (M4aHerbrand.GenuineDescent.genuineBaseChange F M).idelicNorm.range) :
    ∃ θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, IsFiniteOrderHeckeChar L θ ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔔.under (𝓞 L) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff L θ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff L θ 𝔮 = 0)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)),
        𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
          eulerCoeff L θ 𝔮' = (eulerCoeff L θ 𝔮)⁻¹) ∧
      (∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ)) ∧
      (∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0) := by
  have _ := hK
  have hi := cubic_algebra_eq_ofLift L E
  have hiQ := cubic_algebra_ringOfIntegers_rat_eq L ‹Algebra (𝓞 ℚ) (𝓞 L)›
  letI : Algebra L E := (cubic_liftToFields L E).toAlgebra
  haveI : IsGalois L E := cubic_isGalois_of_isGalois_rat L E
  have hprime : (Module.finrank L E).Prime := by
    rw [cubic_finrank_eq_three L E hL hE]
    exact Nat.prime_three
  obtain ⟨θ, h1, h2, h3, h4, h5⟩ :=
    resolvent_main K L E (cubic_liftToFields K E) hKn hL hE (hloc L E hprime)
  refine ⟨θ, h1, ?_, ?_, h4, h5⟩
  · intro 𝔮 𝔔 h𝔔
    have h𝔔' : 𝔔.asIdeal.under (𝓞 L) = 𝔮.asIdeal := congrArg HeightOneSpectrum.asIdeal h𝔔
    rw [cubic_under_eq_of_algebra_eq L E _ _ hi] at h𝔔'
    rw [cubic_ramificationIdx_eq_of_algebra_eq L E _ _ hi, cubic_inertiaDeg_eq_of_algebra_eq L E _ _ hi]
    haveI := 𝔔.isMaximal
    exact h2 𝔮 𝔔.asIdeal h𝔔'
  · intro p 𝔮 𝔮' h h' hne
    have h₁ : 𝔮.asIdeal.under (𝓞 ℚ) = p.asIdeal := congrArg HeightOneSpectrum.asIdeal h
    have h₂ : 𝔮'.asIdeal.under (𝓞 ℚ) = p.asIdeal := congrArg HeightOneSpectrum.asIdeal h'
    rw [cubic_under_eq_of_algebra_eq ℚ L _ _ hiQ] at h₁ h₂
    exact h3 p 𝔮 𝔮' h₁ h₂ hne

end ResolventExists

#print axioms resolvent_exists_of_localUnits

open IsDedekindDomain NumberField NumberField.InfinitePlace HeckeCharacter LanglandsTunnell.Converse
open LanglandsTunnell.CubicLambda

theorem solution
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6) :
    ∃ θ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ, IsFiniteOrderHeckeChar L θ ∧
      (∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔔.under (𝓞 L) = 𝔮 →
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal = 1 →
          IsPrimitiveRoot (eulerCoeff L θ 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal)) ∧
        (𝔮.asIdeal.ramificationIdx' 𝔔.asIdeal ≠ 1 → eulerCoeff L θ 𝔮 = 0)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (𝔮 𝔮' : HeightOneSpectrum (𝓞 L)),
        𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
          eulerCoeff L θ 𝔮' = (eulerCoeff L θ 𝔮)⁻¹) ∧
      (∀ u : InfinitePlace L, u.IsReal → IsArchCompAt L θ u 0 (((0 : ZMod 2)).val : ℤ)) ∧
      (∀ u : InfinitePlace L, u.IsComplex → IsArchCompAt L θ u 0 0) := by
  exact resolvent_exists_of_localUnits K L E hK hKn hL hE
    LanglandsTunnell.P2.Artin.exists_localUnit_notMem_principalIdeles_sup_range_idelicNorm_of_inertia_ne_bot
#print axioms solution

end S_LanglandsTunnell_CubicLambda_exists_resolventChar
end P2MW
export P2MW.S_LanglandsTunnell_CubicLambda_exists_resolventChar (solution)
