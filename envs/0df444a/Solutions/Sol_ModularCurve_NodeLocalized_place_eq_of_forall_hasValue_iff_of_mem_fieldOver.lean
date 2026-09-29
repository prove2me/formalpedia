-- Prove2me | solution 1 for ModularCurve.NodeLocalized.place_eq_of_forall_hasValue_iff_of_mem_fieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8108e777-ade1-52bd-95ef-5475684b27ce

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin_pair
import Theorems.Thm_ModularCurve_functionFieldGeneration_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.ModularCurve"
p2m_open "ModularCurve.NodeLocalized P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.ModularCurve.NodeLocalized"

noncomputable section

namespace CompNEtaProof

private abbrev FB (q : ℕ) [Fact q.Prime] : Type := ↥(modularFunctionFieldBar (1 * q))

variable {q : ℕ} [Fact q.Prime] (K : IntermediateField ℚ (AlgebraicClosure ℚ))

private abbrev algebraQbFB : Algebra (AlgebraicClosure ℚ) (FB q) := (modularFunctionFieldBar (1 * q)).algebra

attribute [local instance] algebraQbFB

private abbrev smulQbFB : SMul (AlgebraicClosure ℚ) (FB q) := Algebra.toSMul

attribute [local instance] smulQbFB

private abbrev moduleQbFB : Module (AlgebraicClosure ℚ) (FB q) := Algebra.toModule

attribute [local instance] moduleQbFB

private scoped instance charZero_FB : CharZero (FB q) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (FB q)).injective

private theorem fact_prime_one_mul : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩

private theorem bar_eq_adjoin : modularFunctionFieldBar (1 * q) =
    IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)} :=
  laurentBaseChange_adjoin_pair (AlgebraicClosure ℚ) (1 * q)
    (functionFieldGeneration_of_prime (fact_prime_one_mul (q := q)).out)

private theorem fieldOver_le_bar :
    fieldOver (1 * q) K ≤ (modularFunctionFieldBar (1 * q)).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨c, rfl⟩ | hx)
  · exact IntermediateField.algebraMap_mem (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
  · show x ∈ modularFunctionFieldBar (1 * q)
    rw [bar_eq_adjoin]
    exact IntermediateField.subset_adjoin _ _ hx

private theorem bar_le_closure :
    (modularFunctionFieldBar (1 * q)).toSubfield ≤
      Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        (fieldOver (1 * q) K : Set (LaurentSeries (AlgebraicClosure ℚ)))) := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)} := by
    rw [← bar_eq_adjoin]; exact hx
  refine Subfield.closure_mono (Set.union_subset_union_right _ ?_) hx'
  intro y hy
  exact Subfield.subset_closure (Or.inr hy)

private theorem algebraMap_mem_fieldOver (c : ↥K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) ∈
      fieldOver (1 * q) K :=
  Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2⟩, rfl⟩)

private def F0 : Subfield (FB q) :=
  (fieldOver (1 * q) K).comap (IntermediateField.val (modularFunctionFieldBar (1 * q))).toRingHom

private theorem mem_F0 {g : FB q} :
    g ∈ F0 (q := q) K ↔ (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K :=
  Iff.rfl

private scoped instance algebraF0FB : Algebra ↥(F0 (q := q) K) (FB q) := (F0 (q := q) K).toAlgebra

private scoped instance smulF0FB : SMul ↥(F0 (q := q) K) (FB q) := Algebra.toSMul

private theorem coe_algebraMap_FB (a : AlgebraicClosure ℚ) :
    ((algebraMap (AlgebraicClosure ℚ) (FB q) a : FB q) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a :=
  rfl

private theorem const_mem_F0 (c : ↥K) :
    algebraMap (AlgebraicClosure ℚ) (FB q) (c : AlgebraicClosure ℚ) ∈ F0 (q := q) K := by
  rw [mem_F0, coe_algebraMap_FB]
  exact algebraMap_mem_fieldOver K c

private def constK : ↥K →+* ↥(F0 (q := q) K) :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q)).comp (algebraMap ↥K (AlgebraicClosure ℚ))).codRestrict
    (F0 (q := q) K) fun c => const_mem_F0 K c

private theorem coe_constK (c : ↥K) :
    ((constK (q := q) K c : ↥(F0 (q := q) K)) : FB q) =
      algebraMap (AlgebraicClosure ℚ) (FB q) (c : AlgebraicClosure ℚ) :=
  rfl

private scoped instance algebraKFB : Algebra ↥K (FB q) :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q)).comp (algebraMap ↥K (AlgebraicClosure ℚ))).toAlgebra

private scoped instance smulKFB : SMul ↥K (FB q) := Algebra.toSMul

private theorem algebraMap_K_FB (c : ↥K) :
    algebraMap ↥K (FB q) c = algebraMap (AlgebraicClosure ℚ) (FB q) (c : AlgebraicClosure ℚ) :=
  rfl

private scoped instance algebraKF0 : Algebra ↥K ↥(F0 (q := q) K) := (constK (q := q) K).toAlgebra

private scoped instance smulKF0 : SMul ↥K ↥(F0 (q := q) K) := Algebra.toSMul

private scoped instance towerKF0FB : IsScalarTower ↥K ↥(F0 (q := q) K) (FB q) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem isIntegral_rat (α : AlgebraicClosure ℚ) : IsIntegral ℚ α := by
  have h : @IsIntegral ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) α := by
    letI : Algebra ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instAlgebra ℚ
    exact (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  obtain ⟨p, hp, hp0⟩ := h
  refine ⟨p, hp, ?_⟩
  rw [Subsingleton.elim (algebraMap ℚ (AlgebraicClosure ℚ))
    (@algebraMap ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ))]
  exact hp0

private theorem isIntegral_K_const (α : AlgebraicClosure ℚ) :
    IsIntegral ↥K (algebraMap (AlgebraicClosure ℚ) (FB q) α) := by
  obtain ⟨p, hp, hp0⟩ := isIntegral_rat α
  refine ⟨p.map (algebraMap ℚ ↥K), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap ↥K (FB q)).comp (algebraMap ℚ ↥K) =
      (algebraMap (AlgebraicClosure ℚ) (FB q)).comp (algebraMap ℚ (AlgebraicClosure ℚ)) :=
    Subsingleton.elim _ _
  rw [hcomp, ← Polynomial.hom_eval₂, hp0, map_zero]

private theorem mem_adjoin_range_const (x : FB q) :
    x ∈ IntermediateField.adjoin ↥(F0 (q := q) K) (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q))) := by
  set E := IntermediateField.adjoin ↥(F0 (q := q) K) (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)))
  have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        (fieldOver (1 * q) K : Set (LaurentSeries (AlgebraicClosure ℚ)))) :=
    bar_le_closure K x.2
  have hle : Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
        (fieldOver (1 * q) K : Set (LaurentSeries (AlgebraicClosure ℚ)))) ≤
      E.toSubfield.map (IntermediateField.val (modularFunctionFieldBar (1 * q))).toRingHom := by
    refine Subfield.closure_le.mpr ?_
    rintro ℓ (⟨a, rfl⟩ | hℓ)
    · exact ⟨algebraMap (AlgebraicClosure ℚ) (FB q) a, IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩, rfl⟩
    · refine ⟨⟨ℓ, fieldOver_le_bar K hℓ⟩, ?_, rfl⟩
      have hg : (⟨ℓ, fieldOver_le_bar K hℓ⟩ : FB q) ∈ F0 (q := q) K := hℓ
      exact E.algebraMap_mem ⟨_, hg⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rwa [← this]

private theorem const_mem_adjoin_of_mem {α c : AlgebraicClosure ℚ}
    (hc : c ∈ IntermediateField.adjoin ↥K ({α} : Set (AlgebraicClosure ℚ))) :
    algebraMap (AlgebraicClosure ℚ) (FB q) c ∈
      IntermediateField.adjoin ↥(F0 (q := q) K) ({algebraMap (AlgebraicClosure ℚ) (FB q) α} : Set (FB q)) := by
  let ι : AlgebraicClosure ℚ →ₐ[↥K] FB q := AlgHom.mk (algebraMap (AlgebraicClosure ℚ) (FB q)) fun _ => rfl
  have h1 : ι c ∈ (IntermediateField.adjoin ↥K ({α} : Set (AlgebraicClosure ℚ))).map ι := ⟨c, hc, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  change ι c ∈ Subfield.closure (Set.range (algebraMap ↥K (FB q)) ∪ {ι α}) at h1
  refine (Subfield.closure_le (t := (IntermediateField.adjoin ↥(F0 (q := q) K)
    ({algebraMap (AlgebraicClosure ℚ) (FB q) α} : Set (FB q))).toSubfield)).mpr ?_ h1
  rintro y (⟨k, rfl⟩ | hy)
  · exact IntermediateField.algebraMap_mem _ (constK (q := q) K k)
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact IntermediateField.subset_adjoin _ _ rfl

private theorem exists_mem_adjoin_const (x : FB q) :
    ∃ α : AlgebraicClosure ℚ, x ∈ IntermediateField.adjoin ↥(F0 (q := q) K)
      ({algebraMap (AlgebraicClosure ℚ) (FB q) α} : Set (FB q)) := by
  classical
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin (mem_adjoin_range_const K x)
  choose c hc using fun t : ↥T => hT t.2

  set L := IntermediateField.adjoin ↥K (Set.range c) with hL
  haveI : FiniteDimensional ↥K ↥L :=
    IntermediateField.finiteDimensional_adjoin fun a _ => (isIntegral_rat a).tower_top
  obtain ⟨β, hβ⟩ := Field.exists_primitive_element ↥K ↥L
  refine ⟨(β : AlgebraicClosure ℚ), (IntermediateField.adjoin_le_iff.mpr ?_ : _ ≤ _) hxT⟩
  intro t ht
  have hct : c ⟨t, ht⟩ ∈ IntermediateField.adjoin ↥K ({(β : AlgebraicClosure ℚ)} : Set (AlgebraicClosure ℚ)) := by
    have h1 : c ⟨t, ht⟩ ∈ L := IntermediateField.subset_adjoin _ _ ⟨⟨t, ht⟩, rfl⟩
    have h2 : (⟨c ⟨t, ht⟩, h1⟩ : ↥L) ∈ IntermediateField.adjoin ↥K ({β} : Set ↥L) := by
      rw [hβ]; exact IntermediateField.mem_top
    have h3 := IntermediateField.adjoin_map ↥K ({β} : Set ↥L) L.val
    rw [Set.image_singleton] at h3
    rw [show IntermediateField.adjoin ↥K ({(β : AlgebraicClosure ℚ)} : Set (AlgebraicClosure ℚ)) =
      (IntermediateField.adjoin ↥K ({β} : Set ↥L)).map L.val from h3.symm]
    exact ⟨_, h2, rfl⟩
  have hct' : algebraMap (AlgebraicClosure ℚ) (FB q) (c ⟨t, ht⟩) = t := hc ⟨t, ht⟩
  rw [← hct']
  exact const_mem_adjoin_of_mem K hct

variable (W : Place (AlgebraicClosure ℚ) (FB q))

private def RP : ValuationSubring ↥(F0 (q := q) K) :=
  W.toValuationSubring.comap (algebraMap ↥(F0 (q := q) K) (FB q))

private theorem mem_RP {g : ↥(F0 (q := q) K)} : g ∈ RP K W ↔ (g : FB q) ∈ W.toValuationSubring := Iff.rfl

private scoped instance algebraRPF0 : Algebra ↥(RP K W) ↥(F0 (q := q) K) := inferInstance

private scoped instance smulRPF0 : SMul ↥(RP K W) ↥(F0 (q := q) K) := Algebra.toSMul

private theorem ord_nonneg_of_mem {f : FB q} (hf : f ∈ W.toValuationSubring) : 0 ≤ W.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : W.toValuationSubring)) (fun h0 => hf0 (congrArg Subtype.val h0)) hπ
  have hcoe : f = ((u : W.toValuationSubring) : FB q) * ((π : FB q) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, W.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem mem_of_ord_nonneg {f : FB q} (hf : f ≠ 0) (h : 0 ≤ W.ord f) : f ∈ W.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  obtain ⟨u, hu⟩ := W.exists_unit_mul_zpow hf hπ
  rw [hu, show W.ord f = (((W.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : W.toValuationSubring).2 (pow_mem (π : W.toValuationSubring).2 _)

private scoped instance isPrincipalIdealRing_RP : IsPrincipalIdealRing ↥(RP K W) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : ∀ g ∈ I, g = 0
  · refine ⟨⟨0, ?_⟩⟩
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot.mpr rfl]
    exact eq_bot_iff.mpr fun g hg => Ideal.mem_bot.mpr (hI g hg)
  push Not at hI
  obtain ⟨g₁, hg₁I, hg₁0⟩ := hI

  let ordN : ↥(RP K W) → ℕ := fun g => (W.ord ((g : ↥(F0 (q := q) K)) : FB q)).toNat
  have hex : ∃ n, ∃ g ∈ I, g ≠ 0 ∧ ordN g = n := ⟨_, g₁, hg₁I, hg₁0, rfl⟩
  obtain ⟨g₀, hg₀I, hg₀0, hg₀n⟩ := Nat.find_spec hex
  have hmin : ∀ g ∈ I, g ≠ 0 → ordN g₀ ≤ ordN g := fun g hg hg0 => by
    rw [hg₀n]; exact Nat.find_min' hex ⟨g, hg, hg0, rfl⟩
  refine ⟨⟨g₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hg₀I)⟩⟩
  intro g hg
  rw [Ideal.submodule_span_eq]
  rcases eq_or_ne g 0 with rfl | hg0
  · exact Ideal.zero_mem _

  have hc0 : ∀ {g : ↥(RP K W)}, g ≠ 0 → (((g : ↥(F0 (q := q) K)) : FB q)) ≠ 0 := fun h h0 =>
    h (Subtype.ext (Subtype.ext h0))
  have hord : W.ord (((g : ↥(F0 (q := q) K)) : FB q)) - W.ord (((g₀ : ↥(F0 (q := q) K)) : FB q)) ≥ 0 := by
    have h1 : 0 ≤ W.ord (((g : ↥(F0 (q := q) K)) : FB q)) := ord_nonneg_of_mem W g.2
    have h2 : 0 ≤ W.ord (((g₀ : ↥(F0 (q := q) K)) : FB q)) := ord_nonneg_of_mem W g₀.2
    have h3 : ordN g₀ ≤ ordN g := hmin g hg hg0
    simp only [ordN] at h3
    omega
  have hquot : (((g : ↥(F0 (q := q) K)) : FB q)) * (((g₀ : ↥(F0 (q := q) K)) : FB q))⁻¹ ∈
      W.toValuationSubring := by
    refine mem_of_ord_nonneg W (mul_ne_zero (hc0 hg0) (inv_ne_zero (hc0 hg₀0))) ?_
    rw [W.ord_mul (hc0 hg0) (inv_ne_zero (hc0 hg₀0)), W.ord_inv]
    omega
  let h : ↥(RP K W) := ⟨(g : ↥(F0 (q := q) K)) * (g₀ : ↥(F0 (q := q) K))⁻¹, hquot⟩
  have hgh : g = h * g₀ := by
    apply Subtype.ext; apply Subtype.ext
    show (((g : ↥(F0 (q := q) K)) : FB q)) =
      (((g : ↥(F0 (q := q) K)) : FB q)) * (((g₀ : ↥(F0 (q := q) K)) : FB q))⁻¹ *
        (((g₀ : ↥(F0 (q := q) K)) : FB q))
    rw [inv_mul_cancel_right₀ (hc0 hg₀0)]
  rw [hgh]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private scoped instance isDedekindDomain_RP : IsDedekindDomain ↥(RP K W) := inferInstance

private def constRP : ↥K →+* ↥(RP K W) :=
  (constK (q := q) K).codRestrict (RP K W) fun c => by
    show algebraMap (AlgebraicClosure ℚ) (FB q) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring
    exact W.algebraMap_mem' _

private scoped instance algebraKRP : Algebra ↥K ↥(RP K W) := (constRP K W).toAlgebra

private scoped instance smulKRP : SMul ↥K ↥(RP K W) := Algebra.toSMul

private scoped instance towerKRPF0 : IsScalarTower ↥K ↥(RP K W) ↥(F0 (q := q) K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private def RPtoOW : ↥(RP K W) →+* ↥W.toValuationSubring :=
  ((algebraMap ↥(F0 (q := q) K) (FB q)).comp (algebraMap ↥(RP K W) ↥(F0 (q := q) K))).codRestrict
    W.toValuationSubring fun g => g.2

section M

variable (α : AlgebraicClosure ℚ)

private def M : IntermediateField ↥(F0 (q := q) K) (FB q) :=
  IntermediateField.adjoin ↥(F0 (q := q) K) ({algebraMap (AlgebraicClosure ℚ) (FB q) α} : Set (FB q))

private scoped instance algebraF0M : Algebra ↥(F0 (q := q) K) ↥(M (q := q) K α) := (M (q := q) K α).algebra

private scoped instance moduleF0M : Module ↥(F0 (q := q) K) ↥(M (q := q) K α) := Algebra.toModule

private scoped instance smulF0M : SMul ↥(F0 (q := q) K) ↥(M (q := q) K α) := Algebra.toSMul

private scoped instance algebraMFB : Algebra ↥(M (q := q) K α) (FB q) := (M (q := q) K α).toAlgebra

private scoped instance smulMFB : SMul ↥(M (q := q) K α) (FB q) := Algebra.toSMul

private scoped instance towerF0MFB : IsScalarTower ↥(F0 (q := q) K) ↥(M (q := q) K α) (FB q) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance algebraRPM : Algebra ↥(RP K W) ↥(M (q := q) K α) :=
  ((algebraMap ↥(F0 (q := q) K) ↥(M (q := q) K α)).comp (algebraMap ↥(RP K W) ↥(F0 (q := q) K))).toAlgebra

private scoped instance smulRPM : SMul ↥(RP K W) ↥(M (q := q) K α) := Algebra.toSMul

private scoped instance towerRPF0M : IsScalarTower ↥(RP K W) ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance algebraKM : Algebra ↥K ↥(M (q := q) K α) :=
  ((algebraMap ↥(F0 (q := q) K) ↥(M (q := q) K α)).comp (constK (q := q) K)).toAlgebra

private scoped instance smulKM : SMul ↥K ↥(M (q := q) K α) := Algebra.toSMul

private scoped instance towerKRPM : IsScalarTower ↥K ↥(RP K W) ↥(M (q := q) K α) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance towerKF0M : IsScalarTower ↥K ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance towerKMFB : IsScalarTower ↥K ↥(M (q := q) K α) (FB q) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem algebraMap_RP_M (g : ↥(RP K W)) :
    ((algebraMap ↥(RP K W) ↥(M (q := q) K α) g : ↥(M (q := q) K α)) : FB q) = ((g : ↥(F0 (q := q) K)) : FB q) := rfl

private def αM : ↥(M (q := q) K α) :=
  ⟨algebraMap (AlgebraicClosure ℚ) (FB q) α, IntermediateField.mem_adjoin_simple_self _ _⟩

private theorem isIntegral_K_αM : IsIntegral ↥K (αM (q := q) K α) := by
  have h := isIntegral_K_const (q := q) K α
  have hval : Function.Injective (IsScalarTower.toAlgHom ↥K ↥(M (q := q) K α) (FB q)) := fun a b hab =>
    Subtype.ext hab
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥K ↥(M (q := q) K α) (FB q)) hval).mp h

private theorem isIntegral_RP_αM : IsIntegral ↥(RP K W) (αM (q := q) K α) := (isIntegral_K_αM (q := q) K α).tower_top

private theorem isIntegral_F0_α : IsIntegral ↥(F0 (q := q) K) (algebraMap (AlgebraicClosure ℚ) (FB q) α) :=
  (isIntegral_K_const (q := q) K α).tower_top

private scoped instance finiteDimensional_M : FiniteDimensional ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_F0_α (q := q) K α)

private scoped instance isIntegral_M : Algebra.IsIntegral ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  ⟨fun z => IsIntegral.of_finite (R := ↥(F0 (q := q) K)) z⟩

private scoped instance charZero_F0 : CharZero ↥(F0 (q := q) K) :=
  charZero_of_injective_algebraMap (algebraMap ↥K ↥(F0 (q := q) K)).injective

private scoped instance isSeparable_M : Algebra.IsSeparable ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  ⟨fun z => (minpoly.irreducible (IsIntegral.of_finite (R := ↥(F0 (q := q) K)) z)).separable⟩

private def pb : PowerBasis ↥(F0 (q := q) K) ↥(M (q := q) K α) :=
  IntermediateField.adjoin.powerBasis (isIntegral_F0_α (q := q) K α)

private theorem pb_gen : (pb (q := q) K α).gen = αM (q := q) K α := by
  rw [pb, IntermediateField.adjoin.powerBasis_gen]; rfl

private theorem isIntegral_F0 (x : FB q) : IsIntegral ↥(F0 (q := q) K) x := by
  obtain ⟨α, hx⟩ := exists_mem_adjoin_const K x
  have h1 : IsIntegral ↥(F0 (q := q) K) (⟨x, hx⟩ : ↥(M (q := q) K α)) := IsIntegral.of_finite (R := ↥(F0 (q := q) K)) _
  exact h1.algebraMap

private theorem exists_mem_F0_not_mem : ∃ g : ↥(F0 (q := q) K), (g : FB q) ∉ W.toValuationSubring := by
  by_contra hall
  push Not at hall
  apply W.ne_top'
  refine eq_top_iff.mpr fun x _ => ?_
  let φ : ↥(F0 (q := q) K) →+* ↥W.toValuationSubring :=
    (algebraMap ↥(F0 (q := q) K) (FB q)).codRestrict W.toValuationSubring fun g => hall g
  have hx : IsIntegral ↥W.toValuationSubring x := by
    have h := (isIntegral_F0 K x).map_of_comp_eq φ (RingHom.id (FB q)) (RingHom.ext fun _ => rfl)
    simpa using h
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W.toValuationSubring) (K := FB q)).mp hx
  rw [← hy]
  exact y.2

private def V : ValuationSubring ↥(M (q := q) K α) := W.toValuationSubring.comap (algebraMap ↥(M (q := q) K α) (FB q))

private theorem mem_V {z : ↥(M (q := q) K α)} : z ∈ V K W α ↔ (z : FB q) ∈ W.toValuationSubring := Iff.rfl

private theorem V_ne_top : V K W α ≠ ⊤ := by
  obtain ⟨g, hg⟩ := exists_mem_F0_not_mem K W
  intro h
  have : algebraMap ↥(F0 (q := q) K) ↥(M (q := q) K α) g ∈ V K W α := by rw [h]; trivial
  exact hg this

private theorem mem_V_of_isIntegral {z : ↥(M (q := q) K α)} (hz : IsIntegral ↥(RP K W) z) : z ∈ V K W α := by
  have h : IsIntegral ↥W.toValuationSubring (z : FB q) :=
    hz.map_of_comp_eq (RPtoOW K W) (algebraMap ↥(M (q := q) K α) (FB q)) (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W.toValuationSubring) (K := FB q)).mp h
  rw [mem_V, ← hy]
  exact y.2

private scoped instance algebraRPS : Algebra ↥(RP K W) ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) :=
  (integralClosure ↥(RP K W) ↥(M (q := q) K α)).algebra

private scoped instance smulRPS : SMul ↥(RP K W) ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) := Algebra.toSMul

private scoped instance algebraSM : Algebra ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) ↥(M (q := q) K α) :=
  (integralClosure ↥(RP K W) ↥(M (q := q) K α)).toAlgebra

private scoped instance smulSM : SMul ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) ↥(M (q := q) K α) := Algebra.toSMul

private scoped instance towerRPSM : IsScalarTower ↥(RP K W) ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) ↥(M (q := q) K α) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private def StoV : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) →+* ↥(V K W α) :=
  (algebraMap ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) ↥(M (q := q) K α)).codRestrict (V K W α)
    fun y => mem_V_of_isIntegral K W α y.2

private theorem coe_StoV (y : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))) : ((StoV K W α y : ↥(V K W α)) : ↥(M (q := q) K α)) = y :=
  rfl

private def qS : Ideal ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) :=
  (IsLocalRing.maximalIdeal ↥(V K W α)).comap (StoV K W α)

private scoped instance qS_isPrime : (qS K W α).IsPrime := Ideal.IsPrime.comap _

private theorem inv_mem_V_of_isUnit {z : ↥(V K W α)} (hz : IsUnit z) : ((z : ↥(M (q := q) K α)))⁻¹ ∈ V K W α := by
  obtain ⟨u, hu⟩ := hz
  have hmul : ((u : ↥(V K W α)) : ↥(M (q := q) K α)) * (((u⁻¹ : (↥(V K W α))ˣ) : ↥(V K W α)) : ↥(M (q := q) K α)) = 1 :=
    congrArg Subtype.val u.mul_inv
  have hinv : (((u⁻¹ : (↥(V K W α))ˣ) : ↥(V K W α)) : ↥(M (q := q) K α)) = ((z : ↥(M (q := q) K α)))⁻¹ := by
    rw [eq_inv_of_mul_eq_one_right hmul, hu]
  rw [← hinv]
  exact ((u⁻¹ : (↥(V K W α))ˣ) : ↥(V K W α)).2

private theorem qS_ne_bot : qS K W α ≠ ⊥ := by

  obtain ⟨g, hg⟩ := exists_mem_F0_not_mem K W
  have hg0 : (g : FB q) ≠ 0 := fun h => hg (h ▸ W.toValuationSubring.zero_mem)
  have hginv : (g : FB q)⁻¹ ∈ W.toValuationSubring :=
    (W.toValuationSubring.mem_or_inv_mem _).resolve_left hg
  let r : ↥(RP K W) := ⟨g⁻¹, by rw [mem_RP]; exact hginv⟩
  let rS : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) :=
    ⟨algebraMap ↥(RP K W) ↥(M (q := q) K α) r, isIntegral_algebraMap⟩
  have hrS : ((rS : ↥(M (q := q) K α)) : FB q) = (g : FB q)⁻¹ := rfl
  intro hbot
  have hrq : rS ∈ qS K W α := by
    show StoV K W α rS ∈ IsLocalRing.maximalIdeal ↥(V K W α)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hg
    have hinv := (mem_V K W α).mp (inv_mem_V_of_isUnit K W α hu)
    have h3 : ((((StoV K W α rS : ↥(V K W α)) : ↥(M (q := q) K α))⁻¹ : ↥(M (q := q) K α)) : FB q) =
        (g : FB q) := by
      show ((((StoV K W α rS : ↥(V K W α)) : ↥(M (q := q) K α)) : FB q))⁻¹ = (g : FB q)
      rw [coe_StoV, hrS, inv_inv]
    rw [h3] at hinv
    exact hinv
  rw [hbot, Ideal.mem_bot] at hrq
  have h1 : ((rS : ↥(M (q := q) K α)) : FB q) = 0 := by
    rw [hrq]
    rfl
  exact inv_ne_zero hg0 (hrS.symm.trans h1)

private scoped instance isDedekindDomain_S : IsDedekindDomain ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) :=
  integralClosure.isDedekindDomain (A := ↥(RP K W)) (K := ↥(F0 (q := q) K)) (L := ↥(M (q := q) K α))

private scoped instance isFractionRing_S : IsFractionRing ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) ↥(M (q := q) K α) :=
  integralClosure.isFractionRing_of_finite_extension (A := ↥(RP K W)) (K := ↥(F0 (q := q) K)) (L := ↥(M (q := q) K α))

private def qH : IsDedekindDomain.HeightOneSpectrum ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)) :=
  ⟨qS K W α, inferInstance, qS_ne_bot K W α⟩

private theorem isUnit_StoV {s : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))} (hs : s ∉ qS K W α) :
    IsUnit (StoV K W α s) := by
  by_contra hnu
  exact hs ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))

private theorem mem_atPrime_iff {z : ↥(M (q := q) K α)} :
    z ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(M (q := q) K α) (qH K W α) ↔
      ∃ (a s : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))) (_ : s ∈ (qH K W α).asIdeal.primeCompl),
        z = algebraMap _ ↥(M (q := q) K α) a * (algebraMap _ ↥(M (q := q) K α) s)⁻¹ :=
  Iff.rfl

private theorem algebraMap_S_M (y : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))) :
    algebraMap _ ↥(M (q := q) K α) y = (y : ↥(M (q := q) K α)) :=
  rfl

private theorem atPrime_le_V :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(M (q := q) K α) (qH K W α) ≤ V K W α := by
  intro z hz
  obtain ⟨a, s, hs, rfl⟩ := (mem_atPrime_iff K W α).mp hz
  rw [algebraMap_S_M, algebraMap_S_M]
  have hs' : s ∉ qS K W α := hs
  have ha : ((StoV K W α a : ↥(V K W α)) : ↥(M (q := q) K α)) ∈ V K W α := (StoV K W α a).2
  have hsinv : ((StoV K W α s : ↥(V K W α)) : ↥(M (q := q) K α))⁻¹ ∈ V K W α :=
    inv_mem_V_of_isUnit K W α (isUnit_StoV K W α hs')
  exact mul_mem ha hsinv

private theorem V_eq_atPrime :
    V K W α = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥(M (q := q) K α) (qH K W α) :=
  (ValuationSubring.eq_of_le_of_ne_top _ (atPrime_le_V K W α) (V_ne_top K W α)).symm

private theorem exists_mul_eq_of_mem_V {z : ↥(M (q := q) K α)} (hz : z ∈ V K W α) :
    ∃ a s : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α)), s ∉ qS K W α ∧
      z * (s : ↥(M (q := q) K α)) = (a : ↥(M (q := q) K α)) := by
  rw [V_eq_atPrime] at hz
  obtain ⟨a, s, hs, rfl⟩ := (mem_atPrime_iff K W α).mp hz
  refine ⟨a, s, hs, ?_⟩
  rw [algebraMap_S_M, algebraMap_S_M]
  have hs0 : (s : ↥(M (q := q) K α)) ≠ 0 := fun h => by
    apply hs
    have : s = 0 := Subtype.ext h
    rw [this]
    exact (qS K W α).zero_mem
  rw [inv_mul_cancel_right₀ hs0]

private theorem discr_smul_mem (y : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))) :
    Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (y : ↥(M (q := q) K α)) ∈
      Algebra.adjoin ↥(RP K W) ({αM (q := q) K α} : Set ↥(M (q := q) K α)) := by
  have hint : IsIntegral ↥(RP K W) (pb (q := q) K α).gen := by rw [pb_gen]; exact isIntegral_RP_αM K W α
  have h := Algebra.discr_mul_isIntegral_mem_adjoin (K := ↥(F0 (q := q) K)) (L := ↥(M (q := q) K α)) (R := ↥(RP K W))
    (B := pb (q := q) K α) hint (z := (y : ↥(M (q := q) K α))) y.2
  rwa [pb_gen] at h

private theorem exists_discr_eq_unit : ∃ d : ↥(RP K W),
    (d : ↥(F0 (q := q) K)) = Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis ∧ IsUnit d := by
  have hgen : IsIntegral ↥K (pb (q := q) K α).gen := by rw [pb_gen]; exact isIntegral_K_αM (q := q) K α
  have hdK : IsIntegral ↥K (Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis) :=
    Algebra.discr_isIntegral (K := ↥(F0 (q := q) K)) fun i => by
      rw [PowerBasis.coe_basis]; exact hgen.pow _
  have hd0 : Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis ≠ 0 := Algebra.discr_not_zero_of_basis _ (pb (q := q) K α).basis
  obtain ⟨d, hd⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(RP K W)) (K := ↥(F0 (q := q) K))).mp hdK.tower_top
  obtain ⟨d', hd'⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := ↥(RP K W)) (K := ↥(F0 (q := q) K))).mp hdK.inv.tower_top
  refine ⟨d, hd, isUnit_iff_exists_inv.mpr ⟨d', ?_⟩⟩
  apply Subtype.ext
  show (d : ↥(F0 (q := q) K)) * (d' : ↥(F0 (q := q) K)) = 1
  rw [show (d : ↥(F0 (q := q) K)) = _ from hd, show (d' : ↥(F0 (q := q) K)) = _ from hd', mul_inv_cancel₀ hd0]

private def VtoOW : ↥(V K W α) →+* ↥W.toValuationSubring :=
  ((algebraMap ↥(M (q := q) K α) (FB q)).comp (V K W α).subtype).codRestrict W.toValuationSubring fun z => z.2

private theorem adjoin_le_B : ∀ y ∈ Algebra.adjoin ↥(RP K W) ({αM (q := q) K α} : Set ↥(M (q := q) K α)),
    ((y : ↥(M (q := q) K α)) : FB q) ∈ Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
      {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}) := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subring.subset_closure (Or.inl ⟨α, rfl⟩)
  | algebraMap r =>
    rw [algebraMap_RP_M]
    exact Subring.subset_closure (Or.inr ⟨(mem_F0 K).mp (r : ↥(F0 (q := q) K)).2, (mem_RP K W).mp r.2⟩)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

private theorem coe_discr_smul (z : ↥(M (q := q) K α)) :
    ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • z : ↥(M (q := q) K α)) : FB q) =
      ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis : ↥(F0 (q := q) K)) : FB q) * (z : FB q) := by
  rw [Algebra.smul_def]
  rfl

private theorem coe_coe_mul (y z : ↥(M (q := q) K α)) :
    (((y * z : ↥(M (q := q) K α)) : FB q) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((y : FB q) : LaurentSeries (AlgebraicClosure ℚ)) * ((z : FB q) : LaurentSeries (AlgebraicClosure ℚ)) :=
  rfl

private theorem coe_coe_discr_smul (z : ↥(M (q := q) K α)) :
    (((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • z : ↥(M (q := q) K α)) : FB q) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      (((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis : ↥(F0 (q := q) K)) : FB q) :
          LaurentSeries (AlgebraicClosure ℚ)) * ((z : FB q) : LaurentSeries (AlgebraicClosure ℚ)) :=
  congrArg Subtype.val (coe_discr_smul K α z)

private theorem coe_RPtoOW_mul_VtoOW (d : ↥(RP K W)) (y : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))) :
    ((RPtoOW K W d * VtoOW K W α (StoV K W α y) : ↥W.toValuationSubring) : FB q) =
      ((d : ↥(F0 (q := q) K)) : FB q) * ((y : ↥(M (q := q) K α)) : FB q) :=
  rfl

private theorem core_unit {s₀ : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))} (hs₀ : s₀ ∉ qS K W α)
    {d : ↥(RP K W)} (hd : (d : ↥(F0 (q := q) K)) = Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis)
    (hdu : IsUnit d) :
    ∃ hs : ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (s₀ : ↥(M (q := q) K α)) :
        ↥(M (q := q) K α)) : FB q) ∈ W.toValuationSubring,
      (⟨_, hs⟩ : ↥W.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥W.toValuationSubring := by
  obtain ⟨u, rfl⟩ := hdu
  obtain ⟨v, hv⟩ := isUnit_StoV K W α hs₀

  let w : (↥W.toValuationSubring)ˣ :=
    Units.map (RPtoOW K W).toMonoidHom u * Units.map (VtoOW K W α).toMonoidHom v
  have hw : (w : ↥W.toValuationSubring) = RPtoOW K W u * VtoOW K W α (StoV K W α s₀) := by
    rw [← hv]
    rfl
  have hdF : ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis : ↥(F0 (q := q) K)) : FB q) =
      (((u : ↥(RP K W)) : ↥(F0 (q := q) K)) : FB q) := by rw [hd]
  have hS : ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (s₀ : ↥(M (q := q) K α)) :
      ↥(M (q := q) K α)) : FB q) = ((w : ↥W.toValuationSubring) : FB q) := by
    rw [coe_discr_smul, hdF, hw, coe_RPtoOW_mul_VtoOW]
  have hsO : ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (s₀ : ↥(M (q := q) K α)) :
      ↥(M (q := q) K α)) : FB q) ∈ W.toValuationSubring := by
    rw [hS]
    exact (w : ↥W.toValuationSubring).2
  refine ⟨hsO, fun hmem => ?_⟩
  have heq : (⟨_, hsO⟩ : ↥W.toValuationSubring) = w := Subtype.ext hS
  rw [heq] at hmem
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)) w.isUnit

private theorem core_eq {x : FB q} {a s₀ : ↥(integralClosure ↥(RP K W) ↥(M (q := q) K α))} (y : ↥(M (q := q) K α))
    (hxs : y * (s₀ : ↥(M (q := q) K α)) = (a : ↥(M (q := q) K α))) (hy : (y : FB q) = x) :
    x * ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (s₀ : ↥(M (q := q) K α)) :
        ↥(M (q := q) K α)) : FB q) =
      ((Algebra.discr ↥(F0 (q := q) K) (pb (q := q) K α).basis • (a : ↥(M (q := q) K α)) :
        ↥(M (q := q) K α)) : FB q) := by
  apply Subtype.ext
  show (x : LaurentSeries (AlgebraicClosure ℚ)) * _ = _
  rw [coe_coe_discr_smul, coe_coe_discr_smul, mul_left_comm, ← hy, ← coe_coe_mul, hxs]

private theorem core {x : FB q} (hx : x ∈ W.toValuationSubring) :
    ∃ b ∈ Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
        {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
      ∃ s ∈ Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
        {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
        ∃ hs : s ∈ W.toValuationSubring,
          (⟨s, hs⟩ : ↥W.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥W.toValuationSubring ∧ x * s = b := by
  obtain ⟨α, hxM⟩ := exists_mem_adjoin_const K x
  have hzV : (⟨x, hxM⟩ : ↥(M (q := q) K α)) ∈ V K W α := hx
  obtain ⟨a, s₀, hs₀, hxs⟩ := exists_mul_eq_of_mem_V K W α hzV
  obtain ⟨d, hd, hdu⟩ := exists_discr_eq_unit K W α
  obtain ⟨hsO, hns⟩ := core_unit K W α hs₀ hd hdu
  have heq := core_eq K W α ⟨x, hxM⟩ hxs rfl
  have hbB := adjoin_le_B K W α _ (discr_smul_mem K W α a)
  have hsB := adjoin_le_B K W α _ (discr_smul_mem K W α s₀)
  exact ⟨_, hbB, _, hsB, hsO, hns, heq⟩

private theorem converse {x : FB q}
    (h : ∃ b ∈ Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
        {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
      ∃ s ∈ Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
        {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
        ∃ hs : s ∈ W.toValuationSubring,
          (⟨s, hs⟩ : ↥W.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥W.toValuationSubring ∧ x * s = b) :
    x ∈ W.toValuationSubring := by
  obtain ⟨b, hb, s, -, hs, hns, hxs⟩ := h
  have hBle : Subring.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (FB q)) ∪
      {g : FB q | (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}) ≤
      W.toValuationSubring.toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro g (⟨a, rfl⟩ | hg)
    · exact W.algebraMap_mem' a
    · exact hg.2
  have hbO : b ∈ W.toValuationSubring := hBle hb
  have hu : IsUnit (⟨s, hs⟩ : ↥W.toValuationSubring) := by
    by_contra hnu
    exact hns ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  obtain ⟨u, hu⟩ := hu
  have hst : s * ((u⁻¹ : (↥W.toValuationSubring)ˣ) : ↥W.toValuationSubring).1 = 1 := by
    have h1 : ((u : ↥W.toValuationSubring) * ((u⁻¹ : (↥W.toValuationSubring)ˣ) : ↥W.toValuationSubring)).1 = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    exact h1
  have hx' : x = b * ((u⁻¹ : (↥W.toValuationSubring)ˣ) : ↥W.toValuationSubring).1 := by
    rw [← hxs, mul_assoc, hst, mul_one]
  rw [hx']
  exact W.toValuationSubring.mul_mem _ _ hbO ((u⁻¹ : (↥W.toValuationSubring)ˣ) : ↥W.toValuationSubring).2

end M

end CompNEtaProof
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.CompNEtaProof"

namespace ModularCurve p2m_export "ModularCurve" "jqModC jqNModC modularFunctionFieldBar deg_eq_one_modularFunctionFieldBar laurentBaseChange_adjoin_pair functionFieldGeneration_of_prime" namespace NodeLocalized p2m_export "ModularCurve.NodeLocalized" "fieldOver" end ModularCurve.NodeLocalized
p2m_open_scoped "ModularCurve ModularCurve.NodeLocalized" in

private theorem ModularCurve.NodeLocalized.mem_valuationSubring_iff_exists_mul_eq_of_fieldOver
    {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (x : ↥(modularFunctionFieldBar (1 * q))) :
    x ∈ W.toValuationSubring ↔
      ∃ b ∈ Subring.closure
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
            {g : ↥(modularFunctionFieldBar (1 * q)) |
              (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
      ∃ s ∈ Subring.closure
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
            {g : ↥(modularFunctionFieldBar (1 * q)) |
              (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
        ∃ hs : s ∈ W.toValuationSubring,
          (⟨s, hs⟩ : ↥W.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥W.toValuationSubring ∧ x * s = b :=
  ⟨CompNEtaProof.core K W, CompNEtaProof.converse K W⟩

end
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.CompNEtaProof"

namespace SsfrobEtaGlue

private theorem isRational_bar {q : ℕ} [Fact q.Prime]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : W.IsRational :=
  (Place.isRational_iff_deg_eq_one W).mpr (deg_eq_one_modularFunctionFieldBar (1 * q) W)

private theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

private theorem hasValue_neg {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  have hm := (v.hasValue_algebraMap (-1 : K)).mul h
  rw [map_neg, map_one, neg_one_mul, neg_one_mul] at hm
  exact hm

private theorem evalAt_eq_of_hasValue {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap a]

private theorem mem_valuationSubring_iff_of_forall_hasValue_iff {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K) :
    g ∈ W₁.toValuationSubring ↔ g ∈ W₂.toValuationSubring := by
  constructor
  · intro h₁
    obtain ⟨c, hc, -⟩ := W₁.exists_hasValue_of_surjective (isRational_bar W₁) h₁
    exact ((heq g hg c).mp hc).mem
  · intro h₂
    obtain ⟨c, hc, -⟩ := W₂.exists_hasValue_of_surjective (isRational_bar W₂) h₂
    exact ((heq g hg c).mpr hc).mem

private theorem evalAt_eq_of_forall_hasValue_iff {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    (g : ↥(modularFunctionFieldBar (1 * q)))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (h₁ : g ∈ W₁.toValuationSubring) :
    W₁.evalAt g = W₂.evalAt g := by
  obtain ⟨c, hc, -⟩ := W₁.exists_hasValue_of_surjective (isRational_bar W₁) h₁
  rw [evalAt_eq_of_hasValue hc, evalAt_eq_of_hasValue ((heq g hg c).mp hc)]

private noncomputable def glueB {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (W₁ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Subring ↥(modularFunctionFieldBar (1 * q)) :=
  Subring.closure
    (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      ∪ {g : ↥(modularFunctionFieldBar (1 * q)) |
          (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K
            ∧ g ∈ W₁.toValuationSubring})

private noncomputable def agreeRing {q : ℕ} [Fact q.Prime]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Subring ↥(modularFunctionFieldBar (1 * q)) where
  carrier := {b | ∃ c : AlgebraicClosure ℚ, W₁.HasValue b c ∧ W₂.HasValue b c}
  one_mem' := ⟨1, W₁.hasValue_one, W₂.hasValue_one⟩
  zero_mem' := ⟨0, by
    have h1 := W₁.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    have h2 := W₂.hasValue_algebraMap (0 : AlgebraicClosure ℚ)
    rw [map_zero] at h1 h2
    exact ⟨h1, h2⟩⟩
  add_mem' := fun ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩ => ⟨c + c', hasValue_add h1 h1', hasValue_add h2 h2'⟩
  mul_mem' := fun ⟨c, h1, h2⟩ ⟨c', h1', h2'⟩ => ⟨c * c', h1.mul h1', h2.mul h2'⟩
  neg_mem' := fun ⟨c, h1, h2⟩ => ⟨-c, hasValue_neg h1, hasValue_neg h2⟩

private theorem exists_hasValue_hasValue_of_mem_glueB {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    {b : ↥(modularFunctionFieldBar (1 * q))} (hb : b ∈ glueB K W₁) :
    ∃ c : AlgebraicClosure ℚ, W₁.HasValue b c ∧ W₂.HasValue b c := by
  have hle : glueB K W₁ ≤ agreeRing W₁ W₂ := by
    rw [glueB, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨hxF, hxO⟩)
    · exact ⟨c, W₁.hasValue_algebraMap c, W₂.hasValue_algebraMap c⟩
    · obtain ⟨c, hc, -⟩ := W₁.exists_hasValue_of_surjective (isRational_bar W₁) hxO
      exact ⟨c, hc, (heq x hxF c).mp hc⟩
  exact hle hb

private theorem mem_maximalIdeal_iff_of_mem_glueB {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    {b : ↥(modularFunctionFieldBar (1 * q))} (hb : b ∈ glueB K W₁) :
    (b ∈ W₁.toValuationSubring ∧ W₁.evalAt b = 0)
      ↔ (b ∈ W₂.toValuationSubring ∧ W₂.evalAt b = 0) := by
  obtain ⟨c, h1, h2⟩ := exists_hasValue_hasValue_of_mem_glueB K W₁ W₂ heq hb
  rw [evalAt_eq_of_hasValue h1, evalAt_eq_of_hasValue h2]
  exact ⟨fun ⟨_, hc0⟩ => ⟨h2.mem, hc0⟩, fun ⟨_, hc0⟩ => ⟨h1.mem, hc0⟩⟩

end SsfrobEtaGlue
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.CompNEtaProof"

namespace CompNEtaSkel

private theorem head_iii
    {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (x : ↥(modularFunctionFieldBar (1 * q))) :
    x ∈ W.toValuationSubring ↔
      ∃ b ∈ Subring.closure
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
            {g : ↥(modularFunctionFieldBar (1 * q)) |
              (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
      ∃ s ∈ Subring.closure
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
            {g : ↥(modularFunctionFieldBar (1 * q)) |
              (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W.toValuationSubring}),
        ∃ hs : s ∈ W.toValuationSubring,
          (⟨s, hs⟩ : ↥W.toValuationSubring) ∉ IsLocalRing.maximalIdeal ↥W.toValuationSubring ∧ x * s = b :=
  ModularCurve.NodeLocalized.mem_valuationSubring_iff_exists_mul_eq_of_fieldOver K W x

private theorem glue_exists_hasValue_hasValue_of_mem_B {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    {b : ↥(modularFunctionFieldBar (1 * q))}
    (hb : b ∈ Subring.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
        {g : ↥(modularFunctionFieldBar (1 * q)) |
          (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W₁.toValuationSubring})) :
    ∃ c : AlgebraicClosure ℚ, W₁.HasValue b c ∧ W₂.HasValue b c :=
  SsfrobEtaGlue.exists_hasValue_hasValue_of_mem_glueB K W₁ W₂ heq hb

private theorem glue_mem_maximalIdeal_iff_of_mem_B {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀)
    {b : ↥(modularFunctionFieldBar (1 * q))}
    (hb : b ∈ Subring.closure
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∪
        {g : ↥(modularFunctionFieldBar (1 * q)) |
          (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K ∧ g ∈ W₁.toValuationSubring})) :
    (b ∈ W₁.toValuationSubring ∧ W₁.evalAt b = 0) ↔ (b ∈ W₂.toValuationSubring ∧ W₂.evalAt b = 0) :=
  SsfrobEtaGlue.mem_maximalIdeal_iff_of_mem_glueB K W₁ W₂ heq hb

private theorem isRational_bar {q : ℕ} [Fact q.Prime]
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : W.IsRational :=
  (Place.isRational_iff_deg_eq_one W).mpr (deg_eq_one_modularFunctionFieldBar (1 * q) W)

private theorem mem_maximalIdeal_of_evalAt_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {s : F} (hs : s ∈ v.toValuationSubring) (h0 : v.evalAt s = 0) :
    (⟨s, hs⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit, not_not,
    ← v.algebraMap_evalAt hv hs, h0, map_zero]

private theorem isUnit_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {s : F} (hs : s ∈ v.toValuationSubring) (h : v.evalAt s ≠ 0) :
    IsUnit (⟨s, hs⟩ : v.toValuationSubring) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← v.algebraMap_evalAt hv hs]
  exact fun h0 => h ((algebraMap K v.ResidueField).injective (h0.trans (map_zero _).symm))

private theorem valuationSubring_le {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, V₁.HasValue g c₀ ↔ V₂.HasValue g c₀) :
    V₁.toValuationSubring ≤ V₂.toValuationSubring := by
  intro x hx
  obtain ⟨b, hb, s, hsB, hs, hns, hxs⟩ := (head_iii K V₁ x).mp hx
  obtain ⟨c, -, hc2⟩ := glue_exists_hasValue_hasValue_of_mem_B K V₁ V₂ hV hb
  obtain ⟨d, -, hd2⟩ := glue_exists_hasValue_hasValue_of_mem_B K V₁ V₂ hV hsB
  have hev2 : V₂.evalAt s ≠ 0 := fun h0 =>
    hns (mem_maximalIdeal_of_evalAt_eq_zero V₁ (isRational_bar V₁) hs
      ((glue_mem_maximalIdeal_iff_of_mem_B K V₁ V₂ hV hsB).mpr ⟨hd2.mem, h0⟩).2)
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero V₂ (isRational_bar V₂) hd2.mem hev2
  have hst : s * ((u⁻¹ : V₂.toValuationSubringˣ) : V₂.toValuationSubring).1 = 1 := by
    have h1 : ((u : V₂.toValuationSubring) * ((u⁻¹ : V₂.toValuationSubringˣ) : V₂.toValuationSubring)).1 = 1 :=
      congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    exact h1
  have hx' : x = b * ((u⁻¹ : V₂.toValuationSubringˣ) : V₂.toValuationSubring).1 := by
    rw [← hxs, mul_assoc, hst, mul_one]
  rw [hx']
  exact V₂.toValuationSubring.mul_mem _ _ hc2.mem ((u⁻¹ : V₂.toValuationSubringˣ) : V₂.toValuationSubring).2

end CompNEtaSkel
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver.CompNEtaProof"

theorem solution
    {q : ℕ} [Fact q.Prime]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (W₁ W₂ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (heq : ∀ g : ↥(modularFunctionFieldBar (1 * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K →
      ∀ c₀ : AlgebraicClosure ℚ, W₁.HasValue g c₀ ↔ W₂.HasValue g c₀) :
    W₁ = W₂ :=
  Place.ext (le_antisymm (CompNEtaSkel.valuationSubring_le K W₁ W₂ heq)
    (CompNEtaSkel.valuationSubring_le K W₂ W₁ fun g hg c₀ => (heq g hg c₀).symm))

end S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_place_eq_of_forall_hasValue_iff_of_mem_fieldOver (solution)
