-- Prove2me | solution 1 for M4aHerbrand.isLocalReciprocityMap_of_idelicArtinMap_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/83345aa3-bbc7-57f7-8205-01599f8b9d15

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LocalReciprocity_IsLocalReciprocityMap
import Theorems.Thm_M4aHerbrand_map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq
import Theorems.Thm_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing"
p2m_attr_erase "instance" "NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
set_option autoImplicit false
set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace Ws45
namespace Docking

set_option maxHeartbeats 6400000 in
theorem natCard_residueField_adicCompletionIntegers_eq
    {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Nat.card (R ⧸ v.asIdeal) := by
  classical
  have hv : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers (v.adicCompletionIntegers K) :=
    Valuation.valuationSubring.integers _

  have step1 : ∀ k : K, v.valuation K k ≤ 1 → ∃ r : R, v.valuation K (k - algebraMap R K r) < 1 := by
    intro k hk
    have hkmem : k ∈ (v.valuation K).valuationSubring := hk
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hkmem
    obtain ⟨a, s, hs, rfl⟩ : ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl), k = algebraMap R K a * (algebraMap R K s)⁻¹ := hkmem
    have hs' : s ∉ v.asIdeal := hs

    haveI := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ : ∃ t : R, s * t - 1 ∈ v.asIdeal := by
      have hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0 := by
        rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk v.asIdeal s)⁻¹)
      refine ⟨t, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, ht, mul_inv_cancel₀ hs0, sub_self]
    refine ⟨a * t, ?_⟩
    have hvs : v.valuation K (algebraMap R K s) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hs'
    have hs0K : algebraMap R K s ≠ 0 := by
      intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
    have hrw : algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t) =
        algebraMap R K a * (algebraMap R K s)⁻¹ * (1 - algebraMap R K (s * t)) := by
      rw [map_mul, map_mul]; field_simp
    rw [hrw, map_mul, map_mul, map_inv₀, hvs, inv_one, mul_one]
    calc v.valuation K (algebraMap R K a) * v.valuation K (1 - algebraMap R K (s * t))
        ≤ 1 * v.valuation K (1 - algebraMap R K (s * t)) := by
          gcongr; exact v.valuation_le_one a
      _ < 1 := by
          have ht' : 1 - s * t ∈ v.asIdeal := by rw [← neg_sub]; exact v.asIdeal.neg_mem ht
          rw [one_mul, ← map_one (algebraMap R K), ← map_sub, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
          exact ht'

  let ψ : R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMap R (v.adicCompletionIntegers K))
  have hψ : Function.Surjective ψ := by
    intro xbar
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar

    have hopen : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by
        have h := hz
        simp only [Set.mem_setOf_eq, Units.val_one] at h
        exact (Valuation.restrict_lt_one_iff Valued.v).1 h
      show Valued.v (z - x) < 1
      calc Valued.v (z - x) = Valued.v (z - y + (y - x)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
        _ < 1 := max_lt hz' hy
    obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hopen
      ⟨x, by simp⟩
    have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - (x : v.adicCompletion K)) < 1 := hk
    have hcoeK : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := fun k =>
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    have hkv : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := hcoeK k
    have hk1 : v.valuation K k ≤ 1 := by
      rw [← hkv]
      calc Valued.v (algebraMap K (v.adicCompletion K) k)
          = Valued.v (algebraMap K (v.adicCompletion K) k - x + x) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) k - x)) (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
        _ ≤ 1 := max_le hk'.le x.2
    obtain ⟨r, hr⟩ := step1 k hk1
    refine ⟨r, ?_⟩
    show IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) = IsLocalRing.residue _ x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      hv.isUnit_iff_valuation_eq_one]

    apply ne_of_lt
    have hcoe : (((algebraMap R (v.adicCompletionIntegers K) r - x : v.adicCompletionIntegers K) : v.adicCompletion K)) =
        algebraMap K (v.adicCompletion K) (algebraMap R K r) - (x : v.adicCompletion K) := by
      rw [AddSubgroupClass.coe_sub, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      rfl
    show Valued.v (((algebraMap R (v.adicCompletionIntegers K) r - x : v.adicCompletionIntegers K) : v.adicCompletion K)) < 1
    rw [hcoe]
    have hrk : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k) < 1 := by
      rw [← map_sub, hcoeK, ← neg_sub, Valuation.map_neg]
      exact hr
    calc Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - (x : v.adicCompletion K))
        = Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k +
            (algebraMap K (v.adicCompletion K) k - x)) := by rw [sub_add_sub_cancel]
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k))
            (Valued.v (algebraMap K (v.adicCompletion K) k - x)) := Valuation.map_add _ _ _
      _ < 1 := max_lt hrk hk'
  have hker : ∀ r ∈ v.asIdeal, ψ r = 0 := by
    intro r hr
    show IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      hv.isUnit_iff_valuation_eq_one]
    apply ne_of_lt
    show Valued.v ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) < 1
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.valuation K (algebraMap R K r) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hr
  let ψbar : R ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal ψ hker
  have hsurj : Function.Surjective ψbar := fun y => by
    obtain ⟨r, rfl⟩ := hψ y
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  have hinj : Function.Injective ψbar := RingHom.injective ψbar
  exact (Nat.card_eq_of_bijective ψbar ⟨hinj, hsurj⟩).symm

section local_frame

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem smul_coe (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (k : F) :
    σ • ((k : w.adicCompletion F)) = (((σ : F ≃ₐ[E] F) k : F) : w.adicCompletion F) := by
  rw [NumberField.PlaceDecomp.smul_def]
  show NumberField.PlaceDecomp.actRingEquiv σ
      ((WithVal.toVal (w.valuation F) k : WithVal (w.valuation F)) : w.adicCompletion F)
    = ((WithVal.toVal (w.valuation F) ((σ : F ≃ₐ[E] F) k) : WithVal (w.valuation F)) : w.adicCompletion F)
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem valued_coe (k : F) : Valued.v (k : w.adicCompletion F) = w.valuation F k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k

theorem exists_valued_sub_coe_lt_one (x : w.adicCompletion F) :
    ∃ k : F, Valued.v (x - (k : w.adicCompletion F)) < 1 := by
  have hopen : IsOpen {y : w.adicCompletion F | Valued.v (y - x) < 1} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v (z - y) < 1 := by
      have h := hz
      simp only [Set.mem_setOf_eq, Units.val_one] at h
      exact (Valuation.restrict_lt_one_iff Valued.v).1 h
    show Valued.v (z - x) < 1
    calc Valued.v (z - x) = Valued.v (z - y + (y - x)) := by rw [sub_add_sub_cancel]
      _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
      _ < 1 := max_lt hz' hy
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap F w).exists_mem_open hopen ⟨x, by simp⟩
  refine ⟨k, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hk

theorem mem_inertiaSubgroup_iff_mem_inertiaSet (h : ↥(NumberField.PlaceDecomp.decomp E F w)) :
    h ∈ ((w.valuation F).valuationSubring).inertiaSubgroup E ↔
      h ∈ LocalReciprocity.inertiaSet (w.adicCompletion F) ↥(NumberField.PlaceDecomp.decomp E F w) := by
  have hint : (w.valuation F).Integers (w.valuation F).valuationSubring := Valuation.valuationSubring.integers _

  have step1 : h ∈ ((w.valuation F).valuationSubring).inertiaSubgroup E ↔
      ∀ x : (w.valuation F).valuationSubring, w.valuation F ((h : F ≃ₐ[E] F) x - x) < 1 := by
    have hcoe : ∀ x : (w.valuation F).valuationSubring,
        (((h • x - x : (w.valuation F).valuationSubring)) : F) = (h : F ≃ₐ[E] F) x - x := fun x => rfl
    have hmax : ∀ x : (w.valuation F).valuationSubring,
        h • x - x ∈ IsLocalRing.maximalIdeal ((w.valuation F).valuationSubring) ↔ w.valuation F ((h : F ≃ₐ[E] F) x - x) < 1 := by
      intro x
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]
      have hle : w.valuation F ((h : F ≃ₐ[E] F) x - x) ≤ 1 := hint.map_le_one (h • x - x)
      change ¬ w.valuation F ((h : F ≃ₐ[E] F) x - x) = 1 ↔ _
      exact ⟨fun hne => lt_of_le_of_ne hle hne, fun hlt => ne_of_lt hlt⟩
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    constructor
    · intro hker x
      rw [← hmax, ← Ideal.Quotient.eq]
      show IsLocalRing.residue _ (h • x) = IsLocalRing.residue _ x
      rw [IsLocalRing.ResidueField.residue_smul]
      exact RingEquiv.congr_fun hker (IsLocalRing.residue _ x)
    · intro hall
      ext y
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
      show h • IsLocalRing.residue _ x = IsLocalRing.residue _ x
      rw [← IsLocalRing.ResidueField.residue_smul]
      exact (Ideal.Quotient.eq).2 ((hmax x).2 (hall x))
  rw [step1]
  simp only [LocalReciprocity.inertiaSet, Set.mem_setOf_eq]
  constructor
  · intro hall x hx
    obtain ⟨k, hk⟩ := exists_valued_sub_coe_lt_one F w x
    have hk1 : w.valuation F k ≤ 1 := by
      rw [← valued_coe F w k]
      calc Valued.v (k : w.adicCompletion F) = Valued.v ((k : w.adicCompletion F) - x + x) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v ((k : w.adicCompletion F) - x)) (Valued.v x) := Valuation.map_add _ _ _
        _ ≤ 1 := max_le (by rw [Valuation.map_sub_swap]; exact hk.le) hx
    have hAk := hall ⟨k, (Valuation.mem_valuationSubring_iff _ _).2 hk1⟩
    have hsub : (((((h : F ≃ₐ[E] F) k - k : F)) : w.adicCompletion F)) =
        (((h : F ≃ₐ[E] F) k : F) : w.adicCompletion F) - (k : w.adicCompletion F) :=
      map_sub (algebraMap F (w.adicCompletion F)) _ _
    have h2 : Valued.v (h • (k : w.adicCompletion F) - (k : w.adicCompletion F)) < 1 := by
      rw [smul_coe, ← hsub, valued_coe]
      exact hAk
    have h1 : Valued.v (h • (x - (k : w.adicCompletion F))) < 1 := by
      rw [NumberField.PlaceDecomp.valued_smul]; exact hk
    have h3 : Valued.v ((k : w.adicCompletion F) - x) < 1 := by rw [Valuation.map_sub_swap]; exact hk
    have hdec : h • x - x = h • (x - (k : w.adicCompletion F)) +
        ((h • (k : w.adicCompletion F) - (k : w.adicCompletion F)) + ((k : w.adicCompletion F) - x)) := by
      rw [smul_sub]; abel
    rw [hdec]
    exact Valuation.map_add_lt _ h1 (Valuation.map_add_lt _ h2 h3)
  · intro hloc x
    have hx1 : Valued.v ((x : F) : w.adicCompletion F) ≤ 1 := by
      rw [valued_coe]; exact (Valuation.mem_valuationSubring_iff _ _).1 x.2
    have := hloc ((x : F) : w.adicCompletion F) hx1
    have hsub : (((((h : F ≃ₐ[E] F) x - x : F)) : w.adicCompletion F)) =
        (((h : F ≃ₐ[E] F) x : F) : w.adicCompletion F) - ((x : F) : w.adicCompletion F) :=
      map_sub (algebraMap F (w.adicCompletion F)) _ _
    rw [smul_coe, ← hsub, valued_coe] at this
    exact this

end local_frame

theorem isArithFrobAt_of_isArithFrobenius
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (φ : ↥(NumberField.PlaceDecomp.decomp E F w))
    (hφ : LocalReciprocity.IsArithFrobenius (v.adicCompletion E) (w.adicCompletion F)
      ↥(NumberField.PlaceDecomp.decomp E F w) φ) :
    IsArithFrobAt (𝓞 E) (φ : F ≃ₐ[E] F) w.asIdeal := by
  haveI := v.isMaximal
  have hq : Nat.card (IsLocalRing.ResidueField ((Valued.v (R := v.adicCompletion E)).valuationSubring)) =
      Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    have h1 : w.asIdeal.under (𝓞 E) = v.asIdeal := by rw [← hw]; rfl
    rw [h1]
    exact natCard_residueField_adicCompletionIntegers_eq E v
  intro x
  show (φ : F ≃ₐ[E] F) • x - x ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have hx1 : Valued.v (((x : F)) : w.adicCompletion F) ≤ 1 := by
    rw [valued_coe]; exact HeightOneSpectrum.valuation_le_one w x
  have key := hφ ((x : F) : w.adicCompletion F) hx1
  rw [hq, smul_coe] at key
  have hcast : ((((φ : F ≃ₐ[E] F) (x : F) - (x : F) ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) : F)) : w.adicCompletion F)
      = (((φ : F ≃ₐ[E] F) (x : F) : F) : w.adicCompletion F) - (((x : F)) : w.adicCompletion F) ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    have hms := map_sub (algebraMap F (w.adicCompletion F)) ((φ : F ≃ₐ[E] F) (x : F)) ((x : F) ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)))
    rw [map_pow] at hms
    exact hms
  rw [← hcast, valued_coe] at key
  have hcoe : algebraMap (𝓞 F) F ((φ : F ≃ₐ[E] F) • x - x ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)))
      = (φ : F ≃ₐ[E] F) (x : F) - (x : F) ^ Nat.card (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := by
    rw [map_sub, map_pow]; rfl
  exact key

section idele

variable (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))

theorem idele_ext {x y : (AdeleRing (𝓞 E) E)ˣ} (hinf : infPart x = infPart y)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 E), finPart w x = finPart w y) : x = y := by
  apply Units.ext
  apply Prod.ext
  · exact congrArg Units.val hinf
  · apply RestrictedProduct.ext
    intro w
    exact congrArg Units.val (hfin w)

theorem eq_of_mem_idelesTrivialOn {x y : (AdeleRing (𝓞 E) E)ˣ}
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hy : y ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hv : finPart v x = finPart v y) : x = y := by
  rw [mem_idelesTrivialOn_iff] at hx hy
  refine idele_ext E (hx.1.trans hy.1.symm) fun w => ?_
  by_cases hw : w = v
  · subst hw; exact hv
  · rw [hx.2 w (Set.mem_compl_singleton_iff.2 hw), hy.2 w (Set.mem_compl_singleton_iff.2 hw)]

theorem valued_finPart_eq_one_of_mem_unitIdelesTrivialOn (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    Valued.v ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 := by
  rw [mem_unitIdelesTrivialOn_iff] at hx
  obtain ⟨h1, h2⟩ := hx.1 v (fun h => h rfl)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have hmul : ((x : AdeleRing (𝓞 E) E).2 v) * (((x⁻¹ : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 v) = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 E) E => y.2 v) x.mul_inv
    exact h
  have hv := congrArg Valued.v hmul
  rw [map_mul, map_one] at hv
  show Valued.v ((x : AdeleRing (𝓞 E) E).2 v) = 1
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((x : AdeleRing (𝓞 E) E).2 v) *
          Valued.v ((((x⁻¹ : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E).2 v)) := hv.symm
      _ ≤ Valued.v ((x : AdeleRing (𝓞 E) E).2 v) * 1 := by gcongr
      _ = _ := mul_one _)

theorem mem_unitIdelesTrivialOn_of_valued_eq_one (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hv : Valued.v ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) :
    x ∈ unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := by
  rw [mem_unitIdelesTrivialOn_iff]
  refine ⟨fun w hw => ?_, (mem_idelesTrivialOn_iff _ _).1 hx⟩
  have hwv : w = v := by
    by_contra h
    exact hw (Set.mem_compl_singleton_iff.2 h)
  subst hwv
  have hv' : Valued.v ((finPart w x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  refine ⟨?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((finPart w x : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((finPart w x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [hv']

theorem placeOrd_eq_of_valued_finPart (x : (AdeleRing (𝓞 E) E)ˣ) (n : ℤ)
    (hv : Valued.v ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-n)) :
    placeOrd E (projFin E x) v = n := by
  unfold placeOrd
  show -WithZero.log (Valued.v ((finPart v x : (v.adicCompletion E)ˣ) : v.adicCompletion E)) = n
  rw [hv, WithZero.log_exp, neg_neg]

end idele

theorem coe_finprod_units {ι M : Type*} [CommMonoid M] [Finite ι] (f : ι → Mˣ) :
    ((∏ᶠ i, f i : Mˣ) : M) = ∏ᶠ i, ((f i : Mˣ) : M) :=
  (Units.coeHom M).map_finprod (Set.toFinite _)

theorem mem_inertiaSet_iff_coe_mem_inertia
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))
    (h : ↥(NumberField.PlaceDecomp.decomp E F w)) :
    h ∈ LocalReciprocity.inertiaSet (w.adicCompletion F) ↥(NumberField.PlaceDecomp.decomp E F w) ↔
      (h : F ≃ₐ[E] F) ∈ w.asIdeal.inertia (F ≃ₐ[E] F) := by
  rw [← mem_inertiaSubgroup_iff_mem_inertiaSet,
    ← IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia E F w, Subgroup.mem_map]
  constructor
  · intro hh; exact ⟨h, hh, rfl⟩
  · rintro ⟨h', hh', he⟩
    have : h' = h := Subtype.ext he
    exact this ▸ hh'

end Ws45.Docking

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)

    (ιv : (v.adicCompletion E)ˣ →* (AdeleRing (𝓞 E) E)ˣ)
    (hιv : ∀ z, ιv z ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (hιv' : ∀ z, finPart v (ιv z) = z)
    (θ : (v.adicCompletion E)ˣ →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hθ : ∀ z, ((θ z : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = r (ιv z)) :
    LocalReciprocity.IsLocalReciprocityMap (v.adicCompletion E) (w.adicCompletion F)
      (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
        v.adicCompletion E →+* w.adicCompletion F)
      ↥(NumberField.PlaceDecomp.decomp E F w) θ := by
  classical
  haveI : w.asIdeal.IsPrime := w.isPrime

  have hUT : unitIdelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) ≤
      idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) := unitIdelesTrivialOn_le_idelesTrivialOn (𝓞 E) E _
  have hX0 := M4aHerbrand.map_idelesTrivialOn_eq_decomp_and_map_unitIdelesTrivialOn_eq_inertia E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v w hw

  have hpin : ∀ x, x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))) → x = ιv (finPart v x) :=
    fun x hx => Ws45.Docking.eq_of_mem_idelesTrivialOn E v hx (hιv _) (hιv' _).symm

  have hi0 : ∀ a : (v.adicCompletion E)ˣ,
      (IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F)) :
        v.adicCompletion E →+* w.adicCompletion F) (a : v.adicCompletion E) ≠ 0 :=
    fun a => (map_ne_zero _).2 a.ne_zero
  refine
    { surjective := ?_
      apply_eq_one_iff := ?_
      mem_of_finprod_quotient_smul_eq := ?_
      image_units_eq_inertiaSet := ?_
      mul_zpow_neg_mem_inertiaSet := ?_ }
  ·
    intro g
    have hg : (g : F ≃ₐ[E] F) ∈ (idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))).map r := by
      rw [hX0.1]; exact g.2
    obtain ⟨x, hx, hgx⟩ := hg
    refine ⟨finPart v x, Subtype.ext ?_⟩
    rw [hθ, ← hpin x hx]
    exact hgx
  ·
    intro a
    rw [← OneMemClass.coe_eq_one, hθ,
      M4aHerbrand.idelicArtinMap_single_eq_one_iff_exists_finprod_smul_eq E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄ v a (ιv a) (hιv a) (hιv' a) w hw]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨(b : w.adicCompletion F), ?_⟩
      rw [Ws45.Docking.coe_finprod_units] at hb
      exact hb
    · rintro ⟨b, hb⟩
      have hb0 : b ≠ 0 := by
        intro h0
        apply hi0 a
        rw [← hb, h0]
        exact finprod_eq_zero _ (1 : ↥(NumberField.PlaceDecomp.decomp E F w)) (smul_zero _) (Set.toFinite _)
      refine ⟨Units.mk0 b hb0, ?_⟩
      rw [Ws45.Docking.coe_finprod_units]
      exact hb
  ·
    intro H' a b hb hN
    haveI : Finite (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H') := inferInstance
    have hb0 : b ≠ 0 := by
      intro h0
      apply hi0 a
      rw [← hN, h0]
      exact finprod_eq_zero _ (((1 : ↥(NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H')
        (smul_zero _) (Set.toFinite _)
    set bu : (w.adicCompletion F)ˣ := Units.mk0 b hb0 with hbu
    have hb' : ∀ h ∈ H', h • bu = bu := fun h hh => Units.ext (by
      rw [NumberField.PlaceDecomp.coe_smul_units, hbu, Units.val_mk0]; exact hb h hh)
    have hN' : (((∏ᶠ c : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ H', (Quotient.out c) • bu : (w.adicCompletion F)ˣ) :
        (w.adicCompletion F)ˣ) : w.adicCompletion F) =
        IsDedekindDomain.HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, hw⟩ : v.Extension (𝓞 F))
          (a : v.adicCompletion E) := by
      rw [Ws45.Docking.coe_finprod_units]
      exact hN
    have key := M4aHerbrand.idelicArtinMap_single_mem_map_subtype_of_finprod_smul_eq E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v a (ιv a) (hιv a) (hιv' a) w hw H' bu hb' hN'
    obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 key
    have : h' = θ a := Subtype.ext (by rw [hθ]; exact he)
    exact this ▸ hh'
  ·
    ext h
    rw [Ws45.Docking.mem_inertiaSet_iff_coe_mem_inertia, ← hX0.2]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hθ]
      exact ⟨ιv a, Ws45.Docking.mem_unitIdelesTrivialOn_of_valued_eq_one E v (ιv a) (hιv a)
        (by rw [hιv']; exact ha), rfl⟩
    · rintro ⟨x, hx, hxh⟩
      refine ⟨finPart v x, Ws45.Docking.valued_finPart_eq_one_of_mem_unitIdelesTrivialOn E v x hx, Subtype.ext ?_⟩
      rw [hθ, ← hpin x (hUT hx)]
      exact hxh
  ·
    intro φ hφ a n ha
    have hφ' := Ws45.Docking.isArithFrobAt_of_isArithFrobenius E F v w hw φ hφ
    have h03 := M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt E F 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      v a (ιv a) (hιv a) (hιv' a) w hw (φ : F ≃ₐ[E] F) hφ'
    have hord : placeOrd E (projFin E (ιv a)) v = n :=
      Ws45.Docking.placeOrd_eq_of_valued_finPart E v (ιv a) n (by rw [hιv']; exact ha)
    rw [hord] at h03
    rw [Ws45.Docking.mem_inertiaSet_iff_coe_mem_inertia, Subgroup.coe_mul, SubgroupClass.coe_zpow, hθ, zpow_neg]
    exact h03

end S_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single
end P2MW
export P2MW.S_M4aHerbrand_isLocalReciprocityMap_of_idelicArtinMap_single (solution)
