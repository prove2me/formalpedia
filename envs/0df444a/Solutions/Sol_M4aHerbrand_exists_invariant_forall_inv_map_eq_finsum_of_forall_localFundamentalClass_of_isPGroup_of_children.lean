-- Prove2me | solution 1 for M4aHerbrand.exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c33da53a-8e2d-57d0-a514-3f91972b9324

import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_Corestriction2
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SIdeleModule
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import Theorems.Thm_groupCohomology_Cores_map_cores_eq_cores_map
import Theorems.Thm_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
import Theorems.Thm_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1
import Theorems.Thm_groupCohomology_natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Theorems.Thm_M4aHerbrand_exists_hom_ideles_ideleClassGroup_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
import Theorems.Thm_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup
import Theorems.Thm_M4aHerbrand_exists_res_ideles_iso_res_mulEquiv_fixedField
import Theorems.Thm_M4aHerbrand_finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp
import Theorems.Thm_M4aHerbrand_ideleGaloisDescent_restrict_intermediateField
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_NumberField_compositum_isPGroup_and_normal_and_inf_eq_bot_and_exists_generators
import Theorems.Thm_NumberField_exists_isGalois_compositum
import Theorems.Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

namespace C9p

variable (E F M : Type) [Field E] [Field F] [Field M] [Algebra E F] [Algebra E M] [Algebra F M]
  [IsScalarTower E F M] [Normal E F]

noncomputable abbrev galKer : Subgroup (M ≃ₐ[E] M) := (AlgEquiv.restrictNormalHom F : (M ≃ₐ[E] M) →* (F ≃ₐ[E] F)).ker

scoped instance galKer_normal : (galKer E F M).Normal := MonoidHom.normal_ker _

variable [Normal E M]

theorem restrictNormalHom_surjective' : Function.Surjective (AlgEquiv.restrictNormalHom F : (M ≃ₐ[E] M) →* (F ≃ₐ[E] F)) :=
  AlgEquiv.restrictNormalHom_surjective M

noncomputable def quotEquiv : (M ≃ₐ[E] M) ⧸ galKer E F M ≃* (F ≃ₐ[E] F) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (restrictNormalHom_surjective' E F M)

theorem quotEquiv_mk (g : M ≃ₐ[E] M) : quotEquiv E F M (QuotientGroup.mk g) = AlgEquiv.restrictNormalHom F g := rfl

theorem algebraMap_quotEquiv_mk (g : M ≃ₐ[E] M) (x : F) :
    algebraMap F M (quotEquiv E F M (QuotientGroup.mk g) x) = g (algebraMap F M x) := by
  rw [quotEquiv_mk]
  exact AlgEquiv.restrictNormal_commutes g F x

omit [Normal E M] in

theorem mem_galKer_iff (g : M ≃ₐ[E] M) : g ∈ galKer E F M ↔ ∀ x : F, g (algebraMap F M x) = algebraMap F M x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x
    have := AlgEquiv.restrictNormal_commutes g F x
    rw [show AlgEquiv.restrictNormalHom F g = g.restrictNormal F from rfl] at h
    rw [h] at this
    simpa using this.symm
  · intro h
    apply AlgEquiv.ext
    intro x
    apply (algebraMap F M).injective
    rw [show AlgEquiv.restrictNormalHom F g = g.restrictNormal F from rfl, AlgEquiv.restrictNormal_commutes]
    simpa using h x

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace C9p

universe u
variable {k G Q : Type} [CommRing k] [Group G] [Group Q] (S : Subgroup G) [S.Normal] (ι : G ⧸ S ≃* Q)
  (X : Rep.{0} k Q) (Y : Rep.{0} k G)
  (j : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) X ⟶ Y)
  (hinj : Function.Injective j.hom)
  (hrange : ∀ c : Y.V, c ∈ Set.range j.hom ↔ ∀ s : G, s ∈ S → Y.ρ s c = c)

include hrange in
theorem mem_invariants_jhom (x : X.V) : j.hom x ∈ Representation.invariants (Y.ρ.comp S.subtype) := by
  rw [Representation.mem_invariants]
  rintro ⟨s, hs⟩
  exact ((hrange (j.hom x)).mp ⟨x, rfl⟩) s hs

noncomputable def eLin : X.V ≃ₗ[k] Representation.invariants (Y.ρ.comp S.subtype) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (j.hom : X.V →ₗ[k] Y.V) (mem_invariants_jhom S ι X Y j hrange))
    ⟨fun a b h => hinj (by have h__af := congrArg Subtype.val h; simp at h__af; exact h__af),
     fun ⟨c, hc⟩ => by
        obtain ⟨x, hx⟩ := (hrange c).mpr (fun s hs => by simpa using hc ⟨s, hs⟩)
        exact ⟨x, Subtype.ext hx⟩⟩

theorem eLin_apply_val (x : X.V) : ((eLin S ι X Y j hinj hrange x : Representation.invariants (Y.ρ.comp S.subtype)) : Y.V) = j.hom x := rfl

theorem jhom_rho (g : G) (x : X.V) : j.hom (X.ρ (ι (QuotientGroup.mk g)) x) = Y.ρ g (j.hom x) := by
  have := Representation.IntertwiningMap.isIntertwining _ _ j.hom g x
  simpa using this

noncomputable def eIso : Rep.res ι.toMonoidHom X ≅ Y.quotientToInvariants S :=
  Rep.mkIso (Representation.Equiv.mk (eLin S ι X Y j hinj hrange) (fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change j.hom (X.ρ (ι.toMonoidHom (QuotientGroup.mk g)) x) = Y.ρ g (j.hom x)
      exact jhom_rho S ι X Y j g x))

theorem eIso_hom_val (x : X.V) : ((Rep.Hom.hom (eIso S ι X Y j hinj hrange).hom x : Representation.invariants (Y.ρ.comp S.subtype)) : Y.V) = j.hom x := rfl

theorem res_eIso_comp_lift :
    (Rep.resFunctor (QuotientGroup.mk' S)).map (eIso S ι X Y j hinj hrange).hom ≫
        Rep.ofHom (Y.ρ.quotientToInvariants_lift S) = j := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

include hinj hrange in

theorem map_injective_and_range_eq_ker (hS : Limits.IsZero (groupCohomology (Rep.res S.subtype Y) 1)) :
    Function.Injective (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) j 2).hom ∧
    LinearMap.range (ModuleCat.Hom.hom (groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) j 2)) =
      LinearMap.ker (ModuleCat.Hom.hom (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype Y)) 2)) := by

  have hfac : groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) j 2 =
      groupCohomology.map ι.toMonoidHom (eIso S ι X Y j hinj hrange).hom 2 ≫
        groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (Y.ρ.quotientToInvariants_lift S)) 2 := by
    rw [← groupCohomology.map_comp, res_eIso_comp_lift]

  obtain ⟨ψ, hψ⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv ι (Y.quotientToInvariants S) X
    (eIso S ι X Y j hinj hrange).symm 2
  have hfirst : ∀ x, (groupCohomology.map ι.toMonoidHom (eIso S ι X Y j hinj hrange).hom 2).hom x = ψ.symm x := by
    intro x; rw [hψ]; rfl
  obtain ⟨hinj2, hrange2⟩ := groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1 Y S hS
  refine ⟨?_, ?_⟩
  · rw [hfac]
    intro a b hab
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hfirst] at hab
    exact ψ.symm.injective (hinj2 hab)
  · rw [hfac, ← hrange2]
    ext y
    simp only [ModuleCat.hom_comp, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, hfirst]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨ψ.symm x, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨ψ z, by rw [LinearEquiv.symm_apply_apply]⟩

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace C9p

theorem addOrderOf_coe_one_div (n : ℕ) (hn : 0 < n) :
    addOrderOf ((((1 : ℚ) / (n : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = n := by
  have h := AddCircle.addOrderOf_div_of_gcd_eq_one (p := (1 : ℚ)) (m := 1) hn (Nat.gcd_one_left n)
  simpa using h

theorem nsmul_coe_one_div (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a • ((((1 : ℚ) / ((a * b : ℕ) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = ((((1 : ℚ) / (b : ℚ)) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  push_cast
  field_simp

theorem span_singleton_eq_top_of_addOrderOf_eq_natCard {M : Type*} [AddCommGroup M] [instM : Module ℤ M] [Finite M] (y : M)
    (hy : addOrderOf y = Nat.card M) : Submodule.span ℤ {y} = ⊤ := by
  have h2 : AddSubgroup.zmultiples y = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hy]
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ AddSubgroup.zmultiples y := by rw [h2]; trivial
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  exact Submodule.mem_span_singleton.mpr ⟨k, int_smul_eq_zsmul instM k y⟩

theorem addMonoidHom_eq_of_span_singleton {M N : Type*} [AddCommGroup M] [instM : Module ℤ M] [AddCommGroup N] (y : M)
    (hy : Submodule.span ℤ {y} = ⊤) (f g : M →+ N) (h : f y = g y) : f = g := by
  ext x
  have hx : x ∈ Submodule.span ℤ {y} := by rw [hy]; trivial
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hk : (k • y : M) = @HSMul.hSMul ℤ M M instHSMul k y := rfl
  rw [show (@HSMul.hSMul ℤ M M (@instHSMul ℤ M instM.toSMul) k y) = k • y from int_smul_eq_zsmul instM k y, map_zsmul, map_zsmul, h]

variable {G : Type} [Group G] [Fintype G] (X : Rep.{0} ℤ G)

attribute [local instance] groupCohomology.Cores.fintypeQuot in

theorem exists_invariant_family
    (invG : groupCohomology X 2 →+ AddCircle (1 : ℚ)) (hinjG : Function.Injective invG)
    (hrG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0)
    (hcardG : Nat.card (groupCohomology X 2) = Nat.card G)
    (h5 : ∀ (S : Subgroup G) [Fintype S], Finite (groupCohomology (Rep.res S.subtype X) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype X) 2) ≤ Fintype.card S) :
    ∃ (inv : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype X) 2 →+ AddCircle (1 : ℚ)),
      (∀ H : Subgroup G, Function.Injective (inv H)) ∧
      (∀ (H : Subgroup G) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧
      (∀ (H : Subgroup G) (x : groupCohomology X 2),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom x) = H.index • invG x) ∧
      (∀ (H : Subgroup G) (τ : Cores.Transversal H) (z : groupCohomology (Rep.res H.subtype X) 2),
        invG (Cores.cores X τ z) = inv H z) := by
  classical
  have hGpos : 0 < Nat.card G := Nat.card_pos

  obtain ⟨u, hu⟩ : ∃ u : groupCohomology X 2, invG u = ((((1 : ℚ) / (Nat.card G : ℚ)) : ℚ) : AddCircle (1 : ℚ)) :=
    (hrG _).mpr (by rw [← AddCircle.coe_nsmul, nsmul_eq_mul, mul_one_div_cancel (by exact_mod_cast hGpos.ne'), AddCircle.coe_period])
  have hordu : addOrderOf u = Nat.card G := by
    rw [← addOrderOf_injective invG hinjG, hu, addOrderOf_coe_one_div _ hGpos]
  haveI : Finite (groupCohomology X 2) := Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hGpos.ne')
  have hspanu : Submodule.span ℤ {u} = ⊤ :=
    span_singleton_eq_top_of_addOrderOf_eq_natCard u (by rw [hordu, hcardG])

  let cor : ∀ S : Subgroup G, groupCohomology (Rep.res S.subtype X) 2 →ₗ[ℤ] groupCohomology X 2 :=
    fun S => Cores.cores X (Classical.choice Cores.Transversal.nonempty)
  have hcor : ∀ (S : Subgroup G) (x : groupCohomology X 2),
      cor S ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x :=
    fun S x => Cores.cores_map_res_eq_index_smul X S _ x

  obtain ⟨hcard, hspan⟩ := groupCohomology.natCard_eq_and_span_map_eq_top_of_addOrderOf_eq_natCard X u hordu h5 cor hcor
  obtain ⟨invG', inv, hiG', hiH, hrG', hrH, hR, huG', huH⟩ :=
    groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top X u hcard hspan

  have heq : invG' = invG := addMonoidHom_eq_of_span_singleton u hspanu _ _ (by rw [huG', hu])
  subst heq
  refine ⟨inv, hiH, hrH, hR, ?_⟩

  intro H τ
  have key : (invG'.comp (Cores.cores X τ).toAddMonoidHom) = inv H := by
    apply addMonoidHom_eq_of_span_singleton _ (hspan H)
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [Cores.cores_map_res_eq_index_smul X H τ u, map_nsmul, hR H u]
  intro z
  exact DFunLike.congr_fun key z

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
open NumberField

namespace C9p

section down
variable (E L F' : Type) [Field E] [Field L] [Field F'] [NumberField E] [NumberField L] [NumberField F']
  [Algebra E L] [Algebra E F'] [Algebra L F'] [IsScalarTower E L F'] [IsGalois E F'] [IsGalois E L]

omit [NumberField E] in

theorem hinf_iff_forall_isUnramified (K : Type) [Field K] [NumberField K] [Algebra E K] [IsGalois E K] :
    (∀ (v : InfinitePlace K) (g : (K ≃ₐ[E] K)), g ∈ MulAction.stabilizer (K ≃ₐ[E] K) v → g = 1) ↔
      ∀ v : InfinitePlace K, v.IsUnramified E := by
  constructor
  · intro h v
    rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot, eq_bot_iff]
    intro g hg
    exact h v g hg
  · intro h v g hg
    have := h v
    rw [InfinitePlace.isUnramified_iff_stabilizer_eq_bot] at this
    rw [this] at hg
    exact hg

omit [NumberField E] in

theorem hinf_of_tower
    (h : ∀ (v : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ MulAction.stabilizer (F' ≃ₐ[E] F') v → g = 1) :
    ∀ (v : InfinitePlace L) (g : (L ≃ₐ[E] L)), g ∈ MulAction.stabilizer (L ≃ₐ[E] L) v → g = 1 := by
  rw [hinf_iff_forall_isUnramified] at h ⊢
  intro v
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F') (k := L) v
  exact (h w).comap (K := L)

end down
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

section up
variable (E F M : Type) [Field E] [Field F] [Field M] [Algebra E F] [Algebra E M] [Algebra F M]
  [IsScalarTower E F M] [Normal E F]

theorem restrictNormal_mem_stabilizer_comap (g : M ≃ₐ[E] M) (W : InfinitePlace M)
    (hg : g ∈ MulAction.stabilizer (M ≃ₐ[E] M) W) :
    AlgEquiv.restrictNormal g F ∈ MulAction.stabilizer (F ≃ₐ[E] F) (W.comap (algebraMap F M)) := by
  rw [MulAction.mem_stabilizer_iff, InfinitePlace.smul_eq_comap] at hg ⊢

  have hcomm : (algebraMap F M).comp ((AlgEquiv.restrictNormal g F).symm : F →+* F) =
      ((g.symm : M ≃ₐ[E] M) : M →+* M).comp (algebraMap F M) := by
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply]
    apply g.injective
    change g (algebraMap F M ((AlgEquiv.restrictNormal g F).symm x)) = g (g.symm (algebraMap F M x))
    rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.restrictNormal_commutes, AlgEquiv.apply_symm_apply]
  calc (W.comap (algebraMap F M)).comap ((AlgEquiv.restrictNormal g F).symm : F →+* F)
      = W.comap ((algebraMap F M).comp ((AlgEquiv.restrictNormal g F).symm : F →+* F)) := by
          rw [InfinitePlace.comap_comp]
    _ = W.comap (((g.symm : M ≃ₐ[E] M) : M →+* M).comp (algebraMap F M)) := by rw [hcomm]
    _ = (W.comap ((g.symm : M ≃ₐ[E] M) : M →+* M)).comap (algebraMap F M) := by rw [InfinitePlace.comap_comp]
    _ = W.comap (algebraMap F M) := by rw [hg]

variable [Normal E M]

theorem forall_fix_of_mem_stabilizer
    (hF : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ MulAction.stabilizer (F ≃ₐ[E] F) v → g = 1)
    (g : M ≃ₐ[E] M) (W : InfinitePlace M) (hg : g ∈ MulAction.stabilizer (M ≃ₐ[E] M) W) :
    ∀ x : F, g (algebraMap F M x) = algebraMap F M x := by
  intro x
  have h1 := hF _ _ (restrictNormal_mem_stabilizer_comap E F M g W hg)
  have h2 := AlgEquiv.restrictNormal_commutes g F x
  rw [h1] at h2
  simpa using h2.symm

theorem hinf_of_compositum (L : Type) [Field L] [Algebra E L] [Algebra L M] [IsScalarTower E L M] [Normal E L]
    (hF : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ MulAction.stabilizer (F ≃ₐ[E] F) v → g = 1)
    (hL : ∀ (v : InfinitePlace L) (g : (L ≃ₐ[E] L)), g ∈ MulAction.stabilizer (L ≃ₐ[E] L) v → g = 1)
    (hgen : ∀ σ : M ≃ₐ[E] M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M x) →
      (∀ y : L, σ (algebraMap L M y) = algebraMap L M y) → σ = 1) :
    ∀ (W : InfinitePlace M) (g : (M ≃ₐ[E] M)), g ∈ MulAction.stabilizer (M ≃ₐ[E] M) W → g = 1 :=
  fun W g hg => hgen g (forall_fix_of_mem_stabilizer E F M hF g W hg) (forall_fix_of_mem_stabilizer E L M hL g W hg)

end up
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false

namespace C9p

theorem exists_cyclic_subLayer (E F' : Type) [Field E] [Field F'] [Algebra E F'] [FiniteDimensional E F'] [IsGalois E F']
    [IsCyclic (F' ≃ₐ[E] F')] (n : ℕ) (hn : n ∣ Nat.card (F' ≃ₐ[E] F')) (hn0 : 0 < n) :
    ∃ L : IntermediateField E F', IsGalois E L ∧ IsCyclic (L ≃ₐ[E] L) ∧ Module.finrank E L = n := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F' ≃ₐ[E] F')
  set N := Nat.card (F' ≃ₐ[E] F') with hN
  have hNpos : 0 < N := Nat.card_pos
  obtain ⟨m, hm⟩ := hn

  let H : Subgroup (F' ≃ₐ[E] F') := Subgroup.zpowers (g ^ n)
  haveI : H.Normal := Subgroup.normal_of_isMulCommutative H
  have hordg : orderOf g = N := by rw [hN]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hcardH : Nat.card H = m := by
    rw [Nat.card_zpowers, orderOf_pow, hordg, hm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ hn0]
  refine ⟨IntermediateField.fixedField H, IsGalois.of_fixedField_normal_subgroup H, ?_, ?_⟩
  ·
    haveI : IsGalois E (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
    exact isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := IntermediateField.fixedField H) F')
  · have h1 : Module.finrank (IntermediateField.fixedField H) F' = m := by
      rw [IntermediateField.finrank_fixedField_eq_card]
      simpa [Nat.card_eq_fintype_card] using hcardH
    have h2 : Module.finrank E F' = N := by rw [hN, IsGalois.card_aut_eq_finrank]
    have h3 := Module.finrank_mul_finrank E (IntermediateField.fixedField H) F'
    rw [h1, h2, hm] at h3
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm; omega
      · exact h
    exact Nat.eq_of_mul_eq_mul_right hm0 h3

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace C9p

variable {k G H : Type} [CommRing k] [Group G] [Group H]

theorem map_map_id_eq_map_id_map (g : G →* H) {X₁ X₂ : Rep.{0} k H} {Y₁ Y₂ : Rep.{0} k G}
    (π₁ : X₁ ⟶ X₂) (π₂ : Y₁ ⟶ Y₂) (J : Rep.res g X₁ ⟶ Y₁) (j : Rep.res g X₂ ⟶ Y₂)
    (h : (Rep.resFunctor g).map π₁ ≫ j = J ≫ π₂) (n : ℕ) (y : groupCohomology X₁ n) :
    (groupCohomology.map g j n).hom ((groupCohomology.map (MonoidHom.id H) π₁ n).hom y) =
      (groupCohomology.map (MonoidHom.id G) π₂ n).hom ((groupCohomology.map g J n).hom y) := by
  have h1 := groupCohomology.map_comp (MonoidHom.id H) g π₁ j n
  have h2 := groupCohomology.map_comp g (MonoidHom.id G) J π₂ n
  rw [h] at h1
  have h3 : groupCohomology.map (MonoidHom.id H) π₁ n ≫ groupCohomology.map g j n =
      groupCohomology.map g J n ≫ groupCohomology.map (MonoidHom.id G) π₂ n := by
    rw [← h1, ← h2]; rfl
  have := congrArg (fun φ => (ModuleCat.Hom.hom φ) y) h3
  simpa [ModuleCat.hom_comp] using this

theorem map_subtype_map_id (S : Subgroup G) {Y₁ Y₂ : Rep.{0} k G} (π : Y₁ ⟶ Y₂) (n : ℕ) (z : groupCohomology Y₁ n) :
    (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype Y₂)) n).hom ((groupCohomology.map (MonoidHom.id G) π n).hom z) =
      (groupCohomology.map (MonoidHom.id S) ((Rep.resFunctor S.subtype).map π) n).hom
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype Y₁)) n).hom z) := by
  have h1 := groupCohomology.map_comp (MonoidHom.id G) S.subtype π (𝟙 (Rep.res S.subtype Y₂)) n
  have h2 := groupCohomology.map_comp S.subtype (MonoidHom.id S) (𝟙 (Rep.res S.subtype Y₁)) ((Rep.resFunctor S.subtype).map π) n
  have h3 : groupCohomology.map (MonoidHom.id G) π n ≫ groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype Y₂)) n =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype Y₁)) n ≫
        groupCohomology.map (MonoidHom.id S) ((Rep.resFunctor S.subtype).map π) n := by
    rw [← h1, ← h2]
    congr 1
  have := congrArg (fun φ => (ModuleCat.Hom.hom φ) z) h3
  simpa [ModuleCat.hom_comp] using this

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false

namespace ExtCitation p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass" namespace LocalLevel p2m_export "ExtCitation.LocalLevel" "IsBase IsLocalFundamentalClass existsUnique_isLocalFundamentalClass isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass" end ExtCitation.LocalLevel
p2m_open_scoped "ExtCitation ExtCitation.LocalLevel" in

theorem ExtCitation.LocalLevel.exists_isBase (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀),
      ExtCitation.LocalLevel.IsBase q L G K₀ := by
  classical

  let K₁ : IntermediateField ℚ_[q] L :=
    { (FixedPoints.subfield G L).toSubring with
      algebraMap_mem' := fun r => by
        change algebraMap ℚ_[q] L r ∈ FixedPoints.subfield G L
        exact fun g => hG g r
      inv_mem' := fun x hx => (FixedPoints.subfield G L).inv_mem hx }
  have hK₁ : ∀ x : L, x ∈ K₁ ↔ ∀ g : G, g • x = x := fun x => Iff.rfl

  let K₀ : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.lift (F := L) K₁
  have hle : K₀ ≤ L := IntermediateField.lift_le K₁

  haveI : FiniteDimensional ℚ_[q] ↥K₁ := IntermediateField.finiteDimensional_left K₁
  haveI : FiniteDimensional ℚ_[q] ↥K₀ :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv K₁).toLinearEquiv
  refine ⟨K₀, inferInstance, ⟨hle, fun x => ?_⟩⟩
  rw [← hK₁]
  exact IntermediateField.mem_lift x

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

namespace C9p

theorem exists_theta (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y) :
    ∃ θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ,
      ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L) := by

  let f : (↥L)ˣ →* (w.adicCompletion K)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hf : ∀ y : (↥L)ˣ, ((f y : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L) := fun y => rfl

  have hequiv : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), f (g • y) = g • f y := by
    intro g y
    apply Units.ext
    rw [hf, h2, NumberField.PlaceDecomp.coe_smul_units, hf]
    apply Φ.injective
    rw [RingEquiv.apply_symm_apply, h3, RingEquiv.apply_symm_apply]
  refine ⟨Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive f)), fun g => ?_⟩, fun y => hf y⟩
  apply LinearMap.ext
  intro y
  change Additive.ofMul (f (g • Additive.toMul y)) = Additive.ofMul (g • f (Additive.toMul y))
  rw [hequiv]

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

namespace C9p

theorem exists_bridge_and_zsmul (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (hsolv : Group.IsSolvable (K ≃ₐ[E] K)) (w : HeightOneSpectrum (𝓞 K))
    (z : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L')
      (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ)
      (Φ : w.adicCompletion K ≃+* L')
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
      (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
      (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
      (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀)
      (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
      (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L'))
      (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ))
      (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀ u')
      (m : ℤ), z = m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u' := by
  haveI := hsolv
  have hsolvD : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w) := inferInstance
  obtain ⟨q, hq, L', hfd, hmsa, hfaith, hmdma, Φ, h1, h2, h3, -⟩ :=
    NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E K w
  obtain ⟨K₀, hK₀fd, hbase⟩ := ExtCitation.LocalLevel.exists_isBase q L' (↥(NumberField.PlaceDecomp.decomp E K w)) h1
  obtain ⟨u', hu', -⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E K w)) h1 h2 hsolvD K₀ hbase
  obtain ⟨θ, hθ⟩ := C9p.exists_theta E K w q L' Φ h2 h3
  obtain ⟨m, hm⟩ := NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass E K w hsolvD q L' Φ h1 h2 h3 K₀ hbase θ hθ u' hu' z
  exact ⟨q, hq, L', hfd, hmsa, hmdma, Φ, h1, h2, h3, K₀, hK₀fd, hbase, θ, hθ, u', hu', m, hm⟩

theorem exists_reading (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (hsolv : Group.IsSolvable (K ≃ₐ[E] K))
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)) :
    ∃ (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
      (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ)
      (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E K v).adicCompletion K ≃+* L' v)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : (NumberField.PlaceAbove.above E K v).adicCompletion K), (Φ v) (g • y) = g • (Φ v) y)
      (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (K₀ v))
      (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v).adicCompletion K) =
          (Φ v).symm (y : L' v))
      (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (K₀ v) (u' v))
      (n : HeightOneSpectrum (𝓞 E) → ℤ),
      ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)).subtype (prG (NumberField.PlaceAbove.above E K v)) 2).hom x =
          n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (θ v) 2).hom (u' v) := by
  have per := fun v : HeightOneSpectrum (𝓞 E) => exists_bridge_and_zsmul E K hsolv (NumberField.PlaceAbove.above E K v)
    ((groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)).subtype (prG (NumberField.PlaceAbove.above E K v)) 2).hom x)
  choose q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' n hn using per
  exact ⟨q, hq, L', hfd, hmsa, hmdma, Φ, h1, h2, h3, K₀, hK₀fd, hbase, θ, hθ, u', hu', n, hn⟩

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

namespace C9p

theorem map_top_injective {k G : Type} [CommRing k] [Group G] (X : Rep.{0} k G) (n : ℕ) :
    Function.Injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype X)) n).hom := by

  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let φ : Rep.res (⊤ : Subgroup G).subtype X ≅ Rep.res e.toMonoidHom X := Iso.refl _
  obtain ⟨ψ, hψ⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv e (Rep.res (⊤ : Subgroup G).subtype X) X φ n
  have : ∀ x, (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype X)) n).hom x = ψ.symm x := by
    intro x; rw [hψ]; rfl
  intro a b h
  rw [this, this] at h
  exact ψ.symm.injective h

theorem addOrderOf_localFundamentalClass (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : ExtCitation.LocalLevel.IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L G K u) :
    addOrderOf u = Nat.card G := by
  classical
  obtain ⟨-, hcard, hspan⟩ := ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass q L G hG hcompat hsolv K hK u hu
  haveI : Fintype G := Fintype.ofFinite G

  have hcT := hcard ⊤
  have hsT := hspan ⊤
  set r := (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom with hr
  have hinj := map_top_injective (Rep.ofMulDistribMulAction G (↥L)ˣ) 2
  rw [← addOrderOf_injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom.toAddMonoidHom hinj u]
  change addOrderOf (r u) = _

  have hfin : Nat.card ↥(groupCohomology (Rep.res (⊤ : Subgroup G).subtype (Rep.ofMulDistribMulAction G (↥L)ˣ)) 2) = Nat.card G := by
    rw [hcT, ← Nat.card_eq_fintype_card, Subgroup.card_top]
  have htop : AddSubgroup.zmultiples (r u) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℤ {r u} := by rw [hr, hsT]; trivial
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [← hk]; exact (int_smul_eq_zsmul _ k _).symm⟩
  rw [← Nat.card_zmultiples, htop, AddSubgroup.card_top, hfin]

theorem map_theta_injective (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L)) :
    Function.Injective (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2 :
      groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ) 2 ⟶
        groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 2).hom := by

  let f : (w.adicCompletion K)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hf : ∀ y, ((f y : (↥L)ˣ) : L) = Φ (y : w.adicCompletion K) := fun y => rfl
  have hequiv : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (w.adicCompletion K)ˣ), f (g • y) = g • f y := by
    intro g y
    apply Units.ext
    rw [hf, NumberField.PlaceDecomp.coe_smul_units, h3, h2, hf]
  let θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ :=
    Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive f)), fun g => by
      apply LinearMap.ext; intro y
      change Additive.ofMul (f (g • Additive.toMul y)) = Additive.ofMul (g • f (Additive.toMul y))
      rw [hequiv]⟩

  have hcomp : θ ≫ θ' = 𝟙 _ := by
    apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro z
    change Additive.ofMul (f (Additive.toMul (θ.hom (Additive.ofMul (Additive.toMul z))))) = z
    have hval : (Additive.toMul (θ.hom (Additive.ofMul (Additive.toMul z))) : (w.adicCompletion K)ˣ) =
        Units.map Φ.symm.toRingHom.toMonoidHom (Additive.toMul z) := Units.ext (hθ (Additive.toMul z))
    rw [hval]
    change Additive.ofMul (f (Units.map Φ.symm.toRingHom.toMonoidHom (Additive.toMul z))) = z
    have : f (Units.map Φ.symm.toRingHom.toMonoidHom (Additive.toMul z)) = Additive.toMul z := by
      apply Units.ext
      rw [hf]
      change Φ (Φ.symm _) = _
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this]
    rfl
  intro a b hab
  have := congrArg (groupCohomology.map (MonoidHom.id _) θ' 2 :
      groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) 2 ⟶
        groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ) 2).hom hab
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_id_comp, hcomp,
    groupCohomology.map_id] at this
  simpa using this

theorem finite_support_reading (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (hsolv : Group.IsSolvable (K ≃ₐ[E] K))
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2))
    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E K v).adicCompletion K ≃+* L' v)
    (h1 : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
    (h2 : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (h3 : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (y : (NumberField.PlaceAbove.above E K v).adicCompletion K), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (hbase : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ)
    (hθ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v).adicCompletion K) =
        (Φ v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ))
    (hu' : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (K₀ v) (u' v))
    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hn : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)).subtype (prG (NumberField.PlaceAbove.above E K v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (θ v) 2).hom (u' v)) :
    (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite := by
  classical
  haveI := hsolv
  obtain ⟨prInf, hprInf⟩ := M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply E K D hactI
  obtain ⟨-, hFIN, -⟩ := M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles E K D hactI prG hprG prInf hprInf 1
  have hT := hFIN x

  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 E) => NumberField.PlaceAbove.above E K v) := by
    intro v₁ v₂ h
    have := NumberField.PlaceAbove.comap_above E K v₁
    rw [show NumberField.PlaceAbove.above E K v₁ = NumberField.PlaceAbove.above E K v₂ from h, NumberField.PlaceAbove.comap_above] at this
    exact HeightOneSpectrum.ext this.symm
  refine (hT.preimage hinj.injOn).subset ?_
  intro v hv

  by_contra hzero
  simp only [Set.mem_preimage, Set.mem_setOf_eq, not_not] at hzero
  apply hv
  have hcoord := hn v
  rw [hzero] at hcoord

  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) (L' v) := ⟨fun {g₁ g₂} hg => by
    haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E K (NumberField.PlaceAbove.above E K v)
    apply eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above E K v).adicCompletion K)
    intro y
    apply (Φ v).injective
    rw [h3, h3, hg]⟩
  have hsolvD : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) := inferInstance
  have e2 := addOrderOf_localFundamentalClass (q v) (L' v) _ (h1 v) (h2 v) hsolvD (K₀ v) (hbase v) (u' v) (hu' v)

  let mθ := (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (θ v) 2 :
    groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) (↥(L' v))ˣ) 2 ⟶
      groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ) 2)
  have hmθ : Function.Injective mθ.hom :=
    map_theta_injective E K (NumberField.PlaceAbove.above E K v) (q v) (L' v) (Φ v) (h2 v) (h3 v) (θ v) (hθ v)
  have e1 : addOrderOf (mθ.hom (u' v)) = addOrderOf (u' v) := addOrderOf_injective mθ.hom.toAddMonoidHom hmθ (u' v)
  have hord : addOrderOf (mθ.hom (u' v)) = Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) := by
    rw [e1, e2]
  have hcoord' : n v • mθ.hom (u' v) = 0 := hcoord.symm
  have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) : ℤ) ∣ n v := by
    rw [← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hcoord'
  obtain ⟨k, hk⟩ := hdvd
  change ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨k, ?_⟩
  have hpos : (Nat.card ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)))).ne'
  rw [hk, zsmul_eq_mul, mul_one]
  push_cast
  field_simp

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand

namespace C9p

theorem exists_principalIdeles_hom (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K))
    (π : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))
    (hπ : ∀ x : (AdeleRing (𝓞 K) K)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 K) K)) :
    ∃ j : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      (∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) ∧
      Function.Injective j.hom ∧ Function.Surjective π.hom ∧
      (∀ y, π.hom y = 0 ↔ y ∈ Set.range j.hom) := by
  let f : Kˣ →* (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  have hf : ∀ a : Kˣ, ((f a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) a := fun a => rfl
  have hequiv : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), f (g • a) = g • f a := by
    intro g a
    apply Units.ext
    rw [hactI, hf, hactF]
    change _ = ((D.unitsAct g (f a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    change _ = D.act g ((f a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    rw [hf, D.compat]
  let j : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ :=
    Rep.ofHom ⟨AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive f), fun g => by
      apply LinearMap.ext; intro y
      change Additive.ofMul (f (g • Additive.toMul y)) = Additive.ofMul (g • f (Additive.toMul y))
      rw [hequiv]⟩
  have hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (f a) := fun a => rfl
  refine ⟨j, hj, ?_, ?_, ?_⟩
  ·
    intro y₁ y₂ h
    have h' : f (Additive.toMul y₁) = f (Additive.toMul y₂) := by
      have := h; exact Additive.ofMul.injective this
    have hinjf : Function.Injective f := by
      intro a b hab
      apply Units.ext
      apply NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
      rw [← hf, ← hf, hab]
    exact Additive.toMul.injective (hinjf h')
  ·
    intro c
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul c)
    exact ⟨Additive.ofMul u, by rw [hπ, hu]; rfl⟩
  ·
    intro y
    constructor
    · intro hy
      have h1 : π.hom (Additive.ofMul (Additive.toMul y)) = 0 := hy
      have h2 := (hπ (Additive.toMul y)).symm.trans h1
      have h0 : (QuotientGroup.mk (Additive.toMul y) : IdeleClassGroup (𝓞 K) K) = 1 := Additive.ofMul.injective h2
      rw [QuotientGroup.eq_one_iff] at h0
      obtain ⟨a, ha⟩ := h0
      refine ⟨Additive.ofMul a, ?_⟩
      exact (hj a).trans (congrArg Additive.ofMul ha)
    · rintro ⟨z, rfl⟩
      have h1 : j.hom z = Additive.ofMul (f (Additive.toMul z)) := hj (Additive.toMul z)
      have h2 : (QuotientGroup.mk (f (Additive.toMul z)) : IdeleClassGroup (𝓞 K) K) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact ⟨Additive.toMul z, rfl⟩
      rw [h1]
      exact (hπ _).trans (by rw [h2]; rfl)

end C9p
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

set_option autoImplicit false
open CategoryTheory groupCohomology

namespace C9p
namespace Step5Aux

theorem shortExact_of_maps {k G : Type} [CommRing k] [Group G] {X : ShortComplex (Rep k G)}
    (hf : Function.Injective X.f.hom) (hg : Function.Surjective X.g.hom)
    (hfg : ∀ y : X.X₂, X.g.hom y = 0 ↔ y ∈ Set.range X.f.hom) : X.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y

end C9p.Step5Aux
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children.C9p"

theorem C9p.exists_of_map_eq_zero_of_shortExact
    {k G : Type} [CommRing k] [Group G] {X₁ X₂ X₃ : Rep.{0} k G} (j : X₁ ⟶ X₂) (π : X₂ ⟶ X₃)
    (hj : Function.Injective j.hom) (hπ : Function.Surjective π.hom)
    (hexact : ∀ y : X₂.V, π.hom y = 0 ↔ y ∈ Set.range j.hom)
    (n : ℕ) (y : groupCohomology X₂ n) (hy : (groupCohomology.map (MonoidHom.id G) π n).hom y = 0) :
    ∃ x : groupCohomology X₁ n, (groupCohomology.map (MonoidHom.id G) j n).hom x = y := by
  let X : ShortComplex (Rep k G) := ShortComplex.mk j π (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro a
    exact (hexact (j.hom a)).2 ⟨a, rfl⟩)
  have hX : X.ShortExact := C9p.Step5Aux.shortExact_of_maps hj hπ hexact
  have hex := groupCohomology.mapShortComplex₂_exact hX n
  rw [ShortComplex.moduleCat_exact_iff] at hex
  exact hex y hy

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem C9p.T_of_TG_of_cores
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (hsolv : Group.IsSolvable (F ≃ₐ[E] F))
    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ))
    (hcores : ∀ (H : Subgroup (F ≃ₐ[E] F)) (τ : groupCohomology.Cores.Transversal H)
      (z : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2)),
      invG (groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) τ z) = inv H z)
    (hTG : (∀

      (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
      (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

      (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
      (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

      (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
      (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
      (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
      (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
      (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
          (Φ v).symm (y : L' v))
      (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
      (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

      (n : HeightOneSpectrum (𝓞 E) → ℤ)
      (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
          n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
      invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))))) :
    (∀ (H : Subgroup (F ≃ₐ[E] F))

      (prH : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
          Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
      (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

      (πH : Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
      (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, πH.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
      (x : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2))

      (q : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (q v).Prime)
      (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (L' v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ)
      (Φ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* L' v)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
      (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
      (K₀ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
      (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
      (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v))
      (θ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
      (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
          (Φ v).symm (y : L' v))
      (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ))
      (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v) (u' v))

      (n : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℤ)
      (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) 2).hom x =
          n v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
              (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ))) 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (θ v) 2).hom (u' v))),
      inv H ((groupCohomology.map (MonoidHom.id ↥H) πH 2).hom x) =
        ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ((((n v : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
  intro H prH hprH πH hπH x qH hqH LH hfLH aLH auLH ΦH hQH hUH hΦH KH hfKH hBH θH hθH uH huH n hn
  classical

  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E F D hactI
  obtain ⟨π, hπ⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply E F D hactI hact
  let τ : groupCohomology.Cores.Transversal H := Classical.choice groupCohomology.Cores.Transversal.nonempty
  obtain ⟨q, hq, L', hfd, hmsa, hmdma, Φ, h1, h2, h3, K₀, hK₀fd, hbase, θ, hθ, u', hu', nG, hnG⟩ :=
    C9p.exists_reading E F hsolv prG (groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) τ x)

  have hπeq : (Rep.resFunctor H.subtype).map π = πH := by
    apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro a
    obtain ⟨y, rfl⟩ : ∃ y : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul y = a := ⟨Additive.toMul a, rfl⟩
    change π.hom (Additive.ofMul y) = πH.hom (Additive.ofMul y)
    rw [hπ, hπH]

  rw [← hπeq, ← hcores H τ, ← groupCohomology.Cores.map_cores_eq_cores_map, hTG prG hprG π hπ _ q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' nG hnG]
  exact M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp E F D hactI H τ x prG hprG q hq L' hfd hmsa hmdma Φ h1 h2 h3
    K₀ hK₀fd hbase θ hθ u' hu' nG hnG prH hprH qH hqH LH hfLH aLH auLH ΦH hQH hUH hΦH KH hfKH hBH θH hθH uH huH n hn

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 12800000 in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)

    (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)

    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))

    (hC6 : ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
        [IsCyclic (F ≃ₐ[E] F)]
        (D : IdeleGaloisDescent (𝓞 F) E F)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
        (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
        (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1),
        (∀ (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)),
        ∀ c : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2),
        ∃ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2),
        (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x = c) ∧
        ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ)),
        Function.Injective invG ∧
        (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
        (∀
        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))
        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))
        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))))

    (hC7 : ∀ (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) (hn : 0 < n),
        ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
        (_ : IsCyclic (F' ≃ₐ[E] F')),
        Nonempty (F' →ₐ[E] CyclotomicField m E) ∧
        (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧
        n ∣ Nat.card (F' ≃ₐ[E] F') ∧
        (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)))

    (hTB : ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
        (D : IdeleGaloisDescent (𝓞 F) E F)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        [MulDistribMulAction (F ≃ₐ[E] F) Fˣ]
        (hactF : ∀ (g : (F ≃ₐ[E] F)) (a : Fˣ), ((g • a : Fˣ) : F) = g (a : F))
        (j : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
        (hj : ∀ a : Fˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a))
        (hinf : ∀ (v : InfinitePlace F) (g : (F ≃ₐ[E] F)), g ∈ NumberField.InfPlaceDecomp.decomp E F v → g = 1)
        (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
        (α : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) 2))
        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))
        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) j 2).hom α) =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = 0)

    (hTW : ∀ (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
        [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
        (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
        (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
        [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
        (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)
        [MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)]
        (hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c)
        (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
        (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x)),
        ∃ (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
        (j : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
        Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)),
        (∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x)) ∧
        (∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
        Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x) : IdeleClassGroup (𝓞 M) M)) ∧
        Function.Injective j.hom ∧
        (∀ c : IdeleClassGroup (𝓞 M) M,
        Additive.ofMul c ∈ Set.range j.hom ↔ ∀ s : M ≃ₐ[E] M, s ∈ S → s • c = c))

    (hIL : ∀ (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
        [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
        (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
        (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)
        (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
        (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))
        (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))
        (y : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))
        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))
        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom y =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v))
        (prM : ∀ w : HeightOneSpectrum (𝓞 M),
        Rep.res (NumberField.PlaceDecomp.decomp E M w).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M w)) (w.adicCompletion M)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 M)) (x : (AdeleRing (𝓞 M) M)ˣ), (prM w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (qM : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (qM v).Prime)
        (LM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
        (_ : ∀ v, FiniteDimensional ℚ_[qM v] (LM v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (LM v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ)
        (ΦM : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E M v).adicCompletion M ≃+* LM v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : ℚ_[qM v]), g • algebraMap ℚ_[qM v] (LM v) y = algebraMap ℚ_[qM v] (LM v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (↥(LM v))ˣ), ((g • y : (↥(LM v))ˣ) : LM v) = g • (y : LM v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (y : (NumberField.PlaceAbove.above E M v).adicCompletion M), (ΦM v) (g • y) = g • (ΦM v) y)
        (KM : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[qM v] (PadicAlgCl (qM v)))
        (_ : ∀ v, FiniteDimensional ℚ_[qM v] (KM v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v))
        (θM : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(LM v))ˣ),
        ((Additive.toMul ((θM v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ) : (NumberField.PlaceAbove.above E M v).adicCompletion M) =
        (ΦM v).symm (y : LM v))
        (uM : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (↥(LM v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (qM v) (LM v) (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (KM v) (uM v))
        (nM : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype (prM (NumberField.PlaceAbove.above E M v)) 2).hom ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J 2).hom y) =
        nM v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v)),
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((nM v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))))

    (hCL : ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
        (D : IdeleGaloisDescent (𝓞 F) E F)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        (H : Subgroup (F ≃ₐ[E] F)) (τ : groupCohomology.Cores.Transversal H)
        (y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2))
        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))
        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom (groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) τ y) =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v))
        (prH : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (qH : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (qH v).Prime)
        (LH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[qH v] (PadicAlgCl (qH v)))
        (_ : ∀ v, FiniteDimensional ℚ_[qH v] (LH v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (LH v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ)
        (ΦH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* LH v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[qH v]), g • algebraMap ℚ_[qH v] (LH v) y = algebraMap ℚ_[qH v] (LH v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(LH v))ˣ), ((g • y : (↥(LH v))ˣ) : LH v) = g • (y : LH v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (ΦH v) (g • y) = g • (ΦH v) y)
        (KH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[qH v] (PadicAlgCl (qH v)))
        (_ : ∀ v, FiniteDimensional ℚ_[qH v] (KH v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (qH v) (LH v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (KH v))
        (θH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(LH v))ˣ),
        ((Additive.toMul ((θH v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
        (ΦH v).symm (y : LH v))
        (uH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (qH v) (LH v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (KH v) (uH v))
        (m : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) 2).hom y =
        m v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
        (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
        (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ))) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (θH v) 2).hom (uH v))),
        ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
        ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ((((m v : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))))

    (hSR : ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
        (H : Subgroup (F ≃ₐ[E] F))
        (D : IdeleGaloisDescent (𝓞 F) E F)
        [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (D' : IdeleGaloisDescent (𝓞 F) ↥(IntermediateField.fixedField H) F)
        [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ]
        (hactI' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField H)] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
        (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
        Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) (w.adicCompletion F)ˣ)
        (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
        (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
        (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
        (hψ : ∀ y, ψ.hom y = y)
        (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
        (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) 2)
        (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
        (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x)
        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
        ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L v))
        (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v))
        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (hn : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v))
        (q' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (q' v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q' v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ)
        (Φ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[q' v]), g • algebraMap ℚ_[q' v] (L' v) y = algebraMap ℚ_[q' v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (Φ' v) (g • y) = g • (Φ' v) y)
        (K₀' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q' v] (K₀' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀' v))
        (θ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(L' v))ˣ),
        ((Additive.toMul ((θ' v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
        (Φ' v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀' v) (u' v)),
        ∀ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')).subtype (prG' (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) 2).hom x' =
        n (v'.under (𝓞 E)) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (θ' v') 2).hom (u' v'))

    (hDS : ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
        (E' : IntermediateField E F) (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (hfin : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
        ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite),
        (∑ᶠ v' : HeightOneSpectrum (𝓞 ↥E'),
        ((((n (v'.under (𝓞 E)) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E' F (NumberField.PlaceAbove.above ↥E' F v')) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) =
        Module.finrank E ↥E' •
        (∑ᶠ v : HeightOneSpectrum (𝓞 E),
        ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))))) :
    ∃ (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup (F ≃ₐ[E] F), ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) →+ AddCircle (1 : ℚ)),

      Function.Injective invG ∧ (∀ H : Subgroup (F ≃ₐ[E] F), Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0) ∧
      (∀ (H : Subgroup (F ≃ₐ[E] F)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F)) (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x) = H.index • invG x) ∧

      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) ∧

      (∀ (H : Subgroup (F ≃ₐ[E] F))

        (prH : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
            Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
              (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (πH : Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, πH.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2))

        (q : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
          (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) 2).hom x =
            n v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
              (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
                (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ))) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (θ v) 2).hom (u' v))),
        inv H ((groupCohomology.map (MonoidHom.id ↥H) πH 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ((((n v : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
  classical

  obtain ⟨a, ha⟩ := hG.exists_card_eq
  have hpa : 0 < p ^ a := pow_pos (Nat.Prime.pos Fact.out) a
  obtain ⟨m, _, F', _, _, _, _, _, -, hinfF', hdvd, -⟩ := hC7 E ∅ (p ^ a) hpa
  obtain ⟨Lsub, hLgal, hLcyc, hLdeg⟩ := C9p.exists_cyclic_subLayer E F' (p ^ a) hdvd hpa
  haveI := hLgal
  haveI := hLcyc
  have hinfL : ∀ (v : InfinitePlace ↥Lsub) (g : (↥Lsub ≃ₐ[E] ↥Lsub)), g ∈ NumberField.InfPlaceDecomp.decomp E (↥Lsub) v → g = 1 :=
    C9p.hinf_of_tower E (↥Lsub) F' hinfF'

  haveI : NumberField ↥Lsub := NumberField.of_module_finite E ↥Lsub
  obtain ⟨M, _, _, _, _, _, _, _, hMgal, hgen⟩ := NumberField.exists_isGalois_compositum E F ↥Lsub
  haveI := hMgal
  have hinfM := C9p.hinf_of_compositum E F M (↥Lsub) hinf hinfL hgen
  have hdegL : Module.finrank E ↥Lsub = Module.finrank E F := by
    rw [hLdeg, ← ha, IsGalois.card_aut_eq_finrank]
  obtain ⟨hMp, hrest⟩ := NumberField.compositum_isPGroup_and_normal_and_inf_eq_bot_and_exists_generators E F (↥Lsub) M p hG hLcyc hdegL hgen

  obtain ⟨DM⟩ := M4aHerbrand.nonempty_ideleGaloisDescent E M
  letI instIM : MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ := MulDistribMulAction.compHom _ DM.unitsAct
  have hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x := fun _ _ => rfl
  letI instCM : MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M) := DM.classMulDistribMulAction
  have hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c :=
    fun g c => DM.classMulDistribMulAction_smul g c

  have hH1M := NumberField.IdeleClassGroup.isZero_H1_of_isPGroup E M p hMp DM hactM

  let SF : Subgroup (M ≃ₐ[E] M) := C9p.galKer E F M
  let ιF : (M ≃ₐ[E] M) ⧸ SF ≃* (F ≃ₐ[E] F) := C9p.quotEquiv E F M
  have hιF : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ιF (QuotientGroup.mk g) x) = g (algebraMap F M x) :=
    C9p.algebraMap_quotEquiv_mk E F M
  let SL : Subgroup (M ≃ₐ[E] M) := C9p.galKer E (↥Lsub) M
  let ιL : (M ≃ₐ[E] M) ⧸ SL ≃* (↥Lsub ≃ₐ[E] ↥Lsub) := C9p.quotEquiv E (↥Lsub) M
  have hιL : ∀ (g : M ≃ₐ[E] M) (x : ↥Lsub), algebraMap (↥Lsub) M (ιL (QuotientGroup.mk g) x) = g (algebraMap (↥Lsub) M x) :=
    C9p.algebraMap_quotEquiv_mk E (↥Lsub) M

  obtain ⟨JF, jF, hJF, hjF, hjFinj, hjFrange⟩ := hTW E F M D DM hactI hact hactIM hactM SF ιF hιF

  obtain ⟨DL⟩ := M4aHerbrand.nonempty_ideleGaloisDescent E ↥Lsub
  letI instIL : MulDistribMulAction (↥Lsub ≃ₐ[E] ↥Lsub) (AdeleRing (𝓞 ↥Lsub) ↥Lsub)ˣ := MulDistribMulAction.compHom _ DL.unitsAct
  have hactIL : ∀ (g : (↥Lsub ≃ₐ[E] ↥Lsub)) (x : (AdeleRing (𝓞 ↥Lsub) ↥Lsub)ˣ), g • x = DL.unitsAct g x := fun _ _ => rfl
  letI instCL : MulDistribMulAction (↥Lsub ≃ₐ[E] ↥Lsub) (IdeleClassGroup (𝓞 ↥Lsub) ↥Lsub) := DL.classMulDistribMulAction
  have hactL : ∀ (g : (↥Lsub ≃ₐ[E] ↥Lsub)) (c : IdeleClassGroup (𝓞 ↥Lsub) ↥Lsub), g • c = DL.classAct g c :=
    fun g c => DL.classMulDistribMulAction_smul g c
  obtain ⟨JL, jL, hJL, hjL, hjLinj, hjLrange⟩ := hTW E (↥Lsub) M DL DM hactIL hactL hactIM hactM SL ιL hιL

  obtain ⟨hinfFinj, hinfFrange⟩ := C9p.map_injective_and_range_eq_ker SF ιF
    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
    (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)) jF hjFinj
    (fun c => by have h__af := hjFrange c; simp at h__af; exact h__af) (hH1M SF)
  obtain ⟨hinfLinj, hinfLrange⟩ := C9p.map_injective_and_range_eq_ker SL ιL
    (Rep.ofMulDistribMulAction (↥Lsub ≃ₐ[E] ↥Lsub) (IdeleClassGroup (𝓞 ↥Lsub) ↥Lsub))
    (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)) jL hjLinj
    (fun c => by have h__af := hjLrange c; simp at h__af; exact h__af) (hH1M SL)

  obtain ⟨πL, hπL⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply E (↥Lsub) DL hactIL hactL
  obtain ⟨prL, hprL⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E (↥Lsub) DL hactIL
  obtain ⟨πM, hπM⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply E M DM hactIM hactM
  obtain ⟨prM, hprM⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E M DM hactIM

  obtain ⟨hSurjL, invL, hinvLinj, hinvLrange, hTGL⟩ := hC6 E (↥Lsub) DL hactIL hactL hinfL

  let K' : IntermediateField E M := IntermediateField.fixedField SF
  have hSFfix : (IntermediateField.fixedField SF).fixingSubgroup = SF := IntermediateField.fixingSubgroup_fixedField SF
  let Θ : ↥SF ≃* (M ≃ₐ[↥K'] M) := (MulEquiv.subgroupCongr hSFfix.symm).trans (IntermediateField.fixingSubgroupEquiv K')
  have hΘ : ∀ (s : ↥SF) (y : M), Θ s y = (s : M ≃ₐ[E] M) y := fun s y => rfl
  obtain ⟨hD'act, hD'class, ⟨D'⟩⟩ := M4aHerbrand.ideleGaloisDescent_restrict_intermediateField (𝓞 M) E M DM K'
  letI instI' : MulDistribMulAction (M ≃ₐ[↥K'] M) (AdeleRing (𝓞 M) M)ˣ := MulDistribMulAction.compHom _ D'.unitsAct
  have hactI' : ∀ (g : (M ≃ₐ[↥K'] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = D'.unitsAct g x := fun _ _ => rfl
  letI instC' : MulDistribMulAction (M ≃ₐ[↥K'] M) (IdeleClassGroup (𝓞 M) M) := D'.classMulDistribMulAction
  have hact' : ∀ (g : (M ≃ₐ[↥K'] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = D'.classAct g c :=
    fun g c => D'.classMulDistribMulAction_smul g c
  haveI : NumberField ↥K' := NumberField.of_module_finite E ↥K'
  obtain ⟨πK, hπK⟩ := M4aHerbrand.exists_hom_ideles_ideleClassGroup_apply (↥K') M D' hactI' hact'
  obtain ⟨prK, hprK⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply (↥K') M D' hactI'
  obtain ⟨eΘ, heΘhom, heΘinv⟩ := M4aHerbrand.exists_res_ideles_iso_res_mulEquiv_fixedField E M DM hactIM SF D' hactI' Θ hΘ
  have hinfK : ∀ (v : InfinitePlace M) (g : (M ≃ₐ[↥K'] M)), g ∈ NumberField.InfPlaceDecomp.decomp (↥K') M v → g = 1 := by
    intro v g hg
    apply AlgEquiv.restrictScalars_injective E
    have h1 : AlgEquiv.restrictScalars E (1 : M ≃ₐ[↥K'] M) = 1 := by ext x; rfl
    rw [h1]
    apply hinfM v
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    exact hg

  have hSFeq : ((IsScalarTower.toAlgHom E F M).fieldRange).fixingSubgroup = SF := by
    ext g
    rw [IntermediateField.mem_fixingSubgroup_iff, C9p.mem_galKer_iff]
    constructor
    · intro h x
      exact h _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
    · rintro h y hy
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      exact h x
  haveI hcycK : IsCyclic (M ≃ₐ[↥K'] M) := by
    obtain ⟨_, _, -, -, -, ⟨tgen, htgen⟩⟩ := hrest
    have hcycN : IsCyclic ↥((IsScalarTower.toAlgHom E F M).fieldRange).fixingSubgroup := ⟨⟨tgen, htgen⟩⟩
    have hcycSF : IsCyclic ↥SF := by
      have e := MulEquiv.subgroupCongr hSFeq
      exact isCyclic_of_surjective e e.surjective
    exact isCyclic_of_surjective Θ Θ.surjective
  obtain ⟨-, invK, hinvKinj, hinvKrange, hTGK⟩ := hC6 (↥K') M D' hactI' hact' hinfK

  obtain ⟨ψT, hψT⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv Θ
    (Rep.res SF.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))
    (Rep.ofMulDistribMulAction (M ≃ₐ[↥K'] M) (AdeleRing (𝓞 M) M)ˣ) eΘ 2
  have hsolvM : Group.IsSolvable (M ≃ₐ[E] M) := by haveI := hMp.isNilpotent; infer_instance
  have hsolvK : Group.IsSolvable (M ≃ₐ[↥K'] M) := inferInstance
  have hsolvL : Group.IsSolvable (↥Lsub ≃ₐ[E] ↥Lsub) := inferInstance
  have hcardGL : Nat.card (↥Lsub ≃ₐ[E] ↥Lsub) = p ^ a := by rw [IsGalois.card_aut_eq_finrank, hLdeg]

  have hBA : ∀ c : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥Lsub ≃ₐ[E] ↥Lsub) (IdeleClassGroup (𝓞 ↥Lsub) ↥Lsub)) 2),
      (groupCohomology.map SF.subtype (𝟙 (Rep.res SF.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)))) 2).hom
        ((groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) jL 2).hom c) = 0 := by
    intro c
    obtain ⟨y, rfl⟩ := hSurjL πL hπL c

    obtain ⟨q, hq, L', hfd, hmsa, hmdma, Φ, h1, h2, h3, K₀, hK₀fd, hbase, θ, hθ, u', hu', n, hn⟩ :=
      C9p.exists_reading E (↥Lsub) hsolvL prL y

    set xM := (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) JL 2).hom y with hxM
    obtain ⟨qM, hqM, LM, hfdM, hmsaM, hmdmaM, ΦM, h1M, h2M, h3M, KM, hKMfd, hbaseM, θM, hθM, uM, huM, nM, hnM⟩ :=
      C9p.exists_reading E M hsolvM prM xM

    have hsumLM := hIL E (↥Lsub) M DL DM hactIL hactIM SL ιL hιL JL hJL y prL hprL q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' n hn
      prM hprM qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nM hnM

    set zI := (groupCohomology.map SF.subtype (𝟙 (Rep.res SF.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ))) 2).hom xM with hzI
    set x' := ψT zI with hx'
    have hx'rel : (groupCohomology.map Θ.toMonoidHom eΘ.inv 2).hom x' = zI := by
      rw [← hψT, hx', LinearEquiv.symm_apply_apply]

    obtain ⟨qK, hqK, LK, hfdK, hmsaK, hmdmaK, ΦK, h1K, h2K, h3K, KK, hKKfd, hbaseK, θK, hθK, uK, huK, -, -⟩ :=
      C9p.exists_reading (↥K') M hsolvK prK x'
    have hread' := hSR E M SF DM hactIM prM hprM D' hactI' prK hprK Θ hΘ eΘ.inv heΘinv xM x' hx'rel
      qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nM hnM
      qK hqK LK hfdK hmsaK hmdmaK ΦK h1K h2K h3K KK hKKfd hbaseK θK hθK uK huK

    have hinvK := hTGK prK hprK πK hπK x' qK hqK LK hfdK hmsaK hmdmaK ΦK h1K h2K h3K KK hKKfd hbaseK θK hθK uK huK
      (fun v' => nM (v'.under (𝓞 E))) hread'

    have hfinM : (Function.support fun v : HeightOneSpectrum (𝓞 E) =>
        ((((nM v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))).Finite :=
      C9p.finite_support_reading E M hsolvM DM hactIM prM hprM xM qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nM hnM

    have hDSout := hDS E M K' nM hfinM

    have hfinrankK : Module.finrank E ↥K' = p ^ a := by
      have h1 : Module.finrank (↥K') M = Nat.card ↥SF := by
        change Module.finrank (IntermediateField.fixedField SF) M = _
        rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_eq_fintype_card]
      have h2 : Module.finrank E M = Nat.card (M ≃ₐ[E] M) := (IsGalois.card_aut_eq_finrank E M).symm
      have h3 := Module.finrank_mul_finrank E (↥K') M
      have h4 : Nat.card (M ≃ₐ[E] M) = Nat.card ((M ≃ₐ[E] M) ⧸ SF) * Nat.card ↥SF := Subgroup.card_eq_card_quotient_mul_card_subgroup SF
      have h5 : Nat.card ((M ≃ₐ[E] M) ⧸ SF) = p ^ a := by rw [Nat.card_congr ιF.toEquiv, ha]
      rw [h1, h2, h4, h5] at h3
      have hSFpos : 0 < Nat.card ↥SF := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hSFpos h3

    have hzero : invK ((groupCohomology.map (MonoidHom.id (M ≃ₐ[↥K'] M)) πK 2).hom x') = 0 := by
      rw [hinvK, hDSout, hfinrankK, hsumLM, ← hTGL prL hprL πL hπL y q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' n hn,
        ← hcardGL]
      exact (hinvLrange _).mp ⟨_, rfl⟩
    have hx'zero : (groupCohomology.map (MonoidHom.id (M ≃ₐ[↥K'] M)) πK 2).hom x' = 0 :=
      hinvKinj (by rw [hzero, map_zero])

    have hsqL : (Rep.resFunctor (ιL.toMonoidHom.comp (QuotientGroup.mk' SL))).map πL ≫ jL = JL ≫ πM := by
      apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro z
      change jL.hom (πL.hom (Additive.ofMul (Additive.toMul z))) = πM.hom (JL.hom (Additive.ofMul (Additive.toMul z)))
      have e1 := congrArg jL.hom (hπL (Additive.toMul z))
      have e2 := hjL (Additive.toMul z)
      have e3 := hπM (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange (↥Lsub) M).β.toMonoidHom (Additive.toMul z))
      have e4 := congrArg πM.hom (hJL (Additive.toMul z))
      exact e1.trans (e2.trans (e3.symm.trans e4.symm))

    have hΘres : ∀ s : ↥SF, (Θ s).restrictScalars E = (s : M ≃ₐ[E] M) := fun s => AlgEquiv.ext (hΘ s)
    let ψC : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (M ≃ₐ[↥K'] M) (IdeleClassGroup (𝓞 M) M)) ⟶
        Rep.res SF.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)) :=
      Rep.ofHom ⟨LinearMap.id, fun s => by
        apply LinearMap.ext; intro cc
        change Additive.ofMul ((Θ s) • (Additive.toMul (cc : Additive (IdeleClassGroup (𝓞 M) M)) : IdeleClassGroup (𝓞 M) M)) =
          Additive.ofMul (((s : ↥SF) : M ≃ₐ[E] M) • (Additive.toMul (cc : Additive (IdeleClassGroup (𝓞 M) M)) : IdeleClassGroup (𝓞 M) M))
        rw [hact', hactM, hD'class D' (Θ s) _, hΘres]⟩
    have hψC : ∀ z, ψC.hom z = z := fun z => rfl
    have hsqK : (Rep.resFunctor Θ.toMonoidHom).map πK ≫ ψC =
        eΘ.inv ≫ (Rep.resFunctor SF.subtype).map πM := by
      apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro z
      change ψC.hom (πK.hom (Additive.ofMul (Additive.toMul z))) = πM.hom (eΘ.inv.hom (Additive.ofMul (Additive.toMul z)))
      have e1 := hψC (πK.hom (Additive.ofMul (Additive.toMul z)))
      have e2 := hπK (Additive.toMul z)
      have e3 := hπM (Additive.toMul z)
      have e4 := congrArg πM.hom (heΘinv (Additive.ofMul (Additive.toMul z)))
      exact e1.trans (e2.trans (e3.symm.trans e4.symm))

    rw [C9p.map_map_id_eq_map_id_map _ πL πM JL jL hsqL 2 y, C9p.map_subtype_map_id SF πM 2, ← hxM, ← hzI, ← hx'rel,
      ← C9p.map_map_id_eq_map_id_map _ πK ((Rep.resFunctor SF.subtype).map πM) eΘ.inv ψC hsqK 2 x', hx'zero, map_zero]

  set infL := ModuleCat.Hom.hom (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) jL 2) with hinfLdef
  set infF := ModuleCat.Hom.hom (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) jF 2) with hinfFdef
  have hle : LinearMap.range infL ≤ LinearMap.range infF := by
    rw [hinfFrange]
    rintro _ ⟨c, rfl⟩
    exact hBA c

  have hcardGL' : IsPGroup p (↥Lsub ≃ₐ[E] ↥Lsub) := IsPGroup.of_card hcardGL
  obtain ⟨-, hcardHL, -⟩ := M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup E (↥Lsub) p hcardGL' DL hactL
  obtain ⟨-, hcardHF, -⟩ := M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup E F p hG D hact
  have hcRL : Nat.card ↥(LinearMap.range infL) = p ^ a := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective infL hinfLinj).toEquiv, hcardHL, hcardGL]
  have hcRF : Nat.card ↥(LinearMap.range infF) = p ^ a := by
    rw [← Nat.card_congr (LinearEquiv.ofInjective infF hinfFinj).toEquiv, hcardHF, ha]
  haveI : Finite ↥(LinearMap.range infF) := Nat.finite_of_card_ne_zero (by rw [hcRF]; exact hpa.ne')
  have hrangeEq : LinearMap.range infL = LinearMap.range infF := by
    apply SetLike.ext'
    apply Set.eq_of_subset_of_ncard_le hle
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      change Nat.card ↥(LinearMap.range infF) ≤ Nat.card ↥(LinearMap.range infL)
      rw [hcRL, hcRF]

  let eqv := LinearEquiv.ofInjective infL hinfLinj
  have hmemF : ∀ x, infF x ∈ LinearMap.range infL := fun x => by rw [hrangeEq]; exact ⟨x, rfl⟩
  let invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) →+ AddCircle (1 : ℚ) :=
    AddMonoidHom.mk' (fun x => invL (eqv.symm ⟨infF x, hmemF x⟩)) (fun x₁ x₂ => by
      change invL (eqv.symm ⟨infF (x₁ + x₂), hmemF (x₁ + x₂)⟩) = invL (eqv.symm ⟨infF x₁, hmemF x₁⟩) + invL (eqv.symm ⟨infF x₂, hmemF x₂⟩)
      rw [← map_add, ← map_add]
      congr 2
      apply Subtype.ext
      simp only [map_add, Submodule.coe_add])

  have hinvG_def : ∀ x c, infF x = infL c → invG x = invL c := by
    intro x c hxc
    change invL (eqv.symm ⟨infF x, hmemF x⟩) = invL c
    congr 1
    apply eqv.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    change infF x = (eqv c : _)
    rw [hxc, LinearEquiv.ofInjective_apply]
  have hinjG : Function.Injective invG := by
    intro x₁ x₂ h
    have h1 : eqv.symm ⟨infF x₁, hmemF x₁⟩ = eqv.symm ⟨infF x₂, hmemF x₂⟩ := hinvLinj h
    have h2 := congrArg Subtype.val (eqv.symm.injective h1)
    exact hinfFinj h2
  have hrangeG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (F ≃ₐ[E] F) • t = 0 := by
    intro t
    rw [ha, ← hcardGL, ← hinvLrange]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, infF x = infL c := by
        have : infL c ∈ LinearMap.range infF := by rw [← hrangeEq]; exact ⟨c, rfl⟩
        obtain ⟨x, hx⟩ := this; exact ⟨x, hx⟩
      exact ⟨x, hinvG_def x c hx⟩

  have hsolvF : Group.IsSolvable (F ≃ₐ[E] F) := by haveI := hG.isNilpotent; infer_instance
  letI : MulSemiringAction (M ≃ₐ[E] M) M := AlgEquiv.applyMulSemiringAction
  letI instMu : MulDistribMulAction (M ≃ₐ[E] M) Mˣ := inferInstance
  have hactFM : ∀ (g : (M ≃ₐ[E] M)) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M) := fun g a => rfl
  obtain ⟨jM, hjM, hjMinj, hπMsurj, hexM⟩ := C9p.exists_principalIdeles_hom E M DM hactIM hactFM πM hπM
  have hsqL' : (Rep.resFunctor (ιL.toMonoidHom.comp (QuotientGroup.mk' SL))).map πL ≫ jL = JL ≫ πM := by
    apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro z
    change jL.hom (πL.hom (Additive.ofMul (Additive.toMul z))) = πM.hom (JL.hom (Additive.ofMul (Additive.toMul z)))
    exact (congrArg jL.hom (hπL (Additive.toMul z))).trans ((hjL (Additive.toMul z)).trans
      ((hπM (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange (↥Lsub) M).β.toMonoidHom (Additive.toMul z))).symm.trans
        (congrArg πM.hom (hJL (Additive.toMul z))).symm))
  have hTG : (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

        (π : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))
        (_ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, π.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        invG ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
    intro prG hprG π hπ x q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' n hn

    have hsqF : (Rep.resFunctor (ιF.toMonoidHom.comp (QuotientGroup.mk' SF))).map π ≫ jF = JF ≫ πM := by
      apply Rep.hom_ext; apply Representation.IntertwiningMap.ext; apply LinearMap.ext; intro z
      change jF.hom (π.hom (Additive.ofMul (Additive.toMul z))) = πM.hom (JF.hom (Additive.ofMul (Additive.toMul z)))
      exact (congrArg jF.hom (hπ (Additive.toMul z))).trans ((hjF (Additive.toMul z)).trans
        ((hπM (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom (Additive.toMul z))).symm.trans
          (congrArg πM.hom (hJF (Additive.toMul z))).symm))

    set xMF := (groupCohomology.map (ιF.toMonoidHom.comp (QuotientGroup.mk' SF)) JF 2).hom x with hxMF
    obtain ⟨qM, hqM, LM, hfdM, hmsaM, hmdmaM, ΦM, h1M, h2M, h3M, KM, hKMfd, hbaseM, θM, hθM, uM, huM, nF, hnF⟩ :=
      C9p.exists_reading E M hsolvM prM xMF
    have hsumF := hIL E F M D DM hactI hactIM SF ιF hιF JF hJF x prG hprG q hq L' hfd hmsa hmdma Φ h1 h2 h3 K₀ hK₀fd hbase θ hθ u' hu' n hn
      prM hprM qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nF hnF

    obtain ⟨c, hc⟩ : infF ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) π 2).hom x) ∈ LinearMap.range infL := by
      rw [hrangeEq]; exact ⟨_, rfl⟩
    obtain ⟨y', rfl⟩ := hSurjL πL hπL c
    obtain ⟨qL, hqL, LL, hfdL, hmsaL, hmdmaL, ΦL, h1L, h2L, h3L, KL, hKLfd, hbaseL, θL, hθL, uL, huL, nL0, hnL0⟩ :=
      C9p.exists_reading E (↥Lsub) hsolvL prL y'
    set xML := (groupCohomology.map (ιL.toMonoidHom.comp (QuotientGroup.mk' SL)) JL 2).hom y' with hxML

    have perL : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℤ,
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype (prM (NumberField.PlaceAbove.above E M v)) 2).hom xML =
          m • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v) := by
      intro v
      haveI := hsolvM
      have hsD : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) := inferInstance
      exact NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass E M (NumberField.PlaceAbove.above E M v) hsD
        (qM v) (LM v) (ΦM v) (h1M v) (h2M v) (h3M v) (KM v) (hbaseM v) (θM v) (hθM v) (uM v) (huM v) _
    choose nL hnL using perL
    have hsumL := hIL E (↥Lsub) M DL DM hactIL hactIM SL ιL hιL JL hJL y' prL hprL qL hqL LL hfdL hmsaL hmdmaL ΦL h1L h2L h3L KL hKLfd hbaseL θL hθL uL huL nL0 hnL0
      prM hprM qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nL hnL

    rw [hinvG_def _ _ hc.symm, hTGL prL hprL πL hπL y' qL hqL LL hfdL hmsaL hmdmaL ΦL h1L h2L h3L KL hKLfd hbaseL θL hθL uL huL nL0 hnL0,
      ← hsumL, ← hsumF]

    have eF := C9p.map_map_id_eq_map_id_map _ π πM JF jF hsqF 2 x
    have eL := C9p.map_map_id_eq_map_id_map _ πL πM JL jL hsqL' 2 y'
    rw [← hinfFdef, ← hxMF] at eF
    rw [← hinfLdef, ← hxML] at eL
    have hdiff0 : (groupCohomology.map (MonoidHom.id (M ≃ₐ[E] M)) πM 2).hom (xMF - xML) = 0 := by
      rw [map_sub, ← eF, ← eL, hc, sub_self]
    obtain ⟨α, hα⟩ := C9p.exists_of_map_eq_zero_of_shortExact jM πM hjMinj hπMsurj hexM 2 (xMF - xML) hdiff0
    have hnα : ∀ v : HeightOneSpectrum (𝓞 E),
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)).subtype (prM (NumberField.PlaceAbove.above E M v)) 2).hom
            ((groupCohomology.map (MonoidHom.id (M ≃ₐ[E] M)) jM 2).hom α) =
          (nF v - nL v) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) (θM v) 2).hom (uM v) := by
      intro v
      have key : ∀ (a b : ℤ) (yy : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v))) ((NumberField.PlaceAbove.above E M v).adicCompletion M)ˣ) 2)),
          a • yy - b • yy = (a - b) • yy := fun a b yy => by rw [sub_eq_add_neg, (sub_zsmul yy a b).symm]
      rw [hα, map_sub, hnF v, hnL v]
      exact key (nF v) (nL v) _
    have hTBout := hTB E M DM hactIM hactFM jM hjM hinfM p hMp α prM hprM qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM
      (fun v => nF v - nL v) hnα
    have hfinF := C9p.finite_support_reading E M hsolvM DM hactIM prM hprM xMF qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nF hnF
    have hfinL := C9p.finite_support_reading E M hsolvM DM hactIM prM hprM xML qM hqM LM hfdM hmsaM hmdmaM ΦM h1M h2M h3M KM hKMfd hbaseM θM hθM uM huM nL hnL
    have hsplit : (∑ᶠ v : HeightOneSpectrum (𝓞 E), (((((nF v - nL v : ℤ) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) =
        (∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((nF v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) -
        (∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((nL v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
      rw [← finsum_sub_distrib hfinF hfinL]
      apply finsum_congr
      intro v
      rw [← AddCircle.coe_sub, ← sub_div]
      push_cast
      rfl
    have h0 : (∑ᶠ v : HeightOneSpectrum (𝓞 E), (((((nF v - nL v : ℤ) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E M (NumberField.PlaceAbove.above E M v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) = 0 := by
      convert hTBout using 3
    rw [hsplit, sub_eq_zero] at h0
    exact h0.symm

  have h5 := NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup E F p hG D hact
  obtain ⟨inv, hiH, hrH, hR, hcoresLaw⟩ := C9p.exists_invariant_family
    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) invG hinjG hrangeG hcardHF h5
  have hT := C9p.T_of_TG_of_cores E F D hactI hact hsolvF invG inv hcoresLaw hTG
  exact ⟨invG, inv, hinjG, hiH, hrangeG, hrH, hR, hTG, hT⟩

end S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children
end P2MW
export P2MW.S_M4aHerbrand_exists_invariant_forall_inv_map_eq_finsum_of_forall_localFundamentalClass_of_isPGroup_of_children (solution)
