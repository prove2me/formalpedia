-- Prove2me | solution 1 for NumberField.exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/68fbb805-bfcd-5c16-9ddb-fb0d5ff810c1

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_distribHaarChar_idelicNorm_genuineBaseChange
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
p2m_attr_erase "instance" "instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open NumberField
open scoped Pointwise Topology

namespace R2FafNAKer

section Discrete

variable (F : Type) [Field F] [NumberField F]

theorem isClosed_of_subset_range_algebraMap (S : Set (AdeleRing (𝓞 F) F))
    (hS : S ⊆ Set.range (algebraMap F (AdeleRing (𝓞 F) F))) : IsClosed S := by
  refine isClosed_of_closure_subset fun a ha => ?_
  obtain ⟨C, hC, hCa⟩ := exists_compact_mem_nhds a
  have hfin : (S ∩ C).Finite := by
    have h := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F hC
    refine (h.image (algebraMap F (AdeleRing (𝓞 F) F))).subset ?_
    rintro x ⟨hxS, hxC⟩
    obtain ⟨ξ, rfl⟩ := hS hxS
    exact ⟨ξ, hxC, rfl⟩
  have ha' : a ∈ closure (S ∩ C) := by
    rw [mem_closure_iff_nhds] at ha ⊢
    intro U hU
    obtain ⟨y, hyU, hyS⟩ := ha (U ∩ C) (Filter.inter_mem hU hCa)
    exact ⟨y, hyU.1, hyS, hyU.2⟩
  rw [hfin.isClosed.closure_eq] at ha'
  exact ha'.1

theorem isClosed_of_subset_principalIdeles (T : Set (AdeleRing (𝓞 F) F)ˣ)
    (hT : T ⊆ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ)) : IsClosed T := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have h1 : (x : AdeleRing (𝓞 F) F) ∈ closure (Units.val '' T) :=
    map_mem_closure Units.continuous_val hx (Set.mapsTo_image _ _)
  have h2 : IsClosed (Units.val '' T) := by
    refine isClosed_of_subset_range_algebraMap F _ ?_
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu⟩ := hT ht
    exact ⟨(u : F), by rw [← hu]; rfl⟩
  rw [h2.closure_eq] at h1
  obtain ⟨t, ht, htx⟩ := h1
  rwa [← Units.ext htx]

end Discrete

theorem sigmaCompactSpace_units (R : Type*) [Monoid R] [TopologicalSpace R] [ContinuousMul R]
    [T1Space R] [SigmaCompactSpace R] : SigmaCompactSpace Rˣ := by
  haveI : SigmaCompactSpace Rᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := R)).symm.isClosedEmbedding.sigmaCompactSpace
  exact Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

section Arith

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem idelicNorm_unitsMap_algebraMap (u : Lˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Units.map (Algebra.norm K : L →* K) u) := by
  ext
  simp only [M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map, MonoidHom.coe_coe]
  exact M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap K L (u : L)

theorem principalIdeles_le_normOneIdeles :
    M4aHerbrand.principalIdeles (𝓞 L) L ≤ NumberField.TateGlobal.normOneIdeles L := by
  rintro _ ⟨u, rfl⟩
  change _ ∈ (MeasureTheory.distribHaarChar (AdeleRing (𝓞 L) L)).ker
  rw [MonoidHom.mem_ker]
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  exact NumberField.AdeleRing.distribHaarChar_algebraMap L u

variable [FiniteDimensional K L] [IsGalois K L]

theorem ker_idelicNorm_le_normOneIdeles :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker ≤
      NumberField.TateGlobal.normOneIdeles L := by
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  change z ∈ (MeasureTheory.distribHaarChar (AdeleRing (𝓞 L) L)).ker
  rw [MonoidHom.mem_ker, ← NumberField.distribHaarChar_idelicNorm_genuineBaseChange K L z, hz,
    map_one]

theorem ker_inf_principalIdeles_le_range (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker ⊓
        M4aHerbrand.principalIdeles (𝓞 L) L ≤
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range := by
  rintro x ⟨hxker, ⟨u, rfl⟩⟩
  have hnorm : Algebra.norm K (u : L) = 1 := by
    have h1 : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) u) = 1 := hxker
    rw [idelicNorm_unitsMap_algebraMap] at h1
    have h2 := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h2
    haveI : Nontrivial (AdeleRing (𝓞 K) K) :=
      inferInstanceAs (Nontrivial (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
    exact (algebraMap K (AdeleRing (𝓞 K) K)).injective (h2.trans (map_one _).symm)
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hgen⟩⟩
  obtain ⟨y, hy⟩ := groupCohomology.exists_div_of_norm_eq_one (g := σ) hgen hnorm
  refine ⟨y⁻¹, ?_⟩
  have hval : ((Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ) y⁻¹ : Lˣ) = u := by
    ext
    rw [MonoidHom.div_apply, MonoidHom.id_apply, Units.val_div_eq_div_val, Units.coe_map,
      MonoidHom.coe_coe, ← hy]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, inv_div_inv]
    rfl
  rw [MonoidHom.comp_apply, hval]

end Arith

end R2FafNAKer

open R2FafNAKer in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ D : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact D ∧
      ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.ker :
          Set (AdeleRing (𝓞 L) L)ˣ) ⊆
        (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
            (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range :
          Set (AdeleRing (𝓞 L) L)ˣ) * D := by
  classical

  set N : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hN
  set M : Subgroup (AdeleRing (𝓞 L) L)ˣ := N.ker with hM
  set A1 : Subgroup (AdeleRing (𝓞 L) L)ˣ := NumberField.TateGlobal.normOneIdeles L with hA1
  set PL : Subgroup (AdeleRing (𝓞 L) L)ˣ := M4aHerbrand.principalIdeles (𝓞 L) L with hPL
  set Γ : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range with hΓ

  have hNc : Continuous N :=
    Continuous.units_map _ (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)
  have hMclosed : IsClosed (M : Set (AdeleRing (𝓞 L) L)ˣ) := by
    have : (M : Set (AdeleRing (𝓞 L) L)ˣ) = N ⁻¹' {1} := by
      ext z
      simp [hM, MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hNc

  have hMA : M ≤ A1 := ker_idelicNorm_le_normOneIdeles K L
  have hPA : PL ≤ A1 := principalIdeles_le_normOneIdeles L

  have hPLclosed : IsClosed (PL : Set (AdeleRing (𝓞 L) L)ˣ) :=
    isClosed_of_subset_principalIdeles L _ subset_rfl
  let P' : Subgroup A1 := PL.subgroupOf A1
  haveI hP'closed : IsClosed (P' : Set A1) := hPLclosed.preimage continuous_subtype_val
  haveI hQ : CompactSpace (A1 ⧸ P') := NumberField.TateGlobal.compactSpace_normOneIdeleClass L

  let M' : Subgroup A1 := M.subgroupOf A1
  let e : M' → (AdeleRing (𝓞 L) L)ˣ := fun x => ((x : A1) : (AdeleRing (𝓞 L) L)ˣ)
  have he : Topology.IsClosedEmbedding e := by
    refine ⟨Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal, ?_⟩
    have : Set.range e = (M : Set (AdeleRing (𝓞 L) L)ˣ) := by
      ext g
      constructor
      · rintro ⟨x, rfl⟩
        exact Subgroup.mem_subgroupOf.1 x.2
      · intro hg
        exact ⟨⟨⟨g, hMA hg⟩, Subgroup.mem_subgroupOf.2 hg⟩, rfl⟩
    rw [this]
    exact hMclosed
  have hemul : ∀ x y : M', e (x * y) = e x * e y := fun x y => rfl
  have heinv : ∀ x : M', e x⁻¹ = (e x)⁻¹ := fun x => rfl
  haveI : LocallyCompactSpace M' := he.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_units _
  haveI : SigmaCompactSpace M' := he.sigmaCompactSpace

  let φ : M' →* A1 ⧸ P' := (QuotientGroup.mk' P').comp M'.subtype
  have hφc : Continuous φ := QuotientGroup.continuous_mk.comp continuous_subtype_val
  let R : Subgroup (A1 ⧸ P') := φ.range
  have hRclosed : IsClosed (R : Set (A1 ⧸ P')) := by
    rw [← (QuotientGroup.isQuotientMap_mk P').isClosed_preimage]
    have hpre : (QuotientGroup.mk : A1 → A1 ⧸ P') ⁻¹' (R : Set (A1 ⧸ P')) =
        (Subtype.val : A1 → (AdeleRing (𝓞 L) L)ˣ) ⁻¹'
          (N ⁻¹' (N '' (PL : Set (AdeleRing (𝓞 L) L)ˣ))) := by
      ext a
      simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_image]
      constructor
      · rintro ⟨m, hm⟩
        have h := QuotientGroup.eq.1 hm
        refine ⟨((m : A1) : (AdeleRing (𝓞 L) L)ˣ)⁻¹ * (a : (AdeleRing (𝓞 L) L)ˣ),
          Subgroup.mem_subgroupOf.1 h, ?_⟩
        have hm1 : N ((m : A1) : (AdeleRing (𝓞 L) L)ˣ) = 1 := Subgroup.mem_subgroupOf.1 m.2
        rw [map_mul, map_inv, hm1, inv_one, one_mul]
      · rintro ⟨p, hp, hpa⟩
        have hpA : p ∈ A1 := hPA hp
        have hmem : (a : (AdeleRing (𝓞 L) L)ˣ) * p⁻¹ ∈ M := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, ← hpa, mul_inv_cancel]
        refine ⟨⟨⟨(a : (AdeleRing (𝓞 L) L)ˣ) * p⁻¹, mul_mem a.2 (inv_mem hpA)⟩,
          Subgroup.mem_subgroupOf.2 hmem⟩, ?_⟩
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        convert hp using 1
        show ((a : (AdeleRing (𝓞 L) L)ˣ) * p⁻¹)⁻¹ * (a : (AdeleRing (𝓞 L) L)ˣ) = p
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    rw [hpre]
    refine IsClosed.preimage continuous_subtype_val (IsClosed.preimage hNc ?_)
    refine isClosed_of_subset_principalIdeles K _ ?_
    rintro _ ⟨p, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map (Algebra.norm K : L →* K) u, (idelicNorm_unitsMap_algebraMap K L u).symm⟩
  haveI : CompactSpace R := isCompact_iff_compactSpace.1 hRclosed.isCompact

  let φ' : M' →* R := φ.rangeRestrict
  have hφ'c : Continuous φ' := hφc.subtype_mk _
  have hφ's : Function.Surjective φ' := MonoidHom.rangeRestrict_surjective φ
  have hφ'o : IsOpenMap φ' := MonoidHom.isOpenMap_of_sigmaCompact φ' hφ's hφ'c

  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : M')
  let V : Set R := φ' '' interior U
  have hVo : IsOpen V := hφ'o _ isOpen_interior
  have h1V : (1 : R) ∈ V := ⟨1, mem_interior_iff_mem_nhds.2 hU1, map_one φ'⟩
  have hcover : (Set.univ : Set R) ⊆ ⋃ r : R, (fun v => r * v) '' V := fun r _ =>
    Set.mem_iUnion.2 ⟨r, 1, h1V, mul_one r⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun r : R => (fun v => r * v) '' V)
    (fun r => (Homeomorph.mulLeft r).isOpenMap _ hVo) hcover
  choose m hm using hφ's

  let D : Set (AdeleRing (𝓞 L) L)ˣ := ⋃ r ∈ t, (fun u : M' => e (m r * u)) '' U
  have hD : IsCompact D :=
    t.isCompact_biUnion fun r _ =>
      hUc.image (he.continuous.comp (continuous_const.mul continuous_id))
  refine ⟨D, hD, fun z hz => ?_⟩

  have hzM : z ∈ M := hz
  let z' : M' := ⟨⟨z, hMA hzM⟩, Subgroup.mem_subgroupOf.2 hzM⟩
  obtain ⟨r, hrt, hr⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (φ' z')))
  obtain ⟨v, ⟨u, hu, rfl⟩, hv⟩ := hr
  have hu' : u ∈ U := interior_subset hu
  have hv' : r * φ' u = φ' z' := hv
  have hkey : φ' (z' * (m r * u)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hm, hv', mul_inv_cancel]
  have hP : ((z' * (m r * u)⁻¹ : M') : A1) ∈ P' := by
    have h1 : φ (z' * (m r * u)⁻¹) = 1 := by
      have := congrArg Subtype.val hkey
      exact this
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hPL' : e (z' * (m r * u)⁻¹) ∈ PL := Subgroup.mem_subgroupOf.1 hP
  have hM' : e (z' * (m r * u)⁻¹) ∈ M := Subgroup.mem_subgroupOf.1 (z' * (m r * u)⁻¹).2
  have hΓ' : e (z' * (m r * u)⁻¹) ∈ Γ := ker_inf_principalIdeles_le_range K L σ hgen ⟨hM', hPL'⟩
  refine ⟨e (z' * (m r * u)⁻¹), hΓ', e (m r * u), Set.mem_biUnion hrt ⟨u, hu', rfl⟩, ?_⟩
  show e (z' * (m r * u)⁻¹) * e (m r * u) = z
  rw [hemul, heinv, inv_mul_cancel_right]

end S_NumberField_exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers
end P2MW
export P2MW.S_NumberField_exists_isCompact_ker_idelicNorm_subset_range_mul_of_forall_mem_zpowers (solution)
