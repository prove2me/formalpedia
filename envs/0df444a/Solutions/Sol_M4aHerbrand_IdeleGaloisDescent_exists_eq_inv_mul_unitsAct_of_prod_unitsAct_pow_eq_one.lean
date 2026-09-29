-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/86b1f263-7c9a-576b-84fc-d5d5e2213371

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_NumberField_SIdeleModule
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory groupCohomology M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp NumberField.PlaceTransport

namespace R4H90

section Generic

theorem subsingleton_H1_units (G F : Type) [Group G] [Finite G] [Field F] [MulSemiringAction G F]
    [FaithfulSMul G F] [MulDistribMulAction G Fˣ]
    (hsmul : ∀ (g : G) (u : Fˣ), ((g • u : Fˣ) : F) = g • (u : F)) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1) := by
  refine ⟨fun a b => ?_⟩
  suffices h : ∀ a : groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1, a = 0 by rw [h a, h b]
  intro a
  refine H1_induction_on a fun x => (H1π_eq_zero_iff _).2 ?_
  have hf := isMulCocycle₁_of_mem_cocycles₁ (M := Fˣ) x.1 x.2
  let e : G ≃* (F ≃ₐ[FixedPoints.subfield G F] F) := FixedPoints.toAlgAutMulEquiv G F
  let tm : Additive Fˣ ≃ Fˣ := Additive.toMul
  let f : G → Fˣ := fun g => tm (x.1 g)
  have hf1 : IsMulCocycle₁ f := hf
  let f' : (F ≃ₐ[FixedPoints.subfield G F] F) → Fˣ := fun φ => f (e.symm φ)
  have he : ∀ (g : G) (y : F), (e g) y = g • y := fun g y => rfl
  have hf' : IsMulCocycle₁ f' := by
    intro φ ψ
    show f (e.symm (φ * ψ)) = φ • f (e.symm ψ) * f (e.symm φ)
    rw [map_mul, hf1 (e.symm φ) (e.symm ψ)]
    congr 1
    ext
    rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hsmul, ← he, MulEquiv.apply_symm_apply]
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f' hf'
  have hcob : IsMulCoboundary₁ f := by
    refine ⟨β, fun g => ?_⟩
    have h2 := hβ (e g)
    simp only [f', MulEquiv.symm_apply_apply] at h2
    rw [← h2]
    congr 1
    ext
    rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe, hsmul, he]
  exact (coboundariesOfIsMulCoboundary₁ hcob).2

attribute [local instance] IsCyclic.commGroup in

theorem exists_eq_inv_mul_smul_of_subsingleton (G M : Type) [Group G] [Finite G] [CommGroup M]
    [MulDistribMulAction G M] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hH1 : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 1))
    (u : M) (hu : ∏ᶠ τ : G, τ • u = 1) : ∃ w : M, u = w⁻¹ * g • w := by
  haveI : IsCyclic G := ⟨⟨g, hg⟩⟩
  letI : Fintype G := Fintype.ofFinite G
  rw [finprod_eq_prod_of_fintype] at hu
  set A := Rep.ofMulDistribMulAction G M
  have hker : (Additive.ofMul u : A) ∈ (Rep.Hom.hom A.norm).ker := by
    show A.norm.hom (Additive.ofMul u) = 0
    simp only [A, Rep.norm, Representation.norm, Rep.hom_ofHom, Representation.IntertwiningMap.coe_mk]
    rw [LinearMap.sum_apply]
    change (∑ d : G, Additive.ofMul (d • u) : Additive M) = 0
    rw [← ofMul_prod, hu, ofMul_one]
  have := (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff A g hg 1 odd_one ⟨_, hker⟩).1
    (Subsingleton.elim _ _)
  obtain ⟨y, hy⟩ := this
  set w : M := (Additive.toMul : Additive M ≃ M) y with hw
  refine ⟨w, ?_⟩
  have h2 := congrArg (Additive.toMul : Additive M ≃ M) hy
  simp only [A, Rep.sub_hom, Rep.hom_id,
    Representation.IntertwiningMap.sub_toLinearMap, Representation.IntertwiningMap.toLinearMap_id,
    LinearMap.sub_apply, Representation.IntertwiningMap.coe_toLinearMap, Rep.applyAsHom_apply,
    Rep.ofMulDistribMulAction_ρ_apply_apply, LinearMap.id_coe, id_eq] at h2
  have h3 : g • w / w = u := h2
  rw [← h3, div_eq_mul_inv, mul_comm]

theorem prod_eq_prod_range (G M : Type) [Group G] [Fintype G] [CommMonoid M] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (f : G → M) :
    ∏ τ : G, f τ = ∏ k ∈ Finset.range (orderOf g), f (g ^ k) := by
  have himg : (Finset.range (orderOf g)).image (g ^ ·) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro τ
    rw [← mem_powers_iff_mem_range_orderOf, mem_powers_iff_mem_zpowers]
    exact hg τ
  rw [← himg, Finset.prod_image]
  intro i hi j hj h
  exact pow_injOn_Iio_orderOf (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h

end Generic

section Places

variable {E L : Type} [Field E] [Field L] [NumberField L] [Algebra E L]

variable (E L) in

theorem finite_aut : Finite (L ≃ₐ[E] L) := by
  let f : (L ≃ₐ[E] L) → (L ≃ₐ[ℚ] L) := fun τ => AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun q => by simp)
  have hf : Function.Injective f := by
    intro a b h
    ext x
    exact congrArg (fun e : L ≃ₐ[ℚ] L => e x) h
  exact Finite.of_injective f hf

theorem smul_eq_of_mem_decomp (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L)
    (hτ : τ ∈ PlaceDecomp.decomp E L w) : τ • w = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [PlaceTransport.mem_smul_asIdeal_iff, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  have hv := PlaceDecomp.valuation_apply_of_mem τ⁻¹ (inv_mem hτ) (algebraMap (𝓞 L) L x)
  change w.valuation L (τ⁻¹ (algebraMap (𝓞 L) L x)) < 1 ↔ _
  rw [hv]

omit [NumberField L] in

theorem faithfulSMul_decomp [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    FaithfulSMul (PlaceDecomp.decomp E L w) (w.adicCompletion L) := by
  refine ⟨fun {τ₁ τ₂} h => ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro l
  have h1 := h ((WithVal.toVal (w.valuation L) l : WithVal (w.valuation L)) : w.adicCompletion L)
  rw [PlaceDecomp.smul_def, PlaceDecomp.smul_def, PlaceDecomp.actRingEquiv_coe, PlaceDecomp.actRingEquiv_coe] at h1
  have h2 := UniformSpace.Completion.coe_injective _
    (congrArg IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion h1)
  simpa [WithVal.congr_apply] using h2

omit [NumberField L] in

theorem faithfulSMul_infDecomp (v : InfinitePlace L) :
    FaithfulSMul (InfPlaceDecomp.decomp E L v) v.Completion := by
  refine ⟨fun {τ₁ τ₂} h => ?_⟩
  apply Subtype.ext
  apply AlgEquiv.ext
  intro l
  have h1 := h ((WithAbs.toAbs v.1 l : WithAbs v.1) : v.Completion)
  rw [InfPlaceDecomp.smul_def, InfPlaceDecomp.smul_def, InfPlaceDecomp.actRingEquiv_coe,
    InfPlaceDecomp.actRingEquiv_coe] at h1
  have h2 := UniformSpace.Completion.coe_injective _
    (congrArg NumberField.InfinitePlace.Completion.toCompletion h1)
  simpa [WithAbs.congr_apply] using h2

theorem subsingleton_H1_fin (w : HeightOneSpectrum (𝓞 L)) :
    Subsingleton (groupCohomology
      (Rep.ofMulDistribMulAction (PlaceDecomp.decomp E L w) (w.adicCompletion L)ˣ) 1) := by
  haveI := finite_aut E L
  haveI := faithfulSMul_decomp (E := E) w
  exact subsingleton_H1_units (PlaceDecomp.decomp E L w) (w.adicCompletion L) fun _ _ => rfl

theorem subsingleton_H1_inf (v : InfinitePlace L) :
    Subsingleton (groupCohomology (InfPlaceDecomp.localUnits E L v) 1) := by
  haveI := finite_aut E L
  haveI := faithfulSMul_infDecomp (E := E) v
  exact subsingleton_H1_units (InfPlaceDecomp.decomp E L v) v.Completion fun _ _ => rfl

end Places

section GaloisBase

variable (L : Type) [Field L] [NumberField L]
variable (E : Type) [Field E] [NumberField E] [Algebra E L] (D' : IdeleGaloisDescent (𝓞 L) E L)

theorem act_snd_apply_of_mem (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ PlaceDecomp.decomp E L w)
    (y : AdeleRing (𝓞 L) L) : (D'.act τ y).2 w = PlaceDecomp.actRingEquiv ⟨τ, hτ⟩ (y.2 w) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) E L
  have hD : D' = GenuineDescent.genuineDescentDatum E L := Subsingleton.elim _ _
  rw [hD]
  exact GenuineDescent.genuineDescentDatum_act_snd_apply E L τ y (smul_eq_of_mem_decomp w τ hτ)

theorem act_fst_apply_of_mem (v : InfinitePlace L) (τ : L ≃ₐ[E] L) (hτ : τ ∈ InfPlaceDecomp.decomp E L v)
    (y : AdeleRing (𝓞 L) L) : (D'.act τ y).1 v = InfPlaceDecomp.actRingEquiv ⟨τ, hτ⟩ (y.1 v) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) E L
  have hD : D' = GenuineDescent.genuineDescentDatum E L := Subsingleton.elim _ _
  rw [hD]
  exact GenuineDescent.genuineDescentDatum_act_fst_apply E L τ y (MulAction.mem_stabilizer_iff.1 hτ)

@[reducible] noncomputable def ideleAction : MulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ :=
  MulDistribMulAction.compHom _ D'.unitsAct

noncomputable def prFin (w : HeightOneSpectrum (𝓞 L)) :
    letI := ideleAction L E D'
    (Rep.res (PlaceDecomp.decomp E L w).subtype (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) ⟶
      Rep.ofMulDistribMulAction ↥(PlaceDecomp.decomp E L w) (w.adicCompletion L)ˣ) :=
  letI := ideleAction L E D'
  Rep.ofHom
    { toLinearMap := (MonoidHom.toAdditive (finPart (R := 𝓞 L) (F := L) w)).toIntLinearMap
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Units.ext
        show ((D'.act τ (Additive.toMul x : (AdeleRing (𝓞 L) L)ˣ)).2 w : w.adicCompletion L) =
          τ • ((Additive.toMul x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2 w
        rw [act_snd_apply_of_mem L E D' w τ τ.2, PlaceDecomp.smul_def] }

theorem prFin_apply (w : HeightOneSpectrum (𝓞 L)) (x : (AdeleRing (𝓞 L) L)ˣ) :
    letI := ideleAction L E D'
    (prFin L E D' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x) := rfl

noncomputable def prInf (v : InfinitePlace L) :
    letI := ideleAction L E D'
    (Rep.res (InfPlaceDecomp.decomp E L v).subtype (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) ⟶
      InfPlaceDecomp.localUnits E L v) :=
  letI := ideleAction L E D'
  Rep.ofHom
    { toLinearMap := (MonoidHom.toAdditive
        ((Units.map (Pi.evalMonoidHom (fun u : InfinitePlace L => u.Completion) v)).comp
          (infPart (R := 𝓞 L) (F := L)))).toIntLinearMap
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        apply Units.ext
        show ((D'.act τ (Additive.toMul x : (AdeleRing (𝓞 L) L)ˣ)).1 v : v.Completion) =
          τ • ((Additive.toMul x : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 v
        rw [act_fst_apply_of_mem L E D' v τ τ.2, InfPlaceDecomp.smul_def] }

theorem prInf_apply (v : InfinitePlace L) (x : (AdeleRing (𝓞 L) L)ˣ) :
    letI := ideleAction L E D'
    (prInf L E D' v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace L => u.Completion) v) (infPart x)) := rfl

theorem subsingleton_H1_ideles [IsGalois E L] :
    letI := ideleAction L E D'
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) 1) := by
  letI := ideleAction L E D'
  obtain ⟨hinj, -, -⟩ :=
    M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles E L D'
      (fun _ _ => rfl) (prFin L E D') (fun w x => rfl) (prInf L E D') (fun v x => rfl) 0
  refine ⟨fun a b => ?_⟩
  have ha : ∀ x : groupCohomology (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ) (0 + 1), x = 0 :=
    fun x => hinj x (fun w => by haveI := subsingleton_H1_fin (E := E) (L := L) w; exact Subsingleton.elim _ _)
      (fun v => by haveI := subsingleton_H1_inf (E := E) (L := L) v; exact Subsingleton.elim _ _)
  exact (ha a).trans (ha b).symm

end GaloisBase

section Cyclic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem numberField_subfield (E : Subfield L) : NumberField E := by
  have hf : Function.Injective ((algebraMap E L).toRatAlgHom.toLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℚ E := Module.Finite.of_injective _ hf
  exact ⟨⟩

noncomputable def restrictDescent (E : Type) [Field E] [Algebra E L] (φ : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))
    (hφ : ∀ τ x, (φ τ) x = τ x) : IdeleGaloisDescent (𝓞 L) E L where
  act := D.act.comp φ
  compat τ x := by
    show D.act (φ τ) (algebraMap L _ x) = _
    rw [D.compat, hφ]
  continuous_act τ := D.continuous_act (φ τ)

theorem restrictDescent_unitsAct (E : Type) [Field E] [Algebra E L] (φ : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L))
    (hφ : ∀ τ x, (φ τ) x = τ x) (τ : L ≃ₐ[E] L) (x : (AdeleRing (𝓞 L) L)ˣ) :
    (restrictDescent K L D E φ hφ).unitsAct τ x = D.unitsAct (φ τ) x := rfl

theorem main (u : (AdeleRing (𝓞 L) L)ˣ)
    (hu : ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) u = 1) :
    ∃ w : (AdeleRing (𝓞 L) L)ˣ, u = w⁻¹ * D.unitsAct σ w := by
  classical
  haveI : Finite (L ≃ₐ[K] L) := finite_aut K L

  set H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers σ with hH
  haveI : Finite H := inferInstance
  let E : Subfield L := FixedPoints.subfield H L
  haveI : NumberField E := numberField_subfield L E

  let e : H ≃* (L ≃ₐ[E] L) := FixedPoints.toAlgAutMulEquiv H L
  have he : ∀ (h : H) (x : L), (e h) x = (h : L ≃ₐ[K] L) x := fun h x => rfl
  let φ : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) := H.subtype.comp e.symm.toMonoidHom
  have hφ : ∀ (τ : L ≃ₐ[E] L) (x : L), (φ τ) x = τ x := by
    intro τ x
    show ((e.symm τ : H) : L ≃ₐ[K] L) x = τ x
    rw [← he, MulEquiv.apply_symm_apply]
  let σH : H := ⟨σ, Subgroup.mem_zpowers σ⟩
  let σ' : L ≃ₐ[E] L := e σH
  have hφσ' : φ σ' = σ := by
    show ((e.symm (e σH) : H) : L ≃ₐ[K] L) = σ
    rw [MulEquiv.symm_apply_apply]
  have hgen : ∀ τ : L ≃ₐ[E] L, τ ∈ Subgroup.zpowers σ' := by
    intro τ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (e.symm τ).2
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, ← MulEquiv.apply_symm_apply e τ]
    congr 1
    apply Subtype.ext
    rw [SubgroupClass.coe_zpow]
    exact hk
  have hord : orderOf σ' = orderOf σ := by
    show orderOf (e.toMonoidHom σH) = orderOf σ
    rw [orderOf_injective e.toMonoidHom e.injective σH]
    exact (Subgroup.orderOf_coe σH).symm

  let D' : IdeleGaloisDescent (𝓞 L) E L := restrictDescent K L D E φ hφ
  letI := ideleAction L E D'

  have hH1 := subsingleton_H1_ideles L E D'

  letI : Fintype (L ≃ₐ[E] L) := Fintype.ofFinite _
  have hnorm : ∏ᶠ τ : L ≃ₐ[E] L, τ • u = 1 := by
    rw [finprod_eq_prod_of_fintype, prod_eq_prod_range (L ≃ₐ[E] L) _ σ' hgen, hord, ← hu]
    refine Finset.prod_congr rfl fun k _ => ?_
    show D.unitsAct (φ (σ' ^ k)) u = D.unitsAct (σ ^ k) u
    rw [map_pow, hφσ']
  obtain ⟨w, hw⟩ := exists_eq_inv_mul_smul_of_subsingleton (L ≃ₐ[E] L) (AdeleRing (𝓞 L) L)ˣ σ' hgen hH1 u hnorm
  refine ⟨w, ?_⟩
  rw [hw]
  show w⁻¹ * D.unitsAct (φ σ') w = w⁻¹ * D.unitsAct σ w
  rw [hφσ']

end Cyclic

end R4H90

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (u : (AdeleRing (𝓞 L) L)ˣ)
    (hu : ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) u = 1) :
    ∃ w : (AdeleRing (𝓞 L) L)ˣ, u = w⁻¹ * D.unitsAct σ w :=
  R4H90.main K L σ D u hu

end S_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one (solution)
