-- Prove2me | solution 1 for NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d4645774-3799-57e6-8765-38e0596a5006

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
import Theorems.Thm_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
import Theorems.Thm_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
import Theorems.Thm_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mStepFin

section General

theorem exists_lift_of_isClosedImmersion {D G Z : Scheme.{u}} [IsReduced D] (f : D ⟶ Z) (γ : G ⟶ Z)
    [IsClosedImmersion γ] (h : Set.range f.base ⊆ Set.range γ.base) : ∃ g : D ⟶ G, g ≫ γ = f := by
  haveI : Surjective (pullback.fst f γ) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro d
    exact h ⟨d, rfl⟩⟩
  haveI : IsIso (pullback.fst f γ) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f γ) ≫ pullback.snd f γ, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem specMap_apply_ne_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
    [IsLocalRing B] [Ring.DimensionLEOne B] (hA : IsLocalRing.maximalIdeal A ≠ ⊥) (f : A →+* B)
    (hf : Function.Injective f) (p : ↥(Spec (CommRingCat.of B))) (hp : p ≠ IsLocalRing.closedPoint B) :
    (Spec.map (CommRingCat.ofHom f)).base p ≠ IsLocalRing.closedPoint A := by
  have hbot : p.asIdeal = ⊥ := by
    by_contra h
    exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal p.isPrime h)))
  intro h
  have h' : (PrimeSpectrum.comap f p).asIdeal = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal h
    simp at this
    exact this
  rw [PrimeSpectrum.comap_asIdeal, hbot, Ideal.comap_bot_of_injective f hf] at h'
  exact hA h'.symm

theorem dense_of_forall_dense_fibre {X Z : Type*} [TopologicalSpace X] (p : X → Z) (S : Set X)
    (h : ∀ z : Z, Dense ((Subtype.val : {x : X // p x = z} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈
      closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) := h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

theorem maximal_fst_of_maximal {X S Z : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (p : ↑(pullback f g))
    (hp : ∀ p' : ↑(pullback f g), p' ⤳ p → (pullback.snd f g).base p' = (pullback.snd f g).base p → p' = p) :
    ∀ x' : X, x' ⤳ (pullback.fst f g).base p → f.base x' = f.base ((pullback.fst f g).base p) →
      x' = (pullback.fst f g).base p := by
  obtain ⟨z, hz⟩ : ∃ z, (pullback.snd f g).base p = z := ⟨_, rfl⟩
  obtain ⟨φ, sq, hφ⟩ : ∃ φ : (pullback.snd f g).fiber z ⟶ f.fiber (g.base z),
      IsPullback φ ((pullback.snd f g).fiberToSpecResidueField z) (f.fiberToSpecResidueField (g.base z))
        (Spec.map (g.residueFieldMap z)) ∧
      φ ≫ f.fiberι (g.base z) = (pullback.snd f g).fiberι z ≫ pullback.fst f g :=
    ⟨_, isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) z,
      pullback.lift_fst _ _ _⟩
  let e₂ := (pullback.snd f g).fiberι z
  let e₁ := f.fiberι (g.base z)
  obtain ⟨ζ, hζ⟩ : p ∈ Set.range e₂.base := by
    rw [Scheme.Hom.range_fiberι]; exact hz
  haveI : Flat (Spec.map (g.residueFieldMap z)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (g.residueFieldMap z).hom.toAlgebra
    exact Module.Flat.of_free
  haveI : Flat φ := by rw [← sq.isoPullback_hom_fst]; infer_instance
  have hφp : e₁.base (φ.base ζ) = (pullback.fst f g).base p := by
    rw [← Scheme.Hom.comp_apply]
    change (φ ≫ f.fiberι (g.base z)).base ζ = _
    rw [hφ, Scheme.Hom.comp_apply]
    exact congrArg _ hζ
  intro x' hx' hfx'
  obtain ⟨ξ', rfl⟩ : x' ∈ Set.range e₁.base := by
    rw [Scheme.Hom.range_fiberι]
    show f.base x' = g.base z
    rw [hfx', ← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz]
  have h1 : ξ' ⤳ φ.base ζ := by
    apply (e₁.isEmbedding.isInducing.specializes_iff).mp
    rw [hφp]
    exact hx'
  obtain ⟨ζ', hζ', hζ'ξ⟩ := Flat.generalizingMap φ h1
  have hζ'ζ : ζ' = ζ := by
    apply e₂.isEmbedding.injective
    rw [hζ]
    refine hp _ ?_ ?_
    · have := hζ'.map e₂.continuous
      rwa [hζ] at this
    · have : e₂.base ζ' ∈ (pullback.snd f g).base ⁻¹' {z} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨ζ', rfl⟩
      rw [hz]; exact this
  rw [hζ'ζ] at hζ'ξ
  rw [← hζ'ξ, hφp]

end General

section StrictLaw

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of A))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

structure Strict : Prop where
  hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))
  hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm))
  hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base))
  hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition])))
  hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of A))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1

def jA (a : Spec (CommRingCat.of A) ⟶ Y) (ha : a ≫ y = 𝟙 _) : Y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (y ≫ a) (𝟙 Y) (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem jA_fst (a : Spec (CommRingCat.of A) ⟶ Y) (ha : a ≫ y = 𝟙 _) : jA y a ha ≫ pullback.fst y y = y ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem jA_snd (a : Spec (CommRingCat.of A) ⟶ Y) (ha : a ≫ y = 𝟙 _) : jA y a ha ≫ pullback.snd y y = 𝟙 Y :=
  pullback.lift_snd _ _ _

theorem dense_preimage_jA (a : Spec (CommRingCat.of A) ⟶ Y) (ha : a ≫ y = 𝟙 _) (S : Set ↑(pullback y y))
    (hS : ∀ x : Y, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((jA y a ha).base ⁻¹' S) := by
  have hainj : Function.Injective a.base := by
    intro s₁ s₂ h
    have := congrArg y.base h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha] at this
  refine dense_of_forall_dense_fibre y.base _ fun s => ?_

  let φ : {b : ↑Y // y.base b = s} → {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} :=
    fun b => ⟨(jA y a ha).base b.1, by rw [← Scheme.Hom.comp_apply, jA_fst, Scheme.Hom.comp_apply, b.2]⟩
  have hφc : Continuous φ := ((jA y a ha).base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hji : Topology.IsInducing (jA y a ha).base := by
    refine Topology.IsInducing.of_comp (jA y a ha).continuous (pullback.snd y y).continuous ?_
    have : (pullback.snd y y).base ∘ (jA y a ha).base = id := by
      funext b
      change ((jA y a ha) ≫ pullback.snd y y).base b = b
      rw [jA_snd]; rfl
    rw [this]; exact Topology.IsInducing.id
  have hφi : Topology.IsInducing φ := by
    refine Topology.IsInducing.of_comp hφc continuous_subtype_val ?_
    exact hji.comp Topology.IsInducing.subtypeVal
  have hE : pullback.fst (pullback.fst y y) a =
      (pullback.fst (pullback.fst y y) a ≫ pullback.snd y y) ≫ jA y a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, jA_fst, pullback.condition, Category.assoc, ← pullback.condition_assoc,
        reassoc_of% (pullback.condition (f := pullback.fst y y) (g := a)), reassoc_of% ha]
    · rw [Category.assoc, jA_snd, Category.comp_id]
  have hφs : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ : q ∈ Set.range (pullback.fst (pullback.fst y y) a).base := by
      rw [Scheme.Pullback.range_fst]; exact ⟨s, hq.symm⟩
    refine ⟨⟨(pullback.snd y y).base q, hainj ?_⟩, ?_⟩
    · change a.base (y.base ((pullback.snd y y).base q)) = a.base s
      congr 1
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ha]
      rfl
    · apply Subtype.ext
      change (jA y a ha).base ((pullback.snd y y).base q) = q
      conv_rhs => rw [← hz, hE]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz]
  have hpre : ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) =
      φ ⁻¹' ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} → ↑(pullback y y)) ⁻¹' S) :=
    rfl
  rw [hpre, hφi.dense_iff]
  intro b
  rw [Set.image_preimage_eq _ hφs, (hS _).closure_eq]
  exact Set.mem_univ _

end StrictLaw

abbrev bS (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

structure Ctx : Type (u + 1) where
  R : Type u
  [cR : CommRing R]
  [domR : IsDomain R]
  [dvrR : IsDiscreteValuationRing R]
  Y : Scheme.{u}
  y : Y ⟶ Spec (CommRingCat.of R)
  [sm : Smooth y]
  [sep : IsSeparated y]
  [loft : LocallyOfFiniteType y]
  [qc : QuasiCompact y]
  U : (pullback y y).Opens
  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  hS : Strict y U m
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U
  R' : Type u
  [cR' : CommRing R']
  [domR' : IsDomain R']
  [dvrR' : IsDiscreteValuationRing R']
  [alg' : Algebra R R']
  [ff' : Module.FaithfullyFlat R R']
  Y' : Scheme.{u}
  y' : Y' ⟶ Spec (CommRingCat.of R')
  [sm' : Smooth y']
  [sep' : IsSeparated y']
  [loft' : LocallyOfFiniteType y']
  [qc' : QuasiCompact y']
  ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'
  [oi : IsOpenImmersion ι.1]
  hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base
  hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base
  U' : (pullback y' y').Opens
  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  hS' : Strict y' U' m'
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 =
          (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1
  R'' : Type u
  [cR'' : CommRing R'']
  [domR'' : IsDomain R'']
  [dvrR'' : IsDiscreteValuationRing R'']
  [alg'' : Algebra R' R'']
  [ff'' : Module.FaithfullyFlat R' R'']
  [algR'' : Algebra R R'']
  [tower : IsScalarTower R R' R'']
  a : Spec (CommRingCat.of R'') ⟶ Y
  ha : a ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R R''))

namespace Ctx

variable (C : Ctx.{u})

scoped instance : CommRing C.R := C.cR
scoped instance : IsDomain C.R := C.domR
scoped instance : IsDiscreteValuationRing C.R := C.dvrR
scoped instance : Smooth C.y := C.sm
scoped instance : IsSeparated C.y := C.sep
scoped instance : LocallyOfFiniteType C.y := C.loft
scoped instance : QuasiCompact C.y := C.qc
scoped instance : CommRing C.R' := C.cR'
scoped instance : IsDomain C.R' := C.domR'
scoped instance : IsDiscreteValuationRing C.R' := C.dvrR'
scoped instance : Algebra C.R C.R' := C.alg'
scoped instance : Module.FaithfullyFlat C.R C.R' := C.ff'
scoped instance : Smooth C.y' := C.sm'
scoped instance : IsSeparated C.y' := C.sep'
scoped instance : LocallyOfFiniteType C.y' := C.loft'
scoped instance : QuasiCompact C.y' := C.qc'
scoped instance : IsOpenImmersion C.ι.1 := C.oi
scoped instance : CommRing C.R'' := C.cR''
scoped instance : IsDomain C.R'' := C.domR''
scoped instance : IsDiscreteValuationRing C.R'' := C.dvrR''
scoped instance : Algebra C.R' C.R'' := C.alg''
scoped instance : Module.FaithfullyFlat C.R' C.R'' := C.ff''
scoped instance : Algebra C.R C.R'' := C.algR''
scoped instance : IsScalarTower C.R C.R' C.R'' := C.tower

abbrev s' : Spec (CommRingCat.of C.R') ⟶ Spec (CommRingCat.of C.R) := bS C.R C.R'

abbrev s'' : Spec (CommRingCat.of C.R'') ⟶ Spec (CommRingCat.of C.R) := bS C.R C.R''

abbrev t : Spec (CommRingCat.of C.R'') ⟶ Spec (CommRingCat.of C.R') := bS C.R' C.R''

theorem t_s' : C.t ≫ C.s' = C.s'' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

theorem t_ne (s : ↥(Spec (CommRingCat.of C.R''))) (hs : s ≠ IsLocalRing.closedPoint C.R'') :
    C.t.base s ≠ IsLocalRing.closedPoint C.R' :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field C.R') _
    (FaithfulSMul.algebraMap_injective C.R' C.R'') s hs

theorem s'_ne (s : ↥(Spec (CommRingCat.of C.R'))) (hs : s ≠ IsLocalRing.closedPoint C.R') :
    C.s'.base s ≠ IsLocalRing.closedPoint C.R :=
  specMap_apply_ne_closedPoint (IsDiscreteValuationRing.not_a_field C.R) _
    (FaithfulSMul.algebraMap_injective C.R C.R') s hs

abbrev Y1 : Scheme.{u} := pullback C.y C.s'

abbrev Y2 : Scheme.{u} := pullback C.y C.s''

abbrev Yp : Scheme.{u} := pullback C.y' C.t

abbrev yp : C.Yp ⟶ Spec (CommRingCat.of C.R'') := pullback.snd C.y' C.t

abbrev π : C.Yp ⟶ C.Y' := pullback.fst C.y' C.t

scoped instance : Smooth C.yp := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
scoped instance : IsSeparated C.yp := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
scoped instance : LocallyOfFiniteType C.yp := MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
scoped instance : QuasiCompact C.yp := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance

def k₁ : C.Y2 ⟶ C.Y1 :=
  pullback.lift (pullback.fst C.y C.s'') (pullback.snd C.y C.s'' ≫ C.t)
    (by rw [Category.assoc, C.t_s']; exact pullback.condition)

@[reassoc (attr := simp)]
theorem k₁_fst : C.k₁ ≫ pullback.fst C.y C.s' = pullback.fst C.y C.s'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem k₁_snd : C.k₁ ≫ pullback.snd C.y C.s' = pullback.snd C.y C.s'' ≫ C.t := pullback.lift_snd _ _ _

theorem isPullback_k₁ : IsPullback C.k₁ (pullback.snd C.y C.s'') (pullback.snd C.y C.s') C.t := by
  refine IsPullback.of_right ?_ C.k₁_snd (IsPullback.of_hasPullback C.y C.s')
  rw [k₁_fst, t_s']
  exact IsPullback.of_hasPullback _ _

def k : C.Y2 ⟶ C.Yp :=
  pullback.lift (C.k₁ ≫ C.ι.1) (pullback.snd C.y C.s'') (by rw [Category.assoc, C.ι.2, k₁_snd])

@[reassoc (attr := simp)]
theorem k_π : C.k ≫ C.π = C.k₁ ≫ C.ι.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem k_yp : C.k ≫ C.yp = pullback.snd C.y C.s'' := pullback.lift_snd _ _ _

theorem isPullback_k : IsPullback C.k C.k₁ C.π C.ι.1 := by
  refine IsPullback.of_right ?_ C.k_π (IsPullback.of_hasPullback C.y' C.t).flip
  rw [k_yp, C.ι.2]
  exact C.isPullback_k₁.flip

scoped instance isOpenImmersion_k : IsOpenImmersion C.k :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_k.flip C.oi

theorem mem_range_k (z : ↥C.Yp) (hz : C.π.base z ∈ Set.range C.ι.1.base) : z ∈ Set.range C.k.base := by
  obtain ⟨w, hw⟩ : z ∈ Set.range (pullback.fst C.π C.ι.1).base := by
    rw [Scheme.Pullback.range_fst]; exact hz
  refine ⟨C.isPullback_k.isoPullback.inv.base w, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hw

def aa : Spec (CommRingCat.of C.R'') ⟶ C.Y2 :=
  pullback.lift C.a (𝟙 _) (by rw [C.ha, Category.id_comp])

@[reassoc (attr := simp)]
theorem aa_fst : C.aa ≫ pullback.fst C.y C.s'' = C.a := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem aa_snd : C.aa ≫ pullback.snd C.y C.s'' = 𝟙 _ := pullback.lift_snd _ _ _

def ap : Spec (CommRingCat.of C.R'') ⟶ C.Yp := C.aa ≫ C.k

theorem ap_yp : C.ap ≫ C.yp = 𝟙 _ := by
  rw [ap, Category.assoc, k_yp, aa_snd]

abbrev y1 : C.Y1 ⟶ Spec (CommRingCat.of C.R') := pullback.snd C.y C.s'

def pi1 : pullback C.y1 C.y1 ⟶ pullback C.y C.y :=
  pullback.map _ _ _ _ (pullback.fst C.y C.s') (pullback.fst C.y C.s') C.s'
    pullback.condition.symm pullback.condition.symm

def ιι : pullback C.y1 C.y1 ⟶ pullback C.y' C.y' :=
  pullback.map _ _ _ _ C.ι.1 C.ι.1 (𝟙 _) (by rw [Category.comp_id, C.ι.2]) (by rw [Category.comp_id, C.ι.2])

@[reassoc]
theorem ιι_fst : C.ιι ≫ pullback.fst C.y' C.y' = pullback.fst C.y1 C.y1 ≫ C.ι.1 := pullback.lift_fst _ _ _

@[reassoc]
theorem ιι_snd : C.ιι ≫ pullback.snd C.y' C.y' = pullback.snd C.y1 C.y1 ≫ C.ι.1 := pullback.lift_snd _ _ _

theorem mem_U'_of_ne (q : ↥(pullback C.y' C.y'))
    (hq : (pullback.fst C.y' C.y' ≫ C.y').base q ≠ IsLocalRing.closedPoint C.R') : q ∈ C.U' := by
  have h1 : (pullback.fst C.y' C.y').base q ∈ Set.range C.ι.1.base :=
    C.hgen _ (by rw [← Scheme.Hom.comp_apply]; exact hq)
  have h2 : (pullback.snd C.y' C.y').base q ∈ Set.range C.ι.1.base :=
    C.hgen _ (by rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hq)
  obtain ⟨q₁, rfl⟩ : q ∈ Set.range C.ιι.base := by
    rw [ιι, Scheme.Pullback.range_map]; exact ⟨h1, h2⟩
  have e2 : C.ιι ≫ pullback.fst C.y' C.y' ≫ C.y' = pullback.fst C.y1 C.y1 ≫ C.y1 := by
    rw [ιι, pullback.lift_fst_assoc, Category.assoc, C.ι.2]

  let U₁ : (pullback C.y1 C.y1).Opens := C.pi1 ⁻¹ᵁ C.U
  have hq₁ : q₁ ∈ U₁ := by
    change C.pi1.base q₁ ∈ C.U
    apply C.hUK
    have e1 : C.pi1 ≫ pullback.fst C.y C.y ≫ C.y = (pullback.fst C.y1 C.y1 ≫ C.y1) ≫ C.s' := by
      rw [pi1, pullback.lift_fst_assoc, Category.assoc, pullback.condition, Category.assoc]
    rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
    apply C.s'_ne
    rw [← e2, Scheme.Hom.comp_apply]
    exact hq

  let wU : (U₁ : Scheme.{u}) ⟶ C.U := C.pi1.resLE C.U U₁ le_rfl
  have hwU : wU ≫ C.U.ι = U₁.ι ≫ C.pi1 := Scheme.Hom.resLE_comp_ι _ _
  let t' : (U₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of C.R') := U₁.ι ≫ pullback.fst C.y1 C.y1 ≫ C.y1
  have ht' : t' = U₁.ι ≫ pullback.snd C.y1 C.y1 ≫ C.y1 := by simp only [t', pullback.condition]
  have hA : wU ≫ C.U.ι ≫ pullback.fst C.y C.y = (U₁.ι ≫ pullback.fst C.y1 C.y1) ≫ pullback.fst C.y C.s' := by
    rw [reassoc_of% hwU, pi1, pullback.lift_fst, Category.assoc]
  have hB : wU ≫ C.U.ι ≫ pullback.snd C.y C.y = (U₁.ι ≫ pullback.snd C.y1 C.y1) ≫ pullback.fst C.y C.s' := by
    rw [reassoc_of% hwU, pi1, pullback.lift_snd, Category.assoc]
  have ha_ : (wU ≫ C.U.ι ≫ pullback.fst C.y C.y) ≫ C.y = t' ≫ C.s' := by
    rw [hA, Category.assoc, pullback.condition]; simp only [t', Category.assoc]
  have hb_ : (wU ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t' ≫ C.s' := by
    rw [hB, Category.assoc, pullback.condition, ht']; simp only [Category.assoc]
  have hc_ : (wU ≫ C.m.1) ≫ C.y = t' ≫ C.s' := by
    rw [Category.assoc, C.m.2]; simpa only [Category.assoc] using ha_
  obtain ⟨w', hw'₁, hw'₂, -⟩ :=
    C.hext t' ⟨wU, by simpa only [Category.assoc] using ha_⟩ ⟨_, ha_⟩ ⟨_, hb_⟩ ⟨_, hc_⟩ rfl rfl rfl
  rw [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂
  have e₁ : pullback.lift (wU ≫ C.U.ι ≫ pullback.fst C.y C.y) t' ha_ = U₁.ι ≫ pullback.fst C.y1 C.y1 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hA]
    · rw [pullback.lift_snd]; simp only [t', Category.assoc]
  have e₂ : pullback.lift (wU ≫ C.U.ι ≫ pullback.snd C.y C.y) t' hb_ = U₁.ι ≫ pullback.snd C.y1 C.y1 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hB]
    · rw [pullback.lift_snd, ht']; simp only [Category.assoc]
  have key : w'.1 ≫ C.U'.ι = U₁.ι ≫ C.ιι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hw'₁, e₁, Category.assoc, Category.assoc, ιι_fst]
    · rw [Category.assoc, hw'₂, e₂, Category.assoc, Category.assoc, ιι_snd]
  have hmem : (U₁.ι ≫ C.ιι).base ⟨q₁, hq₁⟩ ∈ C.U' := by
    rw [← key, Scheme.Hom.comp_apply]; exact (w'.1.base _).2
  rwa [Scheme.Hom.comp_apply] at hmem

def cc : pullback C.yp C.yp ⟶ pullback C.y' C.y' :=
  pullback.map _ _ _ _ C.π C.π C.t pullback.condition.symm pullback.condition.symm

theorem cc_fst : C.cc ≫ pullback.fst C.y' C.y' = pullback.fst C.yp C.yp ≫ C.π := pullback.lift_fst _ _ _

theorem cc_snd : C.cc ≫ pullback.snd C.y' C.y' = pullback.snd C.yp C.yp ≫ C.π := pullback.lift_snd _ _ _

abbrev Up : (pullback C.yp C.yp).Opens := C.cc ⁻¹ᵁ C.U'

theorem mem_Up_of_ne (q : ↥(pullback C.yp C.yp))
    (hq : (pullback.fst C.yp C.yp ≫ C.yp).base q ≠ IsLocalRing.closedPoint C.R'') : q ∈ C.Up := by
  change C.cc.base q ∈ C.U'
  apply C.mem_U'_of_ne
  have e : C.cc ≫ pullback.fst C.y' C.y' ≫ C.y' = (pullback.fst C.yp C.yp ≫ C.yp) ≫ C.t := by
    rw [cc, pullback.lift_fst_assoc, Category.assoc, pullback.condition, Category.assoc]
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact C.t_ne _ hq

abbrev jAp : C.Yp ⟶ pullback C.yp C.yp := jA C.yp C.ap C.ap_yp

abbrev W₀ : C.Yp.Opens := C.jAp ⁻¹ᵁ C.Up

theorem mem_W₀_of_ne (z : ↥C.Yp) (hz : C.yp.base z ≠ IsLocalRing.closedPoint C.R'') : z ∈ C.W₀ := by
  change C.jAp.base z ∈ C.Up
  apply C.mem_Up_of_ne
  have e : C.jAp ≫ pullback.fst C.yp C.yp ≫ C.yp = C.yp := by
    rw [jA_fst_assoc, ap_yp, Category.comp_id]
  rw [← Scheme.Hom.comp_apply, e]
  exact hz

abbrev jW : (C.W₀ : Scheme.{u}) ⟶ C.Up := C.jAp.resLE C.Up C.W₀ le_rfl

theorem jW_ι : C.jW ≫ C.Up.ι = C.W₀.ι ≫ C.jAp := Scheme.Hom.resLE_comp_ι _ _

@[reassoc]
theorem jW_fst : C.jW ≫ C.Up.ι ≫ pullback.fst C.yp C.yp = (C.W₀.ι ≫ C.yp) ≫ C.ap := by
  rw [reassoc_of% C.jW_ι, jA_fst, Category.assoc]

@[reassoc]
theorem jW_snd : C.jW ≫ C.Up.ι ≫ pullback.snd C.yp C.yp = C.W₀.ι := by
  rw [reassoc_of% C.jW_ι, jA_snd, Category.comp_id]

end Ctx
p2m_reactivate "P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Ctx"

structure Glued (C : Ctx.{u}) : Type (u + 1) where
  mp : SchemeHomOver (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp) C.yp
  hmp : mp.1 ≫ C.π = C.cc.resLE C.U' C.Up le_rfl ≫ C.m'.1
  hSp : Strict C.yp C.Up mp
  Y'' : Scheme.{u}
  y'' : Y'' ⟶ Spec (CommRingCat.of C.R'')
  [sm : Smooth y'']
  [sep : IsSeparated y'']
  [loft : LocallyOfFiniteType y'']
  [qc : QuasiCompact y'']
  jj : SchemeHomOver C.yp y''
  τ : SchemeHomOver C.yp y''
  [oij : IsOpenImmersion jj.1]
  [oiτ : IsOpenImmersion τ.1]
  cover : ∀ p : ↥Y'', p ∈ Set.range jj.1.base ∨ p ∈ Set.range τ.1.base
  hjjd : ∀ p : ↥Y'', (∀ p' : ↥Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) → p ∈ Set.range jj.1.base
  tr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (x : SchemeHomOver t C.yp)
      (w : SchemeHomOver t (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp)),
    w.1 ≫ C.Up.ι ≫ pullback.fst C.yp C.yp = t ≫ C.ap → w.1 ≫ C.Up.ι ≫ pullback.snd C.yp C.yp = x.1 →
    x.1 ≫ τ.1 = w.1 ≫ mp.1 ≫ jj.1
  U'' : (pullback y'' y'').Opens
  m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫ y'') y''
  hS'' : Strict y'' U'' m''
  hext'' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R''))
      (w : SchemeHomOver t (C.Up.ι ≫ pullback.fst C.yp C.yp ≫ C.yp)),
    ∃ w' : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
      w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = w.1 ≫ C.Up.ι ≫ pullback.fst C.yp C.yp ≫ jj.1 ∧
      w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = w.1 ≫ C.Up.ι ≫ pullback.snd C.yp C.yp ≫ jj.1 ∧
      w'.1 ≫ m''.1 = w.1 ≫ mp.1 ≫ jj.1

namespace Glued

variable {C : Ctx.{u}} (G : Glued C)

scoped instance : Smooth G.y'' := G.sm
scoped instance : IsSeparated G.y'' := G.sep
scoped instance : LocallyOfFiniteType G.y'' := G.loft
scoped instance : QuasiCompact G.y'' := G.qc
scoped instance : IsOpenImmersion G.jj.1 := G.oij
scoped instance : IsOpenImmersion G.τ.1 := G.oiτ

end Glued
p2m_reactivate "P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Ctx P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Glued"

namespace Ctx

variable (C : Ctx.{u})

theorem nonempty_glued : Nonempty (Glued C) := by

  obtain ⟨mp, hmp, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    NeronModelInfra.exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
      C.t C.y' C.U' C.m' C.hS'.hU₁ C.hS'.hU₂ C.hS'.hΦ C.hS'.hΦ₁ C.hS'.hΦ₂ C.hS'.hΨ C.hS'.hΨ₁ C.hS'.hΨ₂
      C.hS'.hassoc C.yp C.π (IsPullback.of_hasPullback C.y' C.t) C.cc C.cc_fst C.cc_snd

  obtain ⟨G, γ, hγ, -, hΓ, hq12, hq13, hq23, -⟩ :=
    NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      C.yp C.Up mp h1 h2 h3 h4 h5 h6 h7 h8 h9
  haveI := hγ
  haveI := hq12
  haveI := hq13
  haveI := hq23
  have hsub : Set.range (pullback.lift (f := pullback.fst C.yp C.yp ≫ C.yp) (g := C.yp) C.Up.ι mp.1 mp.2.symm).base ⊆
      Set.range γ.base := hΓ ▸ subset_closure

  obtain ⟨Y'', y'', jj, τ, hsm, hsep, hloft, hqc, hjj, hτ, hcov, hjjd, -, hpb, htr⟩ :=
    NeronModelInfra.exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
      C.yp C.Up mp h1 h4 γ hsub C.ap C.ap_yp
  haveI := hsm
  haveI := hsep
  haveI := hloft
  haveI := hqc
  haveI := hjj
  haveI := hτ

  obtain ⟨U'', m'', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, gext⟩ :=
    NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
      C.yp C.Up mp h1 h2 h3 h4 h5 h6 h7 h8 h9 γ hΓ C.ap C.ap_yp y'' jj τ hcov hpb
  exact ⟨⟨mp, hmp, ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun t u v p q => h9 t u v p q⟩, Y'', y'', jj, τ, hcov, hjjd,
    fun t x w => htr t x w, U'', m'', ⟨g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, fun t u v p q => g₉ t u v p q⟩,
    fun t w => gext t w⟩⟩

end Ctx
p2m_reactivate "P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Ctx P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Glued"

namespace Ctx

variable (C : Ctx.{u})

theorem dense_W₀ (G : Glued C) : Dense (C.W₀ : Set ↥C.Yp) :=
  dense_preimage_jA C.yp C.ap C.ap_yp _ G.hSp.hU₁

theorem tr_W₀ (G : Glued C) : C.W₀.ι ≫ G.τ.1 = C.jW ≫ G.mp.1 ≫ G.jj.1 :=
  G.tr (C.W₀.ι ≫ C.yp) ⟨C.W₀.ι, rfl⟩
    ⟨C.jW, by rw [reassoc_of% C.jW_ι, jA_fst_assoc, ap_yp, Category.comp_id]⟩
    C.jW_fst C.jW_snd

theorem gen₂ (G : Glued C) (p : ↥G.Y'') (hp : G.y''.base p ≠ IsLocalRing.closedPoint C.R'') :
    p ∈ Set.range (C.k ≫ G.jj.1).base := by

  obtain ⟨z, rfl⟩ : p ∈ Set.range G.jj.1.base := by
    rcases G.cover p with h | ⟨x, rfl⟩
    · exact h
    · have hx : x ∈ C.W₀ := C.mem_W₀_of_ne x (by
        have e : (G.τ.1 ≫ G.y'').base x = C.yp.base x := by rw [G.τ.2]
        rw [Scheme.Hom.comp_apply] at e
        rw [← e]; exact hp)
      have h := congrArg (fun f => f.base ⟨x, hx⟩) (C.tr_W₀ G)
      simp only [Scheme.Hom.comp_apply] at h
      exact ⟨_, h.symm⟩

  have hz : C.yp.base z ≠ IsLocalRing.closedPoint C.R'' := by
    have e : (G.jj.1 ≫ G.y'').base z = C.yp.base z := by rw [G.jj.2]
    rw [Scheme.Hom.comp_apply] at e
    rw [← e]; exact hp
  have hπz : C.y'.base (C.π.base z) ≠ IsLocalRing.closedPoint C.R' := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact C.t_ne _ hz
  obtain ⟨w, rfl⟩ := C.mem_range_k z (C.hgen _ hπz)
  exact ⟨w, by rw [Scheme.Hom.comp_apply]⟩

theorem max₂ (G : Glued C) (p : ↥G.Y'') (hp : ∀ p' : ↥G.Y'', p' ⤳ p → G.y''.base p' = G.y''.base p → p' = p) :
    p ∈ Set.range (C.k ≫ G.jj.1).base := by
  obtain ⟨z, rfl⟩ := G.hjjd p hp
  have hz : ∀ z' : ↥C.Yp, z' ⤳ z → C.yp.base z' = C.yp.base z → z' = z := by
    intro z' h1 h2
    apply G.jj.1.isOpenEmbedding.injective
    apply hp _ (h1.map G.jj.1.continuous)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, G.jj.2]
    exact h2
  obtain ⟨w, rfl⟩ := C.mem_range_k z (C.hmax _ (maximal_fst_of_maximal C.y' C.t z hz))
  exact ⟨w, by rw [Scheme.Hom.comp_apply]⟩

theorem hext₂ (G : Glued C) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C.R''))
    (w : SchemeHomOver (t' ≫ C.s'') (C.U.ι ≫ pullback.fst C.y C.y ≫ C.y))
    (a b c : SchemeHomOver (t' ≫ C.s'') C.y)
    (ha : a.1 = w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) (hb : b.1 = w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hc : c.1 = w.1 ≫ C.m.1) :
    ∃ w' : SchemeHomOver t' (G.U''.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y''),
      w'.1 ≫ G.U''.ι ≫ pullback.fst G.y'' G.y'' = pullback.lift a.1 t' a.2 ≫ C.k ≫ G.jj.1 ∧
      w'.1 ≫ G.U''.ι ≫ pullback.snd G.y'' G.y'' = pullback.lift b.1 t' b.2 ≫ C.k ≫ G.jj.1 ∧
      w'.1 ≫ G.m''.1 = pullback.lift c.1 t' c.2 ≫ C.k ≫ G.jj.1 := by

  have hT : (t' ≫ C.t) ≫ C.s' = t' ≫ C.s'' := by rw [Category.assoc, C.t_s']
  obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := C.hext (t' ≫ C.t) ⟨w.1, by rw [hT]; exact w.2⟩ ⟨a.1, by rw [hT]; exact a.2⟩
    ⟨b.1, by rw [hT]; exact b.2⟩ ⟨c.1, by rw [hT]; exact c.2⟩ ha hb hc
  simp only [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂ hw'₃

  have hlift : ∀ (x : SchemeHomOver (t' ≫ C.s'') C.y) (h : x.1 ≫ C.y = (t' ≫ C.t) ≫ C.s'),
      pullback.lift x.1 t' x.2 ≫ C.k ≫ C.π = pullback.lift x.1 (t' ≫ C.t) h ≫ C.ι.1 := by
    intro x h
    rw [k_π, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, k₁_fst, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, k₁_snd, pullback.lift_snd_assoc, pullback.lift_snd]

  let wp : T ⟶ pullback C.yp C.yp :=
    pullback.lift (pullback.lift a.1 t' a.2 ≫ C.k) (pullback.lift b.1 t' b.2 ≫ C.k)
      (by simp only [Category.assoc, k_yp, pullback.lift_snd])
  have hwp : wp ≫ C.cc = w'.1 ≫ C.U'.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, cc_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, hw'₁]
      exact hlift a _
    · rw [Category.assoc, cc_snd, pullback.lift_snd_assoc, Category.assoc, Category.assoc, hw'₂]
      exact hlift b _
  have hrange : Set.range wp.base ⊆ Set.range C.Up.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨θ, rfl⟩
    change (wp ≫ C.cc).base θ ∈ C.U'
    rw [hwp, Scheme.Hom.comp_apply]
    exact (w'.1.base θ).2
  let wU : T ⟶ C.Up := IsOpenImmersion.lift C.Up.ι wp hrange
  have hwU : wU ≫ C.Up.ι = wp := IsOpenImmersion.lift_fac _ _ _
  have hres : wU ≫ C.cc.resLE C.U' C.Up le_rfl = w'.1 := by
    rw [← cancel_mono C.U'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, reassoc_of% hwU, hwp]
  have hm : wU ≫ G.mp.1 = pullback.lift c.1 t' c.2 ≫ C.k := by
    apply pullback.hom_ext
    · rw [Category.assoc, G.hmp, reassoc_of% hres, hw'₃]
      exact ((Category.assoc _ _ _).trans (hlift c _)).symm
    · rw [Category.assoc, G.mp.2, reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc, k_yp,
        pullback.lift_snd, Category.assoc, k_yp, pullback.lift_snd]
  obtain ⟨w'', h₁, h₂, h₃⟩ := G.hext'' t' ⟨wU, by
    rw [reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc, k_yp, pullback.lift_snd]⟩
  refine ⟨w'', ?_, ?_, ?_⟩
  · rw [h₁, reassoc_of% hwU, pullback.lift_fst_assoc, Category.assoc]
  · rw [h₂, reassoc_of% hwU, pullback.lift_snd_assoc, Category.assoc]
  · rw [h₃, reassoc_of% hm]

theorem dom (G : Glued C) {T : Scheme.{u}} (x : T ⟶ C.Y2) (x₁ : T ⟶ C.Y1) (x₂ : T ⟶ C.Yp)
    (h₁ : x₁ ≫ pullback.fst C.y C.s' = x ≫ pullback.fst C.y C.s'')
    (h₂ : x₁ ≫ pullback.snd C.y C.s' = x ≫ pullback.snd C.y C.s'' ≫ C.t)
    (h₃ : x₂ ≫ C.π = x₁ ≫ C.ι.1) (h₄ : x₂ ≫ C.yp = x ≫ pullback.snd C.y C.s'') :
    x₂ ≫ G.jj.1 = x ≫ C.k ≫ G.jj.1 := by
  rw [← Category.assoc]
  congr 1
  have hx₁ : x ≫ C.k₁ = x₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, k₁_fst, h₁]
    · rw [Category.assoc, k₁_snd, h₂]
  apply pullback.hom_ext
  · rw [h₃, Category.assoc, k_π, ← Category.assoc, hx₁]
  · rw [h₄, Category.assoc, k_yp]

theorem progress (G : Glued C) :
    ∃ (D : (pullback G.y'' G.y'').Opens) (hle : G.U'' ≤ D)
      (M : SchemeHomOver (D.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'') G.y''),
      (pullback G.y'' G.y'').homOfLE hle ≫ M.1 = G.m''.1 ∧
      ∀ (a₂ : Spec (CommRingCat.of C.R'') ⟶ C.Y2),
        a₂ ≫ pullback.fst C.y C.s'' = C.a → a₂ ≫ pullback.snd C.y C.s'' = 𝟙 _ →
        ∀ {T : Scheme.{u}} (b : T ⟶ C.Y2) (q : T ⟶ pullback G.y'' G.y''),
          q ≫ pullback.fst G.y'' G.y'' = b ≫ pullback.snd C.y C.s'' ≫ a₂ ≫ C.k ≫ G.jj.1 →
          q ≫ pullback.snd G.y'' G.y'' = b ≫ C.k ≫ G.jj.1 →
          Set.range q.base ⊆ (D : Set ↥(pullback G.y'' G.y'')) := by

  obtain ⟨G₂, γ₂, hγ₂, -, hΓ₂, hq₁₂, -, -, -⟩ :=
    NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
      G.y'' G.U'' G.m'' G.hS''.hU₁ G.hS''.hU₂ G.hS''.hΦ G.hS''.hΦ₁ G.hS''.hΦ₂ G.hS''.hΨ G.hS''.hΨ₁ G.hS''.hΨ₂
      G.hS''.hassoc
  haveI := hγ₂
  let q12 : G₂ ⟶ pullback G.y'' G.y'' := γ₂ ≫ pullback.fst (pullback.fst G.y'' G.y'' ≫ G.y'') G.y''
  haveI : IsOpenImmersion q12 := hq₁₂
  let grm : (G.U'' : Scheme.{u}) ⟶ pullback (pullback.fst G.y'' G.y'' ≫ G.y'') G.y'' :=
    pullback.lift (f := pullback.fst G.y'' G.y'' ≫ G.y'') (g := G.y'') G.U''.ι G.m''.1 G.m''.2.symm
  have hsub : Set.range grm.base ⊆ Set.range γ₂.base := hΓ₂ ▸ subset_closure

  let D : (pullback G.y'' G.y'').Opens := q12.opensRange
  have hDr : Set.range D.ι.base ⊆ Set.range q12.base := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => hx
  let l : (D : Scheme.{u}) ⟶ G₂ := IsOpenImmersion.lift q12 D.ι hDr
  have hl : l ≫ γ₂ ≫ pullback.fst _ _ = D.ι := IsOpenImmersion.lift_fac _ _ _
  let M₀ : (D : Scheme.{u}) ⟶ G.Y'' := l ≫ γ₂ ≫ pullback.snd _ _
  have hM₀ : M₀ ≫ G.y'' = D.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'' := by
    simp only [M₀, Category.assoc]
    rw [← pullback.condition (f := pullback.fst G.y'' G.y'' ≫ G.y'') (g := G.y''), reassoc_of% hl]
  have hle : G.U'' ≤ D := by
    intro u hu
    obtain ⟨g, hg⟩ := hsub ⟨⟨u, hu⟩, rfl⟩
    refine ⟨g, ?_⟩
    change (γ₂ ≫ pullback.fst _ _).base g = u
    rw [Scheme.Hom.comp_apply, hg, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl
  haveI : IsReduced (G.U'' : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (G.U''.ι ≫ pullback.fst G.y'' G.y'' ≫ G.y'')
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion grm γ₂ hsub
  have hM : (pullback G.y'' G.y'').homOfLE hle ≫ M₀ = G.m''.1 := by
    have h1 : (pullback G.y'' G.y'').homOfLE hle ≫ l = g₀ := by
      rw [← cancel_mono q12, Category.assoc]
      change _ ≫ l ≫ γ₂ ≫ pullback.fst _ _ = g₀ ≫ γ₂ ≫ pullback.fst _ _
      rw [hl, Scheme.homOfLE_ι, reassoc_of% hg₀, pullback.lift_fst]
    simp only [M₀]
    rw [reassoc_of% h1, reassoc_of% hg₀, pullback.lift_snd]
  refine ⟨D, hle, ⟨M₀, hM₀⟩, hM, ?_⟩

  intro a₂ ha₁ ha₂ T b q hq₁ hq₂
  have haa : a₂ = C.aa := by
    apply pullback.hom_ext
    · rw [ha₁, aa_fst]
    · rw [ha₂, aa_snd]
  subst haa

  let σ₁₂ : C.Yp ⟶ pullback G.y'' G.y'' :=
    pullback.lift (C.yp ≫ C.ap ≫ G.jj.1) G.jj.1
      (by rw [Category.assoc, Category.assoc, G.jj.2, ap_yp, Category.comp_id])
  let σ : C.Yp ⟶ pullback (pullback.fst G.y'' G.y'' ≫ G.y'') G.y'' :=
    pullback.lift σ₁₂ G.τ.1 (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, G.jj.2,
      ap_yp, Category.comp_id, G.τ.2])

  have hW : (C.W₀ : Set ↥C.Yp) ⊆ σ.base ⁻¹' Set.range γ₂.base := by
    intro v hv
    obtain ⟨w'', h₁, h₂, h₃⟩ := G.hext'' (C.W₀.ι ≫ C.yp)
      ⟨C.jW, by rw [reassoc_of% C.jW_ι, jA_fst_assoc, ap_yp, Category.comp_id]⟩
    have hgr : w''.1 ≫ grm = C.W₀.ι ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · rw [Category.assoc, h₁, Category.assoc, pullback.lift_fst]
          exact C.jW_fst_assoc _
        · rw [Category.assoc, h₂, Category.assoc, pullback.lift_snd]
          exact C.jW_snd_assoc _
      · rw [Category.assoc, pullback.lift_snd, h₃, Category.assoc, pullback.lift_snd, tr_W₀]
    have e : σ.base v = (w''.1 ≫ grm).base ⟨v, hv⟩ := by rw [hgr, Scheme.Hom.comp_apply]; rfl
    rw [Set.mem_preimage, e, Scheme.Hom.comp_apply]
    exact hsub ⟨_, rfl⟩
  have hall : σ.base ⁻¹' Set.range γ₂.base = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (C.dense_W₀ G).closure_eq]
    exact closure_minimal hW ((γ₂.isClosedEmbedding.isClosed_range).preimage σ.continuous)

  have hqσ : q = (b ≫ C.k) ≫ σ₁₂ := by
    apply pullback.hom_ext
    · rw [hq₁, Category.assoc, pullback.lift_fst, Category.assoc, k_yp_assoc, ap, Category.assoc]
    · rw [hq₂, Category.assoc, pullback.lift_snd, Category.assoc]
  rintro _ ⟨θ, rfl⟩
  obtain ⟨g, hg⟩ : σ.base ((b ≫ C.k).base θ) ∈ Set.range γ₂.base := by
    rw [← Set.mem_preimage, hall]; trivial
  refine ⟨g, ?_⟩
  change (γ₂ ≫ pullback.fst _ _).base g = q.base θ
  rw [Scheme.Hom.comp_apply, hg, ← Scheme.Hom.comp_apply, pullback.lift_fst, hqσ]
  simp only [Scheme.Hom.comp_apply]

end Ctx
p2m_reactivate "P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Ctx P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Glued"

end P2mStepFin
p2m_reactivate "P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Ctx P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin.Glued P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.P2mStepFin"

open P2mStepFin in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y') [IsOpenImmersion ι.1]
    (hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base)
    (hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)))
    (hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1)
    (hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1)
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Module.FaithfullyFlat R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R R''))) :
    ∃ (Y'' : Scheme.{u}) (y'' : Y'' ⟶ Spec (CommRingCat.of R''))
      (ι₂ : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y'')
      (U'' : (pullback y'' y'').Opens) (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
      Smooth y'' ∧ IsSeparated y'' ∧ LocallyOfFiniteType y'' ∧ QuasiCompact y'' ∧
      IsOpenImmersion ι₂.1 ∧
      (∀ p : Y'', y''.base p ≠ IsLocalRing.closedPoint R'' → p ∈ Set.range ι₂.1.base) ∧
      (∀ p : Y'', (∀ p' : Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) → p ∈ Set.range ι₂.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y'')),
        u.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        p.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.snd y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R''))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
          w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) a).1 ≫ ι₂.1 ∧
          w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) b).1 ≫ ι₂.1 ∧
          w'.1 ≫ m''.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) c).1 ≫ ι₂.1) ∧
      (∃ a'' : Spec (CommRingCat.of R'') ⟶ Y'', a'' ≫ y'' = 𝟙 _) ∧
      (∃ j : pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ⟶ Y'',
        IsOpenImmersion j ∧ j ≫ y'' = pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
          (x₁ : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (x₂ : T ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R'')))),
          x₁ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₁ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' R'')) →
          x₂ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x₁ ≫ ι.1 →
          x₂ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₂ ≫ j = x ≫ ι₂.1) ∧
      (∃ (D : (pullback y'' y'').Opens) (hle : U'' ≤ D)
        (M : SchemeHomOver (D.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
        (pullback y'' y'').homOfLE hle ≫ M.1 = m''.1 ∧
        ∀ (a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))),
          a₂ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = a → a₂ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = 𝟙 _ →
          ∀ {T : Scheme.{u}} (b : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (q : T ⟶ pullback y'' y''),
            q ≫ pullback.fst y'' y'' = b ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 →
            q ≫ pullback.snd y'' y'' = b ≫ ι₂.1 →
            Set.range q.base ⊆ (D : Set ↑(pullback y'' y''))) := by
  let C : Ctx.{u} :=
    ⟨R, Y, y, U, m, ⟨hU₁, hU₂, hΦ, hΦ₁, hΦ₂, hΨ, hΨ₁, hΨ₂, fun t u v p q => hassoc t u v p q⟩, hUK, R', Y', y', ι,
      hgen, hmax, U', m', ⟨hU'₁, hU'₂, hΦ', hΦ'₁, hΦ'₂, hΨ', hΨ'₁, hΨ'₂, fun t u v p q => hassoc' t u v p q⟩,
      fun t' w a b c => hext t' w a b c, R'', a, ha⟩
  obtain ⟨G⟩ := C.nonempty_glued
  refine ⟨G.Y'', G.y'', ⟨C.k ≫ G.jj.1, ?_⟩, G.U'', G.m'', G.sm, G.sep, G.loft, G.qc, inferInstance,
    C.gen₂ G, C.max₂ G, G.hS''.hU₁, G.hS''.hU₂, G.hS''.hΦ, G.hS''.hΦ₁, G.hS''.hΦ₂, G.hS''.hΨ, G.hS''.hΨ₁,
    G.hS''.hΨ₂, fun t u v p q => G.hS''.hassoc t u v p q, ?_, ⟨C.ap ≫ G.jj.1, ?_⟩,
    ⟨G.jj.1, inferInstance, G.jj.2, fun x x₁ x₂ h₁ h₂ h₃ h₄ => C.dom G x x₁ x₂ h₁ h₂ h₃ h₄⟩, C.progress G⟩
  · rw [Category.assoc, G.jj.2, Ctx.k_yp]
  · intro T t' w a b c ha hb hc
    simp only [RelativeGroupLaw.baseChangePointOfBase_coe]
    exact C.hext₂ G t' w a b c ha hb hc
  · rw [Category.assoc, G.jj.2, Ctx.ap_yp]

end
end S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
end P2MW
export P2MW.S_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre (solution)
