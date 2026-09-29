-- Prove2me | solution 1 for NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f51446be-1516-5826-b58e-75f3964432a8

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
import Theorems.Thm_NeronModelInfra_forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
import Theorems.Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mLaw535P

theorem exists_lift_of_isClosedImmersion {D G Z : Scheme.{u}} [IsReduced D] (f : D ⟶ Z) (γ : G ⟶ Z)
    [IsClosedImmersion γ] (h : Set.range f.base ⊆ Set.range γ.base) : ∃ g : D ⟶ G, g ≫ γ = f := by
  haveI : Surjective (pullback.fst f γ) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, Set.eq_univ_iff_forall]
    intro d
    exact h ⟨d, rfl⟩⟩
  haveI : IsIso (pullback.fst f γ) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst f γ) ≫ pullback.snd f γ, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem mem_of_dense_of_forall_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [NoetherianSpace X] {W : Set X} (hWo : IsOpen W) (hWd : Dense W) (x : X)
    (hx : ∀ x' : X, x' ⤳ x → x' = x) : x ∈ W := by
  set C := irreducibleComponent x with hC
  have hCmem : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hCirr : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCcl : IsClosed C := isClosed_irreducibleComponent
  obtain ⟨η, hη⟩ := QuasiSober.sober hCirr hCcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]
    exact mem_irreducibleComponent
  have hηeq : η = x := hx η hηx
  obtain ⟨o, ho, hone, hoC⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hCmem
  obtain ⟨z, hzo, hzW⟩ := hWd.inter_open_nonempty o ho hone
  have hz : η ⤳ z := by
    rw [specializes_iff_mem_closure, hη.def]
    exact hoC hzo
  rw [← hηeq]
  exact hz.mem_open hWo hzW

section Points

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

abbrev jA : Y ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (y ≫ a) (𝟙 Y) (by rw [Category.assoc, ha, Category.comp_id, Category.id_comp])

abbrev sA : pullback y y ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y)
    (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
      (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
    (pullback.snd y y)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id, pullback.condition])

abbrev grm : (U : Scheme.{u}) ⟶ pullback (pullback.fst y y ≫ y) y :=
  pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm

variable (g₀ : (U : Scheme.{u}) ⟶ G) (hg₀ : g₀ ≫ γ = grm y U m)

def mkΓa {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    T ⟶ pullback γ (sA y a ha) :=
  pullback.lift (w ≫ g₀)
    (pullback.lift (f := y) (g := y) x (w ≫ m.1)
      (by rw [Category.assoc, m.2, ← h2, Category.assoc, Category.assoc, pullback.condition]))
    (by
      rw [Category.assoc, hg₀]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
          exact h1
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst]
          exact h2
      · simp only [Category.assoc, pullback.lift_snd])

theorem mkΓa_pτ {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.fst y y = x := by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_fst]

theorem mkΓa_pι {T : Scheme.{u}} (x : T ⟶ Y) (w : T ⟶ (U : Scheme.{u}))
    (h1 : w ≫ U.ι ≫ pullback.fst y y = x ≫ y ≫ a) (h2 : w ≫ U.ι ≫ pullback.snd y y = x) :
    mkΓa y U m γ a ha g₀ hg₀ x w h1 h2 ≫ pullback.snd γ (sA y a ha) ≫ pullback.snd y y = w ≫ m.1 := by
  rw [mkΓa, pullback.lift_snd_assoc, pullback.lift_snd]

include hg₀ in

theorem exists_pτ_eq_and_exists_pι_eq [IsSeparated y] (u : ↑(U : Scheme.{u}))
    (hu : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base) :
    (∃ g : ↑(pullback γ (sA y a ha)), (pullback.snd γ (sA y a ha) ≫ pullback.fst y y).base g =
        (U.ι ≫ pullback.snd y y).base u) ∧
      (∃ g : ↑(pullback γ (sA y a ha)), (pullback.snd γ (sA y a ha) ≫ pullback.snd y y).base g = m.1.base u) := by
  haveI : IsClosedImmersion (a ≫ y) := by rw [ha]; infer_instance
  haveI : IsClosedImmersion a := IsClosedImmersion.of_comp a y
  set w : Spec ((U : Scheme.{u}).residueField u) ⟶ (U : Scheme.{u}) := (U : Scheme.{u}).fromSpecResidueField u
  have hrange : Set.range (w ≫ U.ι ≫ pullback.fst y y).base ⊆ Set.range a.base := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hu
  obtain ⟨α, hα⟩ := exists_lift_of_isClosedImmersion (w ≫ U.ι ≫ pullback.fst y y) a hrange
  have h1 : w ≫ U.ι ≫ pullback.fst y y = (w ≫ U.ι ≫ pullback.snd y y) ≫ y ≫ a := by
    have hα' : α = (w ≫ U.ι ≫ pullback.snd y y) ≫ y := by
      rw [← Category.comp_id α, ← ha, ← Category.assoc, hα, Category.assoc, Category.assoc, Category.assoc,
        Category.assoc, pullback.condition]
    rw [← hα, hα', Category.assoc]
  set z := mkΓa y U m γ a ha g₀ hg₀ _ w h1 rfl
  refine ⟨⟨z.base (IsLocalRing.closedPoint _), ?_⟩, ⟨z.base (IsLocalRing.closedPoint _), ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, mkΓa_pτ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  · rw [← Scheme.Hom.comp_apply, mkΓa_pι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

include hg₀ in

theorem preimage_jA_subset_range_pτ [IsSeparated y] :
    (jA y a ha).base ⁻¹' (U : Set ↑(pullback y y)) ⊆
      Set.range (pullback.snd γ (sA y a ha) ≫ pullback.fst y y).base := by
  intro b hb
  have hu : (U.ι ≫ pullback.fst y y).base (⟨(jA y a ha).base b, hb⟩ : ↑(U : Scheme.{u})) ∈ Set.range a.base := by
    refine ⟨y.base b, ?_⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    change (y ≫ a).base b = (pullback.fst y y).base ((jA y a ha).base b)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨⟨g, hg⟩, -⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu
  refine ⟨g, ?_⟩
  rw [hg, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  change (pullback.snd y y).base ((jA y a ha).base b) = b
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

include hg₀ in

theorem preimage_jA_range_subset_range_pι [IsSeparated y] :
    (jA y a ha).base ⁻¹' Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
      ((Category.assoc _ _ _).trans m.2.symm)).base ⊆
      Set.range (pullback.snd γ (sA y a ha) ≫ pullback.snd y y).base := by
  rintro c ⟨u, hu⟩
  have hu' : (U.ι ≫ pullback.fst y y).base u ∈ Set.range a.base := by
    refine ⟨y.base c, ?_⟩
    rw [← pullback.lift_fst (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm),
      Scheme.Hom.comp_apply, hu]
    change (y ≫ a).base c = (pullback.fst y y).base ((jA y a ha).base c)
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨-, ⟨g, hg⟩⟩ := exists_pτ_eq_and_exists_pι_eq y U m γ a ha g₀ hg₀ _ hu'
  refine ⟨g, ?_⟩
  rw [hg, ← pullback.lift_snd (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm),
    Scheme.Hom.comp_apply, hu, ← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

end Points

section Density

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

theorem mem_of_dense_fibre [NoetherianSpace Y] (W : Set Y) (hW : IsOpen W)
    (s : Spec (CommRingCat.of R)) (hd : Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W))
    (x : Y) (hxs : y.base x = s) (hmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x) : x ∈ W := by
  set e := y.fiberι s with he
  have hemb : Topology.IsEmbedding e.base := e.isEmbedding
  have hrange : Set.range e.base = y.base ⁻¹' {s} := y.range_fiberι s
  obtain ⟨ξ, hξ⟩ : x ∈ Set.range e.base := by rw [hrange]; exact hxs
  haveI : NoetherianSpace ↑(y.fiber s) := hemb.isInducing.noetherianSpace
  have hd' : Dense (e.base ⁻¹' W) := by
    rw [hemb.isInducing.dense_iff]
    intro ζ
    have hζ : e.base ζ ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ζ, rfl⟩
    have h1 : (⟨e.base ζ, hζ⟩ : {b : ↑Y // y.base b = s}) ∈
        closure ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W) := hd _
    rw [closure_subtype] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨⟨b, hb⟩, hbW, rfl⟩
    obtain ⟨ζ', rfl⟩ : b ∈ Set.range e.base := by rw [hrange]; exact hb
    exact ⟨ζ', hbW, rfl⟩
  have hmax' : ∀ ξ' : ↑(y.fiber s), ξ' ⤳ ξ → ξ' = ξ := by
    intro ξ' hξ'
    apply hemb.injective
    rw [hξ]
    refine hmax _ (hξ ▸ hξ'.map e.base.hom.continuous) ?_
    have h1 : e.base ξ' ∈ y.base ⁻¹' {s} := hrange ▸ ⟨ξ', rfl⟩
    rw [h1, hxs]
  have := mem_of_dense_of_forall_specializes (e.base.hom.continuous.isOpen_preimage W hW) hd' ξ hmax'
  rwa [Set.mem_preimage, hξ] at this

variable (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)

theorem dense_fibre_jA [IsSeparated y] (S : Set ↑(pullback y y)) (s : Spec (CommRingCat.of R))
    (hS : Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} →
      ↑(pullback y y)) ⁻¹' S)) :
    Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' ((jA y a ha).base ⁻¹' S)) := by
  haveI : IsClosedImmersion (jA y a ha ≫ pullback.snd y y) := by rw [pullback.lift_snd]; infer_instance
  haveI : IsClosedImmersion (jA y a ha) := IsClosedImmersion.of_comp (jA y a ha) (pullback.snd y y)
  have hainj : Function.Injective a.base := by
    intro s₁ s₂ h
    have := congrArg y.base h
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ha] at this
  let φ : {b : ↑Y // y.base b = s} → {q : ↑(pullback y y) // (pullback.fst y y).base q = a.base s} :=
    fun b => ⟨(jA y a ha).base b.1, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, b.2]⟩
  have hφc : Continuous φ := ((jA y a ha).base.hom.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Topology.IsInducing φ := by
    refine Topology.IsInducing.of_comp hφc continuous_subtype_val ?_
    exact (jA y a ha).isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hE : pullback.fst (pullback.fst y y) a = (pullback.fst (pullback.fst y y) a ≫ pullback.snd y y) ≫ jA y a ha := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.condition, Category.assoc, ← pullback.condition_assoc,
        reassoc_of% (pullback.condition (f := pullback.fst y y) (g := a)), reassoc_of% ha]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
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
  rw [Set.image_preimage_eq _ hφs, hS.closure_eq]
  exact Set.mem_univ _

theorem mem_range_of_maximal [NoetherianSpace Y] {Y' Γ' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    (i j : Y ⟶ Y') (hi : i ≫ y' = y) [IsOpenImmersion i]
    (p₁ p₂ : Γ' ⟶ Y) (hp : p₁ ≫ i = p₂ ≫ j)
    (W : Set Y) (hWo : IsOpen W) (hWd : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹' W))
    (hW : W ⊆ Set.range p₁.base)
    (p : Y') (hp' : ∀ q : Y', q ⤳ p → y'.base q = y'.base p → q = p) (x : Y) (hx : i.base x = p) :
    p ∈ Set.range j.base := by
  have hxmax : ∀ x' : Y, x' ⤳ x → y.base x' = y.base x → x' = x := by
    intro x' h1 h2
    apply i.isOpenEmbedding.injective
    rw [hx]
    refine hp' _ (hx ▸ h1.map i.continuous) ?_
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hi, h2]
  have hxW : x ∈ W := mem_of_dense_fibre y W hWo (y.base x) (hWd _) x rfl hxmax
  obtain ⟨g, hg⟩ := hW hxW
  refine ⟨p₂.base g, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, hg, hx]

end Density

end P2mLaw535P

open P2mLaw535P in
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
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hcov : ∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base)
    (hΓa : IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) := by
  haveI := hΦ
  haveI := hΨ

  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian y
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace y
  haveI : IsNoetherian Y := {}
  haveI : IsReduced (U : Scheme.{u}) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (U.ι ≫ pullback.fst y y ≫ y)

  have hgr : Set.range (grm y U m).base ⊆ Set.range γ.base := hΓ ▸ subset_closure
  obtain ⟨g₀, hg₀⟩ := exists_lift_of_isClosedImmersion (grm y U m) γ hgr

  have hUb : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹'
      ((jA y a ha).base ⁻¹' (U : Set ↑(pullback y y)))) := fun s => dense_fibre_jA y a ha _ s (hU₁ _)
  have hΦb : ∀ s, Dense ((Subtype.val : {b : ↑Y // y.base b = s} → ↑Y) ⁻¹'
      ((jA y a ha).base ⁻¹' Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)) := fun s => dense_fibre_jA y a ha _ s (hΦ₁ _)
  have hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base := by
    intro p hp
    rcases hcov p with h | ⟨x, hx⟩
    · exact h
    · exact mem_range_of_maximal y y' τ.1 ι.1 τ.2 _ _ hΓa.w _ ((jA y a ha).continuous.isOpen_preimage _ U.isOpen)
        hUb (preimage_jA_subset_range_pτ y U m γ a ha g₀ hg₀) p hp x hx
  have hτd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base := by
    intro p hp
    rcases hcov p with ⟨x, hx⟩ | h
    · exact mem_range_of_maximal y y' ι.1 τ.1 ι.2 _ _ hΓa.w.symm _
        ((jA y a ha).continuous.isOpen_preimage _
          (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).isOpenEmbedding.isOpen_range)
        hΦb (preimage_jA_range_subset_range_pι y U m γ a ha g₀ hg₀) p hp x hx
    · exact h

  obtain ⟨U', m', hqΦ, hqΨ, hext, hp1, hp2⟩ :=
    NeronModelInfra.exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
      y U m hU₁ hΦ hΨ hassoc γ hΓ a ha y' ι τ hιd hΓa.w

  haveI := hqΦ
  haveI := hqΨ
  obtain ⟨hΦ', hΨ', hassoc'⟩ :=
    NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
      y U m hU₁ hΦ hΦ₁ hΨ hΨ₁ hassoc y' ι hιd U' m' hext

  obtain ⟨d₁, d₂, d₃, d₄, d₅, d₆⟩ :=
    NeronModelInfra.forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
      y U m hU₁ hU₂ hΦ₁ hΦ₂ hΨ hΨ₁ hΨ₂ a ha y' ι τ hcov hιd hτd U' m' hext hp1 hp2
  exact ⟨U', m', d₁, d₂, hΦ', d₃, d₄, hΨ', d₅, d₆, hassoc', hext⟩

end
end S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section (solution)
