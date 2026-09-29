-- Prove2me | solution 1 for NeronModelInfra.exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b89879e1-774e-5d96-9a3b-04edfba3a353

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mBcStrict

theorem dense_fibre_iff {P Y : Scheme.{u}} (f : P ⟶ Y) (x : Y) (S : Set P) :
    Dense ((Subtype.val : {p : P // f p = x} → P) ⁻¹' S) ↔ Dense ((f.fiberι x) ⁻¹' S) := by
  have hpre : (f.fiberι x) ⁻¹' S = (f.fiberHomeo x) ⁻¹' ((Subtype.val : {p : P // f p = x} → P) ⁻¹' S) := by
    ext z
    simp only [Set.mem_preimage]
    rw [Scheme.Hom.fiberHomeo_apply]
  constructor
  · intro hS
    rw [hpre]
    exact hS.preimage (f.fiberHomeo x).isOpenMap
  · intro hS
    rw [hpre] at hS
    have := hS.preimage (f.fiberHomeo x).symm.isOpenMap
    rwa [← Set.preimage_comp, show ((f.fiberHomeo x) ∘ (f.fiberHomeo x).symm) = id from
      funext fun z => (f.fiberHomeo x).apply_symm_apply z, Set.preimage_id] at this

theorem dense_preimage_of_isPullback {P Y W T : Scheme.{u}} (f : P ⟶ Y) (x : Y)
    (k : T ⟶ Spec (Y.residueField x)) (g : T ⟶ Y) (hgk : g = k ≫ Y.fromSpecResidueField x)
    {lam : W ⟶ P} {q : W ⟶ T} (sq : IsPullback q lam g f)
    (S : Set P) (hS : Dense ((Subtype.val : {p : P // f p = x} → P) ⁻¹' S)) :
    Dense (lam ⁻¹' S) := by
  subst hgk
  have hF : IsPullback (f.fiberι x) (f.fiberToSpecResidueField x) f (Y.fromSpecResidueField x) :=
    IsPullback.of_hasPullback f (Y.fromSpecResidueField x)
  let e : W ⟶ f.fiber x := hF.lift lam (q ≫ k) (by rw [Category.assoc, ← sq.w])
  have he₁ : e ≫ f.fiberι x = lam := hF.lift_fst _ _ _
  have he₂ : e ≫ f.fiberToSpecResidueField x = q ≫ k := hF.lift_snd _ _ _
  have sq' : IsPullback e q (f.fiberToSpecResidueField x) k := by
    refine IsPullback.of_right (h₁₂ := f.fiberι x) (v₁₃ := f) (h₂₂ := Y.fromSpecResidueField x) ?_ he₂ hF
    rw [he₁]
    exact sq.flip
  haveI : UniversallyOpen e :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) sq'.flip inferInstance
  have h1 : Dense ((f.fiberι x) ⁻¹' S) := (dense_fibre_iff f x S).mp hS
  have h2 : lam ⁻¹' S = e ⁻¹' ((f.fiberι x) ⁻¹' S) := by
    rw [← he₁, ← Set.preimage_comp]
    rfl
  rw [h2]
  exact h1.preimage e.isOpenMap

theorem dense_fibre_of_isPullback {X X' Z Z' : Scheme.{u}} (f : X ⟶ Z) (f' : X' ⟶ Z') (c : X' ⟶ X) (p : Z' ⟶ Z)
    (h : IsPullback c f' f p) (x' : Z') (S : Set X)
    (hS : Dense ((Subtype.val : {q : X // f q = p x'} → X) ⁻¹' S)) :
    Dense ((Subtype.val : {q : X' // f' q = x'} → X') ⁻¹' (c ⁻¹' S)) := by
  have sq := (IsPullback.of_hasPullback f' (Z'.fromSpecResidueField x')).paste_horiz h
  have hd := dense_preimage_of_isPullback f (p x') (Spec.map (p.residueFieldMap x'))
    (Z'.fromSpecResidueField x' ≫ p) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p x').symm sq.flip S hS
  rw [dense_fibre_iff]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hd
  exact hd

theorem range_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hs : Function.Surjective h.isoPullback.hom := (Scheme.homeoOfIso h.isoPullback).surjective
  rw [Set.range_eq_univ.mpr hs, Set.image_univ]

end P2mBcStrict

theorem solution
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
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
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y) (hp : IsPullback p y' y g)
    (c : pullback y' y' ⟶ pullback y y)
    (hc₁ : c ≫ pullback.fst y y = pullback.fst y' y' ≫ p) (hc₂ : c ≫ pullback.snd y y = pullback.snd y' y' ≫ p) :
    ∃ m' : SchemeHomOver ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') y',
      m'.1 ≫ p = c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) := by

  have hcU : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι = (c ⁻¹ᵁ U).ι ≫ c := Scheme.Hom.resLE_comp_ι _ _
  have hA : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι ≫ pullback.fst y y = (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ p := by
    rw [← Category.assoc, hcU, Category.assoc, hc₁]
  have hB : c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ U.ι ≫ pullback.snd y y = (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' ≫ p := by
    rw [← Category.assoc, hcU, Category.assoc, hc₂]

  have hw : (c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1) ≫ y = ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') ≫ g := by
    rw [Category.assoc, m.2, reassoc_of% hA]
    simp only [Category.assoc, hp.w]
  have hm'p : hp.lift _ _ hw ≫ p = c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1 := hp.lift_fst _ _ _
  have hm'y : hp.lift _ _ hw ≫ y' = (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y' := hp.lift_snd _ _ _
  let m' : SchemeHomOver ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') y' := ⟨hp.lift _ _ hw, hm'y⟩

  have sq₁ : IsPullback c (pullback.fst y' y') (pullback.fst y y) p := by
    have outer := (IsPullback.of_hasPullback y' y').flip.paste_horiz hp
    rw [← hc₂, ← hp.w] at outer
    exact outer.of_right hc₁ (IsPullback.of_hasPullback y y).flip
  have sq₂ : IsPullback c (pullback.snd y' y') (pullback.snd y y) p := by
    have outer := (IsPullback.of_hasPullback y' y').paste_horiz hp
    rw [← hc₁, ← hp.w] at outer
    exact outer.of_right hc₂ (IsPullback.of_hasPullback y y)

  have presq : IsPullback (c ⁻¹ᵁ U).ι (c.resLE U (c ⁻¹ᵁ U) le_rfl) c U.ι := by
    have := (isPullback_morphismRestrict c U).flip
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict] at this
  have sqΦ : IsPullback
      (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm))
      (c.resLE U (c ⁻¹ᵁ U) le_rfl) c
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)) := by
    have outer := presq.paste_horiz sq₁.flip
    refine IsPullback.of_right (h₁₂ := pullback.fst y' y') (v₁₃ := p) (h₂₂ := pullback.fst y y) ?_ ?_ sq₁.flip
    · simpa only [pullback.lift_fst] using outer
    · apply pullback.hom_ext
      · simp only [Category.assoc, hc₁, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hA.symm
      · simp only [Category.assoc, hc₂, pullback.lift_snd, pullback.lift_snd_assoc]
        exact hm'p
  have sqΨ : IsPullback
      (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])))
      (c.resLE U (c ⁻¹ᵁ U) le_rfl) c
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))) := by
    have outer := presq.paste_horiz sq₂.flip
    refine IsPullback.of_right (h₁₂ := pullback.snd y' y') (v₁₃ := p) (h₂₂ := pullback.snd y y) ?_ ?_ sq₂.flip
    · simpa only [pullback.lift_snd] using outer
    · apply pullback.hom_ext
      · simp only [Category.assoc, hc₁, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hm'p
      · simp only [Category.assoc, hc₂, pullback.lift_snd, pullback.lift_snd_assoc]
        exact hB.symm
  refine ⟨m', hm'p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x'
    exact P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hU₁ (p.base x'))
  · intro x'
    exact P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hU₂ (p.base x'))
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqΦ.flip hΦ
  · intro x'
    have h := P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hΦ₁ (p.base x'))
    rwa [← P2mBcStrict.range_eq_of_isPullback sqΦ] at h
  · intro x'
    have h := P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hΦ₂ (p.base x'))
    rwa [← P2mBcStrict.range_eq_of_isPullback sqΦ] at h
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sqΨ.flip hΨ
  · intro x'
    have h := P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₁ x' _ (hΨ₁ (p.base x'))
    rwa [← P2mBcStrict.range_eq_of_isPullback sqΨ] at h
  · intro x'
    have h := P2mBcStrict.dense_fibre_of_isPullback _ _ c p sq₂ x' _ (hΨ₂ (p.base x'))
    rwa [← P2mBcStrict.range_eq_of_isPullback sqΨ] at h
  ·
    intro T t₀ u v pp qq h1 h2 h3 h4 h5
    have hbar : ∀ w : SchemeHomOver t₀ ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y'),
        (w.1 ≫ c.resLE U (c ⁻¹ᵁ U) le_rfl) ≫ U.ι ≫ pullback.fst y y ≫ y = t₀ ≫ g := fun w => by
      simp only [Category.assoc]
      rw [reassoc_of% hA, hp.w]
      have h2 := w.2
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
      rw [← Category.assoc, ← Category.assoc] at h2
      rw [h2]
    let bar : SchemeHomOver t₀ ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') → SchemeHomOver (t₀ ≫ g) (U.ι ≫ pullback.fst y y ≫ y) :=
      fun w => ⟨w.1 ≫ c.resLE U (c ⁻¹ᵁ U) le_rfl, hbar w⟩
    have post : ∀ {a b : T ⟶ Y'}, a = b → a ≫ p = b ≫ p := fun h => by rw [h]
    have H1 : (bar u).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ U.ι ≫ pullback.fst y y := by
      have e := post h1
      simp only [Category.assoc] at e
      show (u.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB, hA]; exact e
    have H2 : (bar pp).1 ≫ U.ι ≫ pullback.fst y y = (bar u).1 ≫ m.1 := by
      have e := post h2
      simp only [Category.assoc] at e
      show (pp.1 ≫ _) ≫ _ = (u.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hA, ← hm'p]; exact e
    have H3 : (bar pp).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ U.ι ≫ pullback.snd y y := by
      have e := post h3
      simp only [Category.assoc] at e
      show (pp.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB]; exact e
    have H4 : (bar qq).1 ≫ U.ι ≫ pullback.fst y y = (bar u).1 ≫ U.ι ≫ pullback.fst y y := by
      have e := post h4
      simp only [Category.assoc] at e
      show (qq.1 ≫ _) ≫ _ = (u.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hA]; exact e
    have H5 : (bar qq).1 ≫ U.ι ≫ pullback.snd y y = (bar v).1 ≫ m.1 := by
      have e := post h5
      simp only [Category.assoc] at e
      show (qq.1 ≫ _) ≫ _ = (v.1 ≫ _) ≫ _
      simp only [Category.assoc]; rw [hB, ← hm'p]; exact e
    have key := hassoc (t₀ ≫ g) (bar u) (bar v) (bar pp) (bar qq) H1 H2 H3 H4 H5
    apply hp.hom_ext
    · show pp.1 ≫ hp.lift _ _ hw ≫ p = qq.1 ≫ hp.lift _ _ hw ≫ p
      rw [hm'p]
      exact key
    · show pp.1 ≫ hp.lift _ _ hw ≫ y' = qq.1 ≫ hp.lift _ _ hw ≫ y'
      rw [hm'y, pp.2, qq.2]

end S_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
end P2MW
export P2MW.S_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre (solution)
