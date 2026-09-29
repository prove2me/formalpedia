-- Prove2me | solution 1 for NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6c4d0ba8-7fc3-59ed-afb3-ea1497605ef7

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
import Theorems.Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
import Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

universe u v

namespace P2mDefFin

section General

scoped instance subsingleton_spec_residueField (Y : Scheme.{u}) (x : Y) :
    Subsingleton ↥(Spec (Y.residueField x)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (Y.residueField x)))

theorem dense_of_forall_dense_fibre {X Z : Type*} [TopologicalSpace X] (p : X → Z) (S : Set X)
    (h : ∀ z : Z, Dense ((Subtype.val : {x : X // p x = z} → X) ⁻¹' S)) : Dense S := by
  intro x
  have hx : (⟨x, rfl⟩ : {x' : X // p x' = p x}) ∈
      closure ((Subtype.val : {x' : X // p x' = p x} → X) ⁻¹' S) := h (p x) ⟨x, rfl⟩
  rw [closure_subtype] at hx
  exact closure_mono (Set.image_preimage_subset _ _) hx

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

theorem dense_fibre_of_isPullback {P Y P₂ Y₂ : Scheme.{u}} (f : P ⟶ Y) (f₂ : P₂ ⟶ Y₂) (π : P₂ ⟶ P)
    (p : Y₂ ⟶ Y) (sq : IsPullback π f₂ f p) (S : Set P) (x₂ : Y₂)
    (hS : Dense ((Subtype.val : {q : P // f q = p x₂} → P) ⁻¹' S)) :
    Dense ((Subtype.val : {q : P₂ // f₂ q = x₂} → P₂) ⁻¹' (π ⁻¹' S)) := by
  rw [dense_fibre_iff f₂ x₂]
  have hfib : IsPullback (f₂.fiberι x₂) (f₂.fiberToSpecResidueField x₂) f₂ (Y₂.fromSpecResidueField x₂) :=
    IsPullback.of_hasPullback _ _
  have hbig := hfib.paste_horiz sq
  have h := dense_preimage_of_isPullback f (p x₂) (Spec.map (p.residueFieldMap x₂))
    (Y₂.fromSpecResidueField x₂ ≫ p) (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p x₂).symm
    hbig.flip S hS
  rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at h

theorem subset_closure_inter {X : Type*} [TopologicalSpace X] {O A A' : Set X} (hO : IsOpen O)
    (hA : IsOpen A) (h : O ⊆ closure A) (h' : O ⊆ closure A') : O ⊆ closure (A ∩ A') := by
  intro o ho
  rw [mem_closure_iff]
  intro N hN hoN
  obtain ⟨a₁, ⟨ha₁N, ha₁O⟩, ha₁A⟩ : (N ∩ O ∩ A).Nonempty :=
    mem_closure_iff.mp (h ho) (N ∩ O) (hN.inter hO) ⟨hoN, ho⟩
  obtain ⟨a₂, ⟨⟨ha₂N, -⟩, ha₂A⟩, ha₂A'⟩ : (N ∩ O ∩ A ∩ A').Nonempty :=
    mem_closure_iff.mp (h' ha₁O) (N ∩ O ∩ A) ((hN.inter hO).inter hA) ⟨⟨ha₁N, ha₁O⟩, ha₁A⟩
  exact ⟨a₂, ha₂N, ha₂A, ha₂A'⟩

theorem eq_of_comp_ι_eq {X Z S : Scheme.{u}} [IsReduced X] (s : Z ⟶ S) [IsSeparated s]
    {f g : X ⟶ Z} (hs : f ≫ s = g ≫ s) (W : X.Opens) (hW : Dense (W : Set X)) (h : W.ι ≫ f = W.ι ≫ g) :
    f = g := by
  haveI : IsDominant W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hW⟩
  exact ext_of_isDominant_of_isSeparated s hs W.ι h

theorem exists_glue_of_isOpenImmersion {X Z S : Scheme.{u}} [IsReduced X] (p : X ⟶ S) (s : Z ⟶ S)
    [IsSeparated s] {I : Type v} (F : I → Scheme.{u}) (j : ∀ i, F i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (g : ∀ i, F i ⟶ Z) (hg : ∀ i, g i ≫ s = j i ≫ p)
    (hagree : ∀ i i', ∃ W : Set X, IsOpen W ∧ Set.range (j i) ∩ Set.range (j i') ⊆ closure W ∧
      ∀ {T : Scheme.{u}} (t₁ : T ⟶ F i) (t₂ : T ⟶ F i'), t₁ ≫ j i = t₂ ≫ j i' →
        Set.range (t₁ ≫ j i) ⊆ W → t₁ ≫ g i = t₂ ≫ g i') :
    ∃ G : X ⟶ Z, (∀ i, j i ≫ G = g i) ∧ G ≫ s = p := by
  let 𝒰 : Scheme.OpenCover.{v} X := Scheme.Cover.mkOfCovers I F j
    (fun x => by obtain ⟨i, z, hz⟩ := hcov x; exact ⟨i, z, hz⟩) inferInstance
  have hcompat : ∀ i i', pullback.fst (𝒰.f i) (𝒰.f i') ≫ g i = pullback.snd _ _ ≫ g i' := by
    intro i i'
    change pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i'
    obtain ⟨W, hWo, hcl, hW⟩ := hagree i i'
    haveI : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    let e : pullback (j i) (j i') ⟶ X := pullback.fst (j i) (j i') ≫ j i
    let W' : (pullback (j i) (j i')).Opens := ⟨e ⁻¹' W, hWo.preimage e.continuous⟩
    have hmem : ∀ n, e n ∈ Set.range (j i) ∩ Set.range (j i') := fun n =>
      ⟨⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩,
        ⟨pullback.snd (j i) (j i') n, by rw [← Scheme.Hom.comp_apply, ← pullback.condition]⟩⟩
    have hW'd : Dense (W' : Set ↥(pullback (j i) (j i'))) := by
      rw [dense_iff_inter_open]
      rintro N hN ⟨n₀, hn₀⟩
      have he : IsOpenEmbedding e := e.isOpenEmbedding
      obtain ⟨_, ⟨⟨n, hn, rfl⟩, hnW⟩⟩ : (e '' N ∩ W).Nonempty :=
        mem_closure_iff.mp (hcl (hmem n₀)) (e '' N) (he.isOpenMap _ hN) ⟨n₀, hn₀, rfl⟩
      exact ⟨n, hn, hnW⟩
    refine eq_of_comp_ι_eq s ?_ W' hW'd ?_
    · rw [Category.assoc, Category.assoc, hg, hg, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc]
      refine hW (W'.ι ≫ pullback.fst _ _) (W'.ι ≫ pullback.snd _ _)
        (by rw [Category.assoc, Category.assoc, pullback.condition]) ?_
      rintro _ ⟨w, rfl⟩
      change (W'.ι ≫ e) w ∈ W
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact w.2
  refine ⟨𝒰.glueMorphisms g hcompat, fun i => 𝒰.ι_glueMorphisms g hcompat i, ?_⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
  rw [Scheme.Cover.ι_glueMorphisms_assoc]
  exact hg i

end General

section Setup

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

abbrev Psi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
    (m.2.trans (by rw [Category.assoc, pullback.condition]))

def lamSnd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    pullback y c ⟶ pullback y y :=
  pullback.lift (pullback.fst y c) (pullback.snd y c ≫ g) (by rw [Category.assoc, hg, pullback.condition])

@[reassoc]
theorem lamSnd_fst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamSnd y c g hg ≫ pullback.fst y y = pullback.fst y c := pullback.lift_fst _ _ _

@[reassoc]
theorem lamSnd_snd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamSnd y c g hg ≫ pullback.snd y y = pullback.snd y c ≫ g := pullback.lift_snd _ _ _

theorem isPullback_lamSnd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y)
    (hg : g ≫ y = c) : IsPullback (pullback.snd y c) (lamSnd y c g hg) g (pullback.snd y y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.fst y y) (v₂₂ := y) (h₃₁ := y) ?_ (lamSnd_snd y c g hg).symm
    (IsPullback.of_hasPullback y y).flip
  rw [lamSnd_fst, hg]
  exact (IsPullback.of_hasPullback y c).flip

def lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    pullback y c ⟶ pullback y y :=
  pullback.lift (pullback.snd y c ≫ g) (pullback.fst y c) (by rw [Category.assoc, hg, pullback.condition])

@[reassoc]
theorem lamFst_fst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamFst y c g hg ≫ pullback.fst y y = pullback.snd y c ≫ g := pullback.lift_fst _ _ _

@[reassoc]
theorem lamFst_snd {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y) (hg : g ≫ y = c) :
    lamFst y c g hg ≫ pullback.snd y y = pullback.fst y c := pullback.lift_snd _ _ _

theorem isPullback_lamFst {T : Scheme.{u}} (c : T ⟶ Spec (CommRingCat.of R)) (g : T ⟶ Y)
    (hg : g ≫ y = c) : IsPullback (pullback.snd y c) (lamFst y c g hg) g (pullback.fst y y) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd y y) (v₂₂ := y) (h₃₁ := y) ?_ (lamFst_fst y c g hg).symm
    (IsPullback.of_hasPullback y y)
  rw [lamFst_snd, hg]
  exact (IsPullback.of_hasPullback y c).flip

end Setup

section Level

abbrev bS (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']

abbrev Y1 : Scheme.{u} := pullback y (bS R R')

abbrev y1 : Y1 y R' ⟶ Spec (CommRingCat.of R') := pullback.snd y (bS R R')

abbrev p1 : Y1 y R' ⟶ Y := pullback.fst y (bS R R')

abbrev P1 : Scheme.{u} := pullback (y1 y R') (y1 y R')

def pi1 : P1 y R' ⟶ pullback y y :=
  pullback.map _ _ _ _ (p1 y R') (p1 y R') (bS R R') pullback.condition.symm pullback.condition.symm

@[reassoc (attr := simp)]
theorem pi1_fst : pi1 y R' ≫ pullback.fst y y = pullback.fst _ _ ≫ p1 y R' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pi1_snd : pi1 y R' ≫ pullback.snd y y = pullback.snd _ _ ≫ p1 y R' := pullback.lift_snd _ _ _

theorem isPullback_pi1_fst :
    IsPullback (pi1 y R') (pullback.fst (y1 y R') (y1 y R')) (pullback.fst y y) (p1 y R') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi1_fst y R')
    (IsPullback.of_hasPullback y y).flip
  rw [pi1_snd]
  have h := (IsPullback.of_hasPullback (y1 y R') (y1 y R')).flip.paste_horiz
    (IsPullback.of_hasPullback y (bS R R'))
  rwa [← pullback.condition] at h

end Level

structure Cx where

  R : Type u
  [instR : CommRing R]
  [dom : IsDomain R]
  [dvr : IsDiscreteValuationRing R]
  [hens : HenselianLocalRing R]

  Y : Scheme.{u}

  y : Y ⟶ Spec (CommRingCat.of R)
  [smooth : Smooth y]

  U : (pullback y y).Opens

  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  hU₂ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  hΦ : IsOpenImmersion (Phi y U m)
  hΦ₂ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (Set.range (Phi y U m).base))
  hΨ : IsOpenImmersion (Psi y U m)
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1
  hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U

  R' : Type u
  [instR' : CommRing R']
  [dom' : IsDomain R']
  [dvr' : IsDiscreteValuationRing R']
  [alg : Algebra R R']
  [fin : Module.Finite R R']
  [et : Algebra.Etale R R']
  [ff : Module.FaithfullyFlat R R']

  Y' : Scheme.{u}

  y' : Y' ⟶ Spec (CommRingCat.of R')
  [smooth' : Smooth y']
  [sep' : IsSeparated y']

  ι : SchemeHomOver (y1 y R') y'
  [oi : IsOpenImmersion ι.1]

  U' : (pullback y' y').Opens

  m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'
  hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
      (w : SchemeHomOver (t' ≫ bS R R') (U.ι ≫ pullback.fst y y ≫ y))
      (a b c : SchemeHomOver (t' ≫ bS R R') y),
    a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
    ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
      w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (bS R R') a).1 ≫ ι.1 ∧
      w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (bS R R') b).1 ≫ ι.1 ∧
      w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (bS R R') c).1 ≫ ι.1
  hstat : ∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
      (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ : Module.FaithfullyFlat R' R'')
      (a : Spec (CommRingCat.of R'') ⟶ Y),
    a ≫ y = bS R' R'' ≫ bS R R' →
    ∃ τ : pullback y (bS R' R'' ≫ bS R R') ⟶ pullback y' (bS R' R''),
      τ ≫ pullback.snd y' (bS R' R'') = pullback.snd y (bS R' R'' ≫ bS R R') ∧
      ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (bS R' R'' ≫ bS R R')) (w : T ⟶ (U : Scheme.{u}))
        (v : T ⟶ pullback y (bS R R')),
        w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y (bS R' R'' ≫ bS R R') ≫ a →
        w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y (bS R' R'' ≫ bS R R') →
        v ≫ pullback.fst y (bS R R') = w ≫ m.1 →
        v ≫ pullback.snd y (bS R R') = x ≫ pullback.snd y (bS R' R'' ≫ bS R R') ≫ bS R' R'' →
        x ≫ τ ≫ pullback.fst y' (bS R' R'') = v ≫ ι.1

attribute [scoped instance] Cx.instR Cx.dom Cx.dvr Cx.hens Cx.smooth Cx.hΦ Cx.hΨ Cx.instR' Cx.dom' Cx.dvr' Cx.alg
  Cx.fin Cx.et Cx.ff Cx.smooth' Cx.sep' Cx.oi

namespace Cx

variable (C : Cx.{u})

abbrev P : Scheme.{u} := P1 C.y C.R'

abbrev U₁ : C.P.Opens := pi1 C.y C.R' ⁻¹ᵁ C.U

abbrev πU : (C.U₁ : Scheme.{u}) ⟶ C.U := pi1 C.y C.R' ∣_ C.U

@[reassoc]
theorem πU_ι : C.πU ≫ C.U.ι = C.U₁.ι ≫ pi1 C.y C.R' := morphismRestrict_ι _ _

@[reassoc]
theorem πU_fst : C.πU ≫ C.U.ι ≫ pullback.fst C.y C.y = C.U₁.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R' := by
  rw [πU_ι_assoc, pi1_fst]

@[reassoc]
theorem πU_snd : C.πU ≫ C.U.ι ≫ pullback.snd C.y C.y = C.U₁.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R' := by
  rw [πU_ι_assoc, pi1_snd]

def m₁ : (C.U₁ : Scheme.{u}) ⟶ Y1 C.y C.R' :=
  pullback.lift (C.πU ≫ C.m.1) (C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') (by
    rw [Category.assoc, C.m.2, πU_fst_assoc, Category.assoc, Category.assoc, ← pullback.condition])

@[reassoc (attr := simp)]
theorem m₁_p1 : C.m₁ ≫ p1 C.y C.R' = C.πU ≫ C.m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem m₁_y1 : C.m₁ ≫ y1 C.y C.R' = C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' := pullback.lift_snd _ _ _

def G₀ : (C.U₁ : Scheme.{u}) ⟶ C.Y' := C.m₁ ≫ C.ι.1

theorem G₀_y' : C.G₀ ≫ C.y' = C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  rw [G₀, Category.assoc, C.ι.2, m₁_y1]

theorem henselian_R' : HenselianLocalRing C.R' :=
  HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := C.R)

scoped instance isReduced_P : IsReduced C.P :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R')

theorem dense_U₁ : Dense (C.U₁ : Set C.P) :=
  dense_of_forall_dense_fibre (fun q => (pullback.fst (y1 C.y C.R') (y1 C.y C.R')).base q) _ fun x₁ =>
    dense_fibre_of_isPullback (pullback.fst C.y C.y) (pullback.fst _ _) (pi1 C.y C.R') (p1 C.y C.R')
      (isPullback_pi1_fst C.y C.R') _ x₁ (C.hU₁ _)

theorem mem_U₁_of_ne (q : C.P) (hq : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') q ≠
    IsLocalRing.closedPoint C.R') : q ∈ C.U₁ := by
  change pi1 C.y C.R' q ∈ C.U
  refine C.hUK _ fun h => hq ?_
  rw [← Scheme.Hom.comp_apply, pi1_fst_assoc, pullback.condition] at h

  set s : Spec (CommRingCat.of C.R') := (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') q with hs
  have h' : (bS C.R C.R') s = IsLocalRing.closedPoint C.R := by
    rw [hs, ← Scheme.Hom.comp_apply]; simpa only [Category.assoc] using h

  have hinj : Function.Injective (algebraMap C.R C.R') := FaithfulSMul.algebraMap_injective C.R C.R'
  have hcomap : s.asIdeal.comap (algebraMap C.R C.R') = IsLocalRing.maximalIdeal C.R := by
    have := congrArg PrimeSpectrum.asIdeal h'
    simp at this
    exact this
  have hne : s.asIdeal ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.comap_bot_of_injective _ hinj] at hcomap
    exact (IsDiscreteValuationRing.not_isField C.R)
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hcomap.symm)
  have hmax : s.asIdeal.IsMaximal := s.isPrime.isMaximal hne
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

theorem exists_datum (t : C.P)
    (ht : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') t = IsLocalRing.closedPoint C.R') :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'') (_ : Algebra C.R' R'')
      (_ : Module.Finite C.R' R'') (_ : Algebra.Etale C.R' R'') (_ : Module.FaithfullyFlat C.R' R'')
      (a : Spec (CommRingCat.of R'') ⟶ C.Y) (T : Scheme.{u}) (t'' : T ⟶ Spec (CommRingCat.of R''))
      (w₁ w₂ : T ⟶ (C.U : Scheme.{u})) (s : T ⟶ C.P),
      a ≫ C.y = bS C.R' R'' ≫ bS C.R C.R' ∧
      w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = t'' ≫ a ∧
      w₂ ≫ C.U.ι ≫ pullback.fst C.y C.y = w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y ∧
      s ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w₁ ≫ C.m.1 ∧
      s ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y ∧
      s ≫ pullback.fst _ _ ≫ y1 C.y C.R' = t'' ≫ bS C.R' R'' ∧
      t ∈ Set.range s.base := by

  let fst' := pullback.fst (y1 C.y C.R') (y1 C.y C.R'); let snd' := pullback.snd (y1 C.y C.R') (y1 C.y C.R')

  let K : Type u := C.P.residueField t
  let pt : Spec (CommRingCat.of K) ⟶ C.P := C.P.fromSpecResidueField t
  let x₁ : Spec (CommRingCat.of K) ⟶ Y1 C.y C.R' := pt ≫ fst'
  let v₁ : Spec (CommRingCat.of K) ⟶ Y1 C.y C.R' := pt ≫ snd'
  let xK : Spec (CommRingCat.of K) ⟶ C.Y := x₁ ≫ p1 C.y C.R'
  let vK : Spec (CommRingCat.of K) ⟶ C.Y := v₁ ≫ p1 C.y C.R'
  let c₁ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C.R') := x₁ ≫ y1 C.y C.R'
  let cK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of C.R) := c₁ ≫ bS C.R C.R'
  have hxK : xK ≫ C.y = cK := by simp only [xK, cK, c₁, Category.assoc, pullback.condition]
  have hv₁c : v₁ ≫ y1 C.y C.R' = c₁ := by simp only [v₁, c₁, x₁, Category.assoc]; rw [pullback.condition]
  have hvK : vK ≫ C.y = cK := by
    simp only [vK, cK, Category.assoc, pullback.condition]; rw [reassoc_of% hv₁c]
  have hxK' : xK = Spec.map ((fst' ≫ p1 C.y C.R').residueFieldMap t) ≫ C.Y.fromSpecResidueField ((fst' ≫ p1 C.y C.R') t) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [xK, x₁, pt, Category.assoc]
  have hvK' : vK = Spec.map ((snd' ≫ p1 C.y C.R').residueFieldMap t) ≫ C.Y.fromSpecResidueField ((snd' ≫ p1 C.y C.R') t) := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [vK, v₁, pt, Category.assoc]

  let lam := lamSnd C.y cK xK hxK
  let lam' := lamFst C.y cK xK hxK
  let lamv := lamSnd C.y cK vK hvK

  let e₁ := pullback.fst lam (Phi C.y C.U C.m)
  let β := pullback.snd lam (Phi C.y C.U C.m)
  have hd₁ : Dense (Set.range e₁) := by
    rw [Scheme.Pullback.range_fst]
    exact dense_preimage_of_isPullback (pullback.snd C.y C.y) _ (Spec.map ((fst' ≫ p1 C.y C.R').residueFieldMap t))
      xK hxK' (isPullback_lamSnd C.y cK xK hxK) _ (C.hΦ₂ _)

  have hPhi₁ : Phi C.y C.U C.m ≫ pullback.fst C.y C.y = C.U.ι ≫ pullback.fst C.y C.y := pullback.lift_fst _ _ _
  have hPhi₂ : Phi C.y C.U C.m ≫ pullback.snd C.y C.y = C.m.1 := pullback.lift_snd _ _ _
  have hν₀ : (β ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = (e₁ ≫ pullback.snd C.y cK) ≫ cK := by
    calc (β ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = β ≫ (Phi C.y C.U C.m ≫ pullback.fst C.y C.y) ≫ C.y := by
          rw [hPhi₁]; simp only [Category.assoc, pullback.condition]
      _ = (e₁ ≫ lam) ≫ pullback.fst C.y C.y ≫ C.y := by
          simp only [Category.assoc]; rw [pullback.condition_assoc]
      _ = (e₁ ≫ pullback.snd C.y cK) ≫ cK := by
          simp only [Category.assoc, lam, lamSnd_fst_assoc]
          rw [pullback.condition]
  let ν : pullback lam (Phi C.y C.U C.m) ⟶ pullback C.y cK :=
    pullback.lift (β ≫ C.U.ι ≫ pullback.snd C.y C.y) (e₁ ≫ pullback.snd C.y cK) hν₀
  have hν₁ : ν ≫ pullback.fst C.y cK = β ≫ C.U.ι ≫ pullback.snd C.y C.y := pullback.lift_fst _ _ _
  have hν₂ : ν ≫ pullback.snd C.y cK = e₁ ≫ pullback.snd C.y cK := pullback.lift_snd _ _ _
  have hνsq : IsPullback ν β lam' (Psi C.y C.U C.m) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd C.y cK) (v₁₃ := xK) (h₂₂ := pullback.fst C.y C.y) ?_ ?_
      (isPullback_lamFst C.y cK xK hxK)
    · rw [hν₂, pullback.lift_fst]
      have h := (IsPullback.of_hasPullback lam (Phi C.y C.U C.m)).paste_horiz (isPullback_lamSnd C.y cK xK hxK)
      rwa [hPhi₂] at h
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst]
        change ν ≫ lamFst C.y cK xK hxK ≫ pullback.fst C.y C.y = β ≫ C.m.1
        rw [lamFst_fst, reassoc_of% hν₂, ← hPhi₂, ← pullback.condition_assoc]
        change e₁ ≫ pullback.snd C.y cK ≫ xK = e₁ ≫ lamSnd C.y cK xK hxK ≫ pullback.snd C.y C.y
        rw [lamSnd_snd]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd]
        change ν ≫ lamFst C.y cK xK hxK ≫ pullback.snd C.y C.y = β ≫ C.U.ι ≫ pullback.snd C.y C.y
        rw [lamFst_snd, hν₁]
  haveI : IsOpenImmersion ν := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hνsq.flip C.hΨ
  have hd₂ : Dense ((ν ≫ lamv) ⁻¹' (C.U : Set ↑(pullback C.y C.y))) := by
    have h := dense_preimage_of_isPullback (pullback.snd C.y C.y) _
      (Spec.map ((snd' ≫ p1 C.y C.R').residueFieldMap t)) vK hvK' (isPullback_lamSnd C.y cK vK hvK) _ (C.hU₂ _)
    exact h.preimage ν.isOpenMap
  let Zt : (pullback C.y cK).Opens := e₁ ''ᵁ ((ν ≫ lamv) ⁻¹ᵁ C.U)
  have hZt : Dense (Zt : Set ↑(pullback C.y cK)) := DenseRange.dense_image hd₁ e₁.continuous hd₂

  let κ₁ : pullback C.y cK ⟶ Y1 C.y C.R' :=
    pullback.lift (pullback.fst C.y cK) (pullback.snd C.y cK ≫ c₁) (by rw [pullback.condition, Category.assoc])
  have hκ₁p : κ₁ ≫ p1 C.y C.R' = pullback.fst C.y cK := pullback.lift_fst _ _ _
  have hκ₁y : κ₁ ≫ y1 C.y C.R' = pullback.snd C.y cK ≫ c₁ := pullback.lift_snd _ _ _
  have hκ₁ : IsPullback κ₁ (pullback.snd C.y cK) (y1 C.y C.R') c₁ := by
    refine IsPullback.of_right (h₁₂ := p1 C.y C.R') (v₁₃ := C.y) (h₂₂ := bS C.R C.R') ?_ hκ₁y
      (IsPullback.of_hasPullback C.y (bS C.R C.R'))
    rw [hκ₁p]
    exact IsPullback.of_hasPullback C.y cK
  let s₀ : Spec (CommRingCat.of C.R') := (fst' ≫ y1 C.y C.R') t
  let k : Spec (CommRingCat.of K) ⟶ Spec ((Spec (CommRingCat.of C.R')).residueField s₀) :=
    Spec.map ((fst' ≫ y1 C.y C.R').residueFieldMap t)
  have hc₁ : c₁ = k ≫ (Spec (CommRingCat.of C.R')).fromSpecResidueField s₀ := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; simp only [c₁, x₁, pt, Category.assoc]
  let fib := (y1 C.y C.R').fiber s₀
  let e : pullback C.y cK ⟶ fib :=
    pullback.lift κ₁ (pullback.snd C.y cK ≫ k) (by rw [hκ₁y, Category.assoc, ← hc₁])
  have heι : e ≫ (y1 C.y C.R').fiberι s₀ = κ₁ := pullback.lift_fst _ _ _
  have he : IsPullback e (pullback.snd C.y cK) ((y1 C.y C.R').fiberToSpecResidueField s₀) k := by
    refine IsPullback.of_right (h₁₂ := (y1 C.y C.R').fiberι s₀) (v₁₃ := y1 C.y C.R')
      (h₂₂ := (Spec (CommRingCat.of C.R')).fromSpecResidueField s₀) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [heι, ← hc₁]
    exact hκ₁
  haveI : UniversallyOpen e := MorphismProperty.of_isPullback (P := @UniversallyOpen) he.flip inferInstance
  have hV₀ : IsOpen (e.base '' (Zt : Set ↑(pullback C.y cK))) := e.isOpenMap _ Zt.2
  obtain ⟨O, hOo, hOpre⟩ :=
    ((y1 C.y C.R').fiberι s₀).isEmbedding.isInducing.isOpen_iff.mp hV₀
  let OO : (Y1 C.y C.R').Opens := ⟨O, hOo⟩

  haveI : Nonempty ↑(pullback C.y cK) := ⟨(pullback.lift xK (𝟙 _) (by rw [hxK, Category.id_comp]) :
    Spec (CommRingCat.of K) ⟶ pullback C.y cK) (IsLocalRing.closedPoint K)⟩
  obtain ⟨z₀, hz₀⟩ := hZt.nonempty
  let x : Y1 C.y C.R' := (y1 C.y C.R').fiberι s₀ (e z₀)
  have hx : (y1 C.y C.R') x = IsLocalRing.closedPoint C.R' := by
    have : x ∈ (y1 C.y C.R') ⁻¹' {s₀} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨_, rfl⟩
    rw [this]; exact ht
  have hxV : x ∈ OO := by
    change (y1 C.y C.R').fiberι s₀ (e z₀) ∈ O
    rw [← Set.mem_preimage, hOpre]
    exact ⟨z₀, hz₀, rfl⟩

  haveI : HenselianLocalRing C.R' := C.henselian_R'
  obtain ⟨R'', _, _, _, _, _, _, _, hloc, _, a₁, -, ha₁, hmem⟩ :=
    AlgebraicGeometry.Smooth.exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
      (y1 C.y C.R') OO x hx hxV

  let a₀ : Y1 C.y C.R' := a₁ (IsLocalRing.closedPoint R'')
  have ha₀ : (y1 C.y C.R') a₀ = s₀ := by
    rw [← Scheme.Hom.comp_apply, ha₁]
    have : IsLocalHom (CommRingCat.ofHom (algebraMap C.R' R'')).hom := by rwa [CommRingCat.hom_ofHom]
    rw [Spec_closedPoint]
    exact ht.symm
  obtain ⟨f₀, hf₀⟩ : a₀ ∈ Set.range ((y1 C.y C.R').fiberι s₀) := by
    rw [Scheme.Hom.range_fiberι]; exact ha₀
  have hf₀O : f₀ ∈ (y1 C.y C.R').fiberι s₀ ⁻¹' O := by
    rw [Set.mem_preimage, hf₀]; exact hmem
  rw [hOpre] at hf₀O
  obtain ⟨z, hz, hez⟩ := hf₀O
  have hκz : κ₁ z = a₁ (IsLocalRing.closedPoint R'') := by
    rw [← heι, Scheme.Hom.comp_apply, hez, hf₀]
  obtain ⟨μ, hμ₁, hμ₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := κ₁) (g := a₁) z (IsLocalRing.closedPoint R'') hκz
  let M := pullback κ₁ a₁
  let L : Type u := M.residueField μ
  let l₀ : Spec (CommRingCat.of L) ⟶ M := M.fromSpecResidueField μ
  let zL : Spec (CommRingCat.of L) ⟶ pullback C.y cK := l₀ ≫ pullback.fst κ₁ a₁
  let lR : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R'') := l₀ ≫ pullback.snd κ₁ a₁
  let lL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) := zL ≫ pullback.snd C.y cK
  have hzL : Set.range zL.base ⊆ (Zt : Set ↑(pullback C.y cK)) := by
    rintro _ ⟨p, rfl⟩
    change (l₀ ≫ pullback.fst κ₁ a₁) p ∈ Zt
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hμ₁]
    exact hz

  have hr : Set.range zL.base ⊆ Set.range e₁.base := hzL.trans (Set.image_subset_range _ _)
  let a₁' := IsOpenImmersion.lift e₁ zL hr
  have ha₁' : a₁' ≫ e₁ = zL := IsOpenImmersion.lift_fac _ _ _
  have hμC.U : ∀ p, (a₁' ≫ ν ≫ lamv) p ∈ C.U := by
    intro p
    obtain ⟨z', hz', hze⟩ := hzL ⟨p, rfl⟩
    rw [← ha₁', Scheme.Hom.comp_apply] at hze
    rw [Scheme.Hom.comp_apply, ← e₁.isOpenEmbedding.injective hze]
    exact hz'
  let μK := a₁' ≫ ν ≫ lamv
  let w₂ : Spec (CommRingCat.of L) ⟶ C.U := IsOpenImmersion.lift C.U.ι μK (by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨p, rfl⟩; exact hμC.U p)
  have hw₂ : w₂ ≫ C.U.ι = μK := IsOpenImmersion.lift_fac _ _ _
  let w₁ : Spec (CommRingCat.of L) ⟶ C.U := a₁' ≫ β
  let a : Spec (CommRingCat.of R'') ⟶ C.Y := a₁ ≫ p1 C.y C.R'
  let s : Spec (CommRingCat.of L) ⟶ C.P := lL ≫ pt
  have hβΦ : β ≫ Phi C.y C.U C.m = e₁ ≫ lam := pullback.condition.symm
  have hMcond : pullback.fst κ₁ a₁ ≫ κ₁ = pullback.snd κ₁ a₁ ≫ a₁ := pullback.condition
  refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    a, Spec (CommRingCat.of L), lR, w₁, w₂, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    simp only [a, Category.assoc]; rw [pullback.condition, reassoc_of% ha₁]
  ·
    calc w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = a₁' ≫ β ≫ Phi C.y C.U C.m ≫ pullback.fst C.y C.y := by
          simp only [w₁, Category.assoc, hPhi₁]
      _ = zL ≫ pullback.fst C.y cK := by rw [reassoc_of% hβΦ, reassoc_of% ha₁']; simp only [lam, lamSnd_fst]
      _ = lR ≫ a := by
          simp only [zL, lR, a, Category.assoc, ← hκ₁p]
          rw [reassoc_of% hMcond]
  ·
    rw [reassoc_of% hw₂]
    simp only [μK, w₁, Category.assoc, lamv, lamSnd_fst, hν₁]
  ·
    calc s ≫ fst' ≫ p1 C.y C.R' = lL ≫ xK := by simp only [s, lL, xK, x₁, Category.assoc]
      _ = zL ≫ lam ≫ pullback.snd C.y C.y := by simp only [lL, lam, lamSnd_snd, Category.assoc]
      _ = w₁ ≫ C.m.1 := by rw [← reassoc_of% ha₁', ← reassoc_of% hβΦ, hPhi₂]; simp only [w₁, Category.assoc]
  ·
    calc s ≫ snd' ≫ p1 C.y C.R' = lL ≫ vK := by simp only [s, lL, vK, v₁, Category.assoc]
      _ = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y := by
          rw [reassoc_of% hw₂]
          simp only [μK, lL, Category.assoc, lamv, lamSnd_snd, reassoc_of% hν₂, reassoc_of% ha₁']
  ·
    calc s ≫ fst' ≫ y1 C.y C.R' = zL ≫ pullback.snd C.y cK ≫ c₁ := by simp only [s, lL, c₁, x₁, Category.assoc]
      _ = zL ≫ κ₁ ≫ y1 C.y C.R' := by rw [hκ₁y]
      _ = lR ≫ bS C.R' R'' := by
          simp only [zL, lR, Category.assoc]
          rw [reassoc_of% hMcond, ha₁]
  ·
    refine ⟨IsLocalRing.closedPoint L, ?_⟩
    change (lL ≫ pt) _ = t
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

def Agree (V : C.P.Opens) (G : (V : Scheme.{u}) ⟶ C.Y') : Prop :=
  ∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R'),
    s ≫ V.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y →
    s ≫ V.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y →
    v ≫ p1 C.y C.R' = w ≫ C.m.1 →
    v ≫ y1 C.y C.R' = s ≫ V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' →
    s ≫ G = v ≫ C.ι.1

theorem G₀_agree : C.Agree C.U₁ C.G₀ := by
  intro T s w v h₁ h₂ h₃ h₄
  rw [G₀, ← Category.assoc]
  congr 1
  have hsw : s ≫ C.πU = w := by
    rw [← cancel_mono C.U.ι]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, πU_fst]; exact h₁
    · rw [Category.assoc, Category.assoc, πU_snd]; exact h₂
  apply pullback.hom_ext
  · rw [Category.assoc, m₁_p1, reassoc_of% hsw, h₃]
  · rw [Category.assoc, m₁_y1, h₄]

theorem hpiece (t : C.P) : ∃ (V : C.P.Opens) (G : (V : Scheme.{u}) ⟶ C.Y'),
    G ≫ C.y' = V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' ∧ C.Agree V G ∧ t ∈ V := by
  by_cases ht : (pullback.fst (y1 C.y C.R') (y1 C.y C.R') ≫ y1 C.y C.R') t = IsLocalRing.closedPoint C.R'
  · obtain ⟨R'', _, _, _, _, _, _, _, a, T, t'', w₁, w₂, s, ha, hw₁, hw₂, hs₁, hs₂, hs₃, hts⟩ := C.exists_datum t ht
    obtain ⟨τ, hτ₁, hτ₂⟩ := C.hstat R'' inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance a ha
    obtain ⟨V, G, hagree, hmemV⟩ :=
      NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
        C.y C.U C.m C.hU₁ C.hΦ C.hassoc C.R' C.y' C.ι R'' a ha τ hτ₁ hτ₂
    refine ⟨V, G.1, G.2, fun s w v => hagree s w v, ?_⟩
    obtain ⟨p, rfl⟩ := hts
    exact hmemV t'' w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃ ⟨p, rfl⟩
  · exact ⟨C.U₁, C.G₀, C.G₀_y', C.G₀_agree, C.mem_U₁_of_ne t ht⟩

def PF (V : C.P → C.P.Opens) : Option C.P → Scheme.{u}
  | none => (C.U₁ : Scheme.{u})
  | some t => (V t : Scheme.{u})

def Pj (V : C.P → C.P.Opens) : ∀ o, C.PF V o ⟶ C.P
  | none => C.U₁.ι
  | some t => (V t).ι

def Pg (V : C.P → C.P.Opens) (G : ∀ t, (V t : Scheme.{u}) ⟶ C.Y') : ∀ o, C.PF V o ⟶ C.Y'
  | none => C.G₀
  | some t => G t

scoped instance isOpenImmersion_Pj (V : C.P → C.P.Opens) (o : Option C.P) : IsOpenImmersion (C.Pj V o) := by
  cases o with
  | none => exact inferInstanceAs (IsOpenImmersion C.U₁.ι)
  | some t => exact inferInstanceAs (IsOpenImmersion (V t).ι)

theorem exists_G : ∃ G : C.P ⟶ C.Y', C.U₁.ι ≫ G = C.G₀ ∧ G ≫ C.y' = pullback.fst _ _ ≫ y1 C.y C.R' := by
  choose V G hGy hGa hmem using C.hpiece
  have hPy : ∀ o, C.Pg V G o ≫ C.y' = C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
    rintro (_ | t)
    · exact C.G₀_y'
    · exact hGy t

  have hAg : ∀ o {T : Scheme.{u}} (s : T ⟶ C.PF V o) (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R'),
      s ≫ C.Pj V o ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y →
      s ≫ C.Pj V o ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y →
      v ≫ p1 C.y C.R' = w ≫ C.m.1 →
      v ≫ y1 C.y C.R' = s ≫ C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R' →
      s ≫ C.Pg V G o = v ≫ C.ι.1 := by
    rintro (_ | t)
    · exact fun s w v => C.G₀_agree s w v
    · exact fun s w v => hGa t s w v
  obtain ⟨GG, hGG, hGGy⟩ := exists_glue_of_isOpenImmersion (pullback.fst _ _ ≫ y1 C.y C.R') C.y' (C.PF V) (C.Pj V)
    (fun t => ⟨some t, ⟨t, hmem t⟩, Scheme.Opens.ι_apply _ _⟩) (C.Pg V G) hPy
    (fun o o' => by
      refine ⟨(C.U₁ : Set C.P), C.U₁.2, ?_, ?_⟩
      · rw [C.dense_U₁.closure_eq]; exact Set.subset_univ _
      · intro T t₁ t₂ h hW
        have hr : Set.range (t₁ ≫ C.Pj V o ≫ pi1 C.y C.R').base ⊆ Set.range C.U.ι.base := by
          rw [Scheme.Opens.range_ι]
          rintro _ ⟨p, rfl⟩
          rw [← Category.assoc, Scheme.Hom.comp_apply]
          exact hW ⟨p, rfl⟩
        let w := IsOpenImmersion.lift C.U.ι _ hr
        have hw : w ≫ C.U.ι = t₁ ≫ C.Pj V o ≫ pi1 C.y C.R' := IsOpenImmersion.lift_fac _ _ _
        have hv : (w ≫ C.m.1) ≫ C.y = (t₁ ≫ C.Pj V o ≫ pullback.fst _ _ ≫ y1 C.y C.R') ≫ bS C.R C.R' := by
          rw [Category.assoc, C.m.2, reassoc_of% hw]
          simp only [Category.assoc, pi1_fst_assoc]
          rw [pullback.condition]
        let v : T ⟶ Y1 C.y C.R' := pullback.lift _ _ hv
        have e₁ := hAg o t₁ w v (by rw [reassoc_of% hw, pi1_fst]) (by rw [reassoc_of% hw, pi1_snd])
          (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
        have e₂ := hAg o' t₂ w v (by rw [reassoc_of% hw, pi1_fst, reassoc_of% h])
          (by rw [reassoc_of% hw, pi1_snd, reassoc_of% h]) (pullback.lift_fst _ _ _)
          (by rw [pullback.lift_snd, reassoc_of% h])
        rw [e₁, e₂])
  exact ⟨GG, hGG none, hGGy⟩

theorem exists_extension :
    ∃ (D : (pullback C.y' C.y').Opens) (hle : C.U' ≤ D)
      (M : SchemeHomOver (D.ι ≫ pullback.fst C.y' C.y' ≫ C.y') C.y'),
      (pullback C.y' C.y').homOfLE hle ≫ M.1 = C.m'.1 ∧
      ∀ q : ↑(pullback C.y' C.y'), (pullback.fst C.y' C.y').base q ∈ Set.range C.ι.1.base →
        (pullback.snd C.y' C.y').base q ∈ Set.range C.ι.1.base → q ∈ D := by
  obtain ⟨G, hGU, hGy⟩ := C.exists_G

  let ιι : C.P ⟶ pullback C.y' C.y' :=
    pullback.map _ _ _ _ C.ι.1 C.ι.1 (𝟙 _) (by rw [Category.comp_id, C.ι.2]) (by rw [Category.comp_id, C.ι.2])
  have hιι₁ : ιι ≫ pullback.fst C.y' C.y' = pullback.fst _ _ ≫ C.ι.1 := pullback.lift_fst _ _ _
  have hιι₂ : ιι ≫ pullback.snd C.y' C.y' = pullback.snd _ _ ≫ C.ι.1 := pullback.lift_snd _ _ _
  haveI : IsReduced (pullback C.y' C.y') :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.fst C.y' C.y' ≫ C.y')
  let D : (pullback C.y' C.y').Opens := C.U' ⊔ ιι.opensRange
  have hU'D : C.U' ≤ D := le_sup_left
  haveI : IsReduced (D : Scheme.{u}) := isReduced_of_isOpenImmersion D.ι

  let F : Bool → Scheme.{u} := fun b => bif b then (C.U' : Scheme.{u}) else C.P
  have hr₂ : Set.range ιι.base ⊆ Set.range D.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun q hq => Or.inr hq
  let j₂ : C.P ⟶ D := IsOpenImmersion.lift D.ι ιι hr₂
  have hj₂ : j₂ ≫ D.ι = ιι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion j₂ := by
    haveI : IsOpenImmersion (j₂ ≫ D.ι) := by rw [hj₂]; infer_instance
    exact IsOpenImmersion.of_comp j₂ D.ι
  let j : ∀ b, F b ⟶ D := fun b =>
    match b with
    | true => (pullback C.y' C.y').homOfLE hU'D
    | false => j₂
  haveI : ∀ b, IsOpenImmersion (j b) := by
    rintro (_ | _)
    · exact inferInstanceAs (IsOpenImmersion j₂)
    · exact inferInstanceAs (IsOpenImmersion ((pullback C.y' C.y').homOfLE hU'D))
  let g : ∀ b, F b ⟶ C.Y' := fun b =>
    match b with
    | true => C.m'.1
    | false => G

  have hcovt : ∀ x : D, x.1 ∈ C.U' → x ∈ Set.range ((pullback C.y' C.y').homOfLE hU'D).base := by
    intro x hx
    refine ⟨⟨x.1, hx⟩, ?_⟩
    apply D.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
  have hcovf : ∀ x : D, x.1 ∈ Set.range ιι.base → x ∈ Set.range j₂.base := by
    rintro x ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply D.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hj₂, Scheme.Opens.ι_apply, hq]
  have hcov : ∀ x : D, ∃ b, x ∈ Set.range (j b).base := by
    rintro ⟨x, hx | hx⟩
    · exact ⟨true, hcovt _ hx⟩
    · exact ⟨false, hcovf _ hx⟩

  let W : Set D := D.ι.base ⁻¹' (ιι.base '' (C.U₁ : Set C.P))
  have hWo : IsOpen W := (ιι.isOpenMap _ C.U₁.2).preimage D.ι.continuous
  have hWcl : Set.range j₂.base ⊆ closure W := by
    rintro _ ⟨q, rfl⟩
    have h1 : Set.range ιι.base ⊆ closure (ιι.base '' (C.U₁ : Set C.P)) := by
      rw [← Set.image_univ, ← C.dense_U₁.closure_eq]
      exact image_closure_subset_closure_image ιι.continuous
    have h2 : D.ι (j₂ q) ∈ closure (ιι.base '' (C.U₁ : Set C.P)) := by
      rw [← Scheme.Hom.comp_apply, hj₂]
      exact h1 ⟨q, rfl⟩
    change j₂ q ∈ closure (D.ι.base ⁻¹' _)
    rw [← D.ι.isOpenMap.preimage_closure_eq_closure_preimage D.ι.continuous]
    exact h2

  have hagree : ∀ {T : Scheme.{u}} (t₁ : T ⟶ C.U') (t₂ : T ⟶ C.P),
      t₁ ≫ (pullback C.y' C.y').homOfLE hU'D = t₂ ≫ j₂ →
      Set.range (t₁ ≫ (pullback C.y' C.y').homOfLE hU'D).base ⊆ W → t₁ ≫ C.m'.1 = t₂ ≫ G := by
    intro T t₁ t₂ h hW

    have hr : Set.range t₂.base ⊆ Set.range C.U₁.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      have hp : D.ι ((t₁ ≫ (pullback C.y' C.y').homOfLE hU'D) p) ∈ ιι.base '' (C.U₁ : Set C.P) :=
        hW ⟨p, rfl⟩
      rw [h, ← Scheme.Hom.comp_apply, Category.assoc, hj₂, Scheme.Hom.comp_apply] at hp
      obtain ⟨z, hz, hzq⟩ := hp
      rwa [← ιι.isOpenEmbedding.injective hzq]
    let wU := IsOpenImmersion.lift C.U₁.ι t₂ hr
    have hwU : wU ≫ C.U₁.ι = t₂ := IsOpenImmersion.lift_fac _ _ _

    let t' : T ⟶ Spec (CommRingCat.of C.R') := wU ≫ C.U₁.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R'
    have ht' : t' = wU ≫ C.U₁.ι ≫ pullback.snd _ _ ≫ y1 C.y C.R' := by
      simp only [t', pullback.condition]
    let w : SchemeHomOver (t' ≫ bS C.R C.R') (C.U.ι ≫ pullback.fst C.y C.y ≫ C.y) :=
      ⟨wU ≫ C.πU, by
        show (wU ≫ C.πU) ≫ C.U.ι ≫ pullback.fst C.y C.y ≫ C.y = t' ≫ bS C.R C.R'
        rw [Category.assoc, πU_fst_assoc, pullback.condition (f := C.y) (g := bS C.R C.R')]
        simp only [t', Category.assoc]⟩
    have ha : (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) ≫ C.y = t' ≫ bS C.R C.R' := by
      simpa only [Category.assoc] using w.2
    have hb : (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t' ≫ bS C.R C.R' := by
      have e : (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) ≫ C.y := by
        simp only [Category.assoc, pullback.condition]
      exact e.trans ha
    have hc : (w.1 ≫ C.m.1) ≫ C.y = t' ≫ bS C.R C.R' := by
      rw [Category.assoc, C.m.2]; exact ha
    obtain ⟨w', hw'₁, hw'₂, hw'₃⟩ := C.hext t' w ⟨_, ha⟩ ⟨_, hb⟩ ⟨_, hc⟩ rfl rfl rfl
    rw [RelativeGroupLaw.baseChangePointOfBase_coe] at hw'₁ hw'₂ hw'₃

    have e₁ : pullback.lift (w.1 ≫ C.U.ι ≫ pullback.fst C.y C.y) t' ha = wU ≫ C.U₁.ι ≫ pullback.fst _ _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show (wU ≫ C.πU) ≫ C.U.ι ≫ pullback.fst C.y C.y = (wU ≫ C.U₁.ι ≫ pullback.fst _ _) ≫ p1 C.y C.R'
        simp only [Category.assoc, πU_fst]
      · rw [pullback.lift_snd]; simp only [Category.assoc, t']
    have e₂ : pullback.lift (w.1 ≫ C.U.ι ≫ pullback.snd C.y C.y) t' hb = wU ≫ C.U₁.ι ≫ pullback.snd _ _ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show (wU ≫ C.πU) ≫ C.U.ι ≫ pullback.snd C.y C.y = (wU ≫ C.U₁.ι ≫ pullback.snd _ _) ≫ p1 C.y C.R'
        simp only [Category.assoc, πU_snd]
      · rw [pullback.lift_snd, ht']; simp only [Category.assoc]
    have e₃ : pullback.lift (w.1 ≫ C.m.1) t' hc = wU ≫ C.m₁ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show (wU ≫ C.πU) ≫ C.m.1 = (wU ≫ C.m₁) ≫ p1 C.y C.R'
        simp only [Category.assoc, m₁_p1]
      · rw [pullback.lift_snd, Category.assoc, m₁_y1]
    have ht₁ : t₁ = w'.1 := by
      rw [← cancel_mono C.U'.ι]
      have h' : t₁ ≫ C.U'.ι = t₂ ≫ ιι := by
        rw [← hj₂, ← Category.assoc, ← h, Category.assoc, Scheme.homOfLE_ι]
      rw [h', ← hwU]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hιι₁, Category.assoc, hw'₁, e₁, Category.assoc, Category.assoc]
      · rw [Category.assoc, Category.assoc, hιι₂, Category.assoc, hw'₂, e₂, Category.assoc, Category.assoc]
    rw [ht₁, hw'₃, e₃, ← hwU, Category.assoc, Category.assoc, hGU, G₀]
  have hdiag : ∀ b, ∃ W : Set D, IsOpen W ∧ Set.range (j b).base ∩ Set.range (j b).base ⊆ closure W ∧
      ∀ {T : Scheme.{u}} (t₁ t₂ : T ⟶ F b), t₁ ≫ j b = t₂ ≫ j b → Set.range (t₁ ≫ j b).base ⊆ W →
        t₁ ≫ g b = t₂ ≫ g b := by
    intro b
    refine ⟨Set.univ, isOpen_univ, by rw [closure_univ]; exact Set.subset_univ _, ?_⟩
    intro T t₁ t₂ h _
    rw [(cancel_mono (j b)).mp h]

  obtain ⟨M, hM, hMy⟩ := exists_glue_of_isOpenImmersion (D.ι ≫ pullback.fst C.y' C.y' ≫ C.y') C.y' F j hcov g
    (by
      rintro (_ | _)
      · change G ≫ C.y' = j₂ ≫ D.ι ≫ pullback.fst C.y' C.y' ≫ C.y'
        rw [hGy, ← Category.assoc j₂, hj₂, ← Category.assoc, hιι₁, Category.assoc, C.ι.2]
      · change C.m'.1 ≫ C.y' = (pullback C.y' C.y').homOfLE hU'D ≫ D.ι ≫ pullback.fst C.y' C.y' ≫ C.y'
        rw [C.m'.2, Scheme.homOfLE_ι_assoc])
    (by
      rintro (_ | _) (_ | _)
      · exact hdiag false
      · refine ⟨W, hWo, Set.inter_subset_left.trans hWcl, fun t₁ t₂ h hW => ?_⟩
        have hW' : Set.range (t₂ ≫ j true).base ⊆ W := by rwa [h] at hW
        exact (hagree t₂ t₁ h.symm hW').symm
      · exact ⟨W, hWo, Set.inter_subset_right.trans hWcl, fun t₁ t₂ h hW => hagree t₁ t₂ h hW⟩
      · exact hdiag true)
  refine ⟨D, hU'D, ⟨M, hMy⟩, hM true, ?_⟩
  rintro q ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
  refine Or.inr ?_
  change q ∈ Set.range ιι.base
  rw [Scheme.Pullback.range_map]
  exact ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩

end Cx
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing.P2mDefFin.Cx"

end P2mDefFin
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing.P2mDefFin.Cx P2MW.S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing.P2mDefFin"

set_option linter.unusedVariables false in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
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
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y') [IsOpenImmersion ι.1]
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
    (hstat : ∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
        (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ : Module.FaithfullyFlat R' R'')
        (a : Spec (CommRingCat.of R'') ⟶ Y),
      a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
      ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))),
        τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
          (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
          w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
          w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
          v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
          v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
          x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (U'' : (pullback y' y').Opens) (hle : U' ≤ U'')
      (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y' y' ≫ y') y'),
      (pullback y' y').homOfLE hle ≫ m''.1 = m'.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.fst y' y' →
        p.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.snd y' y' →
        q.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ U''.ι ≫ pullback.fst y' y' →
        q.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U'') := by
  let C : P2mDefFin.Cx.{u} :=
    { R := R, Y := Y, y := y, U := U, m := m, hU₁ := hU₁, hU₂ := hU₂, hΦ := hΦ, hΦ₂ := hΦ₂, hΨ := hΨ,
      hassoc := hassoc, hUK := hUK, R' := R', Y' := Y', y' := y', ι := ι, U' := U', m' := m', hext := hext,
      hstat := hstat }
  obtain ⟨D, hle, M, hM, hsq⟩ := C.exists_extension
  have h :=
    NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
      y' U' m' hU'₁ hU'₂ hΦ' hΦ'₁ hΦ'₂ hΨ' hΨ'₁ hΨ'₂ hassoc' D hle M hM
  exact ⟨D, hle, M, hM, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2, hsq⟩

end
end S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing (solution)
