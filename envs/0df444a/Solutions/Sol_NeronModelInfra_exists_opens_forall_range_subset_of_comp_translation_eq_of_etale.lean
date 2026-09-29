-- Prove2me | solution 1 for NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1f49cbdd-32d4-55a6-85bb-a80a11e227cf

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

universe u v

namespace P2mDefFinPiece

section General

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

theorem eq_of_comp_ι_eq {X Z S : Scheme.{u}} [IsReduced X] (s : Z ⟶ S) [IsSeparated s]
    {f g : X ⟶ Z} (hs : f ≫ s = g ≫ s) (W : X.Opens) (hW : Dense (W : Set X)) (h : W.ι ≫ f = W.ι ≫ g) :
    f = g := by
  haveI : IsDominant W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hW⟩
  exact ext_of_isDominant_of_isSeparated s hs W.ι h

end General

section Setup

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev Phi : (U : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)

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

section Piece

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) y)

def sig : Y ⟶ pullback y y :=
  pullback.lift (y ≫ a.1) (𝟙 Y) (by rw [Category.assoc, a.2, Category.comp_id, Category.id_comp])

@[reassoc]
theorem sig_fst : sig y a ≫ pullback.fst y y = y ≫ a.1 := pullback.lift_fst _ _ _

@[reassoc]
theorem sig_snd : sig y a ≫ pullback.snd y y = 𝟙 Y := pullback.lift_snd _ _ _

theorem isPullback_sig : IsPullback (sig y a) y (pullback.fst y y) a.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (sig_fst y a)
    (IsPullback.of_hasPullback y y).flip
  rw [sig_snd, a.2]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

def Ua : Y.Opens := sig y a ⁻¹ᵁ U

def zeta : (Ua y U a : Scheme.{u}) ⟶ U := sig y a ∣_ U

@[reassoc]
theorem zeta_ι : zeta y U a ≫ U.ι = (Ua y U a).ι ≫ sig y a := morphismRestrict_ι _ _

def Phia : (Ua y U a : Scheme.{u}) ⟶ Y := zeta y U a ≫ m.1

@[reassoc]
theorem Phia_y : Phia y U m a ≫ y = (Ua y U a).ι ≫ y := by
  rw [Phia, Category.assoc, m.2, zeta_ι_assoc, sig_fst_assoc, a.2, Category.comp_id]

@[reassoc]
theorem Phia_sig : Phia y U m a ≫ sig y a = zeta y U a ≫ Phi y U m := by
  apply pullback.hom_ext
  · rw [Category.assoc, sig_fst, Phia_y_assoc, Category.assoc, pullback.lift_fst, zeta_ι_assoc, sig_fst]
  · rw [Category.assoc, sig_snd, Category.comp_id, Category.assoc, pullback.lift_snd, Phia]

theorem isPullback_Phia : IsPullback (Phia y U m a) (zeta y U a) (sig y a) (Phi y U m) := by
  refine IsPullback.of_right (h₁₂ := y) (v₁₃ := a.1) (h₂₂ := pullback.fst y y) ?_ (Phia_sig y U m a)
    (isPullback_sig y a).flip
  rw [Phia_y, pullback.lift_fst]
  exact ((isPullback_morphismRestrict (sig y a) U).paste_vert (isPullback_sig y a)).flip

theorem isOpenImmersion_Phia [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (Phia y U m a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_Phia y U m a).flip inferInstance

def Fa : (pullback y y).Opens := (pullback.fst y y ⁻¹ᵁ Ua y U a) ⊓ U

def toUa : (Fa y U a : Scheme.{u}) ⟶ Ua y U a :=
  (pullback y y).homOfLE inf_le_left ≫ (pullback.fst y y ∣_ Ua y U a)

@[reassoc]
theorem toUa_ι : toUa y U a ≫ (Ua y U a).ι = (Fa y U a).ι ≫ pullback.fst y y := by
  rw [toUa, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

def toU : (Fa y U a : Scheme.{u}) ⟶ U := (pullback y y).homOfLE inf_le_right

@[reassoc]
theorem toU_ι : toU y U a ≫ U.ι = (Fa y U a).ι := Scheme.homOfLE_ι _ _

scoped instance isOpenImmersion_toU : IsOpenImmersion (toU y U a) := by
  unfold toU
  infer_instance

def ja' : ((pullback.fst y y ⁻¹ᵁ Ua y U a : (pullback y y).Opens) : Scheme.{u}) ⟶ pullback y y :=
  pullback.lift ((pullback.fst y y ∣_ Ua y U a) ≫ Phia y U m a)
    ((pullback.fst y y ⁻¹ᵁ Ua y U a).ι ≫ pullback.snd y y)
    (by rw [Category.assoc, Phia_y, morphismRestrict_ι_assoc, Category.assoc, pullback.condition])

theorem isPullback_ja' :
    IsPullback (ja' y U m a) (pullback.fst y y ∣_ Ua y U a) (pullback.fst y y) (Phia y U m a) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback y y).flip
  rw [ja', pullback.lift_snd, Phia_y]
  exact (isPullback_morphismRestrict (pullback.fst y y) (Ua y U a)).flip.paste_horiz
    (IsPullback.of_hasPullback y y).flip

scoped instance isOpenImmersion_ja' [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (ja' y U m a) :=
  haveI := isOpenImmersion_Phia y U m a
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_ja' y U m a).flip inferInstance

def ja : (Fa y U a : Scheme.{u}) ⟶ pullback y y := (pullback y y).homOfLE inf_le_left ≫ ja' y U m a

scoped instance isOpenImmersion_ja [IsOpenImmersion (Phi y U m)] : IsOpenImmersion (ja y U m a) := by
  unfold ja; infer_instance

@[reassoc]
theorem ja_fst : ja y U m a ≫ pullback.fst y y = toUa y U a ≫ Phia y U m a := by
  rw [ja, Category.assoc, ja', pullback.lift_fst, toUa, Category.assoc]

@[reassoc]
theorem ja_snd : ja y U m a ≫ pullback.snd y y = (Fa y U a).ι ≫ pullback.snd y y := by
  rw [ja, Category.assoc, ja', pullback.lift_snd, Scheme.homOfLE_ι_assoc]

@[reassoc]
theorem ja_fst_y : ja y U m a ≫ pullback.fst y y ≫ y = (Fa y U a).ι ≫ pullback.fst y y ≫ y := by
  rw [ja_fst_assoc, Phia_y, toUa_ι_assoc]

def ga {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (τ : SchemeHomOver y y') :
    (Fa y U a : Scheme.{u}) ⟶ Y' :=
  toU y U a ≫ m.1 ≫ τ.1

theorem ga_y' {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (τ : SchemeHomOver y y') :
    ga y U m a τ ≫ y' = ja y U m a ≫ pullback.fst y y ≫ y := by
  rw [ga, Category.assoc, Category.assoc, τ.2, m.2, toU_ι_assoc, ja_fst_y]

def theta : (Fa y U a : Scheme.{u}) ⟶ pullback y y := (toU y U a ≫ m.1) ≫ sig y a

def Ga : (Fa y U a : Scheme.{u}).Opens := (ja y U m a ⁻¹ᵁ U) ⊓ (theta y U m a ⁻¹ᵁ U)

theorem universallyOpen_m [Smooth y] [IsOpenImmersion (Phi y U m)] : UniversallyOpen m.1 := by
  have h : m.1 = Phi y U m ≫ pullback.snd y y := (pullback.lift_snd _ _ _).symm
  rw [h]
  infer_instance

theorem dense_Ua
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense ((Ua y U a : Y.Opens) : Set Y) := by
  refine dense_of_forall_dense_fibre (fun c : Y => y c) _ fun s₀ => ?_
  rw [dense_fibre_iff y s₀]
  let c := (Spec (CommRingCat.of R)).fromSpecResidueField s₀
  have hg : (c ≫ a.1) ≫ y = c := by rw [Category.assoc, a.2, Category.comp_id]
  have hfac : pullback.fst y c ≫ sig y a = lamFst y c (c ≫ a.1) hg := by
    apply pullback.hom_ext
    · rw [Category.assoc, sig_fst, lamFst_fst, pullback.condition_assoc]
    · rw [Category.assoc, sig_snd, lamFst_snd, Category.comp_id]
  have hd : Dense ((lamFst y c (c ≫ a.1) hg) ⁻¹' (U : Set ↑(pullback y y))) :=
    dense_preimage_of_isPullback (pullback.fst y y) (a.1 s₀) (Spec.map (a.1.residueFieldMap s₀)) (c ≫ a.1)
      (by rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) (isPullback_lamFst y c _ hg) _
      (hU₁ _)
  have h : (y.fiberι s₀) ⁻¹' ((Ua y U a : Y.Opens) : Set Y) = (lamFst y c (c ≫ a.1) hg) ⁻¹' (U : Set _) := by
    rw [← hfac]
    rfl
  rw [h]
  exact hd

theorem dense_theta_preimage [Smooth y] [IsOpenImmersion (Phi y U m)]
    (hUa : Dense ((Ua y U a : Y.Opens) : Set Y)) :
    Dense ((theta y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) := by
  haveI := universallyOpen_m y U m
  have h : ((theta y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) =
      (toU y U a ≫ m.1) ⁻¹' ((Ua y U a : Y.Opens) : Set Y) := rfl
  rw [h]
  exact hUa.preimage (toU y U a ≫ m.1).isOpenMap

theorem dense_Ga [Smooth y] [IsOpenImmersion (Phi y U m)] (hU : Dense (U : Set ↑(pullback y y)))
    (hUa : Dense ((Ua y U a : Y.Opens) : Set Y)) :
    Dense ((Ga y U m a : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) := by
  have h1 : Dense ((ja y U m a ⁻¹ᵁ U : (Fa y U a : Scheme.{u}).Opens) : Set (Fa y U a)) :=
    hU.preimage (ja y U m a).isOpenMap
  exact h1.inter_of_isOpen_left (dense_theta_preimage y U m a hUa) (ja y U m a ⁻¹ᵁ U).2

theorem agree_piece
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} {y' : Y' ⟶ Spec (CommRingCat.of R)} (ι τ : SchemeHomOver y y')
    (hτa : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
        (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a.1 → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1)
    [IsOpenImmersion (Phi y U m)]
    {T : Scheme.{u}} (t₁ : T ⟶ Fa y U a) (w : T ⟶ U) (h : t₁ ≫ ja y U m a = w ≫ U.ι)
    (hG : ∀ p : T, t₁ p ∈ Ga y U m a) :
    t₁ ≫ ga y U m a τ = w ≫ m.1 ≫ ι.1 := by
  have hθ : Set.range (t₁ ≫ theta y U m a) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (hG p).2
  let q' : T ⟶ U := IsOpenImmersion.lift U.ι (t₁ ≫ theta y U m a) hθ
  have hq' : q' ≫ U.ι = t₁ ≫ theta y U m a := IsOpenImmersion.lift_fac _ _ _
  let tT : T ⟶ Spec (CommRingCat.of R) := t₁ ≫ (Fa y U a).ι ≫ pullback.fst y y ≫ y
  let u : T ⟶ U := t₁ ≫ toUa y U a ≫ zeta y U a
  let v : T ⟶ U := t₁ ≫ toU y U a
  have hu : u ≫ U.ι = t₁ ≫ (Fa y U a).ι ≫ pullback.fst y y ≫ sig y a := by
    simp only [u, Category.assoc, zeta_ι, toUa_ι_assoc]
  have hv : v ≫ U.ι = t₁ ≫ (Fa y U a).ι := by simp only [v, Category.assoc, toU_ι]
  have hw : w ≫ U.ι = t₁ ≫ ja y U m a := h.symm
  have hq : q' ≫ U.ι = v ≫ m.1 ≫ sig y a := by
    rw [hq', theta]
    simp only [v, Category.assoc]
  have hmy : m.1 ≫ y = U.ι ≫ pullback.fst y y ≫ y := m.2
  have e1 : u ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hu, sig_snd, Category.comp_id, reassoc_of% hv]
  have e2 : w ≫ U.ι ≫ pullback.fst y y = u ≫ m.1 := by
    rw [reassoc_of% hw, ja_fst, Phia]
    simp only [u, Category.assoc]
  have e3 : w ≫ U.ι ≫ pullback.snd y y = v ≫ U.ι ≫ pullback.snd y y := by
    rw [reassoc_of% hw, ja_snd, reassoc_of% hv]
  have e4 : q' ≫ U.ι ≫ pullback.fst y y = u ≫ U.ι ≫ pullback.fst y y := by
    rw [reassoc_of% hq, sig_fst, reassoc_of% hmy, reassoc_of% hv, reassoc_of% hu, sig_fst]
  have e5 : q' ≫ U.ι ≫ pullback.snd y y = v ≫ m.1 := by
    rw [reassoc_of% hq, sig_snd, Category.comp_id]
  have hu' : u ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by
    rw [reassoc_of% hu, sig_fst_assoc, a.2, Category.comp_id]
  have hv' : v ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by rw [reassoc_of% hv]
  have hw' : w ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by rw [reassoc_of% hw, ja_fst_y]
  have hq'' : q' ≫ (U.ι ≫ pullback.fst y y ≫ y) = tT := by
    calc q' ≫ (U.ι ≫ pullback.fst y y ≫ y) = (q' ≫ U.ι ≫ pullback.fst y y) ≫ y := by
          simp only [Category.assoc]
      _ = (u ≫ U.ι ≫ pullback.fst y y) ≫ y := by rw [e4]
      _ = tT := by simp only [Category.assoc]; exact hu'
  have hx : (v ≫ m.1) ≫ y = tT := by rw [Category.assoc, hmy, hv']
  have hqa : q' ≫ U.ι ≫ pullback.fst y y = tT ≫ a.1 := by
    rw [e4, reassoc_of% hu, sig_fst]
    simp only [tT, Category.assoc]
  have H1 : w ≫ m.1 = q' ≫ m.1 := hassoc tT ⟨u, hu'⟩ ⟨v, hv'⟩ ⟨w, hw'⟩ ⟨q', hq''⟩ e1 e2 e3 e4 e5
  have H2 : (v ≫ m.1) ≫ τ.1 = q' ≫ m.1 ≫ ι.1 := hτa tT ⟨v ≫ m.1, hx⟩ ⟨q', hq''⟩ hqa e5
  calc t₁ ≫ ga y U m a τ = (v ≫ m.1) ≫ τ.1 := by simp only [ga, v, Category.assoc]
    _ = q' ≫ m.1 ≫ ι.1 := H2
    _ = w ≫ m.1 ≫ ι.1 := by rw [reassoc_of% H1]

end Piece

section Level

abbrev bS (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R'] (R'' : Type u) [CommRing R''] [Algebra R' R'']

abbrev Y1 : Scheme.{u} := pullback y (bS R R')

abbrev Y2 : Scheme.{u} := pullback y (bS R' R'' ≫ bS R R')

abbrev y1 : Y1 y R' ⟶ Spec (CommRingCat.of R') := pullback.snd y (bS R R')

abbrev y2 : Y2 y R' R'' ⟶ Spec (CommRingCat.of R'') := pullback.snd y (bS R' R'' ≫ bS R R')

abbrev p1 : Y1 y R' ⟶ Y := pullback.fst y (bS R R')

abbrev p2 : Y2 y R' R'' ⟶ Y := pullback.fst y (bS R' R'' ≫ bS R R')

def r : Y2 y R' R'' ⟶ Y1 y R' :=
  pullback.lift (p2 y R' R'') (y2 y R' R'' ≫ bS R' R'') (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem r_p1 : r y R' R'' ≫ p1 y R' = p2 y R' R'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem r_y1 : r y R' R'' ≫ y1 y R' = y2 y R' R'' ≫ bS R' R'' := pullback.lift_snd _ _ _

theorem isPullback_r : IsPullback (r y R' R'') (y2 y R' R'') (y1 y R') (bS R' R'') := by
  refine IsPullback.of_right (h₁₂ := p1 y R') (v₁₃ := y) (h₂₂ := bS R R') ?_ (r_y1 y R' R'')
    (IsPullback.of_hasPullback y (bS R R'))
  rw [r_p1]
  exact IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R')

abbrev P1 : Scheme.{u} := pullback (y1 y R') (y1 y R')

abbrev P2 : Scheme.{u} := pullback (y2 y R' R'') (y2 y R' R'')

def pi1 : P1 y R' ⟶ pullback y y :=
  pullback.map _ _ _ _ (p1 y R') (p1 y R') (bS R R') pullback.condition.symm pullback.condition.symm

def pi2 : P2 y R' R'' ⟶ pullback y y :=
  pullback.map _ _ _ _ (p2 y R' R'') (p2 y R' R'') (bS R' R'' ≫ bS R R')
    pullback.condition.symm pullback.condition.symm

def rho : P2 y R' R'' ⟶ P1 y R' :=
  pullback.map _ _ _ _ (r y R' R'') (r y R' R'') (bS R' R'') (r_y1 y R' R'').symm (r_y1 y R' R'').symm

@[reassoc (attr := simp)]
theorem pi1_fst : pi1 y R' ≫ pullback.fst y y = pullback.fst _ _ ≫ p1 y R' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pi1_snd : pi1 y R' ≫ pullback.snd y y = pullback.snd _ _ ≫ p1 y R' := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem pi2_fst : pi2 y R' R'' ≫ pullback.fst y y = pullback.fst _ _ ≫ p2 y R' R'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pi2_snd : pi2 y R' R'' ≫ pullback.snd y y = pullback.snd _ _ ≫ p2 y R' R'' := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem rho_fst : rho y R' R'' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r y R' R'' := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rho_snd : rho y R' R'' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ r y R' R'' := pullback.lift_snd _ _ _

@[reassoc]
theorem rho_pi1 : rho y R' R'' ≫ pi1 y R' = pi2 y R' R'' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pi1_fst, rho_fst_assoc, r_p1, pi2_fst]
  · rw [Category.assoc, pi1_snd, rho_snd_assoc, r_p1, pi2_snd]

theorem isPullback_pi1_fst :
    IsPullback (pi1 y R') (pullback.fst (y1 y R') (y1 y R')) (pullback.fst y y) (p1 y R') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi1_fst y R')
    (IsPullback.of_hasPullback y y).flip
  rw [pi1_snd]
  have h := (IsPullback.of_hasPullback (y1 y R') (y1 y R')).flip.paste_horiz
    (IsPullback.of_hasPullback y (bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_fst :
    IsPullback (pi2 y R' R'') (pullback.fst (y2 y R' R'') (y2 y R' R'')) (pullback.fst y y) (p2 y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi2_fst y R' R'')
    (IsPullback.of_hasPullback y y).flip
  rw [pi2_snd]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).flip.paste_horiz
    (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_snd :
    IsPullback (pi2 y R' R'') (pullback.snd (y2 y R' R'') (y2 y R' R'')) (pullback.snd y y) (p2 y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst y y) (v₁₃ := y) (h₂₂ := y) ?_ (pi2_snd y R' R'')
    (IsPullback.of_hasPullback y y)
  rw [pi2_fst]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).paste_horiz
    (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))
  rwa [← pullback.condition] at h

theorem isPullback_pi2_base :
    IsPullback (pi2 y R' R'') (pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'')
      (pullback.fst y y ≫ y) (bS R' R'' ≫ bS R R') :=
  (isPullback_pi2_fst y R' R'').paste_vert (IsPullback.of_hasPullback y (bS R' R'' ≫ bS R R'))

theorem isPullback_rho_snd :
    IsPullback (rho y R' R'') (pullback.snd (y2 y R' R'') (y2 y R' R'')) (pullback.snd (y1 y R') (y1 y R'))
      (r y R' R'') := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (y1 y R') (y1 y R')) (v₁₃ := y1 y R') (h₂₂ := y1 y R') ?_
    (rho_snd y R' R'') (IsPullback.of_hasPullback (y1 y R') (y1 y R'))
  rw [rho_fst]
  have h := (IsPullback.of_hasPullback (y2 y R' R'') (y2 y R' R'')).paste_horiz (isPullback_r y R' R'')
  rwa [← r_y1] at h

scoped instance etale_bS [Algebra.Etale R' R''] : Etale (bS R' R'') := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
  infer_instance

scoped instance etale_r [Algebra.Etale R' R''] : Etale (r y R' R'') :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_r y R' R'').flip inferInstance

scoped instance etale_rho [Algebra.Etale R' R''] : Etale (rho y R' R'') :=
  MorphismProperty.of_isPullback (P := @Etale) (isPullback_rho_snd y R' R'').flip inferInstance

variable (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)

abbrev U2 : (P2 y R' R'').Opens := pi2 y R' R'' ⁻¹ᵁ U

abbrev piU : (U2 y R' R'' U : Scheme.{u}) ⟶ U := pi2 y R' R'' ∣_ U

@[reassoc]
theorem piU_ι : piU y R' R'' U ≫ U.ι = (U2 y R' R'' U).ι ≫ pi2 y R' R'' := morphismRestrict_ι _ _

@[reassoc]
theorem piU_fst : piU y R' R'' U ≫ U.ι ≫ pullback.fst y y =
    (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ p2 y R' R'' := by
  rw [piU_ι_assoc, pi2_fst]

@[reassoc]
theorem piU_snd : piU y R' R'' U ≫ U.ι ≫ pullback.snd y y =
    (U2 y R' R'' U).ι ≫ pullback.snd _ _ ≫ p2 y R' R'' := by
  rw [piU_ι_assoc, pi2_snd]

theorem m2_w : (piU y R' R'' U ≫ m.1) ≫ y =
    ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'') ≫ (bS R' R'' ≫ bS R R') := by
  rw [Category.assoc, m.2, piU_fst_assoc, Category.assoc, Category.assoc, ← pullback.condition]

def m2 : SchemeHomOver ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R'')
    (y2 y R' R'') :=
  ⟨pullback.lift (piU y R' R'' U ≫ m.1) ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'') (m2_w y R' R'' U m),
    pullback.lift_snd _ _ _⟩

@[reassoc (attr := simp)]
theorem m2_p2 : (m2 y R' R'' U m).1 ≫ p2 y R' R'' = piU y R' R'' U ≫ m.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem m2_y2 : (m2 y R' R'' U m).1 ≫ y2 y R' R'' = (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem Phi2_pi2 : Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m) ≫ pi2 y R' R'' =
    piU y R' R'' U ≫ Phi y U m := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pi2_fst, pullback.lift_fst, pullback.lift_fst_assoc, piU_fst]
  · simp only [Category.assoc, pi2_snd, pullback.lift_snd, pullback.lift_snd_assoc, m2_p2]

theorem isPullback_Phi2 :
    IsPullback (Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m)) (piU y R' R'' U) (pi2 y R' R'')
      (Phi y U m) := by
  have HU : IsPullback (piU y R' R'' U) ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'')
      (U.ι ≫ pullback.fst y y ≫ y) (bS R' R'' ≫ bS R R') :=
    (isPullback_morphismRestrict (pi2 y R' R'') U).paste_vert (isPullback_pi2_base y R' R'')
  refine (IsPullback.of_bot (h₁₁ := piU y R' R'' U) (v₁₁ := Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m))
    (v₁₂ := Phi y U m) ?_ (Phi2_pi2 y R' R'' U m).symm (isPullback_pi2_base y R' R'')).flip
  rwa [pullback.lift_fst_assoc, pullback.lift_fst_assoc]

scoped instance isOpenImmersion_Phi2 [IsOpenImmersion (Phi y U m)] :
    IsOpenImmersion (Phi (y2 y R' R'') (U2 y R' R'' U) (m2 y R' R'' U m)) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_Phi2 y R' R'' U m).flip inferInstance

theorem dense_fibre_U2
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (x₂ : Y2 y R' R'') :
    Dense ((Subtype.val : {q : ↑(P2 y R' R'') // (pullback.fst (y2 y R' R'') (y2 y R' R'')).base q = x₂} →
      ↑(P2 y R' R'')) ⁻¹' (U2 y R' R'' U : Set ↑(P2 y R' R''))) :=
  dense_fibre_of_isPullback (pullback.fst y y) (pullback.fst _ _) (pi2 y R' R'') (p2 y R' R'')
    (isPullback_pi2_fst y R' R'') _ x₂ (hU₁ _)

theorem dense_U2
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y)))) :
    Dense (U2 y R' R'' U : Set ↑(P2 y R' R'')) :=
  dense_of_forall_dense_fibre (fun q => (pullback.fst (y2 y R' R'') (y2 y R' R'')).base q) _
    (dense_fibre_U2 y R' R'' U hU₁)

theorem hassoc2
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
    (u v p q : SchemeHomOver t ((U2 y R' R'' U).ι ≫ pullback.fst (y2 y R' R'') (y2 y R' R'') ≫ y2 y R' R''))
    (h₁ : u.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _)
    (h₂ : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ = u.1 ≫ (m2 y R' R'' U m).1)
    (h₃ : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _)
    (h₄ : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ = u.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _)
    (h₅ : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ = v.1 ≫ (m2 y R' R'' U m).1) :
    p.1 ≫ (m2 y R' R'' U m).1 = q.1 ≫ (m2 y R' R'' U m).1 := by
  let t₀ : T ⟶ Spec (CommRingCat.of R) := t ≫ bS R' R'' ≫ bS R R'
  have hdn : ∀ z : SchemeHomOver t ((U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R''),
      (z.1 ≫ piU y R' R'' U) ≫ (U.ι ≫ pullback.fst y y ≫ y) = t₀ := by
    intro z
    have hz : z.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := z.2
    simp only [Category.assoc, t₀]
    rw [piU_fst_assoc, pullback.condition (f := y) (g := bS R' R'' ≫ bS R R'), reassoc_of% hz]
  have hf : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ U.ι ≫ pullback.fst y y =
      z ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, piU_fst]
  have hs : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ U.ι ≫ pullback.snd y y =
      z ≫ (U2 y R' R'' U).ι ≫ pullback.snd _ _ ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, piU_snd]
  have hm : ∀ z : T ⟶ (U2 y R' R'' U : Scheme.{u}), (z ≫ piU y R' R'' U) ≫ m.1 =
      z ≫ (m2 y R' R'' U m).1 ≫ p2 y R' R'' := by
    intro z; rw [Category.assoc, m2_p2]
  have H := hassoc t₀ ⟨_, hdn u⟩ ⟨_, hdn v⟩ ⟨_, hdn p⟩ ⟨_, hdn q⟩
    (by rw [hs, hf, reassoc_of% h₁])
    (by rw [hf, hm, reassoc_of% h₂])
    (by rw [hs, hs, reassoc_of% h₃])
    (by rw [hf, hf, reassoc_of% h₄])
    (by rw [hs, hm, reassoc_of% h₅])
  apply pullback.hom_ext
  · simpa only [Category.assoc, m2_p2] using H
  · have hp : p.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := p.2
    have hq : q.1 ≫ (U2 y R' R'' U).ι ≫ pullback.fst _ _ ≫ y2 y R' R'' = t := q.2
    simp only [Category.assoc, m2_y2]
    rw [hp, hq]

end Level

structure Ctx where

  R : Type u
  [instR : CommRing R]

  Y : Scheme.{u}

  y : Y ⟶ Spec (CommRingCat.of R)
  [smooth : Smooth y]

  U : (pullback y y).Opens

  m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y
  hU₁ : ∀ x : Y,
    Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y)))
  hΦ : IsOpenImmersion (Phi y U m)
  hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
    u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
    p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
    q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
    p.1 ≫ m.1 = q.1 ≫ m.1

  R' : Type u
  [instR' : CommRing R']
  [alg : Algebra R R']

  Y' : Scheme.{u}

  y' : Y' ⟶ Spec (CommRingCat.of R')
  [sep : IsSeparated y']

  ι : SchemeHomOver (y1 y R') y'

  R'' : Type u
  [instR'' : CommRing R'']
  [dom : IsDomain R'']
  [dvr : IsDiscreteValuationRing R'']
  [alg' : Algebra R' R'']
  [etale : Algebra.Etale R' R'']

  a : Spec (CommRingCat.of R'') ⟶ Y
  ha : a ≫ y = bS R' R'' ≫ bS R R'

  τ : Y2 y R' R'' ⟶ pullback y' (bS R' R'')
  hτ₁ : τ ≫ pullback.snd y' (bS R' R'') = y2 y R' R''
  hτ₂ : ∀ {T : Scheme.{u}} (x : T ⟶ Y2 y R' R'') (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ Y1 y R'),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ y2 y R' R'' ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ p2 y R' R'' →
      v ≫ p1 y R' = w ≫ m.1 →
      v ≫ y1 y R' = x ≫ y2 y R' R'' ≫ bS R' R'' →
      x ≫ τ ≫ pullback.fst y' (bS R' R'') = v ≫ ι.1

attribute [scoped instance] Ctx.instR Ctx.smooth Ctx.hΦ Ctx.instR' Ctx.alg Ctx.sep Ctx.instR'' Ctx.dom Ctx.dvr Ctx.alg'
  Ctx.etale

namespace Ctx

variable (C : Ctx.{u})

def a2 : SchemeHomOver (𝟙 (Spec (CommRingCat.of C.R''))) (y2 C.y C.R' C.R'') :=
  ⟨pullback.lift C.a (𝟙 _) (by rw [C.ha, Category.id_comp]), pullback.lift_snd _ _ _⟩

@[reassoc]
theorem a2_p2 : C.a2.1 ≫ p2 C.y C.R' C.R'' = C.a := pullback.lift_fst _ _ _

def ι2 : SchemeHomOver (y2 C.y C.R' C.R'') (pullback.snd C.y' (bS C.R' C.R'')) :=
  ⟨pullback.lift (r C.y C.R' C.R'' ≫ C.ι.1) (y2 C.y C.R' C.R'') (by rw [Category.assoc, C.ι.2, r_y1]),
    pullback.lift_snd _ _ _⟩

@[reassoc]
theorem ι2_fst : C.ι2.1 ≫ pullback.fst C.y' (bS C.R' C.R'') = r C.y C.R' C.R'' ≫ C.ι.1 := pullback.lift_fst _ _ _

def τ2 : SchemeHomOver (y2 C.y C.R' C.R'') (pullback.snd C.y' (bS C.R' C.R'')) := ⟨C.τ, C.hτ₁⟩

abbrev U₂ : (P2 C.y C.R' C.R'').Opens := U2 C.y C.R' C.R'' C.U

abbrev m₂ := m2 C.y C.R' C.R'' C.U C.m

theorem hτa2 {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (x : SchemeHomOver t (y2 C.y C.R' C.R''))
    (w : SchemeHomOver t (C.U₂.ι ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R''))
    (h₁ : w.1 ≫ C.U₂.ι ≫ pullback.fst _ _ = t ≫ C.a2.1)
    (h₂ : w.1 ≫ C.U₂.ι ≫ pullback.snd _ _ = x.1) :
    x.1 ≫ C.τ2.1 = w.1 ≫ C.m₂.1 ≫ C.ι2.1 := by
  have hx : x.1 ≫ y2 C.y C.R' C.R'' = t := x.2
  have hw : w.1 ≫ C.U₂.ι ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' = t := w.2
  have H := C.hτ₂ x.1 (w.1 ≫ piU C.y C.R' C.R'' C.U) (w.1 ≫ C.m₂.1 ≫ r C.y C.R' C.R'')
    (by rw [Category.assoc, piU_fst, reassoc_of% h₁, a2_p2, reassoc_of% hx])
    (by rw [Category.assoc, piU_snd, reassoc_of% h₂])
    (by simp only [Category.assoc, r_p1, m2_p2])
    (by simp only [Category.assoc, r_y1, m2_y2_assoc]; rw [reassoc_of% hw, reassoc_of% hx])
  apply pullback.hom_ext
  · simpa only [τ2, Category.assoc, ι2_fst] using H
  · have e₂ := C.ι2.2
    simp only [τ2, Category.assoc, C.hτ₁, hx]
    rw [e₂, m2_y2, hw]

abbrev F : (P2 C.y C.R' C.R'').Opens := Fa (y2 C.y C.R' C.R'') C.U₂ C.a2

abbrev j : (C.F : Scheme.{u}) ⟶ P2 C.y C.R' C.R'' := ja (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2

abbrev g2 : (C.F : Scheme.{u}) ⟶ pullback C.y' (bS C.R' C.R'') := ga (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 C.τ2

def g : (C.F : Scheme.{u}) ⟶ C.Y' := C.g2 ≫ pullback.fst C.y' (bS C.R' C.R'')

def f0 : (C.F : Scheme.{u}) ⟶ P1 C.y C.R' := C.j ≫ rho C.y C.R' C.R''

@[reassoc]
theorem f0_fst : C.f0 ≫ pullback.fst _ _ = C.j ≫ pullback.fst _ _ ≫ r C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_fst]

@[reassoc]
theorem f0_snd : C.f0 ≫ pullback.snd _ _ = C.j ≫ pullback.snd _ _ ≫ r C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_snd]

@[reassoc]
theorem f0_pi1 : C.f0 ≫ pi1 C.y C.R' = C.j ≫ pi2 C.y C.R' C.R'' := by
  rw [f0, Category.assoc, rho_pi1]

theorem isOpenMap_f0 : IsOpenMap C.f0.base := by
  rw [f0]; exact (C.j ≫ rho C.y C.R' C.R'').isOpenMap

@[reassoc]
theorem g_y' : C.g ≫ C.y' = C.f0 ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  have h : C.g2 ≫ pullback.snd C.y' (bS C.R' C.R'') = C.j ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' :=
    ga_y' (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 C.τ2
  rw [g, Category.assoc, pullback.condition, reassoc_of% h, f0_fst_assoc, r_y1]

abbrev O : (C.F : Scheme.{u}).Opens := C.j ⁻¹ᵁ C.U₂

def wO : (C.O : Scheme.{u}) ⟶ C.U₂ :=
  IsOpenImmersion.lift C.U₂.ι (C.O.ι ≫ C.j) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact p.2)

@[reassoc]
theorem wO_ι : C.wO ≫ C.U₂.ι = C.O.ι ≫ C.j := IsOpenImmersion.lift_fac _ _ _

scoped instance isReduced_P2 : IsReduced (P2 C.y C.R' C.R'') :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (pullback.fst (y2 C.y C.R' C.R'') (y2 C.y C.R' C.R'') ≫ y2 C.y C.R' C.R'')

theorem O_agree : C.O.ι ≫ C.g2 = C.wO ≫ C.m₂.1 ≫ C.ι2.1 := by
  let WO : (C.O : Scheme.{u}).Opens := C.O.ι ⁻¹ᵁ (theta (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2 ⁻¹ᵁ C.U₂)
  have hWO : Dense (WO : Set C.O) :=
    (dense_theta_preimage (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2
      (dense_Ua (y2 C.y C.R' C.R'') C.U₂ C.a2 (dense_fibre_U2 C.y C.R' C.R'' C.U C.hU₁))).preimage C.O.ι.isOpenMap
  refine eq_of_comp_ι_eq (pullback.snd C.y' (bS C.R' C.R'')) ?_ WO hWO ?_
  · have e₂ := C.ι2.2
    rw [Category.assoc, ga_y', Category.assoc, Category.assoc, e₂, m2_y2, wO_ι_assoc]
  · rw [← Category.assoc, ← Category.assoc]
    refine agree_piece (y2 C.y C.R' C.R'') C.U₂ C.m₂ C.a2
      (fun t u v p q => hassoc2 C.y C.R' C.R'' C.U C.m C.hassoc t u v p q) C.ι2 C.τ2
      (fun t x w => C.hτa2 t x w) _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, wO_ι]
    · intro p
      refine ⟨?_, p.2⟩
      change ((WO.ι ≫ C.O.ι) ≫ C.j) p ∈ C.U₂
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply]
      exact p.1.2

@[reassoc]
theorem O_g : C.O.ι ≫ C.g = C.wO ≫ C.m₂.1 ≫ r C.y C.R' C.R'' ≫ C.ι.1 := by
  rw [g, reassoc_of% C.O_agree, ι2_fst]

theorem g_eq_of_O {T : Scheme.{u}} (o : T ⟶ (C.O : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u}))
    (hw : w ≫ C.U.ι = o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U ≫ C.U.ι)
    (v : T ⟶ Y1 C.y C.R') (hv₁ : v ≫ p1 C.y C.R' = w ≫ C.m.1)
    (hv₂ : v ≫ y1 C.y C.R' = o ≫ C.O.ι ≫ C.f0 ≫ pullback.fst _ _ ≫ y1 C.y C.R') :
    o ≫ C.O.ι ≫ C.g = v ≫ C.ι.1 := by
  have hw' : w = o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U := by
    rw [← cancel_mono C.U.ι, hw]; simp only [Category.assoc]
  rw [O_g]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, r_p1, m2_p2]
    rw [hv₁, hw']; simp only [Category.assoc]
  · simp only [Category.assoc, r_y1, m2_y2_assoc]
    rw [hv₂, wO_ι_assoc, f0_fst_assoc, r_y1]

def V : (P1 C.y C.R').Opens := ⟨Set.range C.f0.base, C.isOpenMap_f0.isOpen_range⟩

abbrev FV : (C.F : Scheme.{u}).Opens := C.f0 ⁻¹ᵁ C.V

scoped instance etale_f0 : Etale C.f0 := by rw [f0]; infer_instance

def c : (C.FV : Scheme.{u}) ⟶ C.V := C.f0 ∣_ C.V

scoped instance etale_c : Etale C.c := by rw [c]; infer_instance

scoped instance surjective_c : Surjective C.c := ⟨by
  rintro ⟨_, x, rfl⟩
  refine ⟨⟨x, ⟨x, rfl⟩⟩, Subtype.ext ?_⟩
  rw [c]
  exact morphismRestrict_base_coe _ _ _⟩

@[reassoc]
theorem FVι_f0 : C.FV.ι ≫ C.f0 = C.c ≫ C.V.ι := by rw [c]; exact (morphismRestrict_ι _ _).symm

def g' : (C.FV : Scheme.{u}) ⟶ C.Y' := C.FV.ι ≫ C.g

theorem key {T : Scheme.{u}} (i : T ⟶ (C.FV : Scheme.{u})) (hi : ∀ p : T, (i ≫ C.FV.ι) p ∈ C.O) :
    ∃ (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R'),
      w ≫ C.U.ι = i ≫ C.c ≫ C.V.ι ≫ pi1 C.y C.R' ∧
      v ≫ p1 C.y C.R' = w ≫ C.m.1 ∧
      v ≫ y1 C.y C.R' = i ≫ C.c ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' ∧
      i ≫ C.g' = v ≫ C.ι.1 := by
  let t : T ⟶ (C.F : Scheme.{u}) := i ≫ C.FV.ι
  have hr : Set.range t.base ⊆ (C.O : Set C.F) := by
    rintro _ ⟨p, rfl⟩; exact hi p
  let o := IsOpenImmersion.lift C.O.ι t (by rwa [Scheme.Opens.range_ι])
  have ho : o ≫ C.O.ι = t := IsOpenImmersion.lift_fac _ _ _
  let w : T ⟶ (C.U : Scheme.{u}) := o ≫ C.wO ≫ piU C.y C.R' C.R'' C.U
  have hw : w ≫ C.U.ι = i ≫ C.c ≫ C.V.ι ≫ pi1 C.y C.R' := by
    simp only [w, Category.assoc]
    rw [piU_ι, wO_ι_assoc, reassoc_of% ho, ← f0_pi1]
    simp only [t, Category.assoc]
    rw [FVι_f0_assoc]
  have hvw : (w ≫ C.m.1) ≫ C.y = (i ≫ C.c ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') ≫ bS C.R C.R' := by
    rw [Category.assoc, C.m.2, reassoc_of% hw, pi1_fst_assoc, pullback.condition (f := C.y) (g := bS C.R C.R')]
    simp only [Category.assoc]
  refine ⟨w, pullback.lift _ _ hvw, hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  have := C.g_eq_of_O o w (by simp only [w, Category.assoc]) (pullback.lift _ _ hvw) (pullback.lift_fst _ _ _)
    (by
      rw [pullback.lift_snd, reassoc_of% ho]
      simp only [t, Category.assoc]
      rw [FVι_f0_assoc])
  rw [reassoc_of% ho] at this
  rw [g']
  simpa only [t, Category.assoc] using this

theorem desc_cond {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ (C.FV : Scheme.{u})) (h : g₁ ≫ C.c = g₂ ≫ C.c) :
    g₁ ≫ C.g' = g₂ ≫ C.g' := by

  let k : Z ⟶ pullback C.c C.c := pullback.lift g₁ g₂ h
  suffices H : pullback.fst C.c C.c ≫ C.g' = pullback.snd C.c C.c ≫ C.g' by
    have := congrArg (k ≫ ·) H
    simpa only [k, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  haveI : IsReduced (pullback C.c C.c) :=
    AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
      (pullback.fst C.c C.c ≫ C.FV.ι ≫ C.F.ι ≫ pullback.fst (y2 C.y C.R' C.R'') (y2 C.y C.R' C.R'') ≫ y2 C.y C.R' C.R'')

  let W : (pullback C.c C.c).Opens := ((pullback.fst C.c C.c ≫ C.FV.ι) ⁻¹ᵁ C.O) ⊓ ((pullback.snd C.c C.c ≫ C.FV.ι) ⁻¹ᵁ C.O)
  have hO : Dense (C.O : Set C.F) := (dense_U2 C.y C.R' C.R'' C.U C.hU₁).preimage C.j.isOpenMap
  have hW : Dense (W : Set ↑(pullback C.c C.c)) := by
    refine Dense.inter_of_isOpen_left ?_ ?_ (TopologicalSpace.Opens.isOpen _)
    · exact hO.preimage (pullback.fst C.c C.c ≫ C.FV.ι).isOpenMap
    · exact hO.preimage (pullback.snd C.c C.c ≫ C.FV.ι).isOpenMap
  refine eq_of_comp_ι_eq C.y' ?_ W hW ?_
  · rw [g', Category.assoc, Category.assoc, Category.assoc, Category.assoc, g_y', FVι_f0_assoc,
      pullback.condition_assoc]
  · obtain ⟨w₁, v₁, hw₁, hv₁, hv₁', H₁⟩ := C.key (W.ι ≫ pullback.fst C.c C.c) (fun p => p.2.1)
    obtain ⟨w₂, v₂, hw₂, hv₂, hv₂', H₂⟩ := C.key (W.ι ≫ pullback.snd C.c C.c) (fun p => p.2.2)
    simp only [Category.assoc] at H₁ H₂
    rw [H₁, H₂]
    congr 1
    have hw12 : w₁ = w₂ := by
      rw [← cancel_mono C.U.ι, hw₁, hw₂]
      simp only [Category.assoc, pullback.condition_assoc]
    apply pullback.hom_ext
    · rw [hv₁, hv₂, hw12]
    · rw [hv₁', hv₂']
      simp only [Category.assoc, pullback.condition_assoc]

def G : (C.V : Scheme.{u}) ⟶ C.Y' :=
  EffectiveEpi.desc C.c C.g' (fun g₁ g₂ h => C.desc_cond g₁ g₂ h)

theorem c_G : C.c ≫ C.G = C.g' := EffectiveEpi.fac _ _ _

theorem G_y' : C.G ≫ C.y' = C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R' := by
  haveI : Epi C.c := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi C.c, reassoc_of% C.c_G, g', Category.assoc, g_y', FVι_f0_assoc]

theorem G_agree {T : Scheme.{u}} (s : T ⟶ (C.V : Scheme.{u})) (w : T ⟶ (C.U : Scheme.{u})) (v : T ⟶ Y1 C.y C.R')
    (h₁ : s ≫ C.V.ι ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.fst C.y C.y)
    (h₂ : s ≫ C.V.ι ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (h₃ : v ≫ p1 C.y C.R' = w ≫ C.m.1)
    (h₄ : v ≫ y1 C.y C.R' = s ≫ C.V.ι ≫ pullback.fst _ _ ≫ y1 C.y C.R') :
    s ≫ C.G = v ≫ C.ι.1 := by
  haveI : Epi (pullback.fst s C.c) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (pullback.fst s C.c), ← Category.assoc, pullback.condition, Category.assoc, C.c_G]
  have hsw : s ≫ C.V.ι ≫ pi1 C.y C.R' = w ≫ C.U.ι := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pi1_fst] using h₁
    · simpa only [Category.assoc, pi1_snd] using h₂
  have hi : ∀ p, (pullback.snd s C.c ≫ C.FV.ι) p ∈ C.O := by
    intro p
    change ((pullback.snd s C.c ≫ C.FV.ι) ≫ C.j ≫ pi2 C.y C.R' C.R'') p ∈ C.U
    rw [← f0_pi1, Category.assoc, FVι_f0_assoc, ← pullback.condition_assoc, hsw, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (w _).2
  obtain ⟨w', v', hw', hv', hv'', H⟩ := C.key (pullback.snd s C.c) hi
  rw [H, ← Category.assoc]
  congr 1
  have hww : w' = pullback.fst s C.c ≫ w := by
    rw [← cancel_mono C.U.ι, hw', Category.assoc, ← hsw, pullback.condition_assoc]
  apply pullback.hom_ext
  · rw [hv', Category.assoc, h₃, hww, Category.assoc]
  · rw [hv'', Category.assoc, h₄, pullback.condition_assoc]

theorem range_subset_V {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of C.R'')) (w₁ w₂ : T ⟶ (C.U : Scheme.{u}))
    (s : T ⟶ P1 C.y C.R')
    (hw₁ : w₁ ≫ C.U.ι ≫ pullback.fst C.y C.y = t ≫ C.a)
    (hw₂ : w₂ ≫ C.U.ι ≫ pullback.fst C.y C.y = w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hs₁ : s ≫ pullback.fst _ _ ≫ p1 C.y C.R' = w₁ ≫ C.m.1)
    (hs₂ : s ≫ pullback.snd _ _ ≫ p1 C.y C.R' = w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y)
    (hs₃ : s ≫ pullback.fst _ _ ≫ y1 C.y C.R' = t ≫ bS C.R' C.R'') :
    Set.range s.base ⊆ (C.V : Set ↑(P1 C.y C.R')) := by

  have hb : (w₁ ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t ≫ bS C.R' C.R'' ≫ bS C.R C.R' := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hw₁, C.ha]
  have hv : (w₂ ≫ C.U.ι ≫ pullback.snd C.y C.y) ≫ C.y = t ≫ bS C.R' C.R'' ≫ bS C.R C.R' := by
    rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hw₂]
    simpa only [Category.assoc] using hb
  let b : T ⟶ Y2 C.y C.R' C.R'' := pullback.lift _ _ hb
  let v : T ⟶ Y2 C.y C.R' C.R'' := pullback.lift _ _ hv
  have hbv₀ : b ≫ y2 C.y C.R' C.R'' = v ≫ y2 C.y C.R' C.R'' := by
    simp only [b, v, pullback.lift_snd]
  let bv : T ⟶ P2 C.y C.R' C.R'' := pullback.lift b v hbv₀
  have hbv : bv ≫ pi2 C.y C.R' C.R'' = w₂ ≫ C.U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pi2_fst, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, hw₂]
    · rw [Category.assoc, pi2_snd, pullback.lift_snd_assoc, pullback.lift_fst, Category.assoc]
  have hbsig : b ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'' = w₁ ≫ C.U.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pi2_fst, sig_fst_assoc, a2_p2, pullback.lift_snd_assoc, Category.assoc,
        hw₁]
    · rw [Category.assoc, Category.assoc, pi2_snd, sig_snd_assoc, pullback.lift_fst, Category.assoc]

  have hF : Set.range bv.base ⊆ (C.F : Set ↑(P2 C.y C.R' C.R'')) := by
    rintro _ ⟨p, rfl⟩
    refine ⟨?_, ?_⟩
    · change (bv ≫ pullback.fst _ _ ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'') p ∈ C.U
      rw [show bv ≫ pullback.fst _ _ ≫ sig (y2 C.y C.R' C.R'') C.a2 ≫ pi2 C.y C.R' C.R'' = w₁ ≫ C.U.ι by
        rw [pullback.lift_fst_assoc, hbsig], Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (w₁ p).2
    · change (bv ≫ pi2 C.y C.R' C.R'') p ∈ C.U
      rw [hbv, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact (w₂ p).2
  let φ := IsOpenImmersion.lift C.F.ι bv (by rwa [Scheme.Opens.range_ι])
  have hφ : φ ≫ C.F.ι = bv := IsOpenImmersion.lift_fac _ _ _

  have hφu : φ ≫ toUa (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ zeta (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ piU C.y C.R' C.R'' C.U =
      w₁ := by
    rw [← cancel_mono C.U.ι, Category.assoc, Category.assoc, Category.assoc, piU_ι, zeta_ι_assoc, toUa_ι_assoc,
      reassoc_of% hφ, ← hbsig, pullback.lift_fst_assoc]
  have hja₁ : C.j ≫ pullback.fst _ _ ≫ p2 C.y C.R' C.R'' =
      toUa (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ zeta (y2 C.y C.R' C.R'') C.U₂ C.a2 ≫ piU C.y C.R' C.R'' C.U ≫ C.m.1 := by
    rw [ja_fst_assoc, Phia, Category.assoc, m2_p2]
  have hja₂ : C.j ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' = C.F.ι ≫ pullback.fst _ _ ≫ y2 C.y C.R' C.R'' := by
    rw [ja_fst_assoc, Phia_y, toUa_ι_assoc]
  have hja₃ : C.j ≫ pullback.snd _ _ = C.F.ι ≫ pullback.snd _ _ := ja_snd _ _ _ _
  have hs : s = φ ≫ C.f0 := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp only [Category.assoc]
    · rw [hs₁, f0_fst_assoc, r_p1, hja₁, reassoc_of% hφu]
    · rw [hs₃, f0_fst_assoc, r_y1, reassoc_of% hja₂, reassoc_of% hφ, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · rw [hs₂, f0_snd_assoc, r_p1, reassoc_of% hja₃, reassoc_of% hφ, pullback.lift_snd_assoc, pullback.lift_fst]
    · rw [← pullback.condition (f := y1 C.y C.R') (g := y1 C.y C.R'), hs₃, f0_fst_assoc, r_y1, reassoc_of% hja₂,
        reassoc_of% hφ, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  rw [hs]
  rintro _ ⟨p, rfl⟩
  exact ⟨φ p, by rw [Scheme.Hom.comp_apply]⟩

end Ctx
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.P2mDefFinPiece.Ctx"

end P2mDefFinPiece
p2m_reactivate "P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.P2mDefFinPiece.Ctx P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.P2mDefFinPiece"

open P2mDefFinPiece in
theorem solution
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) [IsSeparated y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Algebra.Etale R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y)
    (ha : a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶
      pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))))
    (hτ₁ : τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) =
      pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (hτ₂ : ∀ {T : Scheme.{u}}
        (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
        (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
      v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
      v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
      x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (V : (pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).Opens)
      (G : SchemeHomOver (V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'),
      (∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (U : Scheme.{u}))
          (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.fst y y →
        s ≫ V.ι ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.snd y y →
        v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
        v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
            pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        s ≫ G.1 = v ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'')) (w₁ w₂ : T ⟶ (U : Scheme.{u}))
          (s : T ⟶ pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))),
        w₁ ≫ U.ι ≫ pullback.fst y y = t ≫ a →
        w₂ ≫ U.ι ≫ pullback.fst y y = w₁ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₁ ≫ m.1 →
        s ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₂ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          t ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
        Set.range s.base ⊆ (V : Set ↑(pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
          (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))))) := by
  let C : Ctx.{u} :=
    { R := R, Y := Y, y := y, U := U, m := m, hU₁ := hU₁, hΦ := hΦ, hassoc := hassoc, R' := R', Y' := Y', y' := y',
      ι := ι, R'' := R'', a := a, ha := ha, τ := τ, hτ₁ := hτ₁, hτ₂ := hτ₂ }
  refine ⟨C.V, ⟨C.G, C.G_y'⟩, ?_, ?_⟩
  · intro T s w v h₁ h₂ h₃ h₄
    exact C.G_agree s w v h₁ h₂ h₃ h₄
  · intro T t w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃
    exact C.range_subset_V t w₁ w₂ s hw₁ hw₂ hs₁ hs₂ hs₃

end
end S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
end P2MW
export P2MW.S_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale (solution)
