-- Prove2me | solution 1 for HofmannStreicher1994.universe_presentations_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:35:16.876454+00:00
-- url     : https://prove2.me/submissions/aa031eb5-6129-4d92-8db6-92acebef65d0

import Definitions.Def_HofmannStreicher1994_Groupoids
open CategoryTheory HofmannStreicher1994

universe v

theorem hs_obj_id (G : Grpd.{v,v}) (x : G) :
    ((universeEl ⋙ Grpd.forgetToCat).map (𝟙 (Discrete.mk G))).toFunctor.obj x = x := by
  simp [universeEl]
  rfl

theorem hs_map_id_map {G : Grpd.{v,v}} {x y : G} (f : x ⟶ y) :
    ((universeEl ⋙ Grpd.forgetToCat).map (𝟙 (Discrete.mk G))).toFunctor.map f = f := by
  simp [universeEl]
  rfl

def hsObj (X : UniverseTotal.{v}) : UniverseGrothendieck.{v} := ⟨⟨X.1⟩, X.2⟩

noncomputable def hsMap : ∀ {X Y : UniverseTotal.{v}}, (X ⟶ Y) → (hsObj X ⟶ hsObj Y)
  | _, _, .mk g => ⟨𝟙 _, eqToHom (hs_obj_id _ _) ≫ g⟩

theorem hsMap_mk {G : Grpd.{v,v}} {x y : G} (g : x ⟶ y) :
    hsMap (Sigma.SigmaHom.mk g : (⟨G, x⟩ : UniverseTotal.{v}) ⟶ ⟨G, y⟩) =
      ⟨𝟙 _, eqToHom (hs_obj_id _ _) ≫ g⟩ := rfl

theorem hs_comp {G : Grpd.{v,v}} {x y z : G} (f : x ⟶ y) (g : y ⟶ z) :
    (Sigma.SigmaHom.mk f ≫ Sigma.SigmaHom.mk g : (⟨G, x⟩ : UniverseTotal.{v}) ⟶ ⟨G, z⟩) =
      Sigma.SigmaHom.mk (f ≫ g) := rfl

theorem hsMap_id (X : UniverseTotal.{v}) : hsMap (𝟙 X) = 𝟙 (hsObj X) := by
  obtain ⟨G, x⟩ := X
  have : 𝟙 (⟨G, x⟩ : UniverseTotal.{v}) = Sigma.SigmaHom.mk (𝟙 x) := rfl
  erw [this, hsMap_mk]
  apply Grothendieck.ext
  · simp [Grothendieck.id, hs_map_id_map]
    exact Category.comp_id _
  · rfl

theorem hsMap_comp {X Y Z : UniverseTotal.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hsMap (f ≫ g) = hsMap f ≫ hsMap g := by
  obtain ⟨G, x⟩ := X
  obtain ⟨G', y⟩ := Y
  obtain ⟨G'', z⟩ := Z
  cases f with
  | mk f =>
    cases g with
    | mk g =>
      erw [hs_comp, hsMap_mk, hsMap_mk, hsMap_mk]
      apply Grothendieck.ext
      · simp [Grothendieck.comp, hsObj]
        erw [hs_map_id_map]
        repeat erw [eqToHom_refl]
        repeat erw [Category.id_comp]
        rfl
      · exact (Category.id_comp (𝟙 (hsObj ⟨G, x⟩).base)).symm

theorem cancel_eq {C : Type*} [Category C] {a b c : C} (h : a = b) (f g : b ⟶ c)
    (h2 : eqToHom h ≫ f = eqToHom h ≫ g) : f = g := by
  subst h
  simpa using h2

theorem hsMap_inj {G : Grpd.{v,v}} {x y : G} (f g : x ⟶ y)
    (h : hsMap (Sigma.SigmaHom.mk f : (⟨G, x⟩ : UniverseTotal.{v}) ⟶ ⟨G, y⟩) =
      hsMap (Sigma.SigmaHom.mk g)) : f = g := by
  erw [hsMap_mk, hsMap_mk] at h
  have h2 := eq_of_heq (Grothendieck.Hom.mk.inj h).2
  exact cancel_eq _ _ _ h2

theorem eq_eqToHom_comp {C : Type*} [Category C] {a b c : C} (h : a = b) (h' : b = a) (f : a ⟶ c) :
    eqToHom h ≫ eqToHom h' ≫ f = f := by
  subst h
  simp

theorem eq_eqToHom_comp3 {C : Type*} [Category C] {a b c d : C} (h : a = b) (h' : b = c)
    (h'' : c = a) (f : a ⟶ d) :
    eqToHom h ≫ eqToHom h' ≫ eqToHom h'' ≫ f = f := by
  subst h
  subst h'
  simp

theorem hsMap_surj {G : Grpd.{v,v}} {x y : G}
    (fb : ((universeEl ⋙ Grpd.forgetToCat).map (𝟙 (Discrete.mk G))).toFunctor.obj x ⟶ y) :
    hsMap (Sigma.SigmaHom.mk (eqToHom (hs_obj_id _ _).symm ≫ fb) :
      (⟨G, x⟩ : UniverseTotal.{v}) ⟶ ⟨G, y⟩) = ⟨𝟙 _, fb⟩ := by
  erw [hsMap_mk]
  apply Grothendieck.ext
  · apply eq_eqToHom_comp3
  · rfl

noncomputable def hsF : UniverseTotal.{v} ⥤ UniverseGrothendieck.{v} where
  obj := hsObj
  map := hsMap
  map_id := hsMap_id
  map_comp := hsMap_comp


instance : hsF.{v}.Faithful where
  map_injective := by
    intro X Y f g h
    obtain ⟨G, x⟩ := X
    cases f with
    | mk f =>
      cases g with
      | mk g =>
        exact congrArg Sigma.SigmaHom.mk (hsMap_inj f g h)

instance : hsF.{v}.Full where
  map_surjective := by
    intro X Y f
    obtain ⟨G, x⟩ := X
    obtain ⟨G', y⟩ := Y
    obtain ⟨b, fb⟩ := f
    have hG : G = G' := Discrete.eq_of_hom b
    subst hG
    have hb : b = 𝟙 _ := Subsingleton.elim _ _
    subst hb
    exact ⟨Sigma.SigmaHom.mk (eqToHom (hs_obj_id _ _).symm ≫ fb), hsMap_surj fb⟩

instance : hsF.{v}.EssSurj where
  mem_essImage := by
    rintro ⟨⟨G⟩, x⟩
    exact ⟨⟨G, x⟩, ⟨Iso.refl _⟩⟩

theorem solution : Nonempty (UniverseTotal.{v} ≌ UniverseGrothendieck.{v}) := by
  have : hsF.{v}.IsEquivalence := { }
  exact ⟨hsF.asEquivalence⟩
