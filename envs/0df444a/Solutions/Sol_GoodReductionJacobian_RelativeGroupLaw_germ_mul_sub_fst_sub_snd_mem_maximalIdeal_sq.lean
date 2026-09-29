-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2a6674a7-c075-5bc5-8e06-3dfba5ec7d8f

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NeronModelInfra GoodReductionJacobian

namespace InfGroupLawA3

section Algebra

open IsLocalRing

theorem mem_maximalIdeal_sq_of_slices {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (π₁ π₂ : B →+* A) (α β : A →+* B)
    (h0 : maximalIdeal A ≤ (maximalIdeal B).map π₁ ⊔ (maximalIdeal B).map π₂)
    (hα : ∀ a ∈ maximalIdeal A, α a ∈ maximalIdeal B)
    (hβ : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal B)
    (h1 : ∀ b, α (π₁ b) = b) (h1' : ∀ b, β (π₂ b) = b)
    (h2 : ∀ b ∈ maximalIdeal B, α (π₂ b) = 0) (h2' : ∀ b ∈ maximalIdeal B, β (π₁ b) = 0)
    {ψ : A} (hψ : ψ ∈ maximalIdeal A) (hαψ : α ψ = 0) (hβψ : β ψ = 0) :
    ψ ∈ maximalIdeal A ^ 2 := by

  have hπ₁ : ∀ b ∈ maximalIdeal B, π₁ b ∈ maximalIdeal A := by
    intro b hb
    rw [mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    intro hu
    exact hb (by simpa [h1] using hu.map α)
  have hπ₂ : ∀ b ∈ maximalIdeal B, π₂ b ∈ maximalIdeal A := by
    intro b hb
    rw [mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    intro hu
    exact hb (by simpa [h1'] using hu.map β)
  have hmap₁ : (maximalIdeal B).map π₁ ≤ maximalIdeal A :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ hπ₁ b hb
  have hmap₂ : (maximalIdeal B).map π₂ ≤ maximalIdeal A :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ hπ₂ b hb

  have hkerα : ∀ a, α a = 0 → a ∈ maximalIdeal A := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map α
    rw [ha] at this
    exact not_isUnit_zero this
  have hkerβ : ∀ a, β a = 0 → a ∈ maximalIdeal A := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map β
    rw [ha] at this
    exact not_isUnit_zero this
  have h5 : ∀ a, a - π₁ (α a) ∈ maximalIdeal A := fun a ↦ hkerα _ (by simp [h1])
  have h5' : ∀ a, a - π₂ (β a) ∈ maximalIdeal A := fun a ↦ hkerβ _ (by simp [h1'])

  let P : A → Prop := fun a ↦ a - π₁ (α a) - π₂ (β a) ∈ maximalIdeal A ^ 2
  have hP_add : ∀ a a', P a → P a' → P (a + a') := by
    intro a a' ha ha'
    have := Ideal.add_mem _ ha ha'
    change _ ∈ _
    convert this using 1
    simp only [map_add]; ring
  have hsq : ∀ u ∈ maximalIdeal A, ∀ v ∈ maximalIdeal A, u * v ∈ maximalIdeal A ^ 2 :=
    fun u hu v hv ↦ by rw [pow_two]; exact Ideal.mul_mem_mul hu hv
  have hπsq₁ : ∀ b ∈ maximalIdeal B ^ 2, π₁ b ∈ maximalIdeal A ^ 2 := by
    intro b hb
    have : (maximalIdeal B ^ 2).map π₁ ≤ maximalIdeal A ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap₁ 2
    exact this (Ideal.mem_map_of_mem _ hb)
  have hπsq₂ : ∀ b ∈ maximalIdeal B ^ 2, π₂ b ∈ maximalIdeal A ^ 2 := by
    intro b hb
    have : (maximalIdeal B ^ 2).map π₂ ≤ maximalIdeal A ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap₂ 2
    exact this (Ideal.mem_map_of_mem _ hb)

  have hP_smul : ∀ c a, a ∈ maximalIdeal A → P a → P (c * a) := by
    intro c a ha hPa
    change c * a - π₁ (α (c * a)) - π₂ (β (c * a)) ∈ _
    have e1 : c * a - π₁ (α (c * a)) - π₂ (β (c * a)) =
        c * (a - π₁ (α a) - π₂ (β a)) + (c - π₁ (α c)) * π₁ (α a) +
          (c - π₂ (β c)) * π₂ (β a) := by
      simp only [map_mul]; ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hPa
    · exact hsq _ (h5 c) _ (hπ₁ _ (hα _ ha))
    · exact hsq _ (h5' c) _ (hπ₂ _ (hβ _ ha))

  have hP₁ : ∀ a ∈ (maximalIdeal B).map π₁, P a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ ↦ P a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩
      change π₁ b - π₁ (α (π₁ b)) - π₂ (β (π₁ b)) ∈ _
      rw [h1, h2' b hb, map_zero, sub_self, zero_sub, neg_mem_iff]
      exact Ideal.zero_mem _
    · change (0 : A) - π₁ (α 0) - π₂ (β 0) ∈ _; simp
    · intro a a' _ _ ha ha'; exact hP_add _ _ ha ha'
    · intro c a ha' hPa
      exact hP_smul c a (hmap₁ ha') hPa
  have hP₂ : ∀ a ∈ (maximalIdeal B).map π₂, P a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ ↦ P a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩
      change π₂ b - π₁ (α (π₂ b)) - π₂ (β (π₂ b)) ∈ _
      rw [h1', h2 b hb, map_zero, sub_zero, sub_self]
      exact Ideal.zero_mem _
    · change (0 : A) - π₁ (α 0) - π₂ (β 0) ∈ _; simp
    · intro a a' _ _ ha ha'; exact hP_add _ _ ha ha'
    · intro c a ha' hPa
      exact hP_smul c a (hmap₂ ha') hPa

  have hPψ : P ψ := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (h0 hψ)
    exact hP_add _ _ (hP₁ u hu) (hP₂ v hv)
  simpa [P, hαψ, hβψ] using hPψ

end Algebra

section Transport

variable {X Y Z : Scheme.{u}}

noncomputable def stalkMapOfEq (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ g.stalkMap x

lemma stalkMapOfEq_germ (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(Y, U)) :
    stalkMapOfEq g x y h (Y.presheaf.germ U y hy s) =
      X.presheaf.germ (g ⁻¹ᵁ U) x (show g x ∈ U by rw [h]; exact hy) (g.app U s) := by
  simp only [stalkMapOfEq, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

lemma germ_mem_maximalIdeal_iff {U : X.Opens} (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen s := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, X.mem_basicOpen s x hx]

set_option backward.isDefEq.respectTransparency false in
lemma stalkMapOfEq_mem_maximalIdeal (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y)
    (a : Y.presheaf.stalk y) (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    stalkMapOfEq g x y h a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [stalkMapOfEq_germ, germ_mem_maximalIdeal_iff, ← Scheme.preimage_basicOpen,
    Scheme.Hom.mem_preimage, h]
  rwa [germ_mem_maximalIdeal_iff] at ha

lemma stalkMapOfEq_mem_maximalIdeal_iff (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)) :
    stalkMapOfEq g x y h (Y.presheaf.germ U y hy s) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      Y.presheaf.germ U y hy s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  refine ⟨fun H ↦ ?_, stalkMapOfEq_mem_maximalIdeal g x y h _⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at H ⊢
  exact fun hu ↦ H (hu.map _)

lemma germ_app_congr {g g' : X ⟶ Y} (hg : g = g') (U : Y.Opens) (x : X) (h₁ : g x ∈ U)
    (h₂ : g' x ∈ U) (s : Γ(Y, U)) :
    X.presheaf.germ (g ⁻¹ᵁ U) x h₁ (g.app U s) = X.presheaf.germ (g' ⁻¹ᵁ U) x h₂ (g'.app U s) := by
  subst hg; rfl

lemma germ_id_app (U : X.Opens) (x : X) (h₁ : (𝟙 X : X ⟶ X) x ∈ U) (h₂ : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) x h₁ ((𝟙 X : X ⟶ X).app U s) =
      X.presheaf.germ U x h₂ s := by
  rfl

lemma stalkMapOfEq_stalkMapOfEq_germ (g : X ⟶ Y) (g' : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h : g x = y) (h' : g' y = z) (U : Z.Opens) (hz : z ∈ U) (s : Γ(Z, U)) :
    stalkMapOfEq g x y h (stalkMapOfEq g' y z h' (Z.presheaf.germ U z hz s)) =
      X.presheaf.germ ((g ≫ g') ⁻¹ᵁ U) x
        (show (g ≫ g') x ∈ U by rw [Scheme.Hom.comp_apply, h, h']; exact hz)
        ((g ≫ g').app U s) := by
  rw [stalkMapOfEq_germ, stalkMapOfEq_germ]
  rfl

end Transport

section SpecField

variable {k : Type u} [Field k]

lemma germ_eq_zero_of_mem_maximalIdeal_of_field (q : Spec (CommRingCat.of k))
    (V : (Spec (CommRingCat.of k)).Opens) (hq : q ∈ V) (s : Γ(Spec (CommRingCat.of k), V))
    (hs : (Spec (CommRingCat.of k)).presheaf.germ V q hq s ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of k)).presheaf.stalk q)) :
    (Spec (CommRingCat.of k)).presheaf.germ V q hq s = 0 := by
  obtain rfl : IsLocalRing.closedPoint k = q := Subsingleton.elim _ _
  have hF : IsField ((Spec (CommRingCat.of k)).presheaf.stalk (IsLocalRing.closedPoint k)) :=
    MulEquiv.isField (Field.toIsField k)
      (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  rw [IsLocalRing.isField_iff_maximalIdeal_eq] at hF
  rw [hF] at hs
  simpa using hs

end SpecField

section Slices

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

noncomputable def unit : Spec (CommRingCat.of k) ⟶ G := (L.one (𝟙 _)).1

@[reassoc (attr := simp)]
lemma unit_f : unit f L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

noncomputable def mulMap : pullback f f ⟶ G :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩).1

noncomputable def slice₁ : G ⟶ pullback f f :=
  pullback.lift (𝟙 G) (f ≫ unit f L) (by simp)

noncomputable def slice₂ : G ⟶ pullback f f :=
  pullback.lift (f ≫ unit f L) (𝟙 G) (by simp)

@[reassoc (attr := simp)]
lemma slice₁_fst : slice₁ f L ≫ pullback.fst f f = 𝟙 G := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma slice₁_snd : slice₁ f L ≫ pullback.snd f f = f ≫ unit f L := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma slice₂_fst : slice₂ f L ≫ pullback.fst f f = f ≫ unit f L := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma slice₂_snd : slice₂ f L ≫ pullback.snd f f = 𝟙 G := pullback.lift_snd _ _ _

lemma one_eq : L.one f = ⟨f ≫ unit f L, by simp⟩ := by
  have h := L.one_natural (𝟙 _) f f (Category.comp_id f)
  rw [← h]
  rfl

lemma slice₁_mulMap : slice₁ f L ≫ mulMap f L = 𝟙 G := by
  have hψ : slice₁ f L ≫ pullback.fst f f ≫ f = f := by simp
  have h := L.mul_natural (pullback.fst f f ≫ f) f (slice₁ f L) hψ ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩
  have h1 : schemeHomOverComp (slice₁ f L) hψ ⟨pullback.fst f f, rfl⟩ =
      (⟨𝟙 G, by simp⟩ : SchemeHomOver f f) := Subtype.ext (by simp)
  have h2 : schemeHomOverComp (slice₁ f L) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      L.one f := by
    rw [one_eq]; exact Subtype.ext (by simp)
  rw [h1, h2, L.mul_one] at h
  exact congrArg Subtype.val h

lemma slice₂_mulMap : slice₂ f L ≫ mulMap f L = 𝟙 G := by
  have hψ : slice₂ f L ≫ pullback.fst f f ≫ f = f := by simp
  have h := L.mul_natural (pullback.fst f f ≫ f) f (slice₂ f L) hψ ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩
  have h1 : schemeHomOverComp (slice₂ f L) hψ ⟨pullback.fst f f, rfl⟩ = L.one f := by
    rw [one_eq]; exact Subtype.ext (by simp)
  have h2 : schemeHomOverComp (slice₂ f L) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      (⟨𝟙 G, by simp⟩ : SchemeHomOver f f) := Subtype.ext (by simp)
  rw [h1, h2, L.one_mul] at h
  exact congrArg Subtype.val h

noncomputable def unitPair : Spec (CommRingCat.of k) ⟶ pullback f f :=
  pullback.lift (unit f L) (unit f L) rfl

@[reassoc (attr := simp)]
lemma unitPair_fst : unitPair f L ≫ pullback.fst f f = unit f L := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma unitPair_snd : unitPair f L ≫ pullback.snd f f = unit f L := pullback.lift_snd _ _ _

lemma unit_slice₁ : unit f L ≫ slice₁ f L = unitPair f L := by
  apply pullback.hom_ext <;> simp

lemma unit_slice₂ : unit f L ≫ slice₂ f L = unitPair f L := by
  apply pullback.hom_ext <;> simp

lemma unitPair_mulMap : unitPair f L ≫ mulMap f L = unit f L := by
  rw [← unit_slice₁, Category.assoc, slice₁_mulMap, Category.comp_id]

section points

local notation "pt" => IsLocalRing.closedPoint k

lemma fst_z : pullback.fst f f (unitPair f L pt) = unit f L pt := by
  rw [← Scheme.Hom.comp_apply, unitPair_fst]

lemma snd_z : pullback.snd f f (unitPair f L pt) = unit f L pt := by
  rw [← Scheme.Hom.comp_apply, unitPair_snd]

lemma mulMap_z : mulMap f L (unitPair f L pt) = unit f L pt := by
  rw [← Scheme.Hom.comp_apply, unitPair_mulMap]

lemma slice₁_e : slice₁ f L (unit f L pt) = unitPair f L pt := by
  rw [← Scheme.Hom.comp_apply, unit_slice₁]

lemma slice₂_e : slice₂ f L (unit f L pt) = unitPair f L pt := by
  rw [← Scheme.Hom.comp_apply, unit_slice₂]

end points

end Slices

section Identities

variable {X Y Z : Scheme.{u}}

lemma stalkMapOfEq_id_apply (x : X) (h : (𝟙 X : X ⟶ X) x = x) (b : X.presheaf.stalk x) :
    stalkMapOfEq (𝟙 X) x x h b = b := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_germ]
  rfl

lemma stalkMapOfEq_congr {g g' : X ⟶ Y} (hg : g = g') (x : X) (y : Y) (h : g x = y)
    (h' : g' x = y) : stalkMapOfEq g x y h = stalkMapOfEq g' x y h' := by
  subst hg; rfl

lemma stalkMapOfEq_comp_apply (g : X ⟶ Y) (g' : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h : g x = y) (h' : g' y = z) (b : Z.presheaf.stalk z) :
    stalkMapOfEq g x y h (stalkMapOfEq g' y z h' b) =
      stalkMapOfEq (g ≫ g') x z (by rw [Scheme.Hom.comp_apply, h, h']) b := by
  obtain ⟨U, hz, s, rfl⟩ := Z.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_stalkMapOfEq_germ, stalkMapOfEq_germ]

lemma germ_appLE_eq_stalkMapOfEq (g : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (hWU : W ≤ g ⁻¹ᵁ U)
    (x : X) (hx : x ∈ W) (y : Y) (hy : g x = y) (s : Γ(Y, U)) :
    X.presheaf.germ W x hx (g.appLE U W hWU s) =
      stalkMapOfEq g x y hy (Y.presheaf.germ U y (by rw [← hy]; exact hWU hx) s) := by
  rw [stalkMapOfEq_germ]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

set_option backward.isDefEq.respectTransparency false in

lemma stalkMapOfEq_f_unit_apply
    (b : G.presheaf.stalk (unit f L (IsLocalRing.closedPoint k)))
    (hb : b ∈ IsLocalRing.maximalIdeal _)
    (h : (f ≫ unit f L) (unit f L (IsLocalRing.closedPoint k)) =
      unit f L (IsLocalRing.closedPoint k)) :
    stalkMapOfEq (f ≫ unit f L) (unit f L (IsLocalRing.closedPoint k))
      (unit f L (IsLocalRing.closedPoint k)) h b = 0 := by
  obtain ⟨U, he, s, rfl⟩ := G.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_germ]
  have hue : unit f L (f (unit f L (IsLocalRing.closedPoint k))) =
      unit f L (IsLocalRing.closedPoint k) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, unit_f_assoc]
  have hfe : f (unit f L (IsLocalRing.closedPoint k)) ∈ unit f L ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, hue]; exact he
  have key : G.presheaf.germ ((f ≫ unit f L) ⁻¹ᵁ U) (unit f L (IsLocalRing.closedPoint k))
      (show (f ≫ unit f L) (unit f L (IsLocalRing.closedPoint k)) ∈ U by rw [h]; exact he)
      ((f ≫ unit f L).app U s) =
      f.stalkMap (unit f L (IsLocalRing.closedPoint k))
        ((Spec (CommRingCat.of k)).presheaf.germ (unit f L ⁻¹ᵁ U)
          (f (unit f L (IsLocalRing.closedPoint k))) hfe ((unit f L).app U s)) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl
  rw [key, germ_eq_zero_of_mem_maximalIdeal_of_field, map_zero]
  rw [germ_mem_maximalIdeal_iff, ← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hue,
    ← germ_mem_maximalIdeal_iff]
  exact hb

noncomputable def π₁ := stalkMapOfEq (pullback.fst f f) (unitPair f L (IsLocalRing.closedPoint k))
  (unit f L (IsLocalRing.closedPoint k)) (fst_z f L)

noncomputable def π₂ := stalkMapOfEq (pullback.snd f f) (unitPair f L (IsLocalRing.closedPoint k))
  (unit f L (IsLocalRing.closedPoint k)) (snd_z f L)

noncomputable def μ := stalkMapOfEq (mulMap f L) (unitPair f L (IsLocalRing.closedPoint k))
  (unit f L (IsLocalRing.closedPoint k)) (mulMap_z f L)

noncomputable def α := stalkMapOfEq (slice₁ f L) (unit f L (IsLocalRing.closedPoint k))
  (unitPair f L (IsLocalRing.closedPoint k)) (slice₁_e f L)

noncomputable def β := stalkMapOfEq (slice₂ f L) (unit f L (IsLocalRing.closedPoint k))
  (unitPair f L (IsLocalRing.closedPoint k)) (slice₂_e f L)

lemma α_π₁ (b) : α f L (π₁ f L b) = b := by
  rw [α, π₁, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_fst f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (by simp)]
  exact stalkMapOfEq_id_apply _ _ b

lemma α_μ (b) : α f L (μ f L b) = b := by
  rw [α, μ, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_mulMap f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (by simp)]
  exact stalkMapOfEq_id_apply _ _ b

lemma β_π₂ (b) : β f L (π₂ f L b) = b := by
  rw [β, π₂, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_snd f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (by simp)]
  exact stalkMapOfEq_id_apply _ _ b

lemma β_μ (b) : β f L (μ f L b) = b := by
  rw [β, μ, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_mulMap f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (by simp)]
  exact stalkMapOfEq_id_apply _ _ b

lemma f_unit_e : (f ≫ unit f L) (unit f L (IsLocalRing.closedPoint k)) =
    unit f L (IsLocalRing.closedPoint k) := by
  rw [← Scheme.Hom.comp_apply, unit_f_assoc]

lemma α_π₂ (b) (hb : b ∈ IsLocalRing.maximalIdeal _) : α f L (π₂ f L b) = 0 := by
  rw [α, π₂, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_snd f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (f_unit_e f L)]
  exact stalkMapOfEq_f_unit_apply f L b hb _

lemma β_π₁ (b) (hb : b ∈ IsLocalRing.maximalIdeal _) : β f L (π₁ f L b) = 0 := by
  rw [β, π₁, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_fst f L)
    (unit f L (IsLocalRing.closedPoint k)) (unit f L (IsLocalRing.closedPoint k)) _ (f_unit_e f L)]
  exact stalkMapOfEq_f_unit_apply f L b hb _

lemma map_stalkMap_le_map_stalkMapOfEq (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g x))).map (g.stalkMap x).hom ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map (stalkMapOfEq g x y h).hom := by
  have hcomp : (stalkMapOfEq g x y h).hom =
      (g.stalkMap x).hom.comp (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom := rfl
  rw [hcomp, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  intro t ht
  let e : Y.presheaf.stalk (g x) ≅ Y.presheaf.stalk y := Y.presheaf.stalkCongr (Inseparable.of_eq h)
  have hte : t = (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom (e.hom t) := by
    change t = (e.hom ≫ e.inv) t
    rw [Iso.hom_inv_id]; rfl
  rw [hte]
  refine Ideal.mem_map_of_mem _ ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
  intro hu
  apply ht
  have := hu.map (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom
  rwa [← hte] at this

lemma maximalIdeal_le :
    IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk (unitPair f L (IsLocalRing.closedPoint k))) ≤
      (IsLocalRing.maximalIdeal _).map (π₁ f L).hom ⊔ (IsLocalRing.maximalIdeal _).map (π₂ f L).hom := by
  have hchild :=
    AlgebraicGeometry.maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
      f f (unit f L) (unit_f f L) (unit f L) (unit_f f L)
  refine (le_of_eq hchild).trans (sup_le_sup ?_ ?_)
  · exact map_stalkMap_le_map_stalkMapOfEq _ _ _ (fst_z f L)
  · exact map_stalkMap_le_map_stalkMapOfEq _ _ _ (snd_z f L)

end Identities

end InfGroupLawA3

open InfGroupLawA3 in
theorem solution
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (U : G.Opens) (W : (pullback f f).Opens)
    (hWm : W ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ U)
    (hW₁ : W ≤ pullback.fst f f ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd f f ⁻¹ᵁ U)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ U)
    (hee : pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl
      (IsLocalRing.closedPoint k) ∈ W)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk _)) :
    ((pullback f f).presheaf.germ W _ hee).hom
        (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.appLE U W hWm).hom φ
          - ((pullback.fst f f).appLE U W hW₁).hom φ - ((pullback.snd f f).appLE U W hW₂).hom φ)
      ∈ IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk _) ^ 2 := by
  change (pullback f f).presheaf.germ W (unitPair f L (IsLocalRing.closedPoint k)) hee
      ((mulMap f L).appLE U W hWm φ - (pullback.fst f f).appLE U W hW₁ φ -
        (pullback.snd f f).appLE U W hW₂ φ) ∈
    IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk (unitPair f L (IsLocalRing.closedPoint k))) ^ 2
  have hφ' : G.presheaf.germ U (unit f L (IsLocalRing.closedPoint k)) he φ ∈
      IsLocalRing.maximalIdeal _ := hφ
  rw [map_sub, map_sub,
    germ_appLE_eq_stalkMapOfEq (mulMap f L) U W hWm (unitPair f L (IsLocalRing.closedPoint k)) hee _
      (mulMap_z f L),
    germ_appLE_eq_stalkMapOfEq (pullback.fst f f) U W hW₁ (unitPair f L (IsLocalRing.closedPoint k))
      hee _ (fst_z f L),
    germ_appLE_eq_stalkMapOfEq (pullback.snd f f) U W hW₂ (unitPair f L (IsLocalRing.closedPoint k))
      hee _ (snd_z f L)]
  change μ f L _ - π₁ f L _ - π₂ f L _ ∈ _
  refine mem_maximalIdeal_sq_of_slices (π₁ f L).hom (π₂ f L).hom (α f L).hom (β f L).hom
    (maximalIdeal_le f L)
    (fun a ha ↦ stalkMapOfEq_mem_maximalIdeal _ _ _ _ a ha)
    (fun a ha ↦ stalkMapOfEq_mem_maximalIdeal _ _ _ _ a ha)
    (α_π₁ f L) (β_π₂ f L) (α_π₂ f L) (β_π₁ f L) ?_ ?_ ?_
  · refine Ideal.sub_mem _ (Ideal.sub_mem _ ?_ ?_) ?_ <;>
      exact stalkMapOfEq_mem_maximalIdeal _ _ _ _ _ hφ'
  · change α f L (μ f L _ - π₁ f L _ - π₂ f L _) = 0
    rw [map_sub, map_sub, α_μ, α_π₁, α_π₂ f L _ hφ', sub_self, sub_zero]
  · change β f L (μ f L _ - π₁ f L _ - π₂ f L _) = 0
    rw [map_sub, map_sub, β_μ, β_π₁ f L _ hφ', β_π₂, sub_zero, sub_self]

end S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq (solution)
