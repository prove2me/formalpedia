-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_solutionScheme_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3d08738d-4f4a-53cd-ac75-89f7cb58fb2e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_forall_preimage_mem_of_universallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace SolRepAe361a2e

set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem comp_congr {B T T' X : Scheme.{0}} {t : T ⟶ B} {t' : T' ⟶ B} {f : X ⟶ B} {ψ ψ' : T' ⟶ T} (hψ : ψ ≫ t = t')
    (hψ' : ψ' ≫ t = t') (h : ψ = ψ') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ x = GoodReductionJacobian.schemeHomOverComp ψ' hψ' x := by
  subst h; rfl

theorem comp_comp {B T T' T'' X : Scheme.{0}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B} {f : X ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ' hψ' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem range_comp_subset {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g).base ⊆ Set.range g.base := by
  rintro _ ⟨z, rfl⟩
  exact ⟨f.base z, (Scheme.Hom.comp_apply f g z).symm⟩

section Data

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R'] [Algebra R R']
  (A₀ : Type) [CommRing A₀] [Algebra R A₀]
  (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
  (g : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R R'))) gN)
  (W₁ : Type) [CommRing W₁] [Algebra R W₁]
  (υ₁ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) ⟶
    Spec (CommRingCat.of (R' ⊗[R] A₀)))
  (hυ₁ : υ₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A₀))) = pullback.fst _ _)

set_option hygiene false in
local notation "Q" => Spec.map (CommRingCat.ofHom (algebraMap R R'))
set_option hygiene false in
local notation "RES₁" => Spec.map (CommRingCat.ofHom (algebraMap R W₁))
set_option hygiene false in
local notation "SA" => Spec.map (CommRingCat.ofHom (algebraMap R A₀))

def u₁ : pullback Q RES₁ ⟶ N :=
  υ₁ ≫ (pullbackSpecIso R R' A₀).inv ≫ pullback.snd Q SA ≫ j

include hj hυ₁ in
theorem u₁_over : u₁ R' A₀ j W₁ υ₁ ≫ gN = pullback.fst Q RES₁ ≫ Q := by
  rw [u₁, Category.assoc, Category.assoc, Category.assoc, hj, ← pullback.condition, pullbackSpecIso_inv_fst'_assoc, ← Category.assoc,
    hυ₁]

def U₁ : SchemeHomOver (pullback.fst Q RES₁ ≫ Q) gN := ⟨u₁ R' A₀ j W₁ υ₁, u₁_over gN R' A₀ j hj W₁ υ₁ hυ₁⟩

omit [IsOpenImmersion j] in
theorem range_u₁_subset : Set.range (u₁ R' A₀ j W₁ υ₁).base ⊆ Set.range j.base := by
  rintro _ ⟨z, rfl⟩
  refine ⟨((υ₁ ≫ (pullbackSpecIso R R' A₀).inv ≫ pullback.snd Q SA)) z, ?_⟩
  rw [u₁, ← Scheme.Hom.comp_apply]
  simp only [Category.assoc]

end Data

section Master

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
  (R' : Type) [CommRing R'] [Algebra R R']
  (g : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R R'))) gN)

set_option hygiene false in
local notation "Q" => Spec.map (CommRingCat.ofHom (algebraMap R R'))

abbrev pr₁ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.fst Q Q ≫ Q) t ⟶ pullback Q t :=
  pullback.map (pullback.fst Q Q ≫ Q) t Q t (pullback.fst Q Q) (𝟙 T) (𝟙 _) (by simp) (by simp)

abbrev pr₂ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.fst Q Q ≫ Q) t ⟶ pullback Q t :=
  pullback.map (pullback.fst Q Q ≫ Q) t Q t (pullback.snd Q Q) (𝟙 T) (𝟙 _) (by simp [pullback.condition]) (by simp)

abbrev gT {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver (pullback.fst (pullback.fst Q Q ≫ Q) t ≫ pullback.fst Q Q ≫ Q) gN :=
  GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst Q Q ≫ Q) t) rfl g

abbrev pb₂ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst Q t ≫ Q) gN) :
    SchemeHomOver (pullback.fst (pullback.fst Q Q ≫ Q) t ≫ pullback.fst Q Q ≫ Q) gN :=
  GoodReductionJacobian.schemeHomOverComp (pr₂ R' t) (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h

abbrev pb₁ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst Q t ≫ Q) gN) :
    SchemeHomOver (pullback.fst (pullback.fst Q Q ≫ Q) t ≫ pullback.fst Q Q ≫ Q) gN :=
  GoodReductionJacobian.schemeHomOverComp (pr₁ R' t) (by rw [pullback.lift_fst_assoc, Category.assoc]) h

abbrev mT {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst Q t ≫ Q) gN) :
    SchemeHomOver (pullback.fst (pullback.fst Q Q ≫ Q) t ≫ pullback.fst Q Q ≫ Q) gN :=
  L.mul _ (gT gN R' g t) (pb₂ gN R' t h)

variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) (U : SchemeHomOver (pullback.fst Q s ≫ Q) gN)
  {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ S) (hx : x ≫ s = t)
  (φ : pullback Q t ⟶ pullback Q s) (hφ₁ : φ ≫ pullback.fst _ _ = pullback.fst _ _) (hφ₂ : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ x)

abbrev Φ : pullback (pullback.fst Q Q ≫ Q) t ⟶ pullback (pullback.fst Q Q ≫ Q) s :=
  pullback.map (pullback.fst Q Q ≫ Q) t (pullback.fst Q Q ≫ Q) s (𝟙 _) x (𝟙 _) (by simp) (by simpa using hx.symm)

abbrev hx_pt : SchemeHomOver (pullback.fst Q t ≫ Q) gN :=
  GoodReductionJacobian.schemeHomOverComp φ (by rw [← Category.assoc, hφ₁]) U

include hφ₁ hφ₂ in
theorem pr₁_φ : pr₁ R' t ≫ φ = Φ R' s t x hx ≫ pr₁ R' s := by
  apply pullback.hom_ext
  · rw [Category.assoc, hφ₁]; simp
  · rw [Category.assoc, hφ₂]; simp

include hφ₁ hφ₂ in
theorem pr₂_φ : pr₂ R' t ≫ φ = Φ R' s t x hx ≫ pr₂ R' s := by
  apply pullback.hom_ext
  · rw [Category.assoc, hφ₁]; simp
  · rw [Category.assoc, hφ₂]; simp

theorem gT_eq : gT gN R' g t = GoodReductionJacobian.schemeHomOverComp (Φ R' s t x hx) (by simp) (gT gN R' g s) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  congr 1
  simp

include hφ₁ hφ₂ in
theorem pb₂_eq : pb₂ gN R' t (hx_pt gN R' s U t φ hφ₁) =
    GoodReductionJacobian.schemeHomOverComp (Φ R' s t x hx) (by simp) (pb₂ gN R' s U) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  rw [pr₂_φ R' s t x hx φ hφ₁ hφ₂]

include hφ₁ hφ₂ in
theorem pb₁_eq : pb₁ gN R' t (hx_pt gN R' s U t φ hφ₁) =
    GoodReductionJacobian.schemeHomOverComp (Φ R' s t x hx) (by simp) (pb₁ gN R' s U) := by
  apply Subtype.ext
  simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc]
  rw [pr₁_φ R' s t x hx φ hφ₁ hφ₂]

include hφ₁ hφ₂ in
theorem mT_eq : mT gN L R' g t (hx_pt gN R' s U t φ hφ₁) =
    GoodReductionJacobian.schemeHomOverComp (Φ R' s t x hx) (by simp) (mT gN L R' g s U) := by
  rw [mT, mT, L.mul_natural, ← gT_eq, ← pb₂_eq gN R' s U t x hx φ hφ₁ hφ₂]

theorem isPullback_Φ : IsPullback (Φ R' s t x hx) (pullback.snd (pullback.fst Q Q ≫ Q) t)
    (pullback.snd (pullback.fst Q Q ≫ Q) s) x := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback (pullback.fst Q Q ≫ Q) s)
  have h1 : Φ R' s t x hx ≫ pullback.fst (pullback.fst Q Q ≫ Q) s = pullback.fst _ _ := by simp
  rw [h1, hx]
  exact IsPullback.of_hasPullback _ _

theorem exists_Φ_eq (t' : T) (z' : ↥(pullback (pullback.fst Q Q ≫ Q) s))
    (hz' : (pullback.snd (pullback.fst Q Q ≫ Q) s).base z' = x.base t') :
    ∃ z : ↥(pullback (pullback.fst Q Q ≫ Q) t), (Φ R' s t x hx).base z = z' := by
  have hP := isPullback_Φ R' s t x hx
  obtain ⟨z₀, hz₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd (pullback.fst Q Q ≫ Q) s) (g := x) z' t' hz'
  refine ⟨hP.isoPullback.inv.base z₀, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hz₀

include hx hφ₁ hφ₂ in

theorem range_mT_subset_iff (V : Set N) :
    Set.range (mT gN L R' g t (hx_pt gN R' s U t φ hφ₁)).1.base ⊆ V ↔
      ∀ p ∈ Set.range x.base, ∀ z' : ↥(pullback (pullback.fst Q Q ≫ Q) s),
        (pullback.snd (pullback.fst Q Q ≫ Q) s).base z' = p → (mT gN L R' g s U).1.base z' ∈ V := by
  rw [mT_eq gN L R' g s U t x hx φ hφ₁ hφ₂, GoodReductionJacobian.schemeHomOverComp_coe, Set.range_subset_iff]
  constructor
  · rintro h _ ⟨t', rfl⟩ z' hz'
    obtain ⟨z, rfl⟩ := exists_Φ_eq R' s t x hx t' z' hz'
    have := h z
    rwa [Scheme.Hom.comp_apply] at this
  · intro h z
    rw [Scheme.Hom.comp_apply]
    refine h _ ⟨(pullback.snd (pullback.fst Q Q ≫ Q) t).base z, rfl⟩ _ ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    congr 1
    simp

include hφ₁ hφ₂ in

theorem pb₁_eq_mT_iff :
    pb₁ gN R' t (hx_pt gN R' s U t φ hφ₁) = mT gN L R' g t (hx_pt gN R' s U t φ hφ₁) ↔
      Φ R' s t x hx ≫ (pb₁ gN R' s U).1 = Φ R' s t x hx ≫ (mT gN L R' g s U).1 := by
  rw [pb₁_eq gN R' s U t x hx φ hφ₁ hφ₂, mT_eq gN L R' g s U t x hx φ hφ₁ hφ₂, Subtype.ext_iff]
  exact Iff.rfl

end Master

section Decode

variable {R : Type} [CommRing R] {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R))
  (R' : Type) [CommRing R'] [Algebra R R']
  (A₀ : Type) [CommRing A₀] [Algebra R A₀]
  (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
  (W₁ : Type) [CommRing W₁] [Algebra R W₁]
  (υ₁ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) ⟶
    Spec (CommRingCat.of (R' ⊗[R] A₀)))
  (hυ₁ : υ₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A₀))) = pullback.fst _ _)

set_option hygiene false in
local notation "Q" => Spec.map (CommRingCat.ofHom (algebraMap R R'))
set_option hygiene false in
local notation "RES₁" => Spec.map (CommRingCat.ofHom (algebraMap R W₁))
set_option hygiene false in
local notation "SA" => Spec.map (CommRingCat.ofHom (algebraMap R A₀))

abbrev y₁Of {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : pullback Q t ⟶ Spec (CommRingCat.of A₀))
    (ha : a ≫ SA = pullback.fst Q t ≫ Q) :
    SchemeHomOver (pullback.fst Q t) (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A₀)))) :=
  ⟨pullback.lift (pullback.fst Q t) a ha.symm ≫ (pullbackSpecIso R R' A₀).hom, by
    rw [Category.assoc, pullbackSpecIso_hom_fst', pullback.lift_fst]⟩

include hυ₁ in

theorem comp_υ₁_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (θ : pullback Q t ⟶ pullback Q RES₁)
    (hθ : θ ≫ pullback.fst _ _ = pullback.fst _ _) (a : pullback Q t ⟶ Spec (CommRingCat.of A₀))
    (ha : a ≫ SA = pullback.fst Q t ≫ Q) (h : θ ≫ u₁ R' A₀ j W₁ υ₁ = a ≫ j) :
    θ ≫ υ₁ = (y₁Of R' A₀ t a ha).1 := by
  change θ ≫ υ₁ = pullback.lift (pullback.fst Q t) a ha.symm ≫ (pullbackSpecIso R R' A₀).hom
  rw [← Iso.comp_inv_eq]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst']
    rw [hυ₁, hθ]
  · rw [pullback.lift_snd]
    apply (cancel_mono j).mp
    simpa only [u₁, Category.assoc] using h

omit [IsOpenImmersion j] in

theorem comp_u₁_eq {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (θ : pullback Q t ⟶ pullback Q RES₁)
    (a : pullback Q t ⟶ Spec (CommRingCat.of A₀)) (ha : a ≫ SA = pullback.fst Q t ≫ Q)
    (h : θ ≫ υ₁ = (y₁Of R' A₀ t a ha).1) : θ ≫ u₁ R' A₀ j W₁ υ₁ = a ≫ j := by
  rw [u₁, ← Category.assoc, h]
  simp

end Decode

section Two

variable (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'] (A₀ : Type) [CommRing A₀] [Algebra R A₀]

set_option hygiene false in
local notation "Q" => Spec.map (CommRingCat.ofHom (algebraMap R R'))
set_option hygiene false in
local notation "Q₂" => Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))
set_option hygiene false in
local notation "SA" => Spec.map (CommRingCat.ofHom (algebraMap R A₀))

omit [Algebra R A₀] in
theorem iso_inv_fst_Q : (pullbackSpecIso R R' R').inv ≫ pullback.fst Q Q ≫ Q = Q₂ := by
  rw [pullbackSpecIso_inv_fst'_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

omit [Algebra R A₀] in
theorem iso_hom_Q₂ : (pullbackSpecIso R R' R').hom ≫ Q₂ = pullback.fst Q Q ≫ Q := by
  rw [← iso_inv_fst_Q, Iso.hom_inv_id_assoc]

abbrev eInv {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) :
    pullback Q₂ s ⟶ pullback (pullback.fst Q Q ≫ Q) s :=
  pullback.map Q₂ s (pullback.fst Q Q ≫ Q) s (pullbackSpecIso R R' R').inv (𝟙 S) (𝟙 _)
    (by rw [Category.comp_id, iso_inv_fst_Q]) (by simp)

abbrev eHom {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.fst Q Q ≫ Q) s ⟶ pullback Q₂ s :=
  pullback.map (pullback.fst Q Q ≫ Q) s Q₂ s (pullbackSpecIso R R' R').hom (𝟙 S) (𝟙 _)
    (by rw [Category.comp_id, iso_hom_Q₂]) (by simp)

omit [Algebra R A₀] in
theorem eHom_eInv {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) : eHom R R' s ≫ eInv R R' s = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

omit [Algebra R A₀] in
theorem eInv_eHom {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) : eInv R R' s ≫ eHom R R' s = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

scoped instance {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) : IsIso (eInv R R' s) :=
  ⟨eHom R R' s, eInv_eHom R R' s, eHom_eInv R R' s⟩

abbrev yOf {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) (c : pullback (pullback.fst Q Q ≫ Q) s ⟶ Spec (CommRingCat.of A₀))
    (hc : c ≫ SA = pullback.fst (pullback.fst Q Q ≫ Q) s ≫ pullback.fst Q Q ≫ Q) :
    SchemeHomOver (pullback.fst Q₂ s)
      (Spec.map (CommRingCat.ofHom (R := R' ⊗[R] R') (S := (R' ⊗[R] R') ⊗[R] A₀) (algebraMap _ _))) :=
  ⟨pullback.lift (pullback.fst Q₂ s) (eInv R R' s ≫ c)
      (by rw [Category.assoc, hc, pullback.lift_fst_assoc, Category.assoc, iso_inv_fst_Q]) ≫
      (pullbackSpecIso R (R' ⊗[R] R') A₀).hom,
    by rw [Category.assoc, pullbackSpecIso_hom_fst', pullback.lift_fst]⟩

theorem comp_yOf_eq_iff {S X : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R))
    (c₁ c₂ : pullback (pullback.fst Q Q ≫ Q) s ⟶ Spec (CommRingCat.of A₀))
    (hc₁ : c₁ ≫ SA = pullback.fst (pullback.fst Q Q ≫ Q) s ≫ pullback.fst Q Q ≫ Q)
    (hc₂ : c₂ ≫ SA = pullback.fst (pullback.fst Q Q ≫ Q) s ≫ pullback.fst Q Q ≫ Q)
    (ψ : X ⟶ pullback Q₂ s) :
    ψ ≫ (yOf R R' A₀ s c₁ hc₁).1 = ψ ≫ (yOf R R' A₀ s c₂ hc₂).1 ↔ ψ ≫ eInv R R' s ≫ c₁ = ψ ≫ eInv R R' s ≫ c₂ := by
  constructor
  · intro h
    have h' := congrArg (· ≫ (pullbackSpecIso R (R' ⊗[R] R') A₀).inv ≫ pullback.snd _ _) h
    simpa using h'
  · intro h
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp
    · simpa using h

theorem ψ_eInv {S T : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R)) (x : T ⟶ S)
    (hx : x ≫ s = t) :
    pullback.lift (pullback.fst Q₂ t) (pullback.snd Q₂ t ≫ x) (by rw [Category.assoc, hx, pullback.condition]) ≫ eInv R R' s =
      eInv R R' t ≫ pullback.map (pullback.fst Q Q ≫ Q) t (pullback.fst Q Q ≫ Q) s (𝟙 _) x (𝟙 _) (by simp) (by simpa using hx.symm) := by
  apply pullback.hom_ext <;> simp

end Two

end

end SolRepAe361a2e
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique.SolRepAe361a2e"

open SolRepAe361a2e in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN) :
    ∃ (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN),
      (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))) ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h := by
  subst hq
  classical

  obtain ⟨W₁, iW₁, iA₁, -, υ₁, hυ₁, huniv₁⟩ :=
    AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique R R' (R' ⊗[R] A₀)
  letI := iW₁; letI := iA₁
  let U₁ : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R'))) gN := SolRepAe361a2e.U₁ gN R' A₀ j hj W₁ υ₁ hυ₁
  have hU₁ : U₁.1 = u₁ R' A₀ j W₁ υ₁ := rfl

  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let π := pullback.snd (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁)))
  haveI : UniversallyClosed π := inferInstance
  let mRes := mT gN L R' g (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) U₁
  have hΩ : IsOpen {p : ↥(Spec (CommRingCat.of W₁)) | ∀ z, π.base z = p → mRes.1.base z ∈ Set.range j.base} :=
    AlgebraicGeometry.isOpen_setOf_forall_preimage_mem_of_universallyClosed π mRes.1 j.opensRange
  let Ω : (Spec (CommRingCat.of W₁)).Opens := ⟨_, hΩ⟩
  let sΩ : (Ω : Scheme.{0}) ⟶ Spec (CommRingCat.of R) := Ω.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R W₁))
  let φΩ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) sΩ ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) :=
    pullback.map _ _ _ _ (𝟙 _) Ω.ι (𝟙 _) (by simp) (Category.comp_id _)
  let UΩ : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) sΩ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R'))) gN :=
    hx_pt gN R' (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) U₁ sΩ φΩ (by simp [φΩ])

  have hc₁r : Set.range (pb₁ gN R' sΩ UΩ).1.base ⊆ Set.range j.base := by
    have e : (pb₁ gN R' sΩ UΩ).1 = (pr₁ R' sΩ ≫ φΩ) ≫ u₁ R' A₀ j W₁ υ₁ := (Category.assoc _ _ _).symm
    rw [e]
    exact (range_comp_subset _ _).trans (range_u₁_subset R' A₀ j W₁ υ₁)
  have hc₂r : Set.range (mT gN L R' g sΩ UΩ).1.base ⊆ Set.range j.base := by
    rw [range_mT_subset_iff gN L R' g (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) U₁ sΩ Ω.ι rfl φΩ (by simp [φΩ])
      (by simp [φΩ]) (Set.range j.base)]
    intro p hp
    rw [Scheme.Opens.range_ι] at hp
    exact hp
  let c₁ := IsOpenImmersion.lift j _ hc₁r
  have hc₁j : c₁ ≫ j = (pb₁ gN R' sΩ UΩ).1 := IsOpenImmersion.lift_fac _ _ _
  let c₂ := IsOpenImmersion.lift j _ hc₂r
  have hc₂j : c₂ ≫ j = (mT gN L R' g sΩ UΩ).1 := IsOpenImmersion.lift_fac _ _ _
  have hc₁ : c₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = pullback.fst _ sΩ ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [← hj, ← Category.assoc, hc₁j]; exact (pb₁ gN R' sΩ UΩ).2
  have hc₂ : c₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) = pullback.fst _ sΩ ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [← hj, ← Category.assoc, hc₂j]; exact (mT gN L R' g sΩ UΩ).2

  obtain ⟨W₂, iW₂, iA₂, -, υ₂, hυ₂, huniv₂⟩ :=
    AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique R (R' ⊗[R] R') ((R' ⊗[R] R') ⊗[R] A₀)
  letI := iW₂; letI := iA₂
  obtain ⟨f₁, hf₁, -⟩ := huniv₂ Ω sΩ (yOf R R' A₀ sΩ c₁ hc₁)
  obtain ⟨f₂, hf₂, -⟩ := huniv₂ Ω sΩ (yOf R R' A₀ sΩ c₂ hc₂)

  have key : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (xΩ : T ⟶ Ω) (hx : xΩ ≫ sΩ = t),
      Φ R' sΩ t xΩ hx ≫ c₁ = Φ R' sΩ t xΩ hx ≫ c₂ ↔ xΩ ≫ f₁.1 = xΩ ≫ f₂.1 := by
    intro T t xΩ hx
    let ψ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t ⟶
        pullback (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) sΩ :=
      pullback.lift (pullback.fst _ t) (pullback.snd _ t ≫ xΩ) (by rw [Category.assoc, hx, pullback.condition])
    have hψ := ψ_eInv R R' sΩ t xΩ hx

    let z₁ : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W₂))) := ⟨xΩ ≫ f₁.1, by rw [Category.assoc, f₁.2, hx]⟩
    let z₂ : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W₂))) := ⟨xΩ ≫ f₂.1, by rw [Category.assoc, f₂.2, hx]⟩
    have e1 : pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t)
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t ≫ z₁.1)
          (by rw [Category.assoc, z₁.2, pullback.condition]) ≫ υ₂ = ψ ≫ (yOf R R' A₀ sΩ c₁ hc₁).1 := by
      rw [← hf₁, ← Category.assoc ψ _ υ₂]
      congr 1
      apply pullback.hom_ext <;> simp [ψ, z₁]
    have e2 : pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t)
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t ≫ z₂.1)
          (by rw [Category.assoc, z₂.2, pullback.condition]) ≫ υ₂ = ψ ≫ (yOf R R' A₀ sΩ c₂ hc₂).1 := by
      rw [← hf₂, ← Category.assoc ψ _ υ₂]
      congr 1
      apply pullback.hom_ext <;> simp [ψ, z₂]
    have hr₁ : ψ ≫ eInv R R' sΩ ≫ c₁ = eInv R R' t ≫ Φ R' sΩ t xΩ hx ≫ c₁ := (reassoc_of% hψ) c₁
    have hr₂ : ψ ≫ eInv R R' sΩ ≫ c₂ = eInv R R' t ≫ Φ R' sΩ t xΩ hx ≫ c₂ := (reassoc_of% hψ) c₂
    rw [← cancel_epi (eInv R R' t), ← hr₁, ← hr₂, ← comp_yOf_eq_iff R R' A₀ sΩ c₁ c₂ hc₁ hc₂ ψ]
    constructor
    · intro hy
      let y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R' ⊗[R] R')))) t)
          (Spec.map (CommRingCat.ofHom (R := R' ⊗[R] R') (S := (R' ⊗[R] R') ⊗[R] A₀) (algebraMap _ _))) :=
        ⟨ψ ≫ (yOf R R' A₀ sΩ c₁ hc₁).1, by rw [Category.assoc, (yOf R R' A₀ sΩ c₁ hc₁).2, pullback.lift_fst]⟩
      obtain ⟨z, -, huq⟩ := huniv₂ T t y
      have hz₁ : z₁ = z := huq z₁ e1
      have hz₂ : z₂ = z := huq z₂ (e2.trans hy.symm)
      exact (congrArg Subtype.val hz₁).trans (congrArg Subtype.val hz₂).symm
    · intro hz
      have : z₁ = z₂ := Subtype.ext hz
      rw [← e1, ← e2, this]

  let ιP := equalizer.ι f₁.1 f₂.1
  let gP : equalizer f₁.1 f₂.1 ⟶ Spec (CommRingCat.of R) := ιP ≫ sΩ
  let φP : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) gP ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) sΩ :=
    pullback.map _ _ _ _ (𝟙 _) ιP (𝟙 _) (by simp) (Category.comp_id _)
  let u : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) gP ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R'))) gN := hx_pt gN R' sΩ UΩ gP φP (by simp [φP])
  refine ⟨equalizer f₁.1 f₂.1, gP, u, ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    have e : u.1 = (φP ≫ φΩ) ≫ u₁ R' A₀ j W₁ υ₁ := (Category.assoc _ _ _).symm
    rw [e]
    exact (range_comp_subset _ _).trans (range_u₁_subset R' A₀ j W₁ υ₁)
  ·
    change Set.range (mT gN L R' g gP u).1.base ⊆ Set.range j.base
    rw [range_mT_subset_iff gN L R' g sΩ UΩ gP ιP rfl φP (by simp [φP]) (by simp [φP]) (Set.range j.base)]
    intro p _ z' _
    exact hc₂r ⟨z', rfl⟩
  ·
    change pb₁ gN R' gP u = mT gN L R' g gP u
    rw [pb₁_eq_mT_iff gN L R' g sΩ UΩ gP ιP rfl φP (by simp [φP]) (by simp [φP]), ← hc₁j, ← hc₂j]
    have hk := (key gP ιP rfl).mpr (equalizer.condition f₁.1 f₂.1)
    exact (reassoc_of% hk) j

  rintro T t h ⟨h1, h2, h3⟩

  let a := IsOpenImmersion.lift j h.1 h1
  have haj : a ≫ j = h.1 := IsOpenImmersion.lift_fac _ _ _
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R A₀)) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [← hj, ← Category.assoc, haj]; exact h.2
  obtain ⟨x₁, hx₁, hx₁u⟩ := huniv₁ T t (y₁Of R' A₀ t a ha)
  let θ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) :=
    pullback.lift (pullback.fst _ t) (pullback.snd _ t ≫ x₁.1) (by rw [Category.assoc, x₁.2, pullback.condition])
  have hθu : θ ≫ u₁ R' A₀ j W₁ υ₁ = a ≫ j := comp_u₁_eq R' A₀ j W₁ υ₁ t θ a ha hx₁

  have hhθ : h = hx_pt gN R' (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) U₁ t θ (by simp [θ]) :=
    Subtype.ext (by rw [GoodReductionJacobian.schemeHomOverComp_coe, hU₁, hθu, haj])
  have hΩx : Set.range x₁.1.base ⊆ (Ω : Set ↥(Spec (CommRingCat.of W₁))) := by
    have h2' := h2
    rw [hhθ] at h2'
    rw [range_mT_subset_iff gN L R' g (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) U₁ t x₁.1 x₁.2 θ (by simp [θ]) (by simp [θ])
      (Set.range j.base)] at h2'
    intro p hp
    exact h2' p hp
  let xΩ : T ⟶ Ω := IsOpenImmersion.lift Ω.ι x₁.1 (by rw [Scheme.Opens.range_ι]; exact hΩx)
  have hxΩ : xΩ ≫ Ω.ι = x₁.1 := IsOpenImmersion.lift_fac _ _ _
  have hxt : xΩ ≫ sΩ = t := by rw [← Category.assoc, hxΩ]; exact x₁.2

  let φT : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) sΩ :=
    pullback.map _ _ _ _ (𝟙 _) xΩ (𝟙 _) (by simp) (by simpa using hxt.symm)
  have hθφ : θ = φT ≫ φΩ := by
    apply pullback.hom_ext
    · simp [θ, φT, φΩ]
    · simp [θ, φT, φΩ, hxΩ]
  have hhΩ : h = hx_pt gN R' sΩ UΩ t φT (by simp [φT]) := by
    rw [hhθ]
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, hθφ, Category.assoc]
    rfl

  have heq : xΩ ≫ f₁.1 = xΩ ≫ f₂.1 := by
    rw [← key t xΩ hxt, ← cancel_mono j, Category.assoc, Category.assoc, hc₁j, hc₂j,
      ← pb₁_eq_mT_iff gN L R' g sΩ UΩ t xΩ hxt φT (by simp [φT]) (by simp [φT]), ← hhΩ]
    exact h3
  let xP : T ⟶ equalizer f₁.1 f₂.1 := equalizer.lift xΩ heq
  have hxP : xP ≫ ιP = xΩ := equalizer.lift_ι _ _
  refine ⟨⟨xP, by rw [← Category.assoc, hxP, hxt]⟩, ?_, ?_⟩
  ·
    rw [hhθ]
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, hU₁]
    change pullback.map _ _ _ _ _ xP _ _ _ ≫ φP ≫ φΩ ≫ u₁ R' A₀ j W₁ υ₁ = θ ≫ u₁ R' A₀ j W₁ υ₁
    have hmaps : pullback.map _ _ _ _ (𝟙 _) xP (𝟙 _) (by simp)
        (by simpa using (show xP ≫ gP = t by rw [← Category.assoc, hxP, hxt]).symm) ≫ φP = φT := by
      apply pullback.hom_ext
      · simp [φP, φT]
      · simp [φP, φT, ← hxP]
    rw [hθφ]
    exact ((reassoc_of% hmaps) (φΩ ≫ u₁ R' A₀ j W₁ υ₁)).trans (Category.assoc _ _ _).symm
  ·
    intro x' hx'
    apply Subtype.ext

    let θ' : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ⟶
        pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) :=
      pullback.lift (pullback.fst _ t) (pullback.snd _ t ≫ x'.1 ≫ ιP ≫ Ω.ι)
        (by simp only [Category.assoc]; rw [pullback.condition]; congr 1; exact x'.2.symm)
    have hθ' : θ' = pullback.map _ _ _ _ (𝟙 _) x'.1 (𝟙 _) (by simp) (by simpa using x'.2.symm) ≫ φP ≫ φΩ := by
      apply pullback.hom_ext
      · simp [θ', φP, φΩ]
      · simp [θ', φP, φΩ]
    have hθ'u : θ' ≫ u₁ R' A₀ j W₁ υ₁ = a ≫ j := by
      rw [hθ', haj, ← hU₁]
      have := congrArg Subtype.val hx'
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at this
      exact this
    have hθ'υ := comp_υ₁_eq R' A₀ j W₁ υ₁ hυ₁ t θ' (by simp [θ']) a ha hθ'u
    let w : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W₁))) :=
      ⟨x'.1 ≫ ιP ≫ Ω.ι, by simpa only [Category.assoc] using x'.2⟩
    have hw : w = x₁ := hx₁u w hθ'υ
    have h1' : x'.1 ≫ ιP = xΩ := by
      rw [← cancel_mono Ω.ι, Category.assoc, hxΩ]
      exact congrArg Subtype.val hw
    apply equalizer.hom_ext
    rw [h1', hxP]

end S_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_solutionScheme_existsUnique (solution)
