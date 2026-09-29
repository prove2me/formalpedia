-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1c20bbcb-6645-59f4-aeb8-f53baadcdd74

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_eq_snd_comp_of_comp_eq_const_of_isProper
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_baseChange_of_field
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace RIG17

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem one_eq_of_val_eq (L L' : RelativeGroupLaw R f)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : L.one t = L'.one t := by
  apply Subtype.ext
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  have h' := L'.one_natural (𝟙 (Spec (CommRingCat.of R))) t t (Category.comp_id t)
  rw [← h, ← h']
  change t ≫ (L.one (𝟙 _)).1 = t ≫ (L'.one (𝟙 _)).1
  rw [h1]

theorem inv_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) * GoodReductionJacobian.schemeHomOverComp ψ hψ x = 1 := by
    change G.mul t' _ _ = G.one t'
    rw [← G.mul_natural t t' ψ hψ, G.inv_mul_cancel, G.one_natural t t' ψ hψ]
  exact eq_inv_of_mul_eq_one_left h

def Phi (L L' : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t f) :
    SchemeHomOver t f :=
  L'.mul t (L.mul t a b) (L'.inv t (L'.mul t a b))

theorem Phi_natural (L L' : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a b : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (Phi L L' t a b) =
      Phi L L' t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) (GoodReductionJacobian.schemeHomOverComp ψ hψ b) := by
  unfold Phi
  rw [L'.mul_natural, L.mul_natural, inv_natural, L'.mul_natural]

theorem mul_eq_of_Phi_eq_one (L L' : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a b : SchemeHomOver t f) (h : Phi L L' t a b = L'.one t) : L.mul t a b = L'.mul t a b := by
  letI := L'.pointGroup t
  have h' : L.mul t a b * (L'.mul t a b)⁻¹ = 1 := h
  exact mul_inv_eq_one.mp h'

theorem Phi_one_right (L L' : RelativeGroupLaw R f)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t f) :
    Phi L L' t a (L.one t) = L'.one t := by
  unfold Phi
  rw [L.mul_one, one_eq_of_val_eq L L' h1, L'.mul_one]
  exact L'.mul_inv_cancel t a

theorem Phi_one_left (L L' : RelativeGroupLaw R f)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t f) :
    Phi L L' t (L.one t) b = L'.one t := by
  unfold Phi
  rw [L.one_mul, one_eq_of_val_eq L L' h1, L'.one_mul]
  exact L'.mul_inv_cancel t b

section Field

variable {K : Type u} [Field K] {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of K)}

theorem one_val (G : RelativeGroupLaw K g) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem mul_eq_mul_of_field (hY : AbelianSchemePropertyBundle K g) (L L' : RelativeGroupLaw K g)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of K)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of K)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a b : SchemeHomOver t g) :
    L.mul t a b = L'.mul t a b := by
  haveI : IsProper g := hY.proper
  haveI : IsIntegral Y := hY.isIntegral_of_field
  haveI : IsSeparated g := inferInstance
  have hconn : ConnectedSpace ↥Y := inferInstance

  let e : Spec (CommRingCat.of K) ⟶ Y := (L.one (𝟙 _)).1
  have he : e ≫ g = 𝟙 _ := (L.one (𝟙 _)).2

  let pP : pullback g g ⟶ Spec (CommRingCat.of K) := pullback.fst g g ≫ g
  let P1 : SchemeHomOver pP g := ⟨pullback.fst g g, rfl⟩
  let P2 : SchemeHomOver pP g := ⟨pullback.snd g g, pullback.condition.symm⟩
  let φ : pullback g g ⟶ Y := (Phi L L' pP P1 P2).1
  have hφ : φ ≫ g = pullback.fst g g ≫ g := (Phi L L' pP P1 P2).2

  have key : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver s g),
      (Phi L L' s x y).1 = pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ φ := by
    intro S s x y
    have hxy : pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ pP = s := by
      change pullback.lift x.1 y.1 _ ≫ pullback.fst g g ≫ g = s
      rw [pullback.lift_fst_assoc]; exact x.2
    have hn := Phi_natural L L' pP s (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hxy P1 P2
    have e1 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hxy P1 = x :=
      Subtype.ext (pullback.lift_fst _ _ _)
    have e2 : GoodReductionJacobian.schemeHomOverComp (pullback.lift x.1 y.1 (x.2.trans y.2.symm)) hxy P2 = y :=
      Subtype.ext (pullback.lift_snd _ _ _)
    rw [e1, e2] at hn
    rw [← hn]
    rfl

  have hslice1 : pullback.lift (𝟙 Y) (g ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ≫ φ = g ≫ e := by
    have hx : (⟨𝟙 Y, Category.id_comp g⟩ : SchemeHomOver g g) = ⟨𝟙 Y, Category.id_comp g⟩ := rfl
    have k := key g ⟨𝟙 Y, Category.id_comp g⟩ (L.one g)
    have hv : (L.one g).1 = g ≫ e := one_val L g
    have hp : Phi L L' g ⟨𝟙 Y, Category.id_comp g⟩ (L.one g) = L'.one g := Phi_one_right L L' h1 g _
    rw [hp] at k
    have hv' : (L'.one g).1 = g ≫ e := by rw [one_val L' g]; change g ≫ (L'.one (𝟙 _)).1 = g ≫ (L.one (𝟙 _)).1; rw [h1]
    rw [hv'] at k

    refine Eq.trans ?_ k.symm
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst]
    · rw [pullback.lift_snd, pullback.lift_snd, hv]

  have hrig := AlgebraicGeometry.exists_eq_snd_comp_of_comp_eq_const_of_isProper K g g hconn g e he e he φ hφ e hslice1

  have hslice2 : pullback.lift (g ≫ e) (𝟙 Y) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp]) ≫ φ = g ≫ e := by
    have k := key g (L.one g) ⟨𝟙 Y, Category.id_comp g⟩
    have hv : (L.one g).1 = g ≫ e := one_val L g
    have hp : Phi L L' g (L.one g) ⟨𝟙 Y, Category.id_comp g⟩ = L'.one g := Phi_one_left L L' h1 g _
    rw [hp] at k
    have hv' : (L'.one g).1 = g ≫ e := by rw [one_val L' g]; change g ≫ (L'.one (𝟙 _)).1 = g ≫ (L.one (𝟙 _)).1; rw [h1]
    rw [hv'] at k
    refine Eq.trans ?_ k.symm
    congr 1
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst, hv]
    · rw [pullback.lift_snd, pullback.lift_snd]
  have hconst : φ = pP ≫ e := by
    rw [hrig, hslice2]
    change pullback.snd g g ≫ g ≫ e = (pullback.fst g g ≫ g) ≫ e
    rw [← Category.assoc, pullback.condition]

  apply mul_eq_of_Phi_eq_one
  apply Subtype.ext
  rw [key t a b, hconst, ← Category.assoc]
  have hab : pullback.lift a.1 b.1 (a.2.trans b.2.symm) ≫ pP = t := by
    change pullback.lift a.1 b.1 _ ≫ pullback.fst g g ≫ g = t
    rw [pullback.lift_fst_assoc]; exact a.2
  rw [hab, one_val L' t]
  change t ≫ (L.one (𝟙 _)).1 = t ≫ (L'.one (𝟙 _)).1
  rw [h1]

end Field

end RIG17

open RIG17 in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (hX : AbelianSchemePropertyBundle R f) (L L' : RelativeGroupLaw R f)
    (h1 : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = (L'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f) :
    L.mul s x y = L'.mul s x y := by
  classical
  let K := FractionRing R
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) := specGenericFibreInclusion R K
  haveI : IsProper f := hX.proper
  haveI : IsSeparated f := inferInstance
  haveI : Smooth f := hX.smooth
  haveI : Flat f := inferInstance

  have hK : AbelianSchemePropertyBundle K (RelativeGroupLaw.baseChangeStr ι f) := hX.baseChange_of_field ι
  have h1K : ((L.baseChange ι).one (𝟙 _)).1 = ((L'.baseChange ι).one (𝟙 _)).1 := by
    rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChange_one, one_eq_of_val_eq L L' h1]
  have hgen : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver (s ≫ ι) f),
      L.mul _ x y = L'.mul _ x y := by
    intro S s x y
    have h := mul_eq_mul_of_field hK (L.baseChange ι) (L'.baseChange ι) h1K s
      (RelativeGroupLaw.baseChangePointOfBase ι x) (RelativeGroupLaw.baseChangePointOfBase ι y)
    have h' := congrArg (RelativeGroupLaw.baseChangePointToBase ι) h
    rw [RelativeGroupLaw.baseChangePointToBase_mul, RelativeGroupLaw.baseChangePointToBase_mul,
      RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase] at h'
    exact h'

  have hsp := GoodReductionJacobian.RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre R K L' L
    (⟨𝟙 X, Category.id_comp f⟩ : SchemeHomOver f f)
    (fun s x y => by
      have hx : (⟨x.1 ≫ 𝟙 X, by rw [Category.assoc, Category.id_comp f, x.2]⟩ : SchemeHomOver _ f) = x :=
        Subtype.ext (Category.comp_id _)
      have hy : (⟨y.1 ≫ 𝟙 X, by rw [Category.assoc, Category.id_comp f, y.2]⟩ : SchemeHomOver _ f) = y :=
        Subtype.ext (Category.comp_id _)
      rw [hx, hy, Category.comp_id]
      exact congrArg Subtype.val (hgen s x y))
    s x y
  have hx : (⟨x.1 ≫ 𝟙 X, by rw [Category.assoc, Category.id_comp f, x.2]⟩ : SchemeHomOver s f) = x :=
    Subtype.ext (Category.comp_id _)
  have hy : (⟨y.1 ≫ 𝟙 X, by rw [Category.assoc, Category.id_comp f, y.2]⟩ : SchemeHomOver s f) = y :=
    Subtype.ext (Category.comp_id _)
  rw [hx, hy, Category.comp_id] at hsp
  exact Subtype.ext hsp

end S_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_mul_eq_mul_of_one_eq_of_abelianSchemePropertyBundle (solution)
