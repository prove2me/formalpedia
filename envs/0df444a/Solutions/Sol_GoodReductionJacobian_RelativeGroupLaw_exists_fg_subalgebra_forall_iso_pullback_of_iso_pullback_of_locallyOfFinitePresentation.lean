-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4fe59178-066b-5076-83f2-b6f5b318ba11

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw.baseChangePointToBase_coe RelativeGroupLaw.baseChangePointToBase_mul schemeHomOverComp RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "baseChangePointToBase_coe baseChange baseChangePointToBase_mul pointGroup one_natural one mul_natural inv inv_mul_cancel mul fibre"
namespace IsoLawDescent
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Presentations

variable {X S : Scheme.{u}} (f : X ⟶ S)

abbrev W₂ : Scheme.{u} := pullback f f

abbrev w₂ : W₂ f ⟶ S := pullback.fst f f ≫ f

abbrev W₃ : Scheme.{u} := pullback (w₂ f) f

abbrev w₃ : W₃ f ⟶ S := pullback.fst (w₂ f) f ≫ w₂ f

variable {B : Scheme.{u}} (b : B ⟶ S)

abbrev Yb : Scheme.{u} := pullback f b

abbrev fb : Yb f b ⟶ B := pullback.snd f b

abbrev Q₂ : Scheme.{u} := pullback (w₂ f) b

abbrev Q₃ : Scheme.{u} := pullback (w₃ f) b

def p₁ : Q₂ f b ⟶ Yb f b :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)

def p₂ : Q₂ f b ⟶ Yb f b :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd f f) (pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition (f := f) (g := f)]; exact pullback.condition)

@[scoped simp, reassoc] theorem p₁_fst : p₁ f b ≫ pullback.fst f b = pullback.fst _ _ ≫ pullback.fst f f := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem p₁_snd : p₁ f b ≫ pullback.snd f b = pullback.snd _ _ := pullback.lift_snd _ _ _
@[scoped simp, reassoc] theorem p₂_fst : p₂ f b ≫ pullback.fst f b = pullback.fst _ _ ≫ pullback.snd f f := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem p₂_snd : p₂ f b ≫ pullback.snd f b = pullback.snd _ _ := pullback.lift_snd _ _ _

variable {f b}

theorem pair_aux₁ {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    (x ≫ pullback.fst f b) ≫ f = (y ≫ pullback.fst f b) ≫ f := by
  have hx : (x ≫ pullback.fst f b) ≫ f = (x ≫ pullback.snd f b) ≫ b := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hy : (y ≫ pullback.fst f b) ≫ f = (y ≫ pullback.snd f b) ≫ b := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  rw [hx, hy]
  exact congrArg (· ≫ b) h

theorem pair_aux₂ {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pullback.lift (x ≫ pullback.fst f b) (y ≫ pullback.fst f b) (pair_aux₁ x y h) ≫ w₂ f = (x ≫ pullback.snd f b) ≫ b := by
  rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition]

def pair {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) : T ⟶ Q₂ f b :=
  pullback.lift (pullback.lift (x ≫ pullback.fst f b) (y ≫ pullback.fst f b) (pair_aux₁ x y h))
    (x ≫ pullback.snd f b) (pair_aux₂ x y h)

@[scoped simp, reassoc] theorem pair_fst_fst {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pair x y h ≫ pullback.fst _ _ ≫ pullback.fst f f = x ≫ pullback.fst f b := by
  simp only [pair, pullback.lift_fst_assoc, pullback.lift_fst]

@[scoped simp, reassoc] theorem pair_fst_snd {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pair x y h ≫ pullback.fst _ _ ≫ pullback.snd f f = y ≫ pullback.fst f b := by
  simp only [pair, pullback.lift_fst_assoc, pullback.lift_snd]

@[scoped simp, reassoc] theorem pair_snd {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pair x y h ≫ pullback.snd _ _ = x ≫ pullback.snd f b := by
  simp only [pair, pullback.lift_snd]

@[scoped simp, reassoc] theorem pair_p₁ {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pair x y h ≫ p₁ f b = x := by
  apply pullback.hom_ext
  · rw [Category.assoc, p₁_fst, pair_fst_fst]
  · rw [Category.assoc, p₁_snd, pair_snd]

@[scoped simp, reassoc] theorem pair_p₂ {T : Scheme.{u}} (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    pair x y h ≫ p₂ f b = y := by
  apply pullback.hom_ext
  · rw [Category.assoc, p₂_fst, pair_fst_snd]
  · rw [Category.assoc, p₂_snd, pair_snd]
    exact h

theorem hom_ext₂ {T : Scheme.{u}} {k k' : T ⟶ Q₂ f b} (h₁ : k ≫ p₁ f b = k' ≫ p₁ f b) (h₂ : k ≫ p₂ f b = k' ≫ p₂ f b) :
    k = k' := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, p₁_fst] using congrArg (· ≫ pullback.fst f b) h₁
    · simpa only [Category.assoc, p₂_fst] using congrArg (· ≫ pullback.fst f b) h₂
  · simpa only [Category.assoc, p₁_snd] using congrArg (· ≫ pullback.snd f b) h₁

variable (f b)

@[reassoc] theorem p₁_fb : p₁ f b ≫ fb f b = pullback.snd _ _ := p₁_snd f b
@[reassoc] theorem p₂_fb : p₂ f b ≫ fb f b = pullback.snd _ _ := p₂_snd f b
theorem p₁_fb_eq_p₂_fb : p₁ f b ≫ fb f b = p₂ f b ≫ fb f b := by rw [p₁_fb, p₂_fb]

theorem pair_p₁_p₂ : pair (p₁ f b) (p₂ f b) (p₁_fb_eq_p₂_fb f b) = 𝟙 _ :=
  hom_ext₂ (by rw [pair_p₁, Category.id_comp]) (by rw [pair_p₂, Category.id_comp])

variable {f b}

@[reassoc] theorem comp_pair {T T' : Scheme.{u}} (k : T' ⟶ T) (x y : T ⟶ Yb f b) (h : x ≫ fb f b = y ≫ fb f b) :
    k ≫ pair x y h = pair (k ≫ x) (k ≫ y) (by rw [Category.assoc, Category.assoc, h]) :=
  hom_ext₂ (by rw [Category.assoc, pair_p₁, pair_p₁]) (by rw [Category.assoc, pair_p₂, pair_p₂])

variable (f b)

def q₁₂ : Q₃ f b ⟶ Q₂ f b :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)

def q₃ : Q₃ f b ⟶ Yb f b :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _)
    (by rw [Category.assoc, ← pullback.condition (f := w₂ f) (g := f)]; exact pullback.condition)

@[scoped simp, reassoc] theorem q₁₂_fst : q₁₂ f b ≫ pullback.fst (w₂ f) b = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem q₁₂_snd : q₁₂ f b ≫ pullback.snd (w₂ f) b = pullback.snd _ _ := pullback.lift_snd _ _ _
@[scoped simp, reassoc] theorem q₃_fst : q₃ f b ≫ pullback.fst f b = pullback.fst _ _ ≫ pullback.snd _ _ := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem q₃_snd : q₃ f b ≫ pullback.snd f b = pullback.snd _ _ := pullback.lift_snd _ _ _

@[reassoc] theorem q₁₂_p₁_fb : (q₁₂ f b ≫ p₁ f b) ≫ fb f b = pullback.snd _ _ := by
  rw [Category.assoc, p₁_fb, q₁₂_snd]
@[reassoc] theorem q₁₂_p₂_fb : (q₁₂ f b ≫ p₂ f b) ≫ fb f b = pullback.snd _ _ := by
  rw [Category.assoc, p₂_fb, q₁₂_snd]
@[reassoc] theorem q₃_fb : q₃ f b ≫ fb f b = pullback.snd _ _ := q₃_snd f b

variable {f b}

theorem triple_aux₁ {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) : (pair x y hxy ≫ pullback.fst _ _) ≫ w₂ f = (z ≫ pullback.fst f b) ≫ f := by
  have hz : (z ≫ pullback.fst f b) ≫ f = (z ≫ pullback.snd f b) ≫ b := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  rw [Category.assoc, pullback.condition, pair_snd_assoc, hz, Category.assoc]
  exact congrArg (· ≫ b) hxz

theorem triple_aux₂ {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) :
    pullback.lift (pair x y hxy ≫ pullback.fst _ _) (z ≫ pullback.fst f b) (triple_aux₁ x y z hxy hxz) ≫ w₃ f =
      (x ≫ pullback.snd f b) ≫ b := by
  rw [pullback.lift_fst_assoc, Category.assoc, pullback.condition, pair_snd_assoc, Category.assoc]

def triple {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b) (hxz : x ≫ fb f b = z ≫ fb f b) :
    T ⟶ Q₃ f b :=
  pullback.lift (pullback.lift (pair x y hxy ≫ pullback.fst _ _) (z ≫ pullback.fst f b) (triple_aux₁ x y z hxy hxz))
    (x ≫ pullback.snd f b) (triple_aux₂ x y z hxy hxz)

@[scoped simp, reassoc] theorem triple_fst_fst {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) :
    triple x y z hxy hxz ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pair x y hxy ≫ pullback.fst _ _ := by
  simp only [triple, pullback.lift_fst_assoc, pullback.lift_fst]

@[scoped simp, reassoc] theorem triple_fst_snd {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) :
    triple x y z hxy hxz ≫ pullback.fst _ _ ≫ pullback.snd _ _ = z ≫ pullback.fst f b := by
  simp only [triple, pullback.lift_fst_assoc, pullback.lift_snd]

@[scoped simp, reassoc] theorem triple_snd {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) :
    triple x y z hxy hxz ≫ pullback.snd _ _ = x ≫ pullback.snd f b := by
  simp only [triple, pullback.lift_snd]

@[scoped simp, reassoc] theorem triple_q₁₂ {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) : triple x y z hxy hxz ≫ q₁₂ f b = pair x y hxy := by
  apply pullback.hom_ext
  · rw [Category.assoc, q₁₂_fst, triple_fst_fst]
  · rw [Category.assoc, q₁₂_snd, triple_snd, pair_snd]

@[scoped simp, reassoc] theorem triple_q₃ {T : Scheme.{u}} (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) : triple x y z hxy hxz ≫ q₃ f b = z := by
  apply pullback.hom_ext
  · rw [Category.assoc, q₃_fst, triple_fst_snd]
  · rw [Category.assoc, q₃_snd, triple_snd]
    exact hxz

theorem hom_ext₃ {T : Scheme.{u}} {k k' : T ⟶ Q₃ f b} (h₁ : k ≫ q₁₂ f b = k' ≫ q₁₂ f b) (h₂ : k ≫ q₃ f b = k' ≫ q₃ f b) :
    k = k' := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, q₁₂_fst] using congrArg (· ≫ pullback.fst (w₂ f) b) h₁
    · simpa only [Category.assoc, q₃_fst] using congrArg (· ≫ pullback.fst f b) h₂
  · simpa only [Category.assoc, q₁₂_snd] using congrArg (· ≫ pullback.snd (w₂ f) b) h₁

variable (f b)

theorem triple_universal :
    triple (q₁₂ f b ≫ p₁ f b) (q₁₂ f b ≫ p₂ f b) (q₃ f b) (by rw [q₁₂_p₁_fb, q₁₂_p₂_fb]) (by rw [q₁₂_p₁_fb, q₃_fb]) = 𝟙 _ :=
  hom_ext₃ (by rw [triple_q₁₂, Category.id_comp]; exact hom_ext₂ (by rw [pair_p₁]) (by rw [pair_p₂]))
    (by rw [triple_q₃, Category.id_comp])

variable {f b}

@[reassoc] theorem comp_triple {T T' : Scheme.{u}} (k : T' ⟶ T) (x y z : T ⟶ Yb f b) (hxy : x ≫ fb f b = y ≫ fb f b)
    (hxz : x ≫ fb f b = z ≫ fb f b) :
    k ≫ triple x y z hxy hxz = triple (k ≫ x) (k ≫ y) (k ≫ z) (by rw [Category.assoc, Category.assoc, hxy])
      (by rw [Category.assoc, Category.assoc, hxz]) :=
  hom_ext₃ (by rw [Category.assoc, triple_q₁₂, triple_q₁₂, comp_pair]) (by rw [Category.assoc, triple_q₃, triple_q₃])

section Trans

variable {W B₁ B₂ : Scheme.{u}} (w : W ⟶ S) (b₁ : B₁ ⟶ S) (b₂ : B₂ ⟶ S) (u : B₂ ⟶ B₁) (hu : u ≫ b₁ = b₂)

def tW : pullback w b₂ ⟶ pullback w b₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ u) (by rw [Category.assoc, hu, pullback.condition])

@[scoped simp, reassoc] theorem tW_fst : tW w b₁ b₂ u hu ≫ pullback.fst w b₁ = pullback.fst w b₂ := pullback.lift_fst _ _ _
@[scoped simp, reassoc] theorem tW_snd : tW w b₁ b₂ u hu ≫ pullback.snd w b₁ = pullback.snd w b₂ ≫ u := pullback.lift_snd _ _ _

theorem eq_of_comp_tW_eq {T : Scheme.{u}} {k k' : T ⟶ pullback w b₂} (h₁ : k ≫ tW w b₁ b₂ u hu = k' ≫ tW w b₁ b₂ u hu)
    (h₂ : k ≫ pullback.snd w b₂ = k' ≫ pullback.snd w b₂) : k = k' := by
  apply pullback.hom_ext _ h₂
  simpa only [Category.assoc, tW_fst] using congrArg (· ≫ pullback.fst w b₁) h₁

@[reassoc] theorem tW_p₁ : tW (w₂ f) b₁ b₂ u hu ≫ p₁ f b₁ = p₁ f b₂ ≫ tW f b₁ b₂ u hu := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, p₁_fst, tW_fst_assoc, tW_fst, p₁_fst]
  · rw [Category.assoc, Category.assoc, p₁_snd, tW_snd, tW_snd, p₁_snd_assoc]

@[reassoc] theorem tW_p₂ : tW (w₂ f) b₁ b₂ u hu ≫ p₂ f b₁ = p₂ f b₂ ≫ tW f b₁ b₂ u hu := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, p₂_fst, tW_fst_assoc, tW_fst, p₂_fst]
  · rw [Category.assoc, Category.assoc, p₂_snd, tW_snd, tW_snd, p₂_snd_assoc]

@[reassoc] theorem tW_q₁₂ : tW (w₃ f) b₁ b₂ u hu ≫ q₁₂ f b₁ = q₁₂ f b₂ ≫ tW (w₂ f) b₁ b₂ u hu := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, q₁₂_fst, tW_fst_assoc, tW_fst, q₁₂_fst]
  · rw [Category.assoc, Category.assoc, q₁₂_snd, tW_snd, tW_snd, q₁₂_snd_assoc]

@[reassoc] theorem tW_q₃ : tW (w₃ f) b₁ b₂ u hu ≫ q₃ f b₁ = q₃ f b₂ ≫ tW f b₁ b₂ u hu := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, q₃_fst, tW_fst_assoc, tW_fst, q₃_fst]
  · rw [Category.assoc, Category.assoc, q₃_snd, tW_snd, tW_snd, q₃_snd_assoc]

@[reassoc] theorem tW_fb : tW f b₁ b₂ u hu ≫ fb f b₁ = fb f b₂ ≫ u := tW_snd f b₁ b₂ u hu

theorem pair_tW {T : Scheme.{u}} (x y : T ⟶ Yb f b₂) (h : x ≫ fb f b₂ = y ≫ fb f b₂) :
    pair (x ≫ tW f b₁ b₂ u hu) (y ≫ tW f b₁ b₂ u hu) (by rw [Category.assoc, Category.assoc, tW_fb, reassoc_of% h]) =
      pair x y h ≫ tW (w₂ f) b₁ b₂ u hu :=
  hom_ext₂ (by rw [pair_p₁, Category.assoc, tW_p₁, pair_p₁_assoc]) (by rw [pair_p₂, Category.assoc, tW_p₂, pair_p₂_assoc])

theorem triple_tW {T : Scheme.{u}} (x y z : T ⟶ Yb f b₂) (hxy : x ≫ fb f b₂ = y ≫ fb f b₂)
    (hxz : x ≫ fb f b₂ = z ≫ fb f b₂) :
    triple (x ≫ tW f b₁ b₂ u hu) (y ≫ tW f b₁ b₂ u hu) (z ≫ tW f b₁ b₂ u hu)
        (by rw [Category.assoc, Category.assoc, tW_fb, reassoc_of% hxy])
        (by rw [Category.assoc, Category.assoc, tW_fb, reassoc_of% hxz]) =
      triple x y z hxy hxz ≫ tW (w₃ f) b₁ b₂ u hu :=
  hom_ext₃ (by rw [triple_q₁₂, pair_tW, Category.assoc, tW_q₁₂, triple_q₁₂_assoc])
    (by rw [triple_q₃, Category.assoc, tW_q₃, triple_q₃_assoc])

end Trans

end Presentations

section Data

variable {X S : Scheme.{u}} (f : X ⟶ S) {B : Scheme.{u}} (b : B ⟶ S)

structure Dat where

  m : Q₂ f b ⟶ Yb f b

  e : B ⟶ Yb f b

  ι : Yb f b ⟶ Yb f b
  hm : m ≫ fb f b = pullback.snd _ _
  he : e ≫ fb f b = 𝟙 _
  hι : ι ≫ fb f b = fb f b

end Data

section Congr
variable {X S : Scheme.{u}} {f : X ⟶ S} {B : Scheme.{u}} {b : B ⟶ S}

theorem pair_congr {T : Scheme.{u}} {x y x' y' : T ⟶ Yb f b} (h : x ≫ fb f b = y ≫ fb f b) (h' : x' ≫ fb f b = y' ≫ fb f b)
    (hx : x = x') (hy : y = y') : pair x y h = pair x' y' h' := by
  subst hx; subst hy; rfl

end Congr

section OfLaw

variable {X S : Scheme.{u}} (f : X ⟶ S) {R' : Type u} [CommRing R'] (b : Spec (CommRingCat.of R') ⟶ S)

abbrev qb : Q₂ f b ⟶ Spec (CommRingCat.of R') := pullback.snd (w₂ f) b

def P₁ : SchemeHomOver (qb f b) (fb f b) := ⟨p₁ f b, p₁_fb f b⟩

def P₂ : SchemeHomOver (qb f b) (fb f b) := ⟨p₂ f b, p₂_fb f b⟩

def Pid : SchemeHomOver (fb f b) (fb f b) := ⟨𝟙 _, Category.id_comp _⟩

@[scoped simp] theorem P₁_val : (P₁ f b).1 = p₁ f b := rfl
@[scoped simp] theorem P₂_val : (P₂ f b).1 = p₂ f b := rfl
@[scoped simp] theorem Pid_val : (Pid f b).1 = 𝟙 _ := rfl

variable {f b} (L : RelativeGroupLaw R' (fb f b))

def ofLaw : Dat f b where
  m := (L.mul (qb f b) (P₁ f b) (P₂ f b)).1
  e := (L.one (𝟙 _)).1
  ι := (L.inv (fb f b) (Pid f b)).1
  hm := (L.mul (qb f b) (P₁ f b) (P₂ f b)).2
  he := (L.one (𝟙 _)).2
  hι := (L.inv (fb f b) (Pid f b)).2

theorem mul_fb_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')} (x y : SchemeHomOver t (fb f b)) :
    x.1 ≫ fb f b = y.1 ≫ fb f b := x.2.trans y.2.symm

theorem mul_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t (fb f b)) :
    (L.mul t x y).1 = pair x.1 y.1 (mul_fb_eq x y) ≫ (ofLaw L).m := by
  have hψ : pair x.1 y.1 (mul_fb_eq x y) ≫ qb f b = t := by rw [pair_snd]; exact x.2
  have h := L.mul_natural (qb f b) t (pair x.1 y.1 (mul_fb_eq x y)) hψ (P₁ f b) (P₂ f b)
  have hx : schemeHomOverComp (pair x.1 y.1 (mul_fb_eq x y)) hψ (P₁ f b) = x := Subtype.ext (pair_p₁ _ _ _)
  have hy : schemeHomOverComp (pair x.1 y.1 (mul_fb_eq x y)) hψ (P₂ f b) = y := Subtype.ext (pair_p₂ _ _ _)
  rw [hx, hy] at h
  rw [← h]
  rfl

theorem one_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) : (L.one t).1 = t ≫ (ofLaw L).e := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem inv_val {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t (fb f b)) :
    (L.inv t x).1 = x.1 ≫ (ofLaw L).ι := by
  letI := L.pointGroup t
  have hx : schemeHomOverComp x.1 x.2 (Pid f b) = x := Subtype.ext (Category.comp_id _)
  have hmul : L.mul t (schemeHomOverComp x.1 x.2 (L.inv (fb f b) (Pid f b))) x = L.one t := by
    have h0 : L.mul t (schemeHomOverComp x.1 x.2 (L.inv (fb f b) (Pid f b))) (schemeHomOverComp x.1 x.2 (Pid f b)) =
        L.one t := by
      rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
    rwa [hx] at h0
  have hinv : x⁻¹ = schemeHomOverComp x.1 x.2 (L.inv (fb f b) (Pid f b)) := inv_eq_of_mul_eq_one_left hmul
  exact congrArg Subtype.val hinv

theorem pair_P₁_P₂ : pair (P₁ f b).1 (P₂ f b).1 (mul_fb_eq (P₁ f b) (P₂ f b)) = 𝟙 _ := pair_p₁_p₂ f b

end OfLaw

section Rebase

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (a : S' ⟶ S) (b : S'' ⟶ S') (c : S'' ⟶ S) (h : b ≫ a = c)

include h in
theorem isPullback_paste :
    IsPullback (pullback.fst (pullback.snd f a) b ≫ pullback.fst f a) (pullback.snd (pullback.snd f a) b) f c := by
  rw [← h]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback f a)

def rebaseIso : pullback (pullback.snd f a) b ≅ pullback f c :=
  (isPullback_paste f a b c h).isoIsPullback _ _ (IsPullback.of_hasPullback f c)

@[scoped simp, reassoc] theorem rebaseIso_hom_snd : (rebaseIso f a b c h).hom ≫ pullback.snd f c = pullback.snd _ _ :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[scoped simp, reassoc] theorem rebaseIso_hom_fst :
    (rebaseIso f a b c h).hom ≫ pullback.fst f c = pullback.fst _ _ ≫ pullback.fst f a :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

theorem fst_eq_rebaseIso_hom_tW : pullback.fst (pullback.snd f a) b = (rebaseIso f a b c h).hom ≫ tW f a c b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, tW_fst, rebaseIso_hom_fst]
  · rw [Category.assoc, tW_snd, rebaseIso_hom_snd_assoc, pullback.condition]

end Rebase

section TransComp

variable {X S B₁ B₂ B₃ : Scheme.{u}} (w : X ⟶ S) (b₁ : B₁ ⟶ S) (b₂ : B₂ ⟶ S) (b₃ : B₃ ⟶ S)

theorem tW_comp (u : B₂ ⟶ B₁) (hu : u ≫ b₁ = b₂) (u' : B₃ ⟶ B₂) (hu' : u' ≫ b₂ = b₃) :
    tW w b₂ b₃ u' hu' ≫ tW w b₁ b₂ u hu = tW w b₁ b₃ (u' ≫ u) (by rw [Category.assoc, hu, hu']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, tW_fst, tW_fst, tW_fst]
  · rw [Category.assoc, tW_snd, tW_snd_assoc, tW_snd]

theorem tW_congr {u u' : B₂ ⟶ B₁} (hu : u ≫ b₁ = b₂) (hu' : u' ≫ b₁ = b₂) (e : u = u') :
    tW w b₁ b₂ u hu = tW w b₁ b₂ u' hu' := by
  subst e; rfl

end TransComp

section Stages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

abbrev bT (T : Subalgebra A₀ A) : (Spec (CommRingCat.of ↥T) : Scheme.{u}) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))

variable (A₀ A) in

abbrev bA : (Spec (CommRingCat.of A) : Scheme.{u}) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ A))

abbrev uA (T : Subalgebra A₀ A) : (Spec (CommRingCat.of A) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T) :=
  Spec.map (CommRingCat.ofHom (algebraMap ↥T A))

abbrev uT {T₁ T₂ : Subalgebra A₀ A} (h : T₁ ≤ T₂) :
    (Spec (CommRingCat.of ↥T₂) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T₁) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

theorem uA_bT (T : Subalgebra A₀ A) : uA T ≫ bT T = bA A₀ A := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem uT_bT {T₁ T₂ : Subalgebra A₀ A} (h : T₁ ≤ T₂) : uT h ≫ bT T₁ = bT T₂ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem uA_uT {T₁ T₂ : Subalgebra A₀ A} (h : T₁ ≤ T₂) : uA T₂ ≫ uT h = uA T₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem tW_snd_val {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of A₀)) (T : Subalgebra A₀ A) :
    tW w (bT T) (bA A₀ A) (uA T) (uA_bT T) ≫ pullback.snd w (bT T) =
      pullback.snd w (bA A₀ A) ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) :=
  tW_snd _ _ _ _ _

variable (T : Subalgebra A₀ A) (T' : Subalgebra ↥T A)

def flat : Subalgebra A₀ A := T'.restrictScalars A₀

theorem le_flat : T ≤ flat T T' := fun x hx => T'.algebraMap_mem (⟨x, hx⟩ : ↥T)

theorem flat_fg (hT : T.FG) (hT' : T'.FG) : (flat T T').FG := by
  rw [Subalgebra.fg_iff_finiteType] at hT hT' ⊢
  haveI := hT
  haveI := hT'
  haveI : Algebra.FiniteType A₀ ↥T' := Algebra.FiniteType.trans (S := ↥T) inferInstance inferInstance
  exact this

theorem subset_flat {s : Set A} (h : s ⊆ T') : s ⊆ flat T T' := h

theorem flat_mono {T'' : Subalgebra ↥T A} (h : T' ≤ T'') : flat T T' ≤ flat T T'' := fun _ hx => h hx

def flatHom : ↥T' →+* ↥(flat T T') where
  toFun x := ⟨x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

abbrev uF {T₂ : Subalgebra A₀ A} (h : flat T T' ≤ T₂) :
    (Spec (CommRingCat.of ↥T₂) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T') :=
  Spec.map (CommRingCat.ofHom ((Subalgebra.inclusion h).toRingHom.comp (flatHom T T')))

theorem uF_comp {T₂ : Subalgebra A₀ A} (h : flat T T' ≤ T₂) (h' : T ≤ T₂) :
    uF T T' h ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T')) = uT h' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

omit [Algebra A₀ A] in
theorem exists_finset_of_fg {R : Type u} [CommRing R] [Algebra R A] {U : Subalgebra R A} (hU : U.FG) :
    ∃ t : Finset A, (↑t : Set A) ⊆ U ∧ ∀ U' : Subalgebra R A, (↑t : Set A) ⊆ U' → U ≤ U' := by
  obtain ⟨t, ht⟩ := hU
  refine ⟨t, ?_, fun U' h => ?_⟩
  · rw [← ht]; exact Algebra.subset_adjoin
  · rw [← ht]; exact Algebra.adjoin_le h

variable {T} {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [LocallyOfFinitePresentation f]
  {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact w]

theorem exists_tW_comp_eq (a b : pullback w (bT T) ⟶ Yb f (bT T))
    (ha : a ≫ fb f (bT T) = pullback.snd _ _) (hb : b ≫ fb f (bT T) = pullback.snd _ _)
    (hab : tW w (bT T) (bA A₀ A) (uA T) (uA_bT T) ≫ a = tW w (bT T) (bA A₀ A) (uA T) (uA_bT T) ≫ b) (s : Finset A) :
    ∃ (T' : Subalgebra ↥T A), T'.FG ∧ (↑s : Set A) ⊆ T' ∧
      ∀ (T₂ : Subalgebra A₀ A) (_ : flat T T' ≤ T₂) (h : T ≤ T₂),
        tW w (bT T) (bT T₂) (uT h) (uT_bT h) ≫ a = tW w (bT T) (bT T₂) (uT h) (uT_bT h) ≫ b := by
  have hab' : pullback.fst (pullback.snd w (bT T)) (uA T) ≫ a = pullback.fst (pullback.snd w (bT T)) (uA T) ≫ b := by
    rw [fst_eq_rebaseIso_hom_tW w (bT T) (uA T) (bA A₀ A) (uA_bT T), Category.assoc, Category.assoc, hab]
  obtain ⟨T', hT', hs, hk⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType (A₀ := ↥T) (A := A)
      (pullback.snd w (bT T)) (fb f (bT T)) a b ha hb hab' s
  refine ⟨T', hT', hs, fun T₂ h₂ h => ?_⟩
  let b'' : (Spec (CommRingCat.of ↥T') : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T ↥T'))
  have hk' : tW w (bT T) (b'' ≫ bT T) b'' rfl ≫ a = tW w (bT T) (b'' ≫ bT T) b'' rfl ≫ b := by
    rw [fst_eq_rebaseIso_hom_tW w (bT T) b'' (b'' ≫ bT T) rfl, Category.assoc, Category.assoc] at hk
    exact (cancel_epi _).mp hk
  have hv : uF T T' h₂ ≫ b'' ≫ bT T = bT T₂ := by
    rw [← Category.assoc, uF_comp T T' h₂ h, uT_bT]
  have key := congrArg (fun k => tW w (b'' ≫ bT T) (bT T₂) (uF T T' h₂) hv ≫ k) hk'
  simp only [← Category.assoc, tW_comp] at key
  rw [tW_congr w (bT T) (bT T₂) _ (uT_bT h) (uF_comp T T' h₂ h)] at key
  exact key

end Stages

section Hom

theorem mul_val_congr {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (G : RelativeGroupLaw S f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (G.mul t₁ P₁ Q₁).1 = (G.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

theorem baseChange_mul_fst {S S' : Type u} [CommRing S] [CommRing S']
    (u : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (K : RelativeGroupLaw S f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' (pullback.snd f u)) :
    ((K.baseChange u).mul t' x y).1 ≫ pullback.fst f u =
      (K.mul (t' ≫ u)
        ⟨x.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ pullback.fst f u, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩).1 := by
  have h := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_mul u K t' x y)
  rw [RelativeGroupLaw.baseChangePointToBase_coe] at h
  exact h

variable {A₀ : Type u} [CommRing A₀] {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
  (b₁ : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of A₀)) (b₂ : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of A₀))
  (u : Spec (CommRingCat.of R₂) ⟶ Spec (CommRingCat.of R₁)) (hu : u ≫ b₁ = b₂)

theorem mul_tW {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A₀)} (K : RelativeGroupLaw A₀ f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₂)) (x y : SchemeHomOver t (fb f b₂)) :
    ((K.baseChange b₂).mul t x y).1 ≫ tW f b₁ b₂ u hu =
      ((K.baseChange b₁).mul (t ≫ u)
        ⟨x.1 ≫ tW f b₁ b₂ u hu, by rw [Category.assoc, tW_fb, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ tW f b₁ b₂ u hu, by rw [Category.assoc, tW_fb, ← Category.assoc, y.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, tW_fst, baseChange_mul_fst b₂ K t x y, baseChange_mul_fst b₁ K (t ≫ u)]
    exact mul_val_congr K (by rw [Category.assoc, hu]) _ _ _ _ (by simp only [Category.assoc, tW_fst])
      (by simp only [Category.assoc, tW_fst])
  · refine Eq.trans ?_ ((K.baseChange b₁).mul (t ≫ u) _ _).2.symm
    rw [Category.assoc, tW_snd, reassoc_of% ((K.baseChange b₂).mul t x y).2]

variable {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))

def resHom (g : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg : g ≫ fb f₂ b₁ = fb f₁ b₁) : Yb f₁ b₂ ⟶ Yb f₂ b₂ :=
  pullback.lift (tW f₁ b₁ b₂ u hu ≫ g ≫ pullback.fst f₂ b₁) (fb f₁ b₂)
    (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hg, tW_fb_assoc, hu])

@[reassoc] theorem resHom_fst (g : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg : g ≫ fb f₂ b₁ = fb f₁ b₁) :
    resHom b₁ b₂ u hu f₁ f₂ g hg ≫ pullback.fst f₂ b₂ = tW f₁ b₁ b₂ u hu ≫ g ≫ pullback.fst f₂ b₁ :=
  pullback.lift_fst _ _ _

@[reassoc] theorem resHom_fb (g : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg : g ≫ fb f₂ b₁ = fb f₁ b₁) :
    resHom b₁ b₂ u hu f₁ f₂ g hg ≫ fb f₂ b₂ = fb f₁ b₂ :=
  pullback.lift_snd _ _ _

@[reassoc] theorem resHom_tW (g : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg : g ≫ fb f₂ b₁ = fb f₁ b₁) :
    resHom b₁ b₂ u hu f₁ f₂ g hg ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ g := by
  apply pullback.hom_ext
  · rw [Category.assoc, tW_fst, resHom_fst, Category.assoc]
  · rw [Category.assoc, tW_snd, resHom_fb_assoc, Category.assoc, hg, tW_fb]

def resIso (e₀ : Yb f₁ b₁ ≅ Yb f₂ b₁) (he₀ : e₀.hom ≫ fb f₂ b₁ = fb f₁ b₁) : Yb f₁ b₂ ≅ Yb f₂ b₂ where
  hom := resHom b₁ b₂ u hu f₁ f₂ e₀.hom he₀
  inv := resHom b₁ b₂ u hu f₂ f₁ e₀.inv (by rw [← he₀, Iso.inv_hom_id_assoc])
  hom_inv_id := eq_of_comp_tW_eq f₁ b₁ b₂ u hu
    (by rw [Category.assoc, resHom_tW, resHom_tW_assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp])
    (by rw [Category.assoc, resHom_fb, resHom_fb, Category.id_comp])
  inv_hom_id := eq_of_comp_tW_eq f₂ b₁ b₂ u hu
    (by rw [Category.assoc, resHom_tW, resHom_tW_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp])
    (by rw [Category.assoc, resHom_fb, resHom_fb, Category.id_comp])

theorem resIso_hom_fb (e₀ : Yb f₁ b₁ ≅ Yb f₂ b₁) (he₀ : e₀.hom ≫ fb f₂ b₁ = fb f₁ b₁) :
    (resIso b₁ b₂ u hu f₁ f₂ e₀ he₀).hom ≫ fb f₂ b₂ = fb f₁ b₂ :=
  resHom_fb b₁ b₂ u hu f₁ f₂ e₀.hom he₀

theorem resIso_hom_tW (e₀ : Yb f₁ b₁ ≅ Yb f₂ b₁) (he₀ : e₀.hom ≫ fb f₂ b₁ = fb f₁ b₁) :
    (resIso b₁ b₂ u hu f₁ f₂ e₀ he₀).hom ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ e₀.hom :=
  resHom_tW b₁ b₂ u hu f₁ f₂ e₀.hom he₀

theorem mul_mk_val {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A₀)} {R : Type u} [CommRing R]
    {b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀)} (K : RelativeGroupLaw R (fb f b))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a c : T ⟶ Yb f b) (ha : a ≫ fb f b = t) (hc : c ≫ fb f b = t) :
    (K.mul t ⟨a, ha⟩ ⟨c, hc⟩).1 = pair a c (ha.trans hc.symm) ≫ (ofLaw K).m :=
  mul_val K t ⟨a, ha⟩ ⟨c, hc⟩

theorem tW_m {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A₀)} (K : RelativeGroupLaw A₀ f) :
    tW (w₂ f) b₁ b₂ u hu ≫ (ofLaw (K.baseChange b₁)).m = (ofLaw (K.baseChange b₂)).m ≫ tW f b₁ b₂ u hu := by
  have h := mul_tW b₁ b₂ u hu K (qb f b₂) (P₁ f b₂) (P₂ f b₂)
  rw [mul_val (K.baseChange b₁) (qb f b₂ ≫ u)] at h
  let X' : SchemeHomOver (qb f b₂ ≫ u) (fb f b₁) :=
    ⟨(P₁ f b₂).1 ≫ tW f b₁ b₂ u hu, by rw [Category.assoc, tW_fb, ← Category.assoc, (P₁ f b₂).2]⟩
  let Y' : SchemeHomOver (qb f b₂ ≫ u) (fb f b₁) :=
    ⟨(P₂ f b₂).1 ≫ tW f b₁ b₂ u hu, by rw [Category.assoc, tW_fb, ← Category.assoc, (P₂ f b₂).2]⟩
  have e : pair X'.1 Y'.1 (mul_fb_eq X' Y') = tW (w₂ f) b₁ b₂ u hu :=
    hom_ext₂ (by rw [pair_p₁, tW_p₁]; rfl) (by rw [pair_p₂, tW_p₂]; rfl)
  have h' : pair X'.1 Y'.1 (mul_fb_eq X' Y') ≫ (ofLaw (K.baseChange b₁)).m =
      tW (w₂ f) b₁ b₂ u hu ≫ (ofLaw (K.baseChange b₁)).m := by rw [e]
  exact (h.trans h').symm

variable (L₁ : RelativeGroupLaw A₀ f₁) (L₂ : RelativeGroupLaw A₀ f₂)

def homL {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) : Q₂ f₁ b ⟶ Yb f₂ b :=
  (ofLaw (L₁.baseChange b)).m ≫ g

def homR {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) (hg : g ≫ fb f₂ b = fb f₁ b) : Q₂ f₁ b ⟶ Yb f₂ b :=
  pair (p₁ f₁ b ≫ g) (p₂ f₁ b ≫ g) (by rw [Category.assoc, Category.assoc, hg, p₁_fb, p₂_fb]) ≫
    (ofLaw (L₂.baseChange b)).m

theorem homL_fb {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) (hg : g ≫ fb f₂ b = fb f₁ b) : homL f₁ f₂ L₁ b g ≫ fb f₂ b = pullback.snd _ _ := by
  rw [homL, Category.assoc, hg, (ofLaw _).hm]

theorem homR_fb {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) (hg : g ≫ fb f₂ b = fb f₁ b) : homR f₁ f₂ L₂ b g hg ≫ fb f₂ b = pullback.snd _ _ := by
  rw [homR, Category.assoc, (ofLaw _).hm, pair_snd, Category.assoc, hg, p₁_fb]

theorem mul_comp_eq_of_homL_eq_homR {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) (hg : g ≫ fb f₂ b = fb f₁ b) (h : homL f₁ f₂ L₁ b g = homR f₁ f₂ L₂ b g hg)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (fb f₁ b)) :
    ((L₁.baseChange b).mul t x y).1 ≫ g =
      ((L₂.baseChange b).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg, y.2]⟩).1 := by
  have key := congrArg (fun k => pair x.1 y.1 (mul_fb_eq x y) ≫ k) h
  simp only [homL, homR, comp_pair_assoc, pair_p₁_assoc, pair_p₂_assoc] at key
  rw [mul_val, Category.assoc, key, mul_mk_val]

theorem homL_eq_homR_of_mul_comp_eq {R : Type u} [CommRing R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀))
    (g : Yb f₁ b ⟶ Yb f₂ b) (hg : g ≫ fb f₂ b = fb f₁ b)
    (hgmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (fb f₁ b)),
      ((L₁.baseChange b).mul t x y).1 ≫ g =
        ((L₂.baseChange b).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg, x.2]⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg, y.2]⟩).1) :
    homL f₁ f₂ L₁ b g = homR f₁ f₂ L₂ b g hg := by
  have h := hgmul (qb f₁ b) (P₁ f₁ b) (P₂ f₁ b)
  rw [mul_val (L₂.baseChange b)] at h
  exact h

theorem homL_tW (g₀ : Yb f₁ b₁ ⟶ Yb f₂ b₁) (r : Yb f₁ b₂ ⟶ Yb f₂ b₂)
    (hrtW : r ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ g₀) :
    homL f₁ f₂ L₁ b₂ r ≫ tW f₂ b₁ b₂ u hu = tW (w₂ f₁) b₁ b₂ u hu ≫ homL f₁ f₂ L₁ b₁ g₀ := by
  rw [homL, homL, Category.assoc, hrtW, ← Category.assoc, ← tW_m, Category.assoc]

theorem homR_tW (g₀ : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg₀ : g₀ ≫ fb f₂ b₁ = fb f₁ b₁) (r : Yb f₁ b₂ ⟶ Yb f₂ b₂)
    (hr : r ≫ fb f₂ b₂ = fb f₁ b₂) (hrtW : r ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ g₀) :
    homR f₁ f₂ L₂ b₂ r hr ≫ tW f₂ b₁ b₂ u hu = tW (w₂ f₁) b₁ b₂ u hu ≫ homR f₁ f₂ L₂ b₁ g₀ hg₀ := by
  have H : (p₁ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) ≫ fb f₂ b₁ = (p₂ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) ≫ fb f₂ b₁ := by
    simp only [Category.assoc, hg₀, tW_fb, p₁_fb_assoc, p₂_fb_assoc]
  have e1 : tW (w₂ f₁) b₁ b₂ u hu ≫ homR f₁ f₂ L₂ b₁ g₀ hg₀ =
      pair (p₁ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) (p₂ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) H ≫ (ofLaw (L₂.baseChange b₁)).m := by
    rw [homR, comp_pair_assoc]
    congr 1
    exact pair_congr _ _ (by rw [tW_p₁_assoc]) (by rw [tW_p₂_assoc])
  have e2 : homR f₁ f₂ L₂ b₂ r hr ≫ tW f₂ b₁ b₂ u hu =
      pair (p₁ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) (p₂ f₁ b₂ ≫ tW f₁ b₁ b₂ u hu ≫ g₀) H ≫ (ofLaw (L₂.baseChange b₁)).m := by
    rw [homR, Category.assoc, ← tW_m b₁ b₂ u hu L₂, ← Category.assoc, ← pair_tW]
    congr 1
    exact pair_congr _ _ (by rw [Category.assoc, hrtW]) (by rw [Category.assoc, hrtW])
  rw [e1, e2]

theorem mul_comp_eq_of_tW_homL_eq (g₀ : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg₀ : g₀ ≫ fb f₂ b₁ = fb f₁ b₁) (r : Yb f₁ b₂ ⟶ Yb f₂ b₂)
    (hr : r ≫ fb f₂ b₂ = fb f₁ b₂) (hrtW : r ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ g₀)
    (hid : tW (w₂ f₁) b₁ b₂ u hu ≫ homL f₁ f₂ L₁ b₁ g₀ = tW (w₂ f₁) b₁ b₂ u hu ≫ homR f₁ f₂ L₂ b₁ g₀ hg₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₂)) (x y : SchemeHomOver t (fb f₁ b₂)) :
    ((L₁.baseChange b₂).mul t x y).1 ≫ r =
      ((L₂.baseChange b₂).mul t ⟨x.1 ≫ r, by rw [Category.assoc, hr, x.2]⟩ ⟨y.1 ≫ r, by rw [Category.assoc, hr, y.2]⟩).1 := by
  apply mul_comp_eq_of_homL_eq_homR
  apply eq_of_comp_tW_eq f₂ b₁ b₂ u hu
  · rw [homL_tW b₁ b₂ u hu f₁ f₂ L₁ g₀ r hrtW, homR_tW b₁ b₂ u hu f₁ f₂ L₂ g₀ hg₀ r hr hrtW, hid]
  · rw [homL_fb f₁ f₂ L₁ b₂ r hr, homR_fb]

theorem tW_homL_eq_of_mul_comp_eq (g₀ : Yb f₁ b₁ ⟶ Yb f₂ b₁) (hg₀ : g₀ ≫ fb f₂ b₁ = fb f₁ b₁) (r : Yb f₁ b₂ ⟶ Yb f₂ b₂)
    (hr : r ≫ fb f₂ b₂ = fb f₁ b₂) (hrtW : r ≫ tW f₂ b₁ b₂ u hu = tW f₁ b₁ b₂ u hu ≫ g₀)
    (hrmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R₂)) (x y : SchemeHomOver t (fb f₁ b₂)),
      ((L₁.baseChange b₂).mul t x y).1 ≫ r =
        ((L₂.baseChange b₂).mul t ⟨x.1 ≫ r, by rw [Category.assoc, hr, x.2]⟩ ⟨y.1 ≫ r, by rw [Category.assoc, hr, y.2]⟩).1) :
    tW (w₂ f₁) b₁ b₂ u hu ≫ homL f₁ f₂ L₁ b₁ g₀ = tW (w₂ f₁) b₁ b₂ u hu ≫ homR f₁ f₂ L₂ b₁ g₀ hg₀ := by
  rw [← homL_tW b₁ b₂ u hu f₁ f₂ L₁ g₀ r hrtW, ← homR_tW b₁ b₂ u hu f₁ f₂ L₂ g₀ hg₀ r hr hrtW,
    homL_eq_homR_of_mul_comp_eq f₁ f₂ L₁ L₂ b₂ r hr (fun t x y => hrmul t x y)]

end Hom

section Final

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
  {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
  [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
  [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
  (L₁ : RelativeGroupLaw A₀ f₁) (L₂ : RelativeGroupLaw A₀ f₂)
  (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
    pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
  (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
  (hemul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
      (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
    ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t x y).1 ≫ e.hom =
      ((L₂.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t
        ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1)

include he hemul in

theorem exists_forall_iso (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ (B : Type u) [CommRing B] (φ : ↥T →+* B) (χ : A₀ →+* B), φ.comp (algebraMap A₀ ↥T) = χ →
        ∃ (e' : pullback f₁ (Spec.map (CommRingCat.ofHom χ)) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom χ)))
          (he' : e'.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _),
          ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of B))
            (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom χ)))),
            ((L₁.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t x y).1 ≫ e'.hom =
              ((L₂.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t
                ⟨x.1 ≫ e'.hom, by rw [Category.assoc, he', x.2]⟩ ⟨y.1 ≫ e'.hom, by rw [Category.assoc, he', y.2]⟩).1 := by

  obtain ⟨T₁, hT₁, hs₁, e₀, he₀, hq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation (A₀ := A₀) (A := A)
      f₁ f₂ e he s
  have hcomp : tW f₁ (bT T₁) (bA A₀ A) (uA T₁) (uA_bT T₁) ≫ e₀.hom = e.hom ≫ tW f₂ (bT T₁) (bA A₀ A) (uA T₁) (uA_bT T₁) :=
    hq (tW f₁ (bT T₁) (bA A₀ A) (uA T₁) (uA_bT T₁)) (tW f₂ (bT T₁) (bA A₀ A) (uA T₁) (uA_bT T₁))
      (tW_fst _ _ _ _ _) (tW_snd_val _ _) (tW_fst _ _ _ _ _) (tW_snd_val _ _)

  have hid := tW_homL_eq_of_mul_comp_eq (bT T₁) (bA A₀ A) (uA T₁) (uA_bT T₁) f₁ f₂ L₁ L₂ e₀.hom he₀ e.hom he hcomp.symm
    (fun t x y => hemul t x y)
  obtain ⟨T', hT', -, hk⟩ := exists_tW_comp_eq f₂ (w₂ f₁) (homL f₁ f₂ L₁ (bT T₁) e₀.hom)
    (homR f₁ f₂ L₂ (bT T₁) e₀.hom he₀) (homL_fb f₁ f₂ L₁ _ _ he₀) (homR_fb f₁ f₂ L₂ _ _ he₀) hid ∅
  let T : Subalgebra A₀ A := flat T₁ T'
  have h₁T : T₁ ≤ T := le_flat T₁ T'
  refine ⟨T, flat_fg T₁ T' hT₁ hT', hs₁.trans h₁T, fun B _ φ χ hχ => ?_⟩

  let uB : (Spec (CommRingCat.of B) : Scheme.{u}) ⟶ Spec (CommRingCat.of ↥T₁) :=
    Spec.map (CommRingCat.ofHom (φ.comp (Subalgebra.inclusion h₁T).toRingHom))
  have huB : uB ≫ bT T₁ = Spec.map (CommRingCat.ofHom χ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hχ]
    congr 2
  have huB' : Spec.map (CommRingCat.ofHom φ) ≫ uT h₁T = uB := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫ bT T = Spec.map (CommRingCat.ofHom χ) := by
    rw [← huB, ← huB', Category.assoc, uT_bT]
  have hidB : tW (w₂ f₁) (bT T₁) (Spec.map (CommRingCat.ofHom χ)) uB huB ≫ homL f₁ f₂ L₁ (bT T₁) e₀.hom =
      tW (w₂ f₁) (bT T₁) (Spec.map (CommRingCat.ofHom χ)) uB huB ≫ homR f₁ f₂ L₂ (bT T₁) e₀.hom he₀ := by
    have key := congrArg (fun k => tW (w₂ f₁) (bT T) (Spec.map (CommRingCat.ofHom χ)) (Spec.map (CommRingCat.ofHom φ)) hφ ≫ k)
      (hk T le_rfl h₁T)
    simp only [← Category.assoc, tW_comp] at key
    rw [tW_congr (w₂ f₁) (bT T₁) _ _ huB huB'] at key
    exact key
  exact ⟨resIso (bT T₁) _ uB huB f₁ f₂ e₀ he₀, resIso_hom_fb (bT T₁) _ uB huB f₁ f₂ e₀ he₀,
    fun t x y => mul_comp_eq_of_tW_homL_eq (bT T₁) _ uB huB f₁ f₂ L₁ L₂ e₀.hom he₀ _
      (resIso_hom_fb (bT T₁) _ uB huB f₁ f₂ e₀ he₀) (resIso_hom_tW (bT T₁) _ uB huB f₁ f₂ e₀ he₀) hidB t x y⟩

end Final

end GoodReductionJacobian.RelativeGroupLaw.IsoLawDescent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian.RelativeGroupLaw.IsoLawDescent"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.GoodReductionJacobian.RelativeGroupLaw.IsoLawDescent"

open GoodReductionJacobian.RelativeGroupLaw.IsoLawDescent in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
    (L₁ : RelativeGroupLaw A₀ f₁) (L₂ : RelativeGroupLaw A₀ f₂)
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hemul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
        (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
      ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t x y).1 ≫ e.hom =
        ((L₂.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ (B : Type u) [CommRing B] (φ : ↥T →+* B) (χ : A₀ →+* B), φ.comp (algebraMap A₀ ↥T) = χ →
        ∃ (e' : pullback f₁ (Spec.map (CommRingCat.ofHom χ)) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom χ)))
          (he' : e'.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _),
          ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of B))
            (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom χ)))),
            ((L₁.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t x y).1 ≫ e'.hom =
              ((L₂.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t
                ⟨x.1 ≫ e'.hom, by rw [Category.assoc, he', x.2]⟩ ⟨y.1 ≫ e'.hom, by rw [Category.assoc, he', y.2]⟩).1 :=
  exists_forall_iso f₁ f₂ L₁ L₂ e he (fun t x y => hemul t x y) s

end S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation (solution)
