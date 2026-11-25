-- Prove2me | solution 1 for GlobalTheory.ZJ.Core.fibLaw_of_testCart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:10.686796+00:00
-- url     : https://prove2.me/submissions/bddb265e-5e60-4a91-b66d-881695ed8ead

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusPointEqOneOfAxes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FibreLawOfTestCartesian
import Theorems.Thm_GlobalTheory_ZJ_exists_sectionHom
import Theorems.Thm_GlobalTheory_ZJ_eSec_comp_of_isGrpPullback
import Theorems.Thm_GlobalTheory_ZJ_Core_Test_exists_isGt_fibre
import Theorems.Thm_GlobalTheory_ZJ_Core_Test_eSec_comp_f
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm
import Theorems.Thm_GlobalTheory_isMonHom_of_isGt_of_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace Core
theorem _root_.solution : ∀ C : Core, C.TestCart → C.FibLaw := by
  intro C hC p _ y y' τ τ' K _ _ r r' hr hr' hy c d c' d' hc hd
  obtain ⟨G₁, _, _, E₁, φ₁, g₁, h₁⟩ := τ.exists_isGt_fibre K r hr
  obtain ⟨G₂, _, _, E₂, φ₂, g₂, h₂⟩ := τ'.exists_isGt_fibre K r' hr'
  have P₁ := h₁.1.paste_horiz (hC p y τ)
  have P₂ := h₂.1.paste_horiz (hC p y' τ')
  let i : G₁ ⟶ G₂ := Over.homMk (P₂.lift (φ₁ ≫ τ.f) G₁.hom (by rw [P₁.w, hy])) (P₂.lift_snd _ _ _)
  have hi : i.left ≫ φ₂ ≫ τ'.f = φ₁ ≫ τ.f := P₂.lift_fst _ _ _
  have u₁ : η[G₁].left ≫ φ₁ ≫ τ.f = (r ≫ τ.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) (eSec_comp_of_isGrpPullback h₁)).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) τ.eSec_comp_f)))
  have u₂ : η[G₂].left ≫ φ₂ ≫ τ'.f = (r' ≫ τ'.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ'.f) (eSec_comp_of_isGrpPullback h₂)).trans
      ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) τ'.eSec_comp_f)))
  have hone : η[G₁] ≫ i = η[G₂] := by
    apply Over.OverMorphism.ext
    apply P₂.hom_ext
    · rw [Over.comp_left, Category.assoc, hi, u₁, u₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.e) hy).trans (Category.assoc _ _ _))
    · rw [Over.w, Over.w]
  have := isMonHom_of_isGt_of_one K E₁ E₂ G₁ G₂ g₁ g₂ i hone
  obtain ⟨ρ₁, l₁, s₁⟩ := exists_sectionHom h₁ (Over.mk (𝟙 _)) r (Category.id_comp _).symm
  obtain ⟨ρ₂, l₂, -⟩ := exists_sectionHom h₂ (Over.mk (𝟙 _)) r' (Category.id_comp _).symm
  have key : ∀ x, (ρ₁ x).left ≫ τ.f = (ρ₂ (x ≫ i)).left ≫ τ'.f := fun x => by
    rw [l₁, l₂, Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hi]
  have inj : ∀ (x) (z : Over.mk r' ⟶ τ'.H), (ρ₁ x).left ≫ τ.f = z.left ≫ τ'.f → z = ρ₂ (x ≫ i) := fun x z hz => by
    apply Over.OverMorphism.ext
    apply (hC p y' τ').hom_ext
    · exact hz.symm.trans (key x)
    · rw [Over.w, Over.w]
  obtain ⟨c, rfl⟩ := s₁ c
  obtain ⟨d, rfl⟩ := s₁ d
  obtain rfl := inj c c' hc
  obtain rfl := inj d d' hd
  constructor
  · rw [← map_mul, ← map_mul, ← MonObj.mul_comp]
    exact key _
  · rw [← map_inv, ← map_inv, ← GrpObj.inv_comp]
    exact key _
end Core
end GlobalTheory.ZJ
