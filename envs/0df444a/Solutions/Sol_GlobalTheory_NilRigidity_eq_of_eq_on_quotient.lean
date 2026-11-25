-- Prove2me | solution 1 for GlobalTheory.NilRigidity.eq_of_eq_on_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:34.584836+00:00
-- url     : https://prove2.me/submissions/4a5c914b-d0f6-4b7e-a32b-3385201fc659

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfPullbackQuotientEq
import Theorems.Thm_GlobalTheory_NilRigidity_exists_preimage_quotient
import Theorems.Thm_GlobalTheory_globalFns_holds
import Theorems.Thm_GlobalTheory_local_rigidity
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_GlobalTheory_surjective_app_of_isAbelianScheme
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilRigidity
namespace GlobalTheory.NilRigidity
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B')
    (hfg : pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ f.left =
      pullback.fst B.hom (spMap (Ideal.Quotient.mk I)) ≫ g.left)
    (hη : η[B] ≫ f = η[B] ≫ g) : f = g := by
  haveI := hB.proper
  let π := spMap (Ideal.Quotient.mk I)
  let c : B ⟶ B' := f * g⁻¹
  let j := pullback.fst B.hom π
  let j' : Over.mk (j ≫ B.hom) ⟶ B := Over.homMk j rfl
  have h1 : j' ≫ f = j' ≫ g := Over.OverMorphism.ext hfg
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[B] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  have hpt : ∀ x : B.left, c.left x = (η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x) := by
    intro x
    obtain ⟨t₀, ht₀⟩ := exists_preimage_quotient I hI (B.hom x)
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback B.hom π) x t₀ ht₀.symm
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    rfl
  have hη' : (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ B.hom = 𝟙 _ := Over.w η[B]
  have key : c.left = B.hom ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left ≫ c.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
    obtain ⟨V, hV, hV'⟩ := GlobalTheory.local_rigidity B.left (Sp R) B'.left B.hom _ c.left hη' inferInstance
      (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds B hB) (B.hom x)
      ((η[B'] : 𝟙_ (Over (Sp R)) ⟶ B').left (B.hom x)) (fun x' hx' ↦ by rw [hpt, hx'])
    exact ⟨B.hom ⁻¹ᵁ V, hV, hV'⟩
  have key' : c = toUnit B ≫ η[B] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'
end GlobalTheory.NilRigidity
