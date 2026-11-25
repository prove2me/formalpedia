-- Prove2me | solution 1 for GlobalTheory.WeilLocal.local_of_openImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:26.921488+00:00
-- url     : https://prove2.me/submissions/c9403620-104e-4f78-9ce1-fa3f5f0f1f5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsIffOfIsGrpPullbackComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCover
import Theorems.Thm_GlobalTheory_WeilLocal_commIsOf_of_retract
import Theorems.Thm_GlobalTheory_CommPairing_exists_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.WeilLocal
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
private theorem exists_overRes_section_image_openImmersion {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    (V' : T'.left.Opens) :
    ∃ (a : overRes V' ⟶ overRes (j.left ''ᵁ V')) (b : overRes (j.left ''ᵁ V') ⟶ overRes V'),
      b ≫ a = 𝟙 _ ∧ a ≫ overResι (j.left ''ᵁ V') = overResι V' ≫ j := by
  have he : (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left := Scheme.Hom.isoImage_hom_ι _ _
  refine ⟨Over.homMk (j.left.isoImage V').hom ?_, Over.homMk (j.left.isoImage V').inv ?_, ?_, ?_⟩
  · show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι ≫ T.hom = V'.ι ≫ T'.hom
    rw [← Category.assoc, he, Category.assoc, Over.w j]
  · show (j.left.isoImage V').inv ≫ V'.ι ≫ T'.hom = (j.left ''ᵁ V').ι ≫ T.hom
    rw [← Over.w j, ← Category.assoc V'.ι, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').inv ≫ (j.left.isoImage V').hom = 𝟙 _
    exact Iso.inv_hom_id _
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left
    exact he
end GlobalTheory.WeilLocal
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.WeilLocal
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilLocal
theorem _root_.solution (hL : L.IsLB) {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c)) (p : T'.left) :
    ∃ V : T.left.Opens, j.left p ∈ V ∧
      (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
      ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
        CommIsOf A L k θx θy (unitRes V c) := by
  obtain ⟨V', hpV', ⟨θx₀, θy₀, hx₀, hy₀⟩, HV'⟩ := H p
  obtain ⟨a, b, hba, ha⟩ := exists_overRes_section_image_openImmersion j V'
  have hb : b ≫ overResι V' ≫ j = overResι (j.left ''ᵁ V') := by
    rw [← ha, ← Category.assoc, hba, Category.id_comp]
  refine ⟨j.left ''ᵁ V', ⟨p, hpV', rfl⟩, ?_, ?_⟩
  · obtain ⟨θx, hx, -⟩ := exists_pull hL b θx₀
    obtain ⟨θy, hy, -⟩ := exists_pull hL b θy₀
    refine ⟨θx, θy, ?_, ?_⟩
    · rw [hx, hx₀, ← hb]
      simp only [Category.assoc]
    · rw [hy, hy₀, ← hb]
      simp only [Category.assoc]
  · intro θx θy hx hy
    have key := commIsOf_of_retract hL b a hba θx θy
      (c := unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c))
      (fun θ₁ θ₂ h₁ h₂ => HV' θ₁ θ₂ (by rw [h₁, hx, ← Category.assoc, ha, Category.assoc])
        (by rw [h₂, hy, ← Category.assoc, ha, Category.assoc]))
    have hbl : b.left ≫ V'.ι ≫ j.left = (j.left ''ᵁ V').ι := congrArg Over.Hom.left hb
    have hu : Units.map b.left.appTop.hom.toMonoidHom (unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c)) =
        unitRes (j.left ''ᵁ V') c := by
      unfold unitRes
      rw [← hbl]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app,
        CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
      rfl
    rw [hu] at key
    exact key
end GlobalTheory.WeilLocal
