-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.exists_coaction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:20.072216+00:00
-- url     : https://prove2.me/submissions/05b1097a-431c-4f6e-ad30-8f5f6b4267fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_comp_cst
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_comp_univ
import Theorems.Thm_GlobalTheory_TorsorUnit_toSpec_appTop
import Theorems.Thm_GlobalTheory_TorsorUnit_comp_pt
import Theorems.Thm_GlobalTheory_TorsorUnit_le_pt_preimage
import Theorems.Thm_GlobalTheory_TorsorUnit_exists_eq_pt
import Theorems.Thm_GlobalTheory_TorsorUnit_toHom_comp
import Theorems.Thm_GlobalTheory_TorsorUnit_act_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}
open SplitTorusPoints
namespace GlobalTheory.TorsorUnit
theorem _root_.solution [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens}
    (hU : IsAffineOpen (q.left ⁻¹ᵁ V)) :
    ∃ ρ : Γ(G.left, q.left ⁻¹ᵁ V) →+* AddMonoidAlgebra Γ(G.left, q.left ⁻¹ᵁ V) X,
      ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (θ), g.left = pt hU θ →
        ((t ≫ i) * g).left = pt hU ((ev θ (toHom t)).comp ρ) := by
  let C := Γ(G.left, q.left ⁻¹ᵁ V)
  let D : CommRingCat.{0} := .of (AddMonoidAlgebra C X)
  let j : AddMonoidAlgebra C X →+* Γ(Spec D, ⊤) := (Scheme.ΓSpecIso D).inv.hom
  let Z₀ : Over S := Over.mk (pt hU (j.comp (cst X C)) ≫ G.hom)
  let g₀ : Z₀ ⟶ G := Over.homMk (pt hU (j.comp (cst X C))) rfl
  obtain ⟨t₀, ht₀⟩ := (toHom_bijective (Z := Z₀) (X := X)).2
    ((Units.map j.toMonoidHom).comp (univ X C))
  have e : ⊤ ≤ ((t₀ ≫ i) * g₀).left ⁻¹ᵁ q.left ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, act_comp hi, Over.comp_left,
      Scheme.Hom.comp_preimage]
    exact le_pt_preimage hU _
  obtain ⟨ρ₀, hρ₀⟩ := exists_eq_pt hU _ e
  refine ⟨(Scheme.ΓSpecIso D).hom.hom.comp ρ₀, fun Z t g θ hg => ?_⟩
  let π₀ : Z.left ⟶ Spec D := Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ev θ (toHom t)))
  have hπ : π₀.appTop.hom.comp j = ev θ (toHom t) := toSpec_appTop (R := D) _
  have h1 : π₀ ≫ g₀.left = g.left := by
    refine (comp_pt hU π₀ _).trans ?_
    rw [← RingHom.comp_assoc, hπ, ev_comp_cst, hg]
  let π : Z ⟶ Z₀ := Over.homMk π₀ (by
    rw [← Over.w g, ← h1, Category.assoc]; rfl)
  have h2 : π ≫ g₀ = g := Over.OverMorphism.ext h1
  have h3 : π ≫ t₀ = t := by
    apply toHom_bijective.1
    rw [toHom_comp, ht₀, ← ev_comp_univ θ (toHom t), ← hπ]
    rfl
  have h4 : (t ≫ i) * g = π ≫ ((t₀ ≫ i) * g₀) := by
    rw [MonObj.comp_mul, h2, ← Category.assoc, h3]
  rw [h4, Over.comp_left, hρ₀]
  refine (comp_pt hU π₀ _).trans ?_
  rw [← hπ]
  congr 1
  refine RingHom.ext fun c => ?_
  change π₀.appTop.hom (ρ₀ c) = π₀.appTop.hom (((Scheme.ΓSpecIso D).hom ≫
    (Scheme.ΓSpecIso D).inv).hom (ρ₀ c))
  rw [Iso.hom_inv_id]
  rfl
end GlobalTheory.TorsorUnit
