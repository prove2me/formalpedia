-- Prove2me | solution 1 for GlobalTheory.existsUnique_point_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:59.421317+00:00
-- url     : https://prove2.me/submissions/e193a430-e870-461b-bffc-9049ee25f54a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Theorems.Thm_GlobalTheory_AffinePointValues_appLE_specMap_fromSpec
import Theorems.Thm_GlobalTheory_AffinePointValues_specMap_appLE_fromSpec
import Theorems.Thm_GlobalTheory_AffinePointValues_fromSpec_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open AffinePointValues
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) := by
  intro X U hU e he
  let φ : Γ(X.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom e

  have hconst : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U (fun _ _ => trivial) ≫ φ =
      𝟙 _ := by
    ext a
    exact he a
  have hw : (Spec.map φ ≫ hU.fromSpec) ≫ X.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [Category.assoc, fromSpec_comp hU X.hom (fun _ _ => trivial), ← Spec.map_comp,
      Category.assoc, hconst, Spec.map_id]
    rfl
  have hpre : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro p _
    show hU.fromSpec.base ((Spec.map φ).base p) ∈ U
    have h : (Spec.map φ).base p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [IsAffineOpen.fromSpec_preimage_self]; trivial
    exact h
  refine ⟨Over.homMk (Spec.map φ ≫ hU.fromSpec) hw, ⟨hpre, fun f => ?_⟩, ?_⟩
  · show valAt' (Spec.map φ ≫ hU.fromSpec) U f = e f
    rw [valAt', dif_pos hpre]
    exact congrArg (fun g => g.hom f) (appLE_specMap_fromSpec hU φ hpre)
  · rintro y ⟨hy, hv⟩
    apply Over.OverMorphism.ext
    have h1 : y.left.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = φ := by
      ext f
      have := hv f
      rw [valAt', dif_pos hy] at this
      exact this
    rw [← specMap_appLE_fromSpec hU y.left hy, h1]
    rfl
end GlobalTheory
