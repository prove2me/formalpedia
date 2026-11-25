-- Prove2me | solution 1 for GlobalTheory.RingGlue.appLE_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:10:22.353163+00:00
-- url     : https://prove2.me/submissions/5f3974ca-aa5d-4391-ba6c-5f4b05b5bb1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.RingGlue
namespace GlobalTheory.RingGlue
theorem _root_.solution {Y B : Scheme.{0}} {W : Y.Opens} {V : B.Opens} (hV : IsAffineOpen V)
    (ψ : Γ(B, V) ⟶ Γ(Y, W)) (q : Y ⟶ B) (hq : W.ι ≫ q = loc hV ψ) :
    ∃ h : W ≤ q ⁻¹ᵁ V, q.appLE V W h = ψ := by
  have h : W ≤ q ⁻¹ᵁ V := by
    intro y hy
    have h1 : q y = hV.fromSpec ((W.toSpecΓ ≫ Spec.map ψ) ⟨y, hy⟩) := by
      have := congr($(hq) ⟨y, hy⟩)
      exact this
    change q y ∈ (V : Set B)
    rw [h1, ← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨h, ?_⟩
  have h2 : W.toSpecΓ ≫ Spec.map (q.appLE V W h) ≫ hV.fromSpec = W.ι ≫ q := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [hq, loc, ← Category.assoc, ← Category.assoc, cancel_mono] at h2
  have h3 := congr(($h2).appTop)
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc] at h3
  simpa only [cancel_epi, cancel_mono] using h3
end GlobalTheory.RingGlue
