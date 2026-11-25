-- Prove2me | solution 1 for GlobalTheory.UU.TQ.dim_eq_add_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:34:46.18592+00:00
-- url     : https://prove2.me/submissions/f2033090-4b3e-4fe7-a72f-645a5facd0ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothProjOfFree
import Theorems.Thm_GlobalTheory_UU_TQ_smooth_proj_of_free
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_base
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim


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
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
namespace TQ
theorem _root_.solution :
    (∀ (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over S) [GrpObj G] (Q : TQ G X) (g g' : ℕ), SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g' Q.B.hom → g = g' + Module.finrank ℤ X) := by
  intro S hS X _ _ _ G _ Q g g' dG dB
  obtain ⟨y⟩ := hS
  have := Q.i_hom
  have := Q.smooth_proj_of_free
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim Q.q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (Q.isKernel.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom Q.i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w Q.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega
end TQ
end GlobalTheory.UU
