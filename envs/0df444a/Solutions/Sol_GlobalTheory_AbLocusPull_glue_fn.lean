-- Prove2me | solution 1 for GlobalTheory.AbLocusPull.glue_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:22.713621+00:00
-- url     : https://prove2.me/submissions/668047f3-d7da-407b-836f-219ad14b6aff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.AbLocusPull
theorem _root_.solution {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ x k, x ∈ O k → gs (𝟙 X) x V b = gs (𝟙 X) x (O k) (a k) := by
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf O a := by
    intro k l
    apply fn_ext
    intro x hx
    have e1 := gs_res (𝟙 X) x (inf_le_left : O k ⊓ O l ≤ O k) hx (a k)
    have e2 := gs_res (𝟙 X) x (inf_le_right : O k ⊓ O l ≤ O l) hx (a l)
    exact e1.trans ((h k l x hx.1 hx.2).trans e2.symm)
  have hcov : V ≤ iSup O := fun x hx => by
    obtain ⟨k, hk⟩ := hc x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k)) hcov a hcomp
  refine ⟨b, fun x k hx => ?_⟩
  rw [← gs_res (𝟙 X) x (hO k) hx b]
  exact congrArg (gs (𝟙 X) x (O k)) (hb k)
end GlobalTheory.AbLocusPull
