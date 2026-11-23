-- Prove2me | solution 1 for GlobalTheory.LinDescent.glue_fn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:59.793354+00:00
-- url     : https://prove2.me/submissions/74850efd-20d5-49d2-8c35-16d9fda3fe1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.LinDescent
theorem _root_.solution {κ : Type} (V : X.Opens) (O : κ → X.Opens) (hO : ∀ k, O k ≤ V)
    (hc : ∀ x ∈ V, ∃ k, x ∈ O k) (a : ∀ k, Γ(X, O k))
    (h : ∀ k l x, x ∈ O k → x ∈ O l → gs (𝟙 X) x (O k) (a k) = gs (𝟙 X) x (O l) (a l)) :
    ∃ b : Γ(X, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ O k →
      gs r z V b = gs r z (O k) (a k) := by
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' O V (fun k => homOfLE (hO k))
    (fun x hx => Opens.mem_iSup.2 (hc x hx)) a
    (fun k l => fn_ext (V := O k ⊓ O l) fun x hx =>
      (gs_res (𝟙 X) x inf_le_left hx _).trans ((h k l x hx.1 hx.2).trans
        (gs_res (𝟙 X) x inf_le_right hx _).symm))
  exact ⟨b, fun Z r z k hz => (gs_res r z (hO k) hz b).symm.trans (congrArg (gs r z (O k)) (hb k))⟩
end GlobalTheory.LinDescent
