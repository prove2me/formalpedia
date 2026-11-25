-- Prove2me | solution 1 for GlobalTheory.RepUniq.LocCoord.of_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:34.705563+00:00
-- url     : https://prove2.me/submissions/e4638996-b617-4f55-a9f0-1edd3791eb34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsoOfProjectiveCoordinateRepresentation
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.RepUniq
open TopologicalSpace GlobalTheory.Cartier GlobalTheory.ProjSpace
variable {σ : Type} {T T' X X' X'' : Scheme.{0}}
variable {M : LB X} {th : σ → M.Sec} {M' : LB X'} {th' : σ → M'.Sec} {M'' : LB X''} {th'' : σ → M''.Sec}
  {x : T ⟶ X} {x' : T ⟶ X'} {x'' : T ⟶ X''}
namespace GlobalTheory.RepUniq
namespace LocCoord
theorem _root_.solution {v : σ → Γ(T, ⊤)} (H : LocCoord M th x v) (H' : Same M th x M' th' x') :
    LocCoord M' th' x' v := fun t => by
  obtain ⟨W, hW, h₁⟩ := H t
  obtain ⟨V, hV, f', h₃, h₄⟩ := H' t
  obtain ⟨c, hc, e⟩ := (h₁.res (inf_le_left : W ⊓ V ≤ W)).ratio (h₃.res inf_le_right)
  refine ⟨W ⊓ V, ⟨hW, hV⟩, (h₄.res inf_le_right).mul hc fun i => (e i).trans ?_⟩
  rw [resG_resG]
end LocCoord
end GlobalTheory.RepUniq
