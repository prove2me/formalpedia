-- Prove2me | solution 1 for GlobalTheory.SecAff.eq_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:11.817277+00:00
-- url     : https://prove2.me/submissions/beff8ed0-df1d-447e-9b88-409af3a14a76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution {κ : Type} {U : X.Opens} (W : κ → X.Opens) (hW : ∀ a, W a ≤ U)
    (hc : U ≤ ⨆ a, W a) (x y : Γ(X, U)) (h : ∀ a, rs (hW a) x = rs (hW a) y) : x = y :=
  X.sheaf.eq_of_locally_eq' W U (fun a => homOfLE (hW a)) hc x y h
end GlobalTheory.SecAff
