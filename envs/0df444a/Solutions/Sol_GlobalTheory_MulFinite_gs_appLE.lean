-- Prove2me | solution 1 for GlobalTheory.MulFinite.gs_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:58.465268+00:00
-- url     : https://prove2.me/submissions/a3d69812-e806-48bd-9223-2862dc31ff5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField

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
noncomputable section
open GlobalTheory GlobalTheory.MulFinite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial
namespace GlobalTheory.MulFinite
theorem _root_.solution {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (V : Z.Opens) (hle : V ≤ r ⁻¹ᵁ U)
    (h : z ∈ V) (a : Γ(Y, U)) : gs (𝟙 Z) z V ((r.appLE U V hle).hom a) = gs r z U a :=
  (gs_res (𝟙 Z) z hle h _).trans ((gs_pull (𝟙 Z) r z U (hle h) a).trans (by rw [Category.id_comp]))
end GlobalTheory.MulFinite
