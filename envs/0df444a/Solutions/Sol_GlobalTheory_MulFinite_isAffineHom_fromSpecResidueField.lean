-- Prove2me | solution 1 for GlobalTheory.MulFinite.isAffineHom_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:04.229788+00:00
-- url     : https://prove2.me/submissions/578d1e33-ad06-4c97-b39b-b1c13763245c

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
theorem _root_.solution (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : y ∈ U
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_top _
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_bot _
end GlobalTheory.MulFinite
