-- Prove2me | solution 1 for GlobalTheory.EffCartierData.keepsRegular_of_isDominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:30.371824+00:00
-- url     : https://prove2.me/submissions/39d53740-eaf8-4fbe-9746-29afe48c3078

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_keepsRegular_of_notMem_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution [IsIntegral Y] (φ : Y ⟶ X) [IsDominant φ] :
    D.KeepsRegular φ := by
  have : Nonempty X := ⟨φ (genericPoint Y)⟩
  obtain ⟨y, hy⟩ := φ.denseRange.exists_mem_open (Out.nonzeroLocus D.canonical).isOpen
    D.dense_nonzeroLocus_canonical.nonempty
  exact D.keepsRegular_of_notMem_support φ (y := y) (D.coe_nonzeroLocus_canonical.le hy)
end GlobalTheory.EffCartierData
