-- Prove2me | solution 1 for GlobalTheory.JetSer.top_le_preimage_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:13:45.529974+00:00
-- url     : https://prove2.me/submissions/ba93ae8a-06c8-480c-9a80-172c848b9a1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.JetSer
variable {A : Type} [CommRing A] {X : Scheme.{0}}
namespace GlobalTheory.JetSer
theorem _root_.solution {T T' : Scheme.{0}} (r : T' ⟶ T) (p : T ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (r ≫ p) ⁻¹ᵁ U := fun z _ => by
  have : r z ∈ p ⁻¹ᵁ U := h trivial
  simpa using this
end GlobalTheory.JetSer
