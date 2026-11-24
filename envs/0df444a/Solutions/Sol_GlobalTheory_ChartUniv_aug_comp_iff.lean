-- Prove2me | solution 1 for GlobalTheory.ChartUniv.aug_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:46.49104+00:00
-- url     : https://prove2.me/submissions/2263d4b2-30fb-4a3e-9878-4dcb96a14d2e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Theorems.Thm_GlobalTheory_ChartUniv_jetAug_eq
import Theorems.Thm_GlobalTheory_ChartUniv_jetZero_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartUniv
theorem _root_.solution {κ κ' : Type} {m : ℕ} (ψ : JetR R κ m →ₐ[R] JetR R κ' m) :
    (jetAug R κ' m).comp ψ = jetAug R κ m ↔ ∀ j, jetZeroR R κ' m (ψ (zR m j)) = 0 := by
  constructor
  · intro h j
    have := AlgHom.congr_fun h (zR m j)
    rw [AlgHom.comp_apply, jetAug_zR] at this
    rw [jetZero_eq, AlgHom.comp_apply, this, map_zero]
  · intro h
    refine jet_ext fun j => ?_
    rw [AlgHom.comp_apply, jetAug_zR, jetAug_eq, AlgHom.comp_apply, h, map_zero]
end GlobalTheory.ChartUniv
