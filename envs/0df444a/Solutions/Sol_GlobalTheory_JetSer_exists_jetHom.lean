-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_jetHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:40.256528+00:00
-- url     : https://prove2.me/submissions/d8d4e514-6f07-4714-92a2-0dc547bbba04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_jetAug_toJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution {σ : Type} (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ) :
    ∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j) :=
  ⟨jetLift R (RingHom.ker (jetAug R κ m)) (ker_jetAug_pow κ m) (fun j => toJet m (a j))
    (fun j => (jetAug_toJet m (a j)).trans (ha j)), fun j => jetLift_zR _ _ _ _ j⟩
end GlobalTheory.JetSer
