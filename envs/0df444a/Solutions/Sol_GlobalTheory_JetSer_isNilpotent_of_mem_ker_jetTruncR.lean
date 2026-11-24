-- Prove2me | solution 1 for GlobalTheory.JetSer.isNilpotent_of_mem_ker_jetTruncR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:49.389582+00:00
-- url     : https://prove2.me/submissions/920da02f-3046-4f13-89f7-ceda9624b7c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
variable {R : Type} [CommRing R] {κ : Type}
namespace GlobalTheory.JetSer
theorem _root_.solution (m : ℕ) (a : JetR R κ (m + 1))
    (ha : a ∈ RingHom.ker (jetTruncR R κ m).toRingHom) : IsNilpotent a := by
  have e : (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have ha' : jetTruncR R κ m a = 0 := ha
  have h1 : a ∈ RingHom.ker (jetAug R κ (m + 1)) := by
    rw [RingHom.mem_ker, ← e, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  have := Ideal.pow_mem_pow h1 (m + 1 + 1)
  rwa [ker_jetAug_pow, Ideal.mem_bot] at this
end GlobalTheory.JetSer
