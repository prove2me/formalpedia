-- Prove2me | solution 1 for GlobalTheory.Jets.hasSubst_add_sqZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:59:51.038861+00:00
-- url     : https://prove2.me/submissions/d4d6a67e-e71d-4221-97ed-cd98b0eb834d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro s
  rw [map_add, map_mul]
  have h1 : IsNilpotent (constantCoeff e) := ⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩
  exact (Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)
end GlobalTheory.Jets
