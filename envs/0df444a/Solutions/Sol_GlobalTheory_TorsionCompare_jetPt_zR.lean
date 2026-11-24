-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.jetPt_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:27.67924+00:00
-- url     : https://prove2.me/submissions/c5342f16-7f93-4d20-b52b-4ea0798e22a4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
import Theorems.Thm_GlobalTheory_TorsionCompare_psJet_eq_jetOfSeries
import Theorems.Thm_GlobalTheory_TorsionCompare_substJ_zR
import Theorems.Thm_GlobalTheory_TorsionCompare_jetOfSeries_X

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R]
namespace GlobalTheory.TorsionCompare
theorem _root_.solution {n d : ℕ} (i : Fin n) (m : ℕ) (q : Fin 1 × Fin d) :
    jetPt (T := R) i m (zR m q) = zR m (i, q.2) := by
  have : Nonempty (Fin n × Fin d) := ⟨(i, q.2)⟩
  unfold jetPt
  rw [substJ_zR, psJet_eq_jetOfSeries, jetOfSeries_X]
end GlobalTheory.TorsionCompare
