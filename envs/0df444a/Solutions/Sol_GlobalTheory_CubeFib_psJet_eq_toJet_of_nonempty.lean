-- Prove2me | solution 1 for GlobalTheory.CubeFib.psJet_eq_toJet_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:47.766678+00:00
-- url     : https://prove2.me/submissions/cf67ddde-e9e7-472a-8b1c-652a180166b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_mk_iff


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
open GlobalTheory GlobalTheory.CubeFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type} [CommRing k] {d g : ℕ}
namespace GlobalTheory.CubeFib
theorem _root_.solution {n : ℕ} [Nonempty (Fin n × Fin d)] (m : ℕ) (f : PS k n d) :
    psJet m f = GlobalTheory.JetSer.toJet m f := by
  symm
  refine (GlobalTheory.JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_
  rw [MvPowerSeries.coeff_trunc, if_pos]
  have hle : ∀ i, e i ≤ m := fun i => by have := Finsupp.le_degree i e; omega
  refine lt_of_le_of_ne (fun i => ?_) fun h => ?_
  · simpa using (hle i).trans (Nat.le_succ m)
  · have := hle (Classical.arbitrary _)
    rw [h] at this
    simp at this
end GlobalTheory.CubeFib
