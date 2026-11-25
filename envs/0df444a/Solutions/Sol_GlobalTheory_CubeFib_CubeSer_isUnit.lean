-- Prove2me | solution 1 for GlobalTheory.CubeFib.CubeSer.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:06.04217+00:00
-- url     : https://prove2.me/submissions/6c836ecd-d4f2-47cb-9b7f-4495687dc48c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_JetSer_jetAug_toJet


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
namespace CubeSer
theorem _root_.solution {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L}
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {i : L.L.ι} {Φ : PS k 3 d}
    (h : CubeSer c x i Φ) : IsUnit Φ := by
  obtain ⟨h0, h1⟩ := h 0
  have hu := (Semi.res h0 (pullU (jet3 x 0).left _ (c.t.s fun _ => i))).isUnit
  rw [h1] at hu
  have hu2 := hu.map (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) 0))).hom.hom
  rw [Iso.inv_hom_id_apply] at hu2
  have hu3 := hu2.map (Chart.jetAug k (Fin 3 × Fin d) 0)
  rw [GlobalTheory.JetSer.jetAug_toJet] at hu3
  exact MvPowerSeries.isUnit_iff_constantCoeff.2 hu3
end CubeSer
end GlobalTheory.CubeFib
