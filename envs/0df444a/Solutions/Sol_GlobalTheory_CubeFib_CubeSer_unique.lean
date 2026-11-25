-- Prove2me | solution 1 for GlobalTheory.CubeFib.CubeSer.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:13.183352+00:00
-- url     : https://prove2.me/submissions/80235359-ef53-4ab6-aedd-3ccaeed81c76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_JetSer_eq_of_toJet_eq


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
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {i : L.L.ι} {Φ Φ' : PS k 3 d}
    (h : CubeSer c x i Φ) (h' : CubeSer c x i Φ') : Φ = Φ' := by
  refine GlobalTheory.JetSer.eq_of_toJet_eq fun m => ?_
  obtain ⟨_, h1⟩ := h m
  obtain ⟨_, h2⟩ := h' m
  exact (Scheme.ΓSpecIso (CommRingCat.of (JetR k (Fin 3 × Fin d) m))).symm.commRingCatIsoToRingEquiv.injective
    (h1.symm.trans h2)
end CubeSer
end GlobalTheory.CubeFib
