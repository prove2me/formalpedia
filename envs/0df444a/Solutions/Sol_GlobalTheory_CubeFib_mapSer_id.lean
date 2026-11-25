-- Prove2me | solution 1 for GlobalTheory.CubeFib.mapSer_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:42:58.708544+00:00
-- url     : https://prove2.me/submissions/6024b33a-7382-4211-95d8-becd0d01c987

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_JetSer_toJet_X


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
theorem _root_.solution {G : Over (Sp k)} (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G) :
    MapSer (𝟙 G) x x (pt k d 0) := by
  intro m
  refine ⟨AlgHom.id k _, fun j => (GlobalTheory.JetSer.toJet_X m _).symm, ?_⟩
  have : algOverHom (AlgHom.id k (JetR k (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  rw [this, Category.id_comp, Category.comp_id]
end GlobalTheory.CubeFib
