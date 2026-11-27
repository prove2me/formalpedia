-- Prove2me | solution 1 for GlobalTheory.TorsionRepresent.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:28.086494+00:00
-- url     : https://prove2.me/submissions/1d579772-cfe3-4212-8501-17eee32e3500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionFiniteFlatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionRepresent
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ)
namespace GlobalTheory.TorsionRepresent
theorem _root_.solution {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃ y : T ⟶ GlobalTheory.IndefiniteRowSideFullHecke.FlatTorsionIsomorphism.torsScheme G k, y ≫ incl G k = x := by
  refine ⟨pullback.lift x (toUnit _) ?_, pullback.lift_fst _ _ _⟩
  rw [MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
end GlobalTheory.TorsionRepresent
