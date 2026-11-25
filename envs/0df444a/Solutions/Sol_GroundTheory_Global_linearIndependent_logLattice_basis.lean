-- Prove2me | solution 1 for GroundTheory.Global.linearIndependent_logLattice_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:18.700741+00:00
-- url     : https://prove2.me/submissions/80fb0859-924a-4d43-9b33-e9ce490fee62

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
noncomputable section
open scoped Classical
variable (L : Type*) [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (fun i => (b i : InfinitePlace L → ℝ)) := by
  apply LinearIndependent.of_comp (logProj L)
  have := ((b.map (logLatticeEquiv L)).ofZLatticeBasis ℝ (unitLattice L)).linearIndependent
  convert this using 1
  · funext i
    rw [Basis.ofZLatticeBasis_apply, Basis.map_apply]
    rfl
  all_goals rfl
end GroundTheory.Global
