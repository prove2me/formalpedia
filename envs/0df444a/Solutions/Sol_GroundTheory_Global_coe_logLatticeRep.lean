-- Prove2me | solution 1 for GroundTheory.Global.coe_logLatticeRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:08.713032+00:00
-- url     : https://prove2.me/submissions/495df510-7655-49c5-a676-92fe4ce180b5

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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField K] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (g : L ≃ₐ[K] L) (m : logLattice L) :
    (logLatticeRep K L g m : InfinitePlace L → ℝ) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m :=
  rfl
end GroundTheory.Global
