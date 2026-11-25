-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extPair_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:08.845489+00:00
-- url     : https://prove2.me/submissions/14792b31-606f-45d9-9687-cc78d998700f

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitDualParts_extMul_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
theorem _root_.solution {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (β : M →ₗ[O] M' →ₗ[O] O) (r r' : R) (a : M) (a' : M') :
    extPair R β (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = β a a' • (r * r') := by
  simp [extPair, extMul_tmul]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
