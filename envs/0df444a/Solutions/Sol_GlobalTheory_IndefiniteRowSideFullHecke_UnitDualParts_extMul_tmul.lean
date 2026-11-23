-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.extMul_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:29.687318+00:00
-- url     : https://prove2.me/submissions/b66f5d1e-ced4-4464-93d2-b1c62b617c8f

import Mathlib
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_Statement
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_UnitDualParts

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
theorem _root_.solution {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']
    (m : M ⊗[O] M' →ₗ[O] M'') (r r' : R) (a : M) (a' : M') :
    extMul R m (r ⊗ₜ[O] a) (r' ⊗ₜ[O] a') = (r * r') ⊗ₜ[O] m (a ⊗ₜ[O] a') := by
  simp [extMul]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
