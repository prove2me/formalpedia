-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks.cj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:00:21.25817+00:00
-- url     : https://prove2.me/submissions/6dd2c69f-2fbe-44bd-9de1-9161b63de3b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
theorem _root_.solution (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualHermitianLatticesTorsionBlocks
