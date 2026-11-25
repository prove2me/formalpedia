-- Prove2me | solution 1 for GlobalTheory.DegCnt.Compl.idx_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:21:12.717948+00:00
-- url     : https://prove2.me/submissions/8cbec23d-0cf0-47bd-90c0-1e6512961ec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IdxSupRight
import Theorems.Thm_GlobalTheory_DegCnt_Compl_idx_sup_right
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_inf_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Compl
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace GlobalTheory.DegCnt.Compl
theorem _root_.solution (M U U' : Submodule R W) :
    idx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), sup_comm M (U ⊓ _), idx_sup_right,
    ← DelScale.idx_inf_left, ← DelScale.idx_inf_left _ M]
  congr 1
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
end GlobalTheory.DegCnt.Compl
