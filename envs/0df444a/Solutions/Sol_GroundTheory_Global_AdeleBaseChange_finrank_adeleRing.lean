-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.finrank_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:34:04.43296+00:00
-- url     : https://prove2.me/submissions/ca9d0f4a-4d49-4570-8df5-d112204bfa37

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange

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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
variable (K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution : Module.finrank 𝔸[K] 𝔸[L] = Module.finrank K L := by
  rw [Module.finrank_eq_card_basis (adeleBasis (Module.finBasis K L)), Fintype.card_fin]
end GroundTheory.Global.AdeleBaseChange
