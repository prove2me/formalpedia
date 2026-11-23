-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.mk_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:44.227795+00:00
-- url     : https://prove2.me/submissions/aa6a0a1f-6186-4672-a1f0-420aa77afb2e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleClassGroup
namespace GroundTheory.Global.IdeleClassGroup
theorem _root_.solution (x : Kˣ) : mk K (IdeleGroup.diagonal K x) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
end GroundTheory.Global.IdeleClassGroup
