-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.map_conj_inf_ker_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:32.327436+00:00
-- url     : https://prove2.me/submissions/2894e265-bf17-46dc-ae70-accf28139968

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {g : G} (hg : g ∈ (K : Subgroup G)) :
    ((K : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom =
      (K : Subgroup G) ⊓ D.deg.ker := by
  have : ((K : Subgroup G).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact map_conj_inf_ker le_rfl hg
end GroundTheory.LocalField.Abstract.ClassFieldData
