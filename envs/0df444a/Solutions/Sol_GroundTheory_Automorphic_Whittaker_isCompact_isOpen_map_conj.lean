-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isCompact_isOpen_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:58.360905+00:00
-- url     : https://prove2.me/submissions/26034a63-ce8d-4635-a983-e1edd5427775

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
  [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [ContinuousSMul H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {L : Subgroup H} (hLc : IsCompact (L : Set H))
    (hLo : IsOpen (L : Set H)) (h : H) :
    IsCompact ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) ∧
      IsOpen ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) := by
  have e : ((L.map (MulAut.conj h).toMonoidHom : Subgroup H) : Set H) =
      ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)) '' (L : Set H) := by
    ext x
    simp [Subgroup.coe_map, MulAut.conj_apply]
  rw [e]
  exact ⟨hLc.image (Homeomorph.continuous _), (Homeomorph.isOpenMap _) _ hLo⟩
end GroundTheory.Automorphic.Whittaker
