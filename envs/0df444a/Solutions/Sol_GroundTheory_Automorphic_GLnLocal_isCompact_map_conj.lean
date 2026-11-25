-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isCompact_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:19.452748+00:00
-- url     : https://prove2.me/submissions/80e19dbc-bca0-4eb0-b261-cff1c5b389df

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution (g : GL (Fin n) F) {H : Subgroup (GL (Fin n) F)}
    (hH : IsCompact (H : Set (GL (Fin n) F))) :
    IsCompact (H.map (MulAut.conj g).toMonoidHom : Set (GL (Fin n) F)) := by
  rw [Subgroup.coe_map]
  refine hH.image ?_
  have : ⇑(MulAut.conj g).toMonoidHom = fun x => g * x * g⁻¹ := rfl
  rw [this]
  fun_prop
end GroundTheory.Automorphic.GLnLocal
