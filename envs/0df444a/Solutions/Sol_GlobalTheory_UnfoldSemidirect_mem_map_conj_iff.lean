-- Prove2me | solution 1 for GlobalTheory.UnfoldSemidirect.mem_map_conj_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:23.181452+00:00
-- url     : https://prove2.me/submissions/06cbf484-a519-41f2-979a-3fa85a554952

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUnfoldSemidirectProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Subgroup
open GlobalTheory.UnfoldSemidirect
namespace GlobalTheory.UnfoldSemidirect
theorem _root_.solution {G : Type} [Group G] (K : Subgroup G) (g p : G) :
    p ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * p * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]
end GlobalTheory.UnfoldSemidirect
