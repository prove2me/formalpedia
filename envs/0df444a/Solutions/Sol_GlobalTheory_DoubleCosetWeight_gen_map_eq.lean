-- Prove2me | solution 1 for GlobalTheory.DoubleCosetWeight.gen_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:43.752666+00:00
-- url     : https://prove2.me/submissions/8c581151-719b-42b5-a04d-7031aa820127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
import Theorems.Thm_GlobalTheory_DoubleCosetWeight_gen_map_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DoubleCosetWeight
open Subgroup
namespace GlobalTheory.DoubleCosetWeight
theorem _root_.solution {G : Type} [Group G] (T K : Subgroup G) {t : G} (ht : t ∈ T) :
    (gen T K).map (MulAut.conj t).toMonoidHom = gen T K := by
  refine le_antisymm (gen_map_le T K ht) fun x hx => ?_
  have : (MulAut.conj t⁻¹).toMonoidHom x ∈ gen T K :=
    gen_map_le T K (T.inv_mem ht) (mem_map_of_mem _ hx)
  refine ⟨_, this, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]
end GlobalTheory.DoubleCosetWeight
