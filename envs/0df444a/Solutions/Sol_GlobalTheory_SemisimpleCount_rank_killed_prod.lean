-- Prove2me | solution 1 for GlobalTheory.SemisimpleCount.rank_killed_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:31.817433+00:00
-- url     : https://prove2.me/submissions/3c073cc4-91c4-4024-8d1f-7e8b408fb482

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroOfRankEq
import Theorems.Thm_GlobalTheory_SemisimpleCount_mem_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SemisimpleCount
variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
namespace GlobalTheory.SemisimpleCount
theorem _root_.solution :
    Module.rank ℂ (killed I (M × N)) =
      Module.rank ℂ (killed I M) + Module.rank ℂ (killed I N) := by
  have h : killed I (M × N) = (killed I M).prod (killed I N) := by
    ext ⟨a, b⟩
    simp only [mem_killed, Submodule.mem_prod, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  rw [h, ← rank_prod']
  refine LinearEquiv.rank_eq
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory.SemisimpleCount
