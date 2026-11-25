-- Prove2me | solution 1 for GlobalTheory.PowSmulMem.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:02.912718+00:00
-- url     : https://prove2.me/submissions/d8d2e1ef-011f-4149-852e-f640c50cd28f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Theorems.Thm_GlobalTheory_PowSmulMem_exists_pow_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowSmulMem
namespace GlobalTheory.PowSmulMem
theorem _root_.solution : ∀ {E : Type} [inst : CommRing E] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module E V] {O : Subring E} {p : E}, p ∈ O → (∀ (e : E), ∃ (a : ℕ), p ^ a * e ∈ O) → ∀ (Λ Λ' : Submodule (↥O) V), Submodule.FG Λ → Submodule.span E (↑Λ' : Set V) = ⊤ → ∃ (a : ℕ), ∀ v ∈ Λ, p ^ a • v ∈ Λ' := by
  intro E _ V _ _ O p hp hO Λ Λ' hfg hsp
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose f hf using exists_pow_smul_mem hp hO Λ' hsp
  refine ⟨s.sup f, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hf x _ (Finset.le_sup (Finset.mem_coe.mp hx))
  | zero => rw [smul_zero]; exact Λ'.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Λ'.add_mem hx hy
  | smul e x _ hx =>
    have h : p ^ s.sup f • e • x = e • (p ^ s.sup f • x) := by
      change p ^ s.sup f • (e : E) • x = (e : E) • (p ^ s.sup f • x)
      exact smul_comm _ _ _
    rw [h]
    exact Λ'.smul_mem e hx
end GlobalTheory.PowSmulMem
