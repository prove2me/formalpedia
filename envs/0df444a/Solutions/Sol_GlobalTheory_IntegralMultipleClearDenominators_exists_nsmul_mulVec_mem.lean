-- Prove2me | solution 1 for GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:47.301976+00:00
-- url     : https://prove2.me/submissions/81999750-93a5-4895-9c7c-578272927fcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nsmul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultipleClearDenominators
open NumberField
namespace GlobalTheory.IntegralMultipleClearDenominators
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx
end GlobalTheory.IntegralMultipleClearDenominators
