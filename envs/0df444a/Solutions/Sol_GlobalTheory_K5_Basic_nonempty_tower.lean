-- Prove2me | solution 1 for GlobalTheory.K5.Basic.nonempty_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:33.373859+00:00
-- url     : https://prove2.me/submissions/6d79fd9d-95c7-4ebb-bfd0-eac79a1f0225

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_tw_prim_step
import Theorems.Thm_GlobalTheory_K5_Basic_tw_exists_prim_p
import Theorems.Thm_GlobalTheory_K5_Basic_tw_exists_root_chain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (h : IsClo p Ω) : Nonempty (Tower p Ω) := by
  haveI := h.clo
  haveI : CharZero Ω := charZero_of_injective_algebraMap h.inj
  obtain ⟨z, hz⟩ := tw_exists_prim_p (p := p) Ω
  obtain ⟨f, hf0, hf⟩ := tw_exists_root_chain (p := p) z
  obtain ⟨g, hg0, hg⟩ := tw_exists_root_chain (p := p) (algebraMap (O0 p) Ω (qO p))
  have hprim : ∀ n, IsPrimitiveRoot (f n) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [hf0] using hz
    | succ m ih => exact tw_prim_step ih (hf m)
  refine ⟨{ ζ := fun n => Nat.casesOn n 1 f
            qq := g
            prim := ?_
            ζpow := ?_
            q0 := hg0
            qpow := hg }⟩
  · intro n
    cases n with
    | zero => simpa using IsPrimitiveRoot.one
    | succ m => exact hprim m
  · intro n
    cases n with
    | zero =>
      show f 0 ^ p = 1
      rw [hf0, hz.pow_eq_one]
    | succ m => exact hf m
end GlobalTheory.K5.Basic
