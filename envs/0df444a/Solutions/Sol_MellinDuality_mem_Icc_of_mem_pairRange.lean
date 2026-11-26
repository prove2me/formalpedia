-- Prove2me | solution 1 for MellinDuality.mem_Icc_of_mem_pairRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:59.588294+00:00
-- url     : https://prove2.me/submissions/6cfc6fd6-1436-4920-99f7-01d91f3974c3

module
public import Definitions.Def_MellinDuality_Quartic
public import Definitions.Def_MellinDuality_Parseval
public import Definitions.Def_MellinDuality_Pairs
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution {N : ℕ} {ab : ℕ × ℕ} {r : ℕ}
    (hr : r ∈ pairRange N ab) : r ∈ Icc 1 N := by
  simp only [pairRange, mem_Icc] at hr ⊢
  refine ⟨hr.1, hr.2.trans (Nat.div_le_self _ _)⟩
end MellinDuality
