-- Prove2me | solution 1 for NaturalProofs.expand_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:38.023978+00:00
-- url     : https://prove2.me/submissions/e89e4264-b363-4604-824d-fe01b77b9264

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_init_pre
public import Theorems.Thm_NaturalProofs_pre_last

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
namespace NaturalProofs
theorem _root_.solution {k n : ℕ} (i : ℕ) (M : (Fin i → Bool) → Fin (2 * k) → Bool)
    (x : Fin n → Bool) :
    expand M (pre (i + 1) x) = half ((List.ofFn x).getD i false) (M (pre i x)) := by
  simp [expand, init_pre, pre_last]
end NaturalProofs
