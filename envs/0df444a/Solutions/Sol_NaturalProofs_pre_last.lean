-- Prove2me | solution 1 for NaturalProofs.pre_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:22.847044+00:00
-- url     : https://prove2.me/submissions/356e33b9-6cc5-47e8-b057-de4607aa156f

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
namespace NaturalProofs
theorem _root_.solution {n : ℕ} (i : ℕ) (x : Fin n → Bool) :
    pre (i + 1) x (Fin.last i) = (List.ofFn x).getD i false := by
  simp [pre]
end NaturalProofs
