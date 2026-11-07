-- Prove2me | solution 1 for NaturalProofs.init_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:12.593195+00:00
-- url     : https://prove2.me/submissions/5f8628b2-7cb4-4a52-980c-c919b47038c2

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
theorem _root_.solution {n : ℕ} (i : ℕ) (x : Fin n → Bool) : Fin.init (pre (i + 1) x) = pre i x := by
  funext j
  simp [Fin.init, pre]
end NaturalProofs
