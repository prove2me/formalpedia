-- Prove2me | solution 1 for NaturalProofs.startC_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:04.166195+00:00
-- url     : https://prove2.me/submissions/0989bfe6-4f24-405b-9d86-a0c73989e7bb

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_MCircuit_wires_eval


set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))
namespace NaturalProofs
theorem _root_.solution {k n : ℕ} (i : ℕ) (e : Fin i → Bool) (c : (Fin i → Bool) → Fin (2 * k) → Bool)
    (x : Fin n → Bool) (y : Fin (2 * k) → Bool) :
    (startC i e c x).eval y =
      half ((List.ofFn x).getD i false) (Function.update c e y (pre i x)) := by
  funext j
  by_cases h : pre i x = e
  · simp [startC, h, wires_eval, Wire.eval, half]
  · simp [startC, h, wires_eval, Wire.eval]
end NaturalProofs
