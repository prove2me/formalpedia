-- Prove2me | solution 1 for NaturalProofs.hybF_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:56.272571+00:00
-- url     : https://prove2.me/submissions/100828e4-5f76-4163-86b3-e91e2e728345

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
theorem _root_.solution {k n : ℕ} (L : (Fin n → Bool) → Bits k) :
    (hybF G n L : BoolFn n) = fun x => firstBit (L x) := by
  funext x
  have hpre : pre n x = x := by
    funext j
    simp [pre]
  simp [hybF, hpre, walk, List.drop_eq_nil_of_le (by simp : (List.ofFn x).length ≤ n)]
end NaturalProofs
