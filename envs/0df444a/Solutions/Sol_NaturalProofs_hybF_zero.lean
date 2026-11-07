-- Prove2me | solution 1 for NaturalProofs.hybF_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:38.856062+00:00
-- url     : https://prove2.me/submissions/c9f25886-19c3-4daa-ac38-3fcecfd6bc3e

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
theorem _root_.solution {k n : ℕ} (L : (Fin 0 → Bool) → Bits k) (p : Fin 0 → Bool) :
    (hybF G 0 L : BoolFn n) = prf G k n (L p) := by
  funext x
  simp only [hybF, prf, List.drop_zero]
  congr 2
  exact congrArg L (Subsingleton.elim _ _)
end NaturalProofs
