-- Prove2me | solution 1 for NaturalProofs.hybF_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:41:07.716457+00:00
-- url     : https://prove2.me/submissions/8a94835d-d7a5-4202-af04-52cb606da64d

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
public import Theorems.Thm_NaturalProofs_expand_pre

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)
namespace NaturalProofs
theorem _root_.solution {k n : ℕ} (i : ℕ) (hi : i < n) (L : (Fin i → Bool) → Bits k) :
    (hybF G i L : BoolFn n) = hybF G (i + 1) (expand (fun p => G k (L p))) := by
  funext x
  simp only [hybF, expand_pre]
  have hlen : i < (List.ofFn x).length := by simpa using hi
  rw [List.drop_eq_getElem_cons hlen, List.getD_eq_getElem _ _ hlen]
  simp [walk]
end NaturalProofs
