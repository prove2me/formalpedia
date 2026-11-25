-- Prove2me | solution 1 for GlobalTheory.T.diagonal_entry_of_semilinear_mod_subspace_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:46.005834+00:00
-- url     : https://prove2.me/submissions/d0b6f39c-4e4d-465f-bea3-c65d3ccc755a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagonalEntryOfSemilinearModSubspace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagonalEntryOfSemilinearModSubspaceStatement
import Theorems.Thm_GlobalTheory_diagonal_entry_of_semilinear_mod_subspace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by
  first | exact @GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | exact GlobalTheory.diagonal_entry_of_semilinear_mod_subspace | (intros; apply GlobalTheory.diagonal_entry_of_semilinear_mod_subspace <;> assumption)
end _root_.GlobalTheory.T
