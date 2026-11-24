-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:16.564637+00:00
-- url     : https://prove2.me/submissions/b08eeafc-4661-4918-8d8e-66e6e21dba2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_UnipotentDecomposition_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution [IsLocalRing O] {α β : O} (hαβ : ¬ IsUnit (α * β)) :
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) O), Shape α β g → (∀ i, IsUnit (g i i)) →
      ∃ (u : Matrix (Fin n) (Fin n) O) (d : Fin n → Oˣ) (l : Matrix (Fin n) (Fin n) O),
        UpperUnip α u ∧ LowerUnip β l ∧ g = u * Matrix.diagonal (fun i => (d i : O)) * l ∧
          ∀ i, α * β ∣ (d i : O) - g i i := by
  first
  | exact @_root_.GlobalTheory.UnipotentDecomposition.main
  | exact _root_.GlobalTheory.UnipotentDecomposition.main
  | (apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentDecomposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentDecomposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentDecomposition.main ..)
end GlobalTheory.IwahoriFactor
