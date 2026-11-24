-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.existsUnique_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:13.539277+00:00
-- url     : https://prove2.me/submissions/1ff3e5b4-af5a-4fa1-8c7f-2b9ffe9a4d3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_UnipotentBorder_iwahori_factorisation


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
theorem _root_.solution [IsLocalRing O] {α β : O} (hβ : ¬ IsUnit β) (g : GL (Fin n) O)
    (hg : Shape α β (g : Matrix (Fin n) (Fin n) O)) :
    ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O,
      UpperUnip α p.1 ∧ LowerUnip β p.2.2 ∧
        (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  first
  | exact @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation
  | (apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnipotentBorder.iwahori_factorisation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnipotentBorder.iwahori_factorisation ..)
end GlobalTheory.IwahoriFactor
