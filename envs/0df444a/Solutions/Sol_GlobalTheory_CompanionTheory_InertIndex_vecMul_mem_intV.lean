-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertIndex.vecMul_mem_intV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:59:18.348804+00:00
-- url     : https://prove2.me/submissions/43a83fe1-113d-43c0-bd58-a7423fdda3d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LatticeIndexOfSmith
import Theorems.Thm_GlobalTheory_InertZeta_mem_intV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertIndex
theorem _root_.solution {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) {r : Fin n → L} (hr : r ∈ intV L n) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  change ∑ i, r i * M i j ∈ intL L
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)
end GlobalTheory.CompanionTheory.InertIndex
