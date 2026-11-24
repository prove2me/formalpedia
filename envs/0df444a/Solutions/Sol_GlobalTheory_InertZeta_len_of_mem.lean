-- Prove2me | solution 1 for GlobalTheory.InertZeta.len_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:44:59.013119+00:00
-- url     : https://prove2.me/submissions/e161543b-a354-4dd2-bdf4-05bc557002c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
import Theorems.Thm_GlobalTheory_InertZeta_HasLen_len_eq
import Theorems.Thm_GlobalTheory_InertZeta_hasLen_of_isInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
namespace GlobalTheory.InertZeta
theorem _root_.solution {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : len (mat k) = 0 := by
  apply HasLen.len_eq
  apply hasLen_of_isInt
  intro i j
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨A, hA⟩ := (Subgroup.mem_inf.mp hk).2
  show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L
  rw [← hA]
  exact ((A : Matrix (Fin n) (Fin n) (intL L)) i j).2
end GlobalTheory.InertZeta
