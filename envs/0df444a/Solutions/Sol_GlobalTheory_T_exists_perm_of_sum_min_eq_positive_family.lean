-- Prove2me | solution 1 for GlobalTheory.T.exists_perm_of_sum_min_eq_positive_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:43.541589+00:00
-- url     : https://prove2.me/submissions/5b7873fb-97b8-4f59-b6a5-07ebddcaa6f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamily
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsPermOfSumMinEqPositiveFamilyStatement
import Theorems.Thm_GlobalTheory_exists_equiv_of_sum_min_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ), (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) → ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  first | exact @GlobalTheory.exists_equiv_of_sum_min_eq | exact GlobalTheory.exists_equiv_of_sum_min_eq | (intros; apply GlobalTheory.exists_equiv_of_sum_min_eq <;> assumption)
end _root_.GlobalTheory.T
