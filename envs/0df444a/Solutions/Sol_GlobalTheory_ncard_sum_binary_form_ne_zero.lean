-- Prove2me | solution 1 for GlobalTheory.ncard_sum_binary_form_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:43.790866+00:00
-- url     : https://prove2.me/submissions/eae6491a-66e5-481f-842e-aaea311f58f9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NcardSumBinaryFormNeZero
import Theorems.Thm_GlobalTheory_BinaryFormCount_card_fibre
import Theorems.Thm_GlobalTheory_BinaryFormCount_card_sum_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory
open Finset
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] [Finite k] (t n : k)
    (hD : t ^ 2 - 4 * n ≠ 0) (η : ℝ) (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (M : ℕ) :
    ({x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard : ℝ)
      * (Nat.card k : ℝ)
      = ((Nat.card k : ℝ) - 1) * ((Nat.card k : ℝ) ^ (2 * M) - (η * (Nat.card k : ℝ)) ^ M) := by
  classical
  haveI := Fintype.ofFinite k
  have hz := BinaryFormCount.card_sum_zero
    (fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (Fintype.card k) η
    (by rw [Fintype.card_prod]; push_cast; ring) (BinaryFormCount.card_fibre hD h1 h2) M
  have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M → k × k)))
    (fun x => ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0)
  have hb : {x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard
      = #{x : Fin M → k × k |
        ¬ ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0} := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    refine Finset.card_nbij' (fun x i => (x (i, 0), x (i, 1)))
      (fun x p => ![(x p.1).1, (x p.1).2] p.2) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      simpa using hx
    · intro x _
      ext ⟨i, j⟩
      fin_cases j <;> simp
    · intro x _
      ext i <;> simp
  rw [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at hs
  have h3 := congrArg (Nat.cast : ℕ → ℝ) hs
  push_cast at h3
  rw [hb, Nat.card_eq_fintype_card, pow_mul, pow_two]
  rw [pow_mul, pow_two] at hz
  linear_combination (Fintype.card k : ℝ) * h3 - hz
end GlobalTheory
