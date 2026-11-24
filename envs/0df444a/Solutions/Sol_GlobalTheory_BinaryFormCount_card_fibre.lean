-- Prove2me | solution 1 for GlobalTheory.BinaryFormCount.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:14.455388+00:00
-- url     : https://prove2.me/submissions/903193af-0764-43ec-b29d-d578c55f2133

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NcardSumBinaryFormNeZero
import Theorems.Thm_GlobalTheory_BinaryFormCount_card_fibre_eq
import Theorems.Thm_GlobalTheory_BinaryFormCount_card_zero

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
open GlobalTheory GlobalTheory.BinaryFormCount
open Finset
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]
namespace GlobalTheory.BinaryFormCount
theorem _root_.solution {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (c : k) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c} : ℝ)
      = Fintype.card k - η + if c = 0 then η * Fintype.card k else 0 := by
  have hz := card_zero hD h1 h2
  by_cases hc : c = 0
  · rw [if_pos hc, hc, hz]
  rw [if_neg hc, card_fibre_eq hD hc, add_zero]
  have tot := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (k × k))) (t := univ)
    (f := fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (fun _ _ => mem_univ _)
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : k)),
    Finset.sum_congr rfl (fun d hd => card_fibre_eq hD (Finset.ne_of_mem_erase hd)),
    sum_const, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_prod,
    smul_eq_mul] at tot
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h3 := congrArg (Nat.cast : ℕ → ℝ) tot
  push_cast [Nat.cast_sub hq.le] at h3
  rw [hz] at h3
  have hq' : (Fintype.card k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card k := by exact_mod_cast hq
    linarith
  apply mul_left_cancel₀ hq'
  linear_combination -h3
end GlobalTheory.BinaryFormCount
