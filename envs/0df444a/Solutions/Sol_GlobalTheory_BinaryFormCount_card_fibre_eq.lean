-- Prove2me | solution 1 for GlobalTheory.BinaryFormCount.card_fibre_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:59.018255+00:00
-- url     : https://prove2.me/submissions/901688f9-a0f8-4126-9f79-c922c0c6c77a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NcardSumBinaryFormNeZero

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
theorem _root_.solution {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {c : k} (hc : c ≠ 0) :
    #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c}
      = #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 1} := by
  obtain ⟨u, v, huv⟩ := UnramifiedHermitian.exists_binary_eq_of_finite hD c
  symm
  refine Finset.card_nbij' (fun p => (p.1 * u - n * p.2 * v, p.1 * v + p.2 * u + t * p.2 * v))
    (fun p => ((p.1 * (u + t * v) + n * p.2 * v) / c, (p.2 * u - p.1 * v) / c)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + huv
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    field_simp
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + c * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv
end GlobalTheory.BinaryFormCount
