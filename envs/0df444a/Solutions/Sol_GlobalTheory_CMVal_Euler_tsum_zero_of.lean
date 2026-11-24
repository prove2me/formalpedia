-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.tsum_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:51.906489+00:00
-- url     : https://prove2.me/submissions/0cbe68de-47c9-48ff-87c3-20c47804f6ef

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_translate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (u : G) (hu : ω u ≠ 1)
    (h : ∀ y, u⁻¹ * y ∈ M ↔ y ∈ M) : ∑' z, cs U ω M z = 0 := by
  have h1 := tsum_translate hω hM u
  have h2 : {y | u⁻¹ * y ∈ M} = M := Set.ext h
  rw [h2] at h1
  have h3 : (ω u - 1) * ∑' z, cs U ω M z = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hu)
end GlobalTheory.CMVal.Euler
