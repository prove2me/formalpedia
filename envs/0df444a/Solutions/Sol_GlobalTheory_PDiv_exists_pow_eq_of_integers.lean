-- Prove2me | solution 1 for GlobalTheory.PDiv.exists_pow_eq_of_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:35.889966+00:00
-- url     : https://prove2.me/submissions/9a1c2016-05a7-4f31-ba3b-d4be3942577c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPMemSqCounitKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowEqOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PDiv
namespace GlobalTheory.PDiv
theorem _root_.solution {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {n : ℕ} (hn : 0 < n) (a : O) : ∃ b : O, b ^ n = a := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C a) hn
  have h1 : v c ^ n ≤ 1 := by
    rw [← map_pow, hc]
    exact hv.map_le_one a
  obtain ⟨b, rfl⟩ := hv.exists_of_le_one ((pow_le_one_iff hn.ne').1 h1)
  exact ⟨b, hv.hom_inj (by rw [map_pow, hc])⟩
end GlobalTheory.PDiv
