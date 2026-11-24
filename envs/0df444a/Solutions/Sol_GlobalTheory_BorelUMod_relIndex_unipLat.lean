-- Prove2me | solution 1 for GlobalTheory.BorelUMod.relIndex_unipLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:34.942277+00:00
-- url     : https://prove2.me/submissions/1a8f61f8-2199-46da-b9dc-8606010deef9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_relIndex_unipLat
import Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_upLat
import Theorems.Thm_GlobalTheory_BorelUMod_relIndex_upLat_eq_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
namespace GlobalTheory.BorelUMod
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by
  rw [Cayley.relIndex_unipLat L ϖ σ q n h c C hc hC hI]
  have h1 := relIndex_upLat_eq_sq L ϖ σ q n h c C hc.1 hC.1 hI.1
  rw [UpLatIndex.relIndex_upLat L ϖ σ q n h c C hI.1, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm, pow_mul] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm
end GlobalTheory.BorelUMod
