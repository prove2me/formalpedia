-- Prove2me | solution 1 for GlobalTheory.BorelUMod.isCompact_vball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:38:39.337894+00:00
-- url     : https://prove2.me/submissions/a5c6df45-cb95-48e4-b573-692ba2ec62b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Theorems.Thm_GlobalTheory_BorelUMod_ball_eq_image
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
theorem _root_.solution [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)
end GlobalTheory.BorelUMod
