-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_valuation_two_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:53.05134+00:00
-- url     : https://prove2.me/submissions/ee1bc5aa-1a5a-408a-92b9-9239b46794a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsSquareUnderRingHomAdicCompletionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexUnitsLocalSquaresFiniteRealPlacesLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ e : ℕ, v.valuation F 2 = WithZero.exp (-(e : ℤ)) := by
  have h2 : (2 : F) = algebraMap (𝓞 F) F 2 := (map_ofNat _ 2).symm
  have hle : v.valuation F 2 ≤ 1 := by
    rw [h2]
    exact v.valuation_le_one 2
  have hne : v.valuation F 2 ≠ 0 := (Valuation.ne_zero_iff _).mpr two_ne_zero
  have hk : WithZero.log (v.valuation F 2) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log (v.valuation F 2)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
end GlobalTheory.QNorm
