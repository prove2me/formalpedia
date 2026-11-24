-- Prove2me | solution 1 for GlobalTheory.T.prod_absNorm_pow_valuation_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:17.046382+00:00
-- url     : https://prove2.me/submissions/257d65f1-265b-473d-a406-9185c2ffdfb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ProdAbsNormPowValuationTwoLeStatement
import Theorems.Thm_GlobalTheory_QNorm_prod_absNorm_pow_le_two_pow


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | exact GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | (intros; apply GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow <;> assumption)
end _root_.GlobalTheory.T
