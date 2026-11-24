-- Prove2me | solution 1 for GlobalTheory.WpFam.RowsSummed.norm_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:58.446338+00:00
-- url     : https://prove2.me/submissions/26fefb39-a85a-416b-9293-22b59f8d1812

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumResidueClassSplitBySignStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowSumEqQExpansionSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.RowsSummed
namespace GlobalTheory.WpFam.RowsSummed
theorem _root_.solution (N : ℕ) (j : ZMod N) : ‖ch N j‖ = 1 := by
  unfold ch
  rw [Complex.norm_exp]
  simp [Complex.div_re]
end GlobalTheory.WpFam.RowsSummed
