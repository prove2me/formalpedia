-- Prove2me | solution 1 for GlobalTheory.T.weierstrass_constant_q_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:06.017041+00:00
-- url     : https://prove2.me/submissions/eb774bbf-b8c5-4a39-884a-4ef258e7babb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassConstantQExpansionStatement
import Theorems.Thm_GlobalTheory_WpFam_hasQ_gN


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  first | exact @GlobalTheory.WpFam.hasQ_gN | exact GlobalTheory.WpFam.hasQ_gN | (intros; apply GlobalTheory.WpFam.hasQ_gN <;> assumption)
end _root_.GlobalTheory.T
