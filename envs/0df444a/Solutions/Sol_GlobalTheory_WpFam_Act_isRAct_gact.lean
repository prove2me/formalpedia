-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.isRAct_gact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:53.575424+00:00
-- url     : https://prove2.me/submissions/2374cfed-272f-4861-864a-efc627524ee4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
import Theorems.Thm_GlobalTheory_WpFam_Act_redGL_mul
import Theorems.Thm_GlobalTheory_WpFam_Act_redGL_one

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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.Act
namespace GlobalTheory.WpFam.Act
theorem _root_.solution (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by
  constructor
  · intro x; simp [gact, redGL_one]
  · intro x γ δ; simp only [gact, redGL_mul]; group
end GlobalTheory.WpFam.Act
