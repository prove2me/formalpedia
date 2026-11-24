-- Prove2me | solution 1 for GlobalTheory.Klein.not_red_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:12.469293+00:00
-- url     : https://prove2.me/submissions/8d8c7faf-99bb-446c-8c73-a5de44fa5069

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Klein
open Formalism.L2.Th1.F
open scoped ComplexConjugate
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
theorem _root_.solution (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {z : ℂ} (h : z ∈ L.lattice) : ¬ Red ι L r z :=
  fun h' => h'.1 h
end GlobalTheory.Klein
