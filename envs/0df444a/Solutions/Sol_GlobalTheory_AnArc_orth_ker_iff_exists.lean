-- Prove2me | solution 1 for GlobalTheory.AnArc.orth_ker_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:53:21.376988+00:00
-- url     : https://prove2.me/submissions/48acac3e-5179-43d0-8a6e-c5e26e3ca151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_AnArc_orth_ker_iff
import Theorems.Thm_GlobalTheory_AnArc_y_l_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ ∃ n, v = La.mk 0 n 0 :=
  (A.orth_ker_iff v).trans (A.y_l_eq_zero_iff v)
end GlobalTheory.AnArc
