-- Prove2me | solution 1 for GlobalTheory.AnArc.smul_periodMap_mk_zero_fst_eq_neg_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:22.349886+00:00
-- url     : https://prove2.me/submissions/af8226b8-3a22-41a9-948b-3bc36dc49950

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_AnArc_EF_n_left


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
theorem _root_.solution (s : ℂ) (n : A.X →+ ℤ) (v' : A.La) :
    (s • A.P0 (La.mk 0 n 0)).1 v'.y = -(s * A.EF (La.mk 0 n 0) v') := by
  simp [EF_n_left]
end GlobalTheory.AnArc
