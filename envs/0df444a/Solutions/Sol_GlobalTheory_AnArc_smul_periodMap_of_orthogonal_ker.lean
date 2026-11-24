-- Prove2me | solution 1 for GlobalTheory.AnArc.smul_periodMap_of_orthogonal_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:44.475797+00:00
-- url     : https://prove2.me/submissions/18e1ad4c-d2b2-4448-8fc9-b7704d9e38b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_AnArc_orth_ker_iff_exists
import Theorems.Thm_GlobalTheory_AnArc_smul_periodMap_mk_zero_fst_eq_neg_form

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
theorem _root_.solution {v : A.La} (h : ∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) (s : ℂ) :
    (s • A.P0 v).2 = 0 ∧ ∀ v' : A.La, (s • A.P0 v).1 v'.y = -(s * A.EF v v') := by
  obtain ⟨n, rfl⟩ := (A.orth_ker_iff_exists v).1 h
  exact ⟨by simp, A.smul_periodMap_mk_zero_fst_eq_neg_form s n⟩
end GlobalTheory.AnArc
