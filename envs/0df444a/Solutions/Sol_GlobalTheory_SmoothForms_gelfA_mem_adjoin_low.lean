-- Prove2me | solution 1 for GlobalTheory.SmoothForms.gelfA_mem_adjoin_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:24.134554+00:00
-- url     : https://prove2.me/submissions/3954be9a-90dc-4840-8e92-543522d654c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GelfAMemAdjoinLow
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_central_of_filt_low
import Theorems.Thm_GlobalTheory_SmoothForms_GelfGen_gelfA_mem_filt
import Theorems.Thm_GlobalTheory_T_commute_gelfandInvariantMatrixUnits_of_glRel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms
noncomputable section
open GlobalTheory.SmoothForms.PermWord
namespace GlobalTheory.SmoothForms
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ m : ℕ, gelfA E m ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  intro A _ _ n E hE m
  exact GlobalTheory.SmoothForms.GelfGen.central_of_filt_low hE (m + 2) _ (GlobalTheory.SmoothForms.GelfGen.gelfA_mem_filt E m)
    (GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE m)
end GlobalTheory.SmoothForms
