-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.apply_self_ne_zero_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:28.885321+00:00
-- url     : https://prove2.me/submissions/4df253e4-e7f8-4755-b4a5-63fccf182054

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_inv_apply_of_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g : GL (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) F) i i ≠ 0 := by
  have h := mul_inv_apply_of_diagonal hg i i
  rw [one_apply_eq] at h
  exact left_ne_zero_of_mul_eq_one h
end GroundTheory.Automorphic.Parabolic
