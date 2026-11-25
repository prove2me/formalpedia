-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:26.444948+00:00
-- url     : https://prove2.me/submissions/cf8b5d4e-55de-44e1-8f7f-de89aa4354dd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_add
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
open Cartan
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (μ : Fin n → ℤ) : diagPow F n (-μ) = (diagPow F n μ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← diagPow_add, neg_add_cancel, diagPow_zero]
end GroundTheory.Automorphic.Parabolic
