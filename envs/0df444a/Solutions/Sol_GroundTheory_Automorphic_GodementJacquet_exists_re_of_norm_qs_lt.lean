-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_re_of_norm_qs_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:18.596733+00:00
-- url     : https://prove2.me/submissions/264fffec-7d06-4135-857d-09c24c39eac4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_norm_qs
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard


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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ‖qs F s‖ < ε := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  refine ⟨-Real.logb (LocalField.residueCard F) ε, fun s hs => ?_⟩
  rw [norm_qs]
  calc (LocalField.residueCard F : ℝ) ^ (-s.re)
      < (LocalField.residueCard F : ℝ) ^ (Real.logb (LocalField.residueCard F) ε) :=
        (Real.rpow_lt_rpow_left_iff hq).2 (by linarith)
    _ = ε := Real.rpow_logb (by positivity) hq.ne' hε
end GroundTheory.Automorphic.GodementJacquet
