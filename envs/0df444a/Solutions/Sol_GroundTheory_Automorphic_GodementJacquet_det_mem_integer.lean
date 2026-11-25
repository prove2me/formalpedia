-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.det_mem_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:26:44.971418+00:00
-- url     : https://prove2.me/submissions/ce2bb5ab-ac11-4273-a0f3-1816cf3a7fa3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe

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
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    X.det ∈ 𝒪[F] := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => hX _ _) _
end GroundTheory.Automorphic.GodementJacquet
