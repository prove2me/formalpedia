-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:49:48.693394+00:00
-- url     : https://prove2.me/submissions/20d5ddd8-6d59-49ae-80c0-6a5713444740

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le

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
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : congruenceSubgroup F n 0 = integralGL F n := by
  refine le_antisymm (congruenceSubgroup_le F n 0) fun g hg => ?_
  rw [mem_congruenceSubgroup_iff, pow_zero]
  refine ⟨hg, fun i j => ?_⟩
  have h0 := ((mem_integralGL_iff F n).mp hg).1 i j
  have h1 : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  exact (Valuation.mem_integer_iff _ _).mp (Subring.sub_mem _ h0 h1)
end GroundTheory.Automorphic.GLnLocal
