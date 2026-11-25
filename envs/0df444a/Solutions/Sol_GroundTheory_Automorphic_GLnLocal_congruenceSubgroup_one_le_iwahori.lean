-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_one_le_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:54.093636+00:00
-- url     : https://prove2.me/submissions/e6e21fcd-a464-44fe-b3f1-818eb16d0794

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_iwahori_iff

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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution : congruenceSubgroup F n 1 ≤ iwahori F n := by
  intro g hg
  obtain ⟨hK, hg⟩ := (mem_congruenceSubgroup_iff F n).mp hg
  have hK' := ((mem_integralGL_iff F n).mp hK).1
  rw [mem_iwahori_iff]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).mp (hK' i j), fun i j hij => ?_, fun i => ?_⟩
  · have h := hg i j
    rw [Matrix.one_apply_ne hij.ne', sub_zero, pow_one] at h
    exact h.trans_lt (valuation_uniformizer_lt_one F)
  · have h := hg i i
    rw [Matrix.one_apply_eq, pow_one] at h
    have hlt : valuation F (g i i - 1) < valuation F 1 := by
      rw [map_one]
      exact h.trans_lt (valuation_uniformizer_lt_one F)
    rw [Valuation.map_eq_of_sub_lt _ hlt, map_one]
end GroundTheory.Automorphic.GLnLocal
