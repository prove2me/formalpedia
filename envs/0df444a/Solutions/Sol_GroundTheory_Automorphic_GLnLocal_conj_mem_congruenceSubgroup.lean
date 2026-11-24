-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:15.962812+00:00
-- url     : https://prove2.me/submissions/8286993e-5633-4d7b-be3a-b0ed3719d924

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal

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
theorem _root_.solution {m : ℕ} {k x : GL (Fin n) F} (hk : k ∈ integralGL F n)
    (hx : x ∈ congruenceSubgroup F n m) : k * x * k⁻¹ ∈ congruenceSubgroup F n m := by
  obtain ⟨u, rfl⟩ := hk
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨u * y * u⁻¹, (reduction F n m).normal_ker.conj_mem y hy u, by simp [map_mul, map_inv]⟩
end GroundTheory.Automorphic.GLnLocal
