-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:23.301773+00:00
-- url     : https://prove2.me/submissions/2e5ac192-02f4-4520-907f-7dd2768d2d16

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_iwahori_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply


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
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hpI : p ∈ iwahori F n) :
    ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hpI
  rw [mem_iwahori_iff F n]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [leviProj_apply]
    split_ifs
    · exact h1 i j
    · rw [map_zero]
      exact zero_le
  · rw [leviProj_apply]
    split_ifs
    · exact h2 i j hij
    · rw [map_zero]
      exact zero_lt_one
  · rw [leviProj_apply, if_pos rfl]
    exact h3 i
end GroundTheory.Automorphic.Parabolic
