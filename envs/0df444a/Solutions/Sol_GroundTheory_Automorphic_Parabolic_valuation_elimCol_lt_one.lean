-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_elimCol_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:37:58.878304+00:00
-- url     : https://prove2.me/submissions/10ed8f26-2c00-4aeb-be38-fbb795dc5392

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_lt_of_elimKey_lt
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hβ : Monotone β) {h : GL (Fin n) F} (hh : h ∈ iwahori F n)
    (a i k : Fin n) : valuation F (elimCol β (h : Matrix (Fin n) (Fin n) F) a i k) < 1 := by
  obtain ⟨-, h2, h3⟩ := (mem_iwahori_iff F n).1 hh
  rw [elimCol_apply]
  split_ifs with hik
  · rw [map_div₀, h3 a, div_one]
    exact h2 i a (lt_of_elimKey_lt hik.2 hβ)
  · rw [map_zero]
    exact zero_lt_one
end GroundTheory.Automorphic.Parabolic
