-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimGL_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:43.093886+00:00
-- url     : https://prove2.me/submissions/64603157-8049-4145-b679-f00edafff71f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_one_apply_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_elimCol_lt_one
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
    (a : Fin n) : elimGL β (h : Matrix (Fin n) (Fin n) F) a ∈ iwahori F n := by
  have hD := valuation_elimCol_lt_one hβ hh a
  rw [mem_iwahori_iff F n]
  refine ⟨fun i k => ?_, fun i k hki => ?_, fun i => ?_⟩
  · rw [elimGL_apply]
    exact Valuation.map_sub_le _ (valuation_one_apply_le i k) (hD i k).le
  · rw [elimGL_apply, one_apply_ne hki.ne', zero_sub, Valuation.map_neg]
    exact hD i k
  · rw [elimGL_apply, one_apply_eq]
    refine (Valuation.map_eq_of_sub_lt _ ?_).trans (map_one _)
    rw [sub_sub_cancel_left, Valuation.map_neg, map_one]
    exact hD i i
end GroundTheory.Automorphic.Parabolic
