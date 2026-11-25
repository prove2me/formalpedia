-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.elimGL_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:38.096386+00:00
-- url     : https://prove2.me/submissions/a1d0cb85-6eb7-4a66-831c-6c1beddd5878

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_inv_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_congruenceSubgroup_of_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_elimCol_le

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
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a : Fin n) :
    elimGL β (h : Matrix (Fin n) (Fin n) F) a ∈ congruenceSubgroup F n m :=
  mem_congruenceSubgroup_of_le
    (fun i k => by
      rw [elimGL_apply, sub_sub_cancel_left, Valuation.map_neg]
      exact valuation_elimCol_le hm hh a i k)
    (fun i k => by
      rw [elimGL_inv_apply, add_sub_cancel_left]
      exact valuation_elimCol_le hm hh a i k)
end GroundTheory.Automorphic.Parabolic
