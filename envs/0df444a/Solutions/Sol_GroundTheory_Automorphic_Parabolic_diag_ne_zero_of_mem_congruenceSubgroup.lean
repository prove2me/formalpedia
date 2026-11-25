-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diag_ne_zero_of_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:52.070988+00:00
-- url     : https://prove2.me/submissions/b20f3c73-10b4-4ec3-8438-285c4b73ffc4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diag_ne_zero_of_mem_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_one_le_iwahori


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
    (hh : h ∈ congruenceSubgroup F n m) (a : Fin n) : h a a ≠ 0 :=
  diag_ne_zero_of_mem_iwahori
    (congruenceSubgroup_one_le_iwahori F n (congruenceSubgroup_antitone F n hm hh)) a
end GroundTheory.Automorphic.Parabolic
