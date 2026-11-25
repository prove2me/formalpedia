-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diag_ne_zero_of_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:21:21.908739+00:00
-- url     : https://prove2.me/submissions/69c3ea4f-8d83-43ef-a65e-f391c30362c8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
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
theorem _root_.solution {h : GL (Fin n) F} (hh : h ∈ iwahori F n) (a : Fin n) :
    h a a ≠ 0 := fun e => by
  have := ((mem_iwahori_iff F n).1 hh).2.2 a
  rw [e, map_zero] at this
  exact zero_ne_one this
end GroundTheory.Automorphic.Parabolic
