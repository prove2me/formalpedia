-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:40.568731+00:00
-- url     : https://prove2.me/submissions/662f9c82-0b9c-4a6a-aeaf-ae9ca026bb73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_congruenceSubgroup_of_le
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
theorem _root_.solution {m : ℕ} {p : GL (Fin n) F}
    (hp : p ∈ blockUpper F n β) (hpK : p ∈ congruenceSubgroup F n m) :
    ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ congruenceSubgroup F n m := by
  have key : ∀ q : blockUpper F n β, (q : GL (Fin n) F) ∈ congruenceSubgroup F n m →
      ∀ i j, valuation F (((leviProj F n β q : levi F n β) : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m := by
    intro q hq i j
    rw [leviProj_apply]
    split_ifs with hij
    · exact ((mem_congruenceSubgroup_iff F n).1 hq).2 i j
    · rw [one_apply_ne (fun hh => hij (by rw [hh])), sub_zero, map_zero]
      exact zero_le
  refine mem_congruenceSubgroup_of_le (key ⟨p, hp⟩ hpK) ?_
  have : ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F)⁻¹ =
      ((leviProj F n β (⟨p, hp⟩ : blockUpper F n β)⁻¹ : levi F n β) : GL (Fin n) F) := by
    rw [map_inv, Subgroup.coe_inv]
  rw [this]
  exact key _ ((congruenceSubgroup F n m).inv_mem hpK)
end GroundTheory.Automorphic.Parabolic
