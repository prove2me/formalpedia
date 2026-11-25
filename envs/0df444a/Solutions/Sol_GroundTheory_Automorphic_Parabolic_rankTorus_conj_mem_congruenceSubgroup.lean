-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:44.559416+00:00
-- url     : https://prove2.me/submissions/a9b5513b-b186-47a7-a287-2e59344adb2c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_congruenceSubgroup_of_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_rankTorus_conj_sub_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_mem_blockUpper


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
theorem _root_.solution {e m : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β) :
    rankTorus F n β e * u * (rankTorus F n β e)⁻¹ ∈
      congruenceSubgroup F n (m + e) ⊓ unipotentRadical F n β := by
  have hb : ∀ w ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, ∀ i j,
      valuation F ((rankTorus F n β e * w * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ (m + e) := by
    intro w hw i j
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    refine (valuation_rankTorus_conj_sub_le hwN i j).trans ?_
    rw [pow_add, mul_comm (valuation F ϖ ^ m)]
    gcongr
    exact ((mem_congruenceSubgroup_iff F n).1 hwK).2 i j
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb u hu) ?_,
    conj_mem_unipotentRadical (rankTorus_mem_blockUpper e) (Subgroup.mem_inf.1 hu).2⟩
  have : (rankTorus F n β e * u * (rankTorus F n β e)⁻¹)⁻¹ =
      rankTorus F n β e * u⁻¹ * (rankTorus F n β e)⁻¹ := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hu)
end GroundTheory.Automorphic.Parabolic
