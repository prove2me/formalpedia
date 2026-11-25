-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:25.177458+00:00
-- url     : https://prove2.me/submissions/afe43a02-769b-4d33-9d40-bf5c64cc063d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_congruenceSubgroup_of_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_rankTorus_inv_conj_sub_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_mem_levi


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
theorem _root_.solution {e m : ℕ} {z : GL (Fin n) F}
    (hz : z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) :
    (rankTorus F n β e)⁻¹ * z * rankTorus F n β e ∈
      congruenceSubgroup F n (m + e) ⊓ oppositeUnipotentRadical F n β := by
  have hb : ∀ w ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β, ∀ i j,
      valuation F (((rankTorus F n β e)⁻¹ * w * rankTorus F n β e : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ (m + e) := by
    intro w hw i j
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    refine (valuation_rankTorus_inv_conj_sub_le hwN i j).trans ?_
    rw [pow_add, mul_comm (valuation F ϖ ^ m)]
    gcongr
    exact ((mem_congruenceSubgroup_iff F n).1 hwK).2 i j
  have htP : (rankTorus F n β e)⁻¹ ∈ blockUpper F n (OrderDual.toDual ∘ β) :=
    Subgroup.inv_mem _ (Subgroup.mem_inf.1 (rankTorus_mem_levi (F := F) (β := β) e)).2
  have hN := conj_mem_unipotentRadical htP (Subgroup.mem_inf.1 hz).2
  rw [inv_inv] at hN
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb z hz) ?_, hN⟩
  have : ((rankTorus F n β e)⁻¹ * z * rankTorus F n β e)⁻¹ =
      (rankTorus F n β e)⁻¹ * z⁻¹ * rankTorus F n β e := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hz)
end GroundTheory.Automorphic.Parabolic
