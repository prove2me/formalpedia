-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_central_contracting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:59.874798+00:00
-- url     : https://prove2.me/submissions/3ea76eda-cf1f-4896-9ba9-e58be120a3c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_commute
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_mem_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_pow


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
variable (β)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (m : ℕ) :
    ∃ a ∈ levi F n β, (∀ y ∈ levi F n β, a * y = y * a) ∧
      (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β,
        a * u * a⁻¹ ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β) ∧
      (∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
        a⁻¹ * z * a ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) ∧
      ∀ U ∈ 𝓝 (1 : GL (Fin n) F), ∃ k : ℕ,
        (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, a ^ k * u * (a ^ k)⁻¹ ∈ U) ∧
        ∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
          (a ^ k)⁻¹ * z * a ^ k ∈ U := by
  have hmono : congruenceSubgroup F n (m + 1) ≤ congruenceSubgroup F n m :=
    congruenceSubgroup_antitone F n (by omega)
  refine ⟨rankTorus F n β 1, rankTorus_mem_levi 1, fun y hy => rankTorus_commute 1 hy,
    fun u hu => ?_, fun z hz => ?_, fun U hU => ?_⟩
  · have := Subgroup.mem_inf.1 (rankTorus_conj_mem_congruenceSubgroup (e := 1) hu)
    exact Subgroup.mem_inf.2 ⟨hmono this.1, this.2⟩
  · have := Subgroup.mem_inf.1 (rankTorus_inv_conj_mem_congruenceSubgroup (e := 1) hz)
    exact Subgroup.mem_inf.2 ⟨hmono this.1, this.2⟩
  · obtain ⟨t, -, ht⟩ := (hasBasis_nhds_one F n).mem_iff.1 hU
    have hle : congruenceSubgroup F n (m + t) ≤ congruenceSubgroup F n t :=
      congruenceSubgroup_antitone F n (by omega)
    refine ⟨t, fun u hu => ht ?_, fun z hz => ht ?_⟩
    · rw [rankTorus_pow, one_mul]
      exact hle (Subgroup.mem_inf.1 (rankTorus_conj_mem_congruenceSubgroup hu)).1
    · rw [rankTorus_pow, one_mul]
      exact hle (Subgroup.mem_inf.1 (rankTorus_inv_conj_mem_congruenceSubgroup hz)).1
end GroundTheory.Automorphic.Parabolic
