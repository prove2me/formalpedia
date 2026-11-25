-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagPow_conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:17.802961+00:00
-- url     : https://prove2.me/submissions/7dcb4e98-12ff-4b7b-92f6-862825b6730e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagPow_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_zpow_mul_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_zpow_mul_mem


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
open Cartan
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {μ : Fin n → ℤ} {u : GL (Fin n) F} {t m : ℕ}
    {C : ℤ} (hC : ((t + m : ℕ) : ℤ) < C)
    (hu : ∀ i j, u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hu' : ∀ i j, (u⁻¹ : GL (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i)
    (hb : ∀ i j, (uniformizer F : F) ^ t * u i j ∈ 𝒪[F])
    (hb' : ∀ i j, (uniformizer F : F) ^ t * (u⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) :
    diagPow F n μ * u * (diagPow F n μ)⁻¹ ∈ congruenceSubgroup F n m := by
  have key : ∀ x : F, ∀ i j, (x = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i) →
      (uniformizer F : F) ^ t * x ∈ 𝒪[F] →
      (uniformizer F : F) ^ (μ i - μ j) * x ∈ 𝒪[F] ∧
        valuation F ((uniformizer F : F) ^ (μ i - μ j) * x - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
          valuation F (uniformizer F : F) ^ m := by
    intro x i j hx hxb
    rcases hx with hx | hx
    · by_cases hij : i = j
      · subst hij
        rw [hx, sub_self, zpow_zero, one_mul, one_apply_eq, sub_self, map_zero]
        exact ⟨one_mem _, zero_le'⟩
      · rw [hx, one_apply_ne hij, mul_zero, sub_zero, map_zero]
        exact ⟨zero_mem _, zero_le'⟩
    · have hij : i ≠ j := by
        rintro rfl
        omega
      rw [one_apply_ne hij, sub_zero]
      exact ⟨zpow_mul_mem hxb (by omega), valuation_zpow_mul_le hxb (by push_cast at hC ⊢; omega)⟩
  rw [mem_congruenceSubgroup_iff, mem_integralGL_iff]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [diagPow_conj_apply]
    exact (key _ i j (hu i j) (hb i j)).1
  · have : (diagPow F n μ * u * (diagPow F n μ)⁻¹)⁻¹ = diagPow F n μ * u⁻¹ * (diagPow F n μ)⁻¹ := by
      group
    rw [this, diagPow_conj_apply]
    exact (key _ i j (hu' i j) (hb' i j)).1
  · rw [diagPow_conj_apply]
    exact (key _ i j (hu i j) (hb i j)).2
end GroundTheory.Automorphic.Parabolic
