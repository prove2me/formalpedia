-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.unipotentCompactG_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:44:36.273542+00:00
-- url     : https://prove2.me/submissions/720170d3-aac5-4866-aed5-4804e72a0631

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompactG
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_lt
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (γ : Fin n → ℕ)
variable {γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {e e' : ℕ} (h : e ≤ e') :
    unipotentCompactG (F := F) γ e ≤ unipotentCompactG γ e' := by
  intro u hu
  obtain ⟨huN, hu'⟩ := mem_unipotentCompactG.1 hu
  refine mem_unipotentCompactG.2 ⟨huN, ?_⟩
  have key : ∀ v ∈ unipotentRadical F n γ,
      (rankTorus F n γ e * v * (rankTorus F n γ e)⁻¹ : GL (Fin n) F) ∈ integralGL F n →
        ∀ i j, ((rankTorus F n γ e' * v * (rankTorus F n γ e')⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
    intro v hv hint i j
    have hij := ((mem_integralGL_iff F n).1 hint).1 i j
    rw [rankTorus_conj_apply] at hij ⊢
    obtain ⟨hvP, hv1⟩ := mem_unipotentRadical.1 hv
    rcases lt_trichotomy (γ i) (γ j) with hlt | heq | hgt
    · have hr := blockRank_lt hlt
      have : (((e' * blockRank γ j : ℕ) : ℤ) - ((e' * blockRank γ i : ℕ) : ℤ)) =
          (((e * blockRank γ j : ℕ) : ℤ) - ((e * blockRank γ i : ℕ) : ℤ)) +
            (((e' - e) * (blockRank γ j - blockRank γ i) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub h, Nat.cast_sub hr.le]
        ring
      rw [this, zpow_add₀ uniformizer_ne_zero, zpow_natCast]
      have e1 : ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
          ((e * blockRank γ i : ℕ) : ℤ))) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i))) *
              (v : Matrix (Fin n) (Fin n) F) i j =
          ((GLnLocal.uniformizer F : F) ^ ((((e * blockRank γ j : ℕ) : ℤ) -
            ((e * blockRank γ i : ℕ) : ℤ))) * (v : Matrix (Fin n) (Fin n) F) i j) *
            (GLnLocal.uniformizer F : F) ^ ((e' - e) * (blockRank γ j - blockRank γ i)) := by
        ring
      rw [e1]
      exact mul_mem hij (pow_mem (GLnLocal.uniformizer F).2 _)
    · rw [blockRank_eq heq, sub_self] at hij ⊢
      exact hij
    · rw [hvP hgt, mul_zero]
      exact zero_mem _
  rw [mem_integralGL_iff F n]
  refine ⟨key u huN hu', ?_⟩
  intro i j
  have : (rankTorus F n γ e' * u * (rankTorus F n γ e')⁻¹)⁻¹ =
      rankTorus F n γ e' * u⁻¹ * (rankTorus F n γ e')⁻¹ := by group
  rw [this]
  have h' : (rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹)⁻¹ =
      rankTorus F n γ e * u⁻¹ * (rankTorus F n γ e)⁻¹ := by group
  have hinv := (integralGL F n).inv_mem hu'
  rw [h'] at hinv
  exact key u⁻¹ ((unipotentRadical F n γ).inv_mem huN) hinv i j
end GroundTheory.Automorphic.Parabolic
