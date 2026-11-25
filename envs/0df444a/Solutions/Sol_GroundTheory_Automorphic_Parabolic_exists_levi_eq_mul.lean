-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_levi_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:18.885843+00:00
-- url     : https://prove2.me/submissions/d37cb966-b877-4427-8c67-a52b471fafca

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_of_mem_levi
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_exists_blockUpper_mul_integralGL__7c8211cc1088


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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ integralGL F n, m = b * k := by
  let ρ : Fin n → ℕ ×ₗ ℕ := fun i => toLex (γ i, β (w i))
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_blockUpper_mul_integralGL' (β := ρ) m
  have hρ : ∀ {i j : Fin n}, γ j < γ i → ρ j < ρ i := fun h => by
    show toLex (γ _, β (w _)) < toLex (γ _, β (w _))
    rw [Prod.Lex.lt_iff]
    exact Or.inl h
  have hpQ : p ∈ blockUpper F n γ := fun i j hij => hp (hρ hij)
  have hmQ : m ∈ blockUpper F n γ := levi_le_blockUpper hm
  have hkQ : k ∈ blockUpper F n γ := by
    have : k = p⁻¹ * m := by rw [hpk]; group
    rw [this]
    exact (blockUpper F n γ).mul_mem ((blockUpper F n γ).inv_mem hpQ) hmQ
  set b := leviProj F n γ ⟨p, hpQ⟩
  set k' := leviProj F n γ ⟨k, hkQ⟩
  refine ⟨b, ⟨b.2, fun i j hij => ?_⟩, k', ⟨k'.2, leviProj_mem_integralGL (p := ⟨k, hkQ⟩) hk⟩, ?_⟩
  · show ((leviProj F n γ ⟨p, hpQ⟩ : levi F n γ) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs with h
    · apply hp
      show toLex (γ j, β (w j)) < toLex (γ i, β (w i))
      rw [Prod.Lex.lt_iff]
      exact Or.inr ⟨h.symm, hij⟩
    · rfl
  · have h1 : leviProj F n γ ⟨m, hmQ⟩ = b * k' := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hpk
    rw [leviProj_of_mem_levi hm] at h1
    exact congrArg Subtype.val h1
end GroundTheory.Automorphic.Parabolic
