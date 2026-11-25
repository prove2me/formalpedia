-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_isCompact_support_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:31.510221+00:00
-- url     : https://prove2.me/submissions/2bd147b9-987b-4023-ae93-1ce65fd36605

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClopen_support_parabolicInd
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_isCompact_subset_doubleCoset
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable (w : Equiv.Perm (Fin n))
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ L : Set (GL (Fin n) F), IsCompact L ∧ L ⊆ blockUpper F n γ ∧
      ∀ q ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * q) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, permGL F w * x * (permGL F w)⁻¹ ∈ blockUpper F n β ∧
          ∃ l ∈ L, q = x * l := by
  set C := doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  set S := {g : GL (Fin n) F | (f : GL (Fin n) F → W) g ≠ 0}
  have hS := isClopen_support_parabolicInd f
  have hSY : S ⊆ Y := fun g hg => by
    by_contra hgY
    exact hg (hf g hgY)
  set Kc := (integralGL F n : Set (GL (Fin n) F)) ∩ (S ∩ closure C)
  have hKc : IsCompact Kc := (isCompact_integralGL F n).inter_right (hS.1.inter isClosed_closure)
  have hKcC : Kc ⊆ C := by
    rintro g ⟨-, hgS, hgC⟩
    rw [← hCY]
    exact ⟨hgC, hSY hgS⟩
  have hCl : IsLocallyClosed C := ⟨Y, closure C, hYo, isClosed_closure, by rw [inter_comm, hCY]⟩
  obtain ⟨L, hL, hLQ, hKL⟩ := exists_isCompact_subset_doubleCoset
    (Measures.isClosed_blockUpper F n β) (Measures.isClosed_blockUpper F n γ) hCl hKc hKcC
  refine ⟨L, hL, hLQ, fun q hq hfq => ?_⟩
  obtain ⟨p, hp, k, hk, hpk⟩ := exists_blockUpper_mul_integralGL' (β := β) (permGL F w * q)
  have hfk : (f : GL (Fin n) F → W) k ≠ 0 := by
    intro h0
    apply hfq
    rw [hpk, ((mem_parabolicIndSpace σ).1 f.2).1 ⟨p, hp⟩ k, h0, map_zero, smul_zero]
  have hkC : k ∈ C := by
    refine mem_doubleCoset.2 ⟨p⁻¹, (blockUpper F n β).inv_mem hp, q, hq, ?_⟩
    rw [mul_assoc, hpk, inv_mul_cancel_left]
  obtain ⟨p', hp', l, hl, hkl⟩ := hKL k ⟨hk, hfk, subset_closure hkC⟩
  refine ⟨q * l⁻¹, (blockUpper F n γ).mul_mem hq ((blockUpper F n γ).inv_mem (hLQ hl)), ?_, l, hl,
    by group⟩
  have : permGL F w * (q * l⁻¹) * (permGL F w)⁻¹ = p * p' := by
    have h1 : permGL F w * q = p * (p' * permGL F w * l) := by rw [hpk, hkl]
    calc permGL F w * (q * l⁻¹) * (permGL F w)⁻¹
        = (permGL F w * q) * l⁻¹ * (permGL F w)⁻¹ := by group
      _ = p * p' := by rw [h1]; group
  rw [this]
  exact (blockUpper F n β).mul_mem hp hp'
end GroundTheory.Automorphic.Parabolic
