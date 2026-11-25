-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:51.982123+00:00
-- url     : https://prove2.me/submissions/4d662e72-6401-4ff3-8a64-99ddb8958bcb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_of_mem_adjoin

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
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]
omit [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {T₁ T₂ : Set (End ℂ M)} (h : IsSimpleUnder (T₁ ∪ T₂))
    (hc : ∀ a ∈ T₁, ∀ b ∈ T₂, Commute a b) {N : Submodule ℂ M} (hN : N ≠ ⊥) (hNs : IsStable T₁ N)
    {a : End ℂ M} (ha : ∀ b ∈ T₂, Commute a b) (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by
  set B := Algebra.adjoin ℂ T₂
  set P : Submodule ℂ M := ⨆ b : B, N.map (b : End ℂ M)
  have hmap : ∀ b : B, N.map (b : End ℂ M) ≤ P := fun b => le_iSup (fun b : B => N.map (b : End ℂ M)) b
  have hst : IsStable (T₁ ∪ T₂) P := by
    intro t ht x hx
    have hle : P ≤ P.comap t := by
      refine iSup_le fun b => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap]
      rcases ht with ht | ht
      · have hcomm : Commute t (b : End ℂ M) :=
          commute_of_mem_adjoin (fun s hs => hc t ht s hs) b b.2
        have : t ((b : End ℂ M) n) = (b : End ℂ M) (t n) := by
          rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
        rw [this]
        exact hmap b ⟨t n, hNs t ht n hn, rfl⟩
      · have htb : t * (b : End ℂ M) ∈ B := B.mul_mem (Algebra.subset_adjoin ht) b.2
        exact hmap ⟨_, htb⟩ ⟨n, hn, rfl⟩
    exact hle hx
  have hP : P ≠ ⊥ := by
    intro hP
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : n ∈ P := hmap 1 ⟨n, hn, by simp⟩
    rwa [hP] at this
  have hPtop : P = ⊤ := (h.2 P hst).resolve_left hP
  have hker : P ≤ LinearMap.ker a := by
    refine iSup_le fun b => ?_
    rintro _ ⟨n, hn, rfl⟩
    rw [LinearMap.mem_ker]
    have hcomm : Commute a (b : End ℂ M) := commute_of_mem_adjoin ha b b.2
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, h0 n hn, map_zero]
  ext x
  have : x ∈ LinearMap.ker a := hker (hPtop ▸ Submodule.mem_top)
  simpa using this
end GroundTheory.Automorphic.RestrictedTensor
