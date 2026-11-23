-- Prove2me | solution 1 for GlobalTheory.LatticeRep.transl_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:43.812911+00:00
-- url     : https://prove2.me/submissions/4f13634e-a711-425f-ae54-a8893df49252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeRep
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}
open Classical
open scoped BigOperators
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}
namespace GlobalTheory.LatticeRep
namespace _root_.GlobalTheory.LatticeRep
theorem _root_.solution (hs : Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) = ⊤) {p : M → Prop}
    (mem : ∀ x v, _root_.GlobalTheory.FinWeil.Fixes W A v → p (W x v)) (zero : p 0) (add : ∀ a b, p a → p b → p (a + b))
    (smul : ∀ (c : ℂ) a, p a → p (c • a)) (m : M) : p m := by
  have hm : m ∈ Submodule.span ℂ (_root_.GlobalTheory.LatticeRep.Transl W A) := by
    rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, v, hv, rfl⟩ := hy
    exact mem x v hv
  | zero => exact zero
  | add a b _ _ ha hb => exact add a b ha hb
  | smul c a _ ha => exact smul c a ha
end _root_.GlobalTheory.LatticeRep
end GlobalTheory.LatticeRep
