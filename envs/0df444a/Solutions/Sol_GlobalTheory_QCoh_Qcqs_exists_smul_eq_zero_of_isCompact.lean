-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.exists_smul_eq_zero_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:17.438397+00:00
-- url     : https://prove2.me/submissions/695c427e-45f1-4d19-ba09-b17876c752a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)
namespace GlobalTheory.QCoh.Qcqs
theorem _root_.solution
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hbot : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (a : A W) (ha : φ W a = 0) :
    ∃ s ∈ S, s • a = 0 := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → ∀ a : A ⟨W, h⟩,
      φ ⟨W, h⟩ a = 0 → ∃ s ∈ S, s • a = 0) W hW ?_ ?_ hWU hW a ha
  · intro h _ a _
    have := hbot ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ a ha
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, e₁⟩ := ih T'.2 hT (rA h₁ a) (by rw [hφ, ha, map_zero])
    obtain ⟨s₂, hs₂, e₂⟩ := hker V' V.2 (rA h₂ a) (by rw [hφ, ha, map_zero])
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, sepA h₁ h₂ le_rfl _ ?_ ?_⟩
    · rw [map_smul, mul_comm, mul_smul, e₁, smul_zero]
    · rw [map_smul, mul_smul, e₂, smul_zero]
end GlobalTheory.QCoh.Qcqs
