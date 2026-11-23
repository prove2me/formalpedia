-- Prove2me | solution 1 for GlobalTheory.QCoh.Qcqs.exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:46.18477+00:00
-- url     : https://prove2.me/submissions/199ba797-46c4-4e9d-a25b-4d2cb4f98d34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_zero_of_isCompact
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



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
    (hrB : ∀ {V₁ V₂ V₃} (h : V₁ ≤ V₂) (h' : V₂ ≤ V₃) (b : B V₃),
      rB h (rB h' b) = rB (h.trans h') b)
    (hbotA : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (hbotB : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (B V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (sepB : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ b : B W, rB h₁ b = 0 → rB h₂ b = 0 → b = 0)
    (glueA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ (a₁ : A V₁) (a₂ : A V₂), rA (inf_le_left : V₁ ⊓ V₂ ≤ V₁) a₁ = rA inf_le_right a₂ →
        ∃ a : A W, rA h₁ a = a₁ ∧ rA h₂ a = a₂)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (hsurj : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ b : B V, ∃ s ∈ S, ∃ a : A V, s • b = φ V a)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (hW' : IsQuasiSeparated (W.1 : Set X))
    (b : B W) : ∃ s ∈ S, ∃ a : A W, s • b = φ W a := by
  obtain ⟨W, hWU⟩ := W
  refine compact_open_induction_on
    (P := fun W ↦ ∀ (h : W ∈ Set.Iic U), IsCompact (W : Set X) → IsQuasiSeparated (W : Set X) →
      ∀ b : B ⟨W, h⟩, ∃ s ∈ S, ∃ a : A ⟨W, h⟩, s • b = φ ⟨W, h⟩ a) W hW ?_ ?_ hWU hW hW' b
  · intro h _ _ b
    have := hbotB ⟨⊥, h⟩ rfl
    exact ⟨1, S.one_mem, 0, Subsingleton.elim _ _⟩
  · intro T hT V ih h _ hqs b
    let T' : Set.Iic U := ⟨T, (le_sup_left.trans h : T ≤ U)⟩
    let V' : Set.Iic U := ⟨V.1, (le_sup_right.trans h : V.1 ≤ U)⟩
    have h₁ : T' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_left (a := T)
    have h₂ : V' ≤ ⟨T ⊔ V.1, h⟩ := le_sup_right (a := T)
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := ih T'.2 hT (hqs.of_subset Set.subset_union_left) (rB h₁ b)
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := hsurj V' V.2 (rB h₂ b)
    have hc : IsCompact ((T' ⊓ V').1 : Set X) :=
      hqs _ _ Set.subset_union_left T.2 hT Set.subset_union_right V.1.2 V.2.isCompact
    obtain ⟨s, hs, e⟩ := exists_smul_eq_zero_of_isCompact S U rA rB φ hφ hbotA sepA hker
      (T' ⊓ V') hc (s₂ • rA inf_le_left a₁ - s₁ • rA inf_le_right a₂) (by
        rw [map_sub, map_smul, map_smul, hφ, hφ, ← e₁, ← e₂, map_smul, map_smul, hrB, hrB,
          smul_comm, sub_self])
    obtain ⟨a, ha₁, ha₂⟩ := glueA h₁ h₂ le_rfl (s • s₂ • a₁) (s • s₁ • a₂) (by
      rw [smul_sub, sub_eq_zero] at e
      simpa only [map_smul] using e)
    refine ⟨s * (s₁ * s₂), mul_mem hs (mul_mem hs₁ hs₂), a, ?_⟩
    rw [← sub_eq_zero]
    refine sepB h₁ h₂ le_rfl _ ?_ ?_
    · rw [map_sub, ← hφ, ha₁, map_smul, map_smul, map_smul, ← e₁, mul_comm s₁, mul_smul, mul_smul,
        sub_self]
    · rw [map_sub, ← hφ, ha₂, map_smul, map_smul, map_smul, ← e₂, mul_smul, mul_smul, sub_self]
end GlobalTheory.QCoh.Qcqs
