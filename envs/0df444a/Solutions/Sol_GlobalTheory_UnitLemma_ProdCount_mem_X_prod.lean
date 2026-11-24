-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.mem_X_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:30.040687+00:00
-- url     : https://prove2.me/submissions/1aacf62d-19d1-4ed3-9e0c-2a59dbfb6e7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_isLat_prod
import Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_herm_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (B₁ B₂ : InvAlg K) (x₁ : B₁.A) (x₂ : B₂.A) (L₁ : Submodule K.O B₁.A)
    (L₂ : Submodule K.O B₂.A) :
    L₁.prod L₂ ∈ (B₁.prod B₂).X (x₁, x₂) ↔ L₁ ∈ B₁.X x₁ ∧ L₂ ∈ B₂.X x₂ := by
  have z₁ : ∀ y, B₁.herm x₁ y 0 = 0 := fun y => by simp [InvAlg.herm]
  have z₂ : ∀ y, B₂.herm x₂ y 0 = 0 := fun y => by simp [InvAlg.herm]
  have w₁ : ∀ y, B₁.herm x₁ 0 y = 0 := fun y => by simp [InvAlg.herm]
  have w₂ : ∀ y, B₂.herm x₂ 0 y = 0 := fun y => by simp [InvAlg.herm]
  have hd : ∀ y : B₁.A × B₂.A,
      (∀ z : B₁.A × B₂.A, z ∈ L₁.prod L₂ → (B₁.prod B₂).herm (x₁, x₂) y z ∈ (algebraMap K.O K.E).range) ↔
      (∀ z ∈ L₁, B₁.herm x₁ y.1 z ∈ (algebraMap K.O K.E).range) ∧
      (∀ z ∈ L₂, B₂.herm x₂ y.2 z ∈ (algebraMap K.O K.E).range) := by
    intro y
    simp only [herm_prod, Submodule.mem_prod]
    constructor
    · intro h
      refine ⟨fun z hz => ?_, fun z hz => ?_⟩
      · have := h (z, 0) ⟨hz, L₂.zero_mem⟩
        rwa [z₂, add_zero] at this
      · have := h (0, z) ⟨L₁.zero_mem, hz⟩
        rwa [z₁, zero_add] at this
    · rintro ⟨h1, h2⟩ z hz
      exact add_mem (h1 _ hz.1) (h2 _ hz.2)
  change (IsLat K.O K.E (L₁.prod L₂) ∧
      (∀ y : B₁.A × B₂.A, y ∈ L₁.prod L₂ → ((B₁.g, B₂.g) : B₁.A × B₂.A) * y ∈ L₁.prod L₂) ∧
      ∀ y : B₁.A × B₂.A, y ∈ L₁.prod L₂ ↔ ∀ z : B₁.A × B₂.A, z ∈ L₁.prod L₂ →
        (B₁.prod B₂).herm (x₁, x₂) y z ∈ (algebraMap K.O K.E).range) ↔
    (IsLat K.O K.E L₁ ∧ (∀ y ∈ L₁, B₁.g * y ∈ L₁) ∧
      ∀ y, y ∈ L₁ ↔ ∀ z ∈ L₁, B₁.herm x₁ y z ∈ (algebraMap K.O K.E).range) ∧
    (IsLat K.O K.E L₂ ∧ (∀ y ∈ L₂, B₂.g * y ∈ L₂) ∧
      ∀ y, y ∈ L₂ ↔ ∀ z ∈ L₂, B₂.herm x₂ y z ∈ (algebraMap K.O K.E).range)
  rw [isLat_prod]
  simp only [hd]
  simp only [Submodule.mem_prod, Prod.fst_mul, Prod.snd_mul]
  constructor
  · rintro ⟨⟨l1, l2⟩, s, d⟩
    refine ⟨⟨l1, fun y hy => (s (y, 0) ⟨hy, L₂.zero_mem⟩).1, fun y => ?_⟩,
      ⟨l2, fun y hy => (s (0, y) ⟨L₁.zero_mem, hy⟩).2, fun y => ?_⟩⟩
    · have := d (y, 0)
      simpa only [L₂.zero_mem, w₂, zero_mem, implies_true, and_true] using this
    · have := d (0, y)
      simpa only [L₁.zero_mem, w₁, zero_mem, implies_true, true_and] using this
  · rintro ⟨⟨l1, s1, d1⟩, l2, s2, d2⟩
    exact ⟨⟨l1, l2⟩, fun y hy => ⟨s1 _ hy.1, s2 _ hy.2⟩, fun y => and_congr (d1 _) (d2 _)⟩
end GlobalTheory.UnitLemma.ProdCount
