-- Prove2me | solution 1 for GlobalTheory.SmoothForms.bicomm_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:32.644916+00:00
-- url     : https://prove2.me/submissions/36b9a2cc-99da-4fe1-b5c0-b7285b8c4f49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpan
import Theorems.Thm_GlobalTheory_SmoothForms_bicomm_left_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution {ι G : Type} [Fintype ι] [DecidableEq ι] [Group G] [Fintype G] (ρ : G → Matrix ι ι ℂ)
    (h1 : ρ 1 = 1) (hmul : ∀ g h, ρ g * ρ h = ρ (h * g)) (M : Matrix ι ι ℂ)
    (hM : ∀ T : Matrix ι ι ℂ, (∀ g, T * ρ g = ρ g * T) → M * T = T * M) :
    M ∈ Submodule.span ℂ (Set.range ρ) := by
  set B := Submodule.span ℂ (Set.range ρ) with hB
  have hst : ∀ g, ∀ X ∈ B, ρ g * X ∈ B := by
    intro g X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hmul]
      exact Submodule.subset_span ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add]; exact B.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact B.smul_mem c hx
  obtain ⟨q, hq⟩ := LinearMap.exists_extend (LinearMap.id : B →ₗ[ℂ] B)
  have hq' : ∀ X ∈ B, (q X : Matrix ι ι ℂ) = X := fun X hX => by
    have := LinearMap.congr_fun hq ⟨X, hX⟩
    exact congrArg Subtype.val this
  let p : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    ∑ g : G, LinearMap.mulLeft ℂ (ρ g⁻¹) ∘ₗ B.subtype ∘ₗ q ∘ₗ LinearMap.mulLeft ℂ (ρ g)
  have hp : ∀ X, p X = ∑ g : G, ρ g⁻¹ * (q (ρ g * X) : Matrix ι ι ℂ) := fun X => by
    simp [p, LinearMap.sum_apply]
  have hpB : ∀ X, p X ∈ B := fun X => by
    rw [hp]
    exact B.sum_mem fun g _ => hst _ _ (q _).2
  have hone : (1 : Matrix ι ι ℂ) ∈ B := Submodule.subset_span ⟨1, h1⟩
  have hp1 : p 1 = (Fintype.card G : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [hp]
    have : ∀ g : G, ρ g⁻¹ * (q (ρ g * 1) : Matrix ι ι ℂ) = 1 := fun g => by
      rw [hq' _ (hst _ _ hone), mul_one, hmul, mul_inv_cancel, h1]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hpρ : ∀ h X, p (ρ h * X) = ρ h * p X := fun h X => by
    rw [hp, hp, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft]
    rw [← mul_assoc, hmul, ← mul_assoc, hmul]
    simp
  have := bicomm_left_mul ρ p hpρ M hM 1
  rw [hp1, mul_one, Matrix.mul_smul, mul_one] at this
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h3 := B.smul_mem (Fintype.card G : ℂ)⁻¹ (hpB M)
  rwa [this, smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
end GlobalTheory.SmoothForms
