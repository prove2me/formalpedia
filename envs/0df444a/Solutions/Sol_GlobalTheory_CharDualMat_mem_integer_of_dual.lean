-- Prove2me | solution 1 for GlobalTheory.CharDualMat.mem_integer_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:24.170241+00:00
-- url     : https://prove2.me/submissions/a6dd357d-b1c3-4023-b894-6f98685e81eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Theorems.Thm_GlobalTheory_CharDualMat_exists_ball_trivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharDualMat
namespace _root_.GlobalTheory.CharDualMat
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (hne : ψ ≠ 1) (a : k)
    (h : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) → ψ (s * a) = 1) : a ∈ 𝒪[k] := by
  by_contra ha
  have hva : 1 < valuation k a := by
    rw [Valuation.mem_integer_iff] at ha
    exact not_le.1 ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hva
  obtain ⟨γ, hγ, hball⟩ := _root_.GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hmul : ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a * u) = 1 := by
    intro s hs u hu
    have := h (s * u) (fun u' hu' => by rw [mul_assoc]; exact hs _ (mul_mem hu hu'))
    rw [mul_right_comm]
    exact this
  have hpow : ∀ n : ℕ, ∀ s : k, (∀ u : k, u ∈ 𝒪[k] → ψ (s * u) = 1) →
      ∀ u : k, u ∈ 𝒪[k] → ψ (s * a ^ n * u) = 1 := by
    intro n
    induction n with
    | zero => intro s hs; simpa using hs
    | succ n ih => intro s hs; rw [pow_succ, ← mul_assoc]; exact hmul _ (ih s hs)
  apply hne
  ext t
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation k t * γ⁻¹) hva
  have hlt : valuation k t * γ⁻¹ < valuation k a ^ (n + 1) :=
    lt_of_le_of_lt hn (pow_lt_pow_right₀ hva n.lt_succ_self)
  have hapos : valuation k a ^ (n + 1) ≠ 0 := pow_ne_zero _ (by simpa using ha0)
  have hlt' : valuation k t < γ * valuation k a ^ (n + 1) := by
    calc valuation k t = valuation k t * γ⁻¹ * γ := (inv_mul_cancel_right₀ hγ _).symm
      _ < valuation k a ^ (n + 1) * γ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 hγ)
      _ = γ * valuation k a ^ (n + 1) := mul_comm _ _
  have hs : ∀ u : k, u ∈ 𝒪[k] → ψ (t * (a ^ (n + 1))⁻¹ * u) = 1 := by
    intro u hu
    apply hball
    rw [Valuation.mem_integer_iff] at hu
    rw [map_mul, map_mul, map_inv₀, map_pow]
    calc valuation k t * (valuation k a ^ (n + 1))⁻¹ * valuation k u
        ≤ valuation k t * (valuation k a ^ (n + 1))⁻¹ := mul_le_of_le_one_right' hu
      _ < γ := mul_inv_lt_of_lt_mul₀ hlt'
  have := hpow (n + 1) _ hs 1 (one_mem _)
  rw [mul_one, inv_mul_cancel_right₀ (pow_ne_zero _ ha0)] at this
  rw [this, AddChar.one_apply]
end _root_.GlobalTheory.CharDualMat
end GlobalTheory.CharDualMat
