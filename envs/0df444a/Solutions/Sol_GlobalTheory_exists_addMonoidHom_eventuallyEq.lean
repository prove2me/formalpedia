-- Prove2me | solution 1 for GlobalTheory.exists_addMonoidHom_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:59.491799+00:00
-- url     : https://prove2.me/submissions/ed7773a8-9570-4795-8851-69c6f23dbf80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Metric Set Filter Asymptotics
open scoped Topology
namespace GlobalTheory
section Taylor
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
end Taylor
section Halving
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
end Halving
section Extension
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
private theorem eventually_half_pow_smul_mem {s : Set V} (hs : s ∈ 𝓝 (0 : V)) (v : V) :
    ∀ᶠ j : ℕ in atTop, (2⁻¹ : ℝ) ^ j • v ∈ s := by
  have : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  exact this.eventually hs
end Extension
end GlobalTheory
end

set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]
namespace GlobalTheory
theorem _root_.solution {g : V → A}
    (hg : ∀ᶠ p in 𝓝 (0 : V × V), g (p.1 + p.2) = g p.1 + g p.2) :
    ∃ e : V →+ A, e =ᶠ[𝓝 0] g := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hg
  have hadd : ∀ x ∈ ball (0 : V) r, ∀ y ∈ ball (0 : V) r, g (x + y) = g x + g y :=
    fun x hx y hy => hball (x, y) (by rw [← Prod.mk_zero_zero, ← ball_prod_same]; exact ⟨hx, hy⟩)
  have hhalf : ∀ x ∈ ball (0 : V) r, (2⁻¹ : ℝ) • x ∈ ball (0 : V) r := by
    intro x hx
    rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul]
    norm_num
    linarith [norm_nonneg x]
  have hstep : ∀ x ∈ ball (0 : V) r, ∀ k : ℕ, (2⁻¹ : ℝ) ^ k • x ∈ ball (0 : V) r ∧
      (2 ^ k : ℕ) • g ((2⁻¹ : ℝ) ^ k • x) = g x := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have h1 := hhalf _ ih.1
      rw [pow_succ' (2⁻¹ : ℝ), mul_smul]
      refine ⟨h1, ?_⟩
      rw [pow_succ, mul_smul, two_smul, ← hadd _ h1 _ h1, ← add_smul]
      norm_num
      simpa using ih.2
  have hex : ∀ v : V, ∃ j : ℕ, (2⁻¹ : ℝ) ^ j • v ∈ ball (0 : V) r := fun v =>
    (eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) v).exists
  let e : V → A := fun v => (2 ^ Nat.find (hex v) : ℕ) • g ((2⁻¹ : ℝ) ^ Nat.find (hex v) • v)
  have he : ∀ (v : V) (j : ℕ), (2⁻¹ : ℝ) ^ j • v ∈ ball (0 : V) r →
      e v = (2 ^ j : ℕ) • g ((2⁻¹ : ℝ) ^ j • v) := by
    intro v j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.find_min' (hex v) hj)
    rw [pow_add, mul_smul, add_comm, pow_add, mul_smul, (hstep _ (Nat.find_spec (hex v)) k).2]
  refine ⟨AddMonoidHom.mk' e fun v w => ?_, ?_⟩
  · obtain ⟨j, h1, h2, h3⟩ := ((eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) v).and
      ((eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) w).and
        (eventually_half_pow_smul_mem (ball_mem_nhds 0 hr) (v + w)))).exists
    rw [he _ j h1, he _ j h2, he _ j h3, smul_add, hadd _ h1 _ h2, smul_add]
  · filter_upwards [ball_mem_nhds 0 hr] with v hv
    simpa using he v 0 (by simpa using hv)
end GlobalTheory
