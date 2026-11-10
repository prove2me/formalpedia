-- Prove2me | solution 1 for MarketInterference.FluidLimit.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:54:06.002737+00:00
-- url     : https://prove2.me/submissions/7ee1eca1-2f3c-46b6-9a16-42aeabc2d20f

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_NetworkLP

open Pointwise

namespace Aux_MarketInterference_l1

open MarketInterference.FluidBias

theorem hF {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (τ : ℝ) (hτ : 0 < τ) (D : Fin nd → ℝ) (S : Fin ns → ℝ)
    (y : E → ℝ) :
    Feasible N τ D S (τ • y) ↔ Feasible N 1 (fun i => 1 / τ * D i) (fun j => 1 / τ * S j) y := by
  unfold Feasible
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, one_mul]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall_congr' fun e => ⟨fun ⟨a, b⟩ => ⟨?_, ?_⟩, fun ⟨a, b⟩ => ⟨?_, ?_⟩⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
  · refine forall_congr' fun i => ?_
    rw [one_div_mul_eq_div, le_div_iff₀' hτ]
  · refine forall_congr' fun j => ?_
    rw [one_div_mul_eq_div, le_div_iff₀' hτ]
  · refine forall_congr' fun u => ?_
    exact mul_right_inj' hτ.ne'

theorem hobj {nd ns : ℕ} {I E : Type} [Fintype E] (N : Network nd ns I E) (τ : ℝ) (y : E → ℝ) :
    obj N (τ • y) = τ * obj N y := by
  unfold obj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Aux_MarketInterference_l1

open MarketInterference.FluidBias in
theorem solution {nd ns : ℕ} {I E : Type} [Fintype E] [DecidableEq I]
    (N : MarketInterference.FluidBias.Network nd ns I E) (τ : ℝ) (hτ : 0 < τ) (d : Fin nd → ℕ) (s : Fin ns → ℕ) :
    (1 / τ) * MarketInterference.FluidBias.Phi N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) =
        MarketInterference.FluidBias.Phi N 1 (fun i => 1 / τ * (d i : ℝ)) (fun j => 1 / τ * (s j : ℝ)) ∧
      ∀ x : E → ℝ, MarketInterference.FluidBias.IsOptimal N 1 (fun i => 1 / τ * (d i : ℝ)) (fun j => 1 / τ * (s j : ℝ)) x ↔
        MarketInterference.FluidBias.IsOptimal N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) (τ • x) := by
  have hinv : ∀ z : E → ℝ, τ • (τ⁻¹ • z) = z := by
    intro z
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have hFe := Aux_MarketInterference_l1.hF N τ hτ (fun i => (d i : ℝ)) (fun j => (s j : ℝ))
  have hob := Aux_MarketInterference_l1.hobj N τ
  refine ⟨?_, fun x => ?_⟩
  · have hset : obj N '' {x | Feasible N τ (fun i => (d i : ℝ)) (fun j => (s j : ℝ)) x}
        = τ • (obj N '' {x | Feasible N 1 (fun i => 1 / τ * (d i : ℝ))
            (fun j => 1 / τ * (s j : ℝ)) x}) := by
      ext r
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨obj N (τ⁻¹ • x), ⟨τ⁻¹ • x, ?_, rfl⟩, ?_⟩
        · rw [← hFe, hinv]; exact hx
        · rw [← hob, hinv]
      · rintro ⟨t, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨τ • y, (hFe y).mpr hy, hob y⟩
    unfold Phi
    rw [hset, Real.sSup_smul_of_nonneg hτ.le, smul_eq_mul, ← mul_assoc, one_div,
      inv_mul_cancel₀ hτ.ne', one_mul]
  · unfold IsOptimal
    rw [hFe x]
    refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h y hy => ?_⟩
    · have hz' : Feasible N 1 (fun i => 1 / τ * (d i : ℝ)) (fun j => 1 / τ * (s j : ℝ)) (τ⁻¹ • z) := by
        rw [← hFe, hinv]; exact hz
      have h1 := h _ hz'
      calc obj N z = obj N (τ • (τ⁻¹ • z)) := by rw [hinv]
        _ = τ * obj N (τ⁻¹ • z) := hob _
        _ ≤ τ * obj N x := mul_le_mul_of_nonneg_left h1 hτ.le
        _ = obj N (τ • x) := (hob x).symm
    · have := h (τ • y) ((hFe y).mpr hy)
      rw [hob, hob] at this
      exact le_of_mul_le_mul_left this hτ
