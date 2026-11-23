-- Prove2me | solution 1 for KernelRank.exists_eq_exp_of_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:25:25.526862+00:00
-- url     : https://prove2.me/submissions/9e591fd5-c611-4934-b765-34a0b4c5c3a4

import Mathlib
import Definitions.Def_KernelRankLean_Semigroup

set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
open KernelRank
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace KernelRank
theorem _root_.solution (M : ℝ → 𝔸) (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ A : 𝔸, ∀ t, 0 ≤ t → M t = exp (t • A) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  -- A continuous extension to the whole line, for integrating.
  set M' : ℝ → 𝔸 := fun s => M (max s 0) with hM'
  have hM'c : Continuous M' :=
    hcont.comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0
  have hM'eq : ∀ s, 0 ≤ s → M' s = M s := fun s hs => by simp [M', max_eq_left hs]
  have havg : Tendsto (fun δ : ℝ => δ⁻¹ • ∫ s in (0)..δ, M' s)
      (𝓝[>] 0) (𝓝 (1 : 𝔸)) := by
    simpa [hM'eq 0 le_rfl, h0] using
      (hM'c.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, u, hu⟩ :=
    (hpos.and (havg.eventually (Units.isOpen.mem_nhds isUnit_one))).exists
  set N : 𝔸 := ∫ s in (0)..δ, M' s with hN
  let A : 𝔸 := δ⁻¹ • ((M δ - 1) * ↑u⁻¹)
  -- `M x * N` is the integral of `M` over `[x, x + δ]`.
  have hF : ∀ x, 0 ≤ x →
      M x * N = (∫ s in (0)..(x + δ), M' s) - ∫ s in (0)..x, M' s := by
    intro x hx
    have hcomm := (ContinuousLinearMap.mul ℝ 𝔸 (M x)).intervalIntegral_comp_comm
      (hM'c.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at hcomm
    calc M x * N = ∫ s in (0)..δ, M x * M' s := hcomm.symm
      _ = ∫ s in (0)..δ, M' (x + s) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [uIcc_of_le hδ.le] at hs
          rw [hM'eq _ (add_nonneg hx hs.1), hM'eq _ hs.1, hadd x s hx hs.1]
      _ = ∫ s in x..(x + δ), M' s := by
          rw [intervalIntegral.integral_comp_add_left, add_zero]
      _ = _ := (intervalIntegral.integral_interval_sub_left (hM'c.intervalIntegrable _ _)
          (hM'c.intervalIntegrable _ _)).symm
  have hMF : ∀ x, 0 ≤ x →
      M x = δ⁻¹ • ((∫ s in (0)..(x + δ), M' s) - ∫ s in (0)..x, M' s) * ↑u⁻¹ := by
    intro x hx
    rw [← hF x hx, ← mul_smul_comm, ← hu, mul_assoc, Units.mul_inv, mul_one]
  -- So `M` has right derivative `M t * A`.
  have hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt M (M t * A) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun x => ∫ s in (0)..(x + δ), M' s) (M' (t + δ)) t :=
      (hM'c.integral_hasStrictDerivAt 0 (t + δ)).hasDerivAt.comp_add_const t δ
    have h2 := (hM'c.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hD := (((h1.sub h2).hasDerivWithinAt (s := Ici t)).const_smul δ⁻¹).mul_const
      (↑u⁻¹ : 𝔸)
    refine (hD.congr (fun x hx => hMF x (ht.trans hx)) (hMF t ht)).congr_deriv ?_
    rw [hM'eq _ (by linarith), hM'eq _ ht, hadd t δ ht hδ.le, smul_mul_assoc]
    simp only [A, mul_smul_comm]
    congr 1
    noncomm_ring
  refine ⟨A, fun t ht => ?_⟩
  -- `M x * exp (-x A)` has zero right derivative, so it stays `1`.
  set E : ℝ → 𝔸 := fun x => M x * exp (x • -A) with hE
  have hEd : ∀ x, 0 ≤ x → HasDerivWithinAt E 0 (Ici x) x := by
    intro x hx
    have he := (hasDerivAt_exp_smul_const (-A) x).hasDerivWithinAt (s := Ici x)
    have hc : Commute A (exp (x • -A)) := ((Commute.refl A).neg_right.smul_right x).exp_right
    convert (hderiv x hx).fun_mul he using 1
    rw [mul_assoc, hc.eq, mul_neg, mul_neg, add_neg_cancel]
  have hEc : ContinuousOn E (Icc 0 t) := fun x hx =>
    ((hcont x hx.1).mono Icc_subset_Ici_self).mul
      (hasDerivAt_exp_smul_const (-A) x).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hEc (fun x hx => hEd x hx.1) t ⟨ht, le_rfl⟩
  have hE0 : E 0 = 1 := by simp [E, h0]
  have hinv : exp (t • -A) * exp (t • A) = 1 := by
    rw [← exp_add_of_commute (((Commute.refl A).neg_left.smul_left t).smul_right t), smul_neg,
      neg_add_cancel, exp_zero]
  calc M t = M t * (exp (t • -A) * exp (t • A)) := by rw [hinv, mul_one]
    _ = E t * exp (t • A) := by rw [← mul_assoc]
    _ = exp (t • A) := by rw [hconst, hE0, one_mul]
end KernelRank
