-- Prove2me | solution 1 for LimitPoA.RegVar.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:58:23.54604+00:00
-- url     : https://prove2.me/submissions/e779e091-2a96-48d8-9b31-8d045f4b15c6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

open Filter Topology LimitPoA.RegVar KellyStochasticNetworks
open scoped Pointwise

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0)
    (g : ℝ) (hg : 0 < g) (d : Fin Γ.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand Γ d) :
    PoA Γ τ d =
      PoA Γ (scaled Γ τ (totalDemand Γ d) g) (fun k => d k / totalDemand Γ d) := by
  set T := totalDemand Γ d with hTdef
  set σ := scaled Γ τ T g with hσ
  set d' : Fin Γ.Sd → ℝ := fun k => d k / T with hd'
  have hT0 : T ≠ 0 := hT.ne'
  -- the rescaling map
  let sc : (Fin Γ.R → ℝ) → (Fin Γ.R → ℝ) := fun f r => f r / T
  have load_sc : ∀ f a, load Γ (sc f) a = load Γ f a / T := by
    intro f a
    simp only [load, linkFlow, sc, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have stc_sc : ∀ f s, stratCost Γ σ (sc f) s = stratCost Γ τ f s / g := by
    intro f s
    simp only [stratCost, load_sc, hσ, scaled, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_div_cancel₀ _ hT0]
    ring
  have cost_sc : ∀ f, cost Γ σ (sc f) = (T * g)⁻¹ * cost Γ τ f := by
    intro f
    simp only [cost, load_sc, hσ, scaled, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_div_cancel₀ _ hT0]
    field_simp
  have prof_sc : ∀ f, IsProfile Γ d' (sc f) ↔ IsProfile Γ d f := by
    intro f
    simp only [IsProfile, wardropFeasible, Set.mem_setOf_eq, sc, hd']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun r => ?_, fun k => ?_⟩
      · have := h1 r
        exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hT))
      · have := h2 k
        rw [← Finset.sum_div] at this
        exact (div_left_inj' hT0).mp this
    · rintro ⟨h1, h2⟩
      refine ⟨fun r => div_nonneg (h1 r) hT.le, fun k => ?_⟩
      rw [← Finset.sum_div, h2 k]
  have ne_sc : ∀ f, IsNE Γ σ d' (sc f) ↔ IsNE Γ τ d f := by
    intro f
    have hp := prof_sc f
    simp only [IsProfile] at hp
    simp only [IsNE, IsWardropEquilibrium, hp]
    have e1 : ∀ s, (∑ j, σ j (linkFlow Γ.inc (sc f) j) * Γ.inc j s) = stratCost Γ τ f s / g :=
      fun s => stc_sc f s
    simp only [e1]
    have e2 : ∀ r, (0 < sc f r ↔ 0 < f r) := fun r => by
      simp only [sc]; exact div_pos_iff_of_pos_right hT
    simp only [e2]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun r r' hr hpos => ?_⟩
      have := h r r' hr hpos
      have := (div_le_div_iff_of_pos_right hg).mp this
      simpa [stratCost, load] using this
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun r r' hr hpos => ?_⟩
      have := h r r' hr hpos
      exact (div_le_div_iff_of_pos_right hg).mpr (by simpa [stratCost, load] using this)
  have surj : ∀ f', f' = sc (fun r => T * f' r) := by
    intro f'; funext r; simp only [sc]; field_simp
  have img : ∀ (P : (Fin Γ.R → ℝ) → Prop) (P' : (Fin Γ.R → ℝ) → Prop),
      (∀ f, P' (sc f) ↔ P f) →
      cost Γ σ '' {f | P' f} = (T * g)⁻¹ • (cost Γ τ '' {f | P f}) := by
    intro P P' hP
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨f', hf', rfl⟩
      refine ⟨cost Γ τ (fun r => T * f' r), ⟨_, (hP _).mp ?_, rfl⟩, ?_⟩
      · rw [← surj]; exact hf'
      · rw [← cost_sc, ← surj]
    · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨sc f, (hP f).mpr hf, cost_sc f⟩
  have hc : 0 ≤ (T * g)⁻¹ := inv_nonneg.mpr (mul_pos hT hg).le
  have hc0 : (T * g)⁻¹ ≠ 0 := inv_ne_zero (mul_pos hT hg).ne'
  unfold PoA NECost SOCost
  rw [img (IsNE Γ τ d) (IsNE Γ σ d') ne_sc, img (IsProfile Γ d) (IsProfile Γ d') prof_sc,
    Real.sSup_smul_of_nonneg hc, Real.sInf_smul_of_nonneg hc, smul_eq_mul, smul_eq_mul,
    mul_div_mul_left _ _ hc0]
