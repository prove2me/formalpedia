-- Prove2me | solution 1 for MDPFinance.BayesianModels.lemma_5_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:41:01.138718+00:00
-- url     : https://prove2.me/submissions/61dd6c09-0ad0-4fa2-aa7e-b66c86273329

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior

open MeasureTheory ProbabilityTheory

namespace MDP541Aux

theorem main {Θ : Type*} [MeasurableSpace Θ] (Q0 : Measure Θ) [IsProbabilityMeasure Q0]
    (q : ℕ → Θ → ℝ) (hq : ∀ j, Measurable (q j)) (μ : ℕ → Measure Θ) (n : ℕ)
    (h0 : μ 0 = Q0)
    (hrec : ∀ k, 0 < (∫⁻ θ, ENNReal.ofReal (q k θ) ∂(μ k)) →
      (∫⁻ θ, ENNReal.ofReal (q k θ) ∂(μ k)) < ⊤ → ∀ C : Set Θ, MeasurableSet C →
      μ (k + 1) C = (∫⁻ θ in C, ENNReal.ofReal (q k θ) ∂(μ k)) /
        (∫⁻ θ, ENNReal.ofReal (q k θ) ∂(μ k)))
    (hfin : ∀ k ≤ n, (∫⁻ θ, ∏ j ∈ Finset.range k, ENNReal.ofReal (q j θ) ∂Q0) < ⊤)
    (hpos : 0 < ∫⁻ θ, ∏ j ∈ Finset.range n, ENNReal.ofReal (q j θ) ∂Q0)
    (C : Set Θ) (hC : MeasurableSet C) :
    μ n C = (∫⁻ θ in C, ∏ k ∈ Finset.range n, ENNReal.ofReal (q k θ) ∂Q0) /
        (∫⁻ θ, ∏ k ∈ Finset.range n, ENNReal.ofReal (q k θ) ∂Q0) := by
  set p : ℕ → Θ → ENNReal := fun k θ => ∏ j ∈ Finset.range k, ENNReal.ofReal (q j θ) with hp
  have pm : ∀ k, Measurable (p k) := fun k => by
    simp only [hp]; exact Finset.measurable_prod _ (fun j _ => (hq j).ennreal_ofReal)
  set P : ℕ → ENNReal := fun k => ∫⁻ θ, p k θ ∂Q0 with hP
  have Ppos : ∀ k ≤ n, 0 < P k := by
    intro k hk
    rw [pos_iff_ne_zero]
    intro hz
    have hae : p k =ᵐ[Q0] 0 := (lintegral_eq_zero_iff (pm k)).1 hz
    have : P n = 0 := by
      rw [hP]; simp only
      rw [lintegral_eq_zero_iff (pm n)]
      filter_upwards [hae] with θ hθ
      simp only [hp, Pi.zero_apply] at hθ ⊢
      rw [← Finset.prod_range_mul_prod_Ico _ hk, hθ, zero_mul]
    exact hpos.ne' this
  have claim : ∀ k ≤ n, μ k = Q0.withDensity (fun θ => p k θ * (P k)⁻¹) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [hp, hP, h0]
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hPk0 := Ppos k (by omega)
      have hPkt := hfin k (by omega)
      have hPk0' := Ppos (k+1) hk
      have hPkt' := hfin (k+1) hk
      have hint : ∀ D : Set Θ, MeasurableSet D →
          ∫⁻ θ in D, ENNReal.ofReal (q k θ) ∂(μ k) = (∫⁻ θ in D, p (k+1) θ ∂Q0) * (P k)⁻¹ := by
        intro D hD
        rw [ihk, setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop)
          (hq k).ennreal_ofReal hD, ← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hPk0.ne')]
        refine setLIntegral_congr_fun hD (fun θ _ => ?_)
        simp only [Pi.mul_apply, hp, Finset.prod_range_succ]
        ring
      have htot : ∫⁻ θ, ENNReal.ofReal (q k θ) ∂(μ k) = P (k+1) * (P k)⁻¹ := by
        have := hint Set.univ MeasurableSet.univ
        simpa only [Measure.restrict_univ] using this
      have hinv0 : (P k)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hPkt.ne
      have hinvt : (P k)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hPk0.ne'
      ext D hD
      rw [hrec k (by rw [htot]; exact ENNReal.mul_pos hPk0'.ne' hinv0)
        (by rw [htot]; exact ENNReal.mul_lt_top hPkt' (lt_top_iff_ne_top.2 hinvt)) D hD,
        hint D hD, htot, ENNReal.mul_div_mul_right _ _ hinv0 hinvt, withDensity_apply _ hD,
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hPk0'.ne'), div_eq_mul_inv]
  rw [claim n le_rfl, withDensity_apply _ hC,
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (Ppos n le_rfl).ne'), div_eq_mul_inv]

end MDP541Aux

open MDPFinance.BayesianModels in
theorem solution {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ]
    [MeasurableSpace A] [MeasurableSpace Z] (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (n : ℕ)
    (xs : ℕ → EX) (as : ℕ → A) (zs : ℕ → Z)
    (hfin : ∀ k ≤ n, (∫⁻ θ, ∏ j ∈ Finset.range k,
      ENNReal.ofReal (M.qZ (xs j) θ (as j) (zs (j + 1))) ∂M.Q0) < ⊤)
    (hpos : 0 < ∫⁻ θ, ∏ j ∈ Finset.range n,
      ENNReal.ofReal (M.qZ (xs j) θ (as j) (zs (j + 1))) ∂M.Q0)
    (C : Set Θ) (hC : MeasurableSet C) :
    Pf.mu n xs as zs C =
      (∫⁻ θ in C, ∏ k ∈ Finset.range n, ENNReal.ofReal (M.qZ (xs k) θ (as k) (zs (k + 1))) ∂M.Q0) /
        (∫⁻ θ, ∏ k ∈ Finset.range n, ENNReal.ofReal (M.qZ (xs k) θ (as k) (zs (k + 1))) ∂M.Q0) := by
  haveI := M.isProbQ0
  have hq : ∀ j, Measurable fun θ => M.qZ (xs j) θ (as j) (zs (j + 1)) := fun j =>
    M.hqZ_meas.comp (show Measurable fun θ : Θ => (xs j, θ, as j, zs (j + 1)) by fun_prop)
  exact MDP541Aux.main M.Q0 (fun j θ => M.qZ (xs j) θ (as j) (zs (j + 1))) hq
    (fun k => Pf.mu k xs as zs) n (Pf.hmu0 xs as zs)
    (fun k => Pf.hmu_rec k xs as zs) hfin hpos C hC
