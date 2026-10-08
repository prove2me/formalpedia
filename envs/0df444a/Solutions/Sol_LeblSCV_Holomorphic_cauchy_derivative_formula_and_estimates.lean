-- Prove2me | solution 1 for LeblSCV.Holomorphic.cauchy_derivative_formula_and_estimates
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:03:45.8206+00:00
-- url     : https://prove2.me/submissions/ead1f485-3fa5-4983-8375-62e49d3cac2d

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm
import Definitions.Def_LeblSCV_Holomorphic_wirtinger
import Definitions.Def_LeblSCV_Holomorphic_wirtingerIter
import Definitions.Def_LeblSCV_Holomorphic_distinguishedBoundary
import Theorems.Thm_LeblSCV_Holomorphic_cauchy_integral_formula_polydisc

set_option autoImplicit false
open Complex MeasureTheory Set Metric Filter Topology

namespace SCVOrth

theorem continuous_torusMap' {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap a r) := by
  unfold torusMap
  fun_prop

theorem torusMap_mem_sphere {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (θ : Fin n → ℝ) (k : Fin n) : torusMap a r θ k ∈ sphere (a k) (r k) := by
  simp [torusMap, abs_of_nonneg (hr k)]

/-- The torus integral of a product of one-variable functions is the product of circle integrals. -/
theorem torusIntegral_prod : ∀ (n : ℕ) (a : Fin n → ℂ) (r : Fin n → ℝ), (∀ k, 0 ≤ r k) →
    ∀ (φ : Fin n → ℂ → ℂ), (∀ k, ContinuousOn (φ k) (sphere (a k) (r k))) →
    torusIntegral (fun ζ : Fin n → ℂ => ∏ k, φ k (ζ k)) a r =
      ∏ k, ∮ z in C(a k, r k), φ k z := by
  intro n
  induction n with
  | zero =>
    intro a r hr φ hφ
    simp
  | succ n ih =>
    intro a r hr φ hφ
    have hint : TorusIntegrable (fun ζ : Fin (n + 1) → ℂ => ∏ k, φ k (ζ k)) a r := by
      unfold TorusIntegrable
      refine Continuous.integrableOn_Icc ?_
      refine continuous_finsetProd _ (fun k _ => ?_)
      exact (hφ k).comp_continuous ((continuous_apply k).comp (continuous_torusMap' a r))
        (fun θ => torusMap_mem_sphere a r hr θ k)
    rw [torusIntegral_succ hint, Fin.prod_univ_succ]
    have : ∀ x : ℂ, torusIntegral (fun y : Fin n → ℂ => ∏ k : Fin (n + 1), φ k ((Fin.cons x y : Fin (n + 1) → ℂ) k))
        (a ∘ Fin.succ) (r ∘ Fin.succ) = φ 0 x * ∏ j : Fin n, ∮ z in C(a j.succ, r j.succ), φ j.succ z := by
      intro x
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [torusIntegral_const_mul]
      congr 1
      exact ih (a ∘ Fin.succ) (r ∘ Fin.succ) (fun j => hr j.succ) (fun j => φ j.succ)
        (fun j => hφ j.succ)
    simp only [this]
    have h2 : ∮ x in C(a 0, r 0), φ 0 x * ∏ j : Fin n, ∮ z in C(a j.succ, r j.succ), φ j.succ z =
        (∮ x in C(a 0, r 0), φ 0 x) * ∏ j : Fin n, ∮ z in C(a j.succ, r j.succ), φ j.succ z := by
      simpa only [smul_eq_mul] using circleIntegral.integral_smul_const (fun x => φ 0 x)
        (∏ j : Fin n, ∮ z in C(a j.succ, r j.succ), φ j.succ z) (a 0) (r 0)
    rw [h2]

theorem circle_orth (c : ℂ) (R : ℝ) (hR : 0 < R) (β α : ℕ) :
    ∮ z in C(c, R), (z - c) ^ β / (z - c) ^ (α + 1) = if β = α then 2 * Real.pi * I else 0 := by
  have hz : ∀ z ∈ sphere c R, (z - c) ^ β / (z - c) ^ (α + 1) = (z - c) ^ ((β : ℤ) - (α + 1 : ℕ)) := by
    intro z hz
    have hne : z - c ≠ 0 := by
      intro h0
      have : z = c := sub_eq_zero.1 h0
      rw [mem_sphere, this, dist_self] at hz
      linarith
    rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast]
  rw [circleIntegral.integral_congr hR.le hz]
  by_cases h : β = α
  · subst h
    have : ((β : ℤ) - ((β + 1 : ℕ) : ℤ)) = -1 := by push_cast; ring
    rw [this, if_pos rfl]
    simp only [zpow_neg_one]
    exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hR)
  · rw [if_neg h]
    refine circleIntegral.integral_sub_zpow_of_ne ?_ c c R
    intro h'
    apply h
    omega

theorem torus_orth {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 < r k)
    (β α : Fin n → ℕ) :
    torusIntegral (fun ζ : Fin n → ℂ => (∏ k, (ζ k - a k) ^ β k) / ∏ k, (ζ k - a k) ^ (α k + 1)) a r =
      if β = α then (2 * Real.pi * I) ^ n else 0 := by
  classical
  have e : ∀ ζ : Fin n → ℂ, (∏ k, (ζ k - a k) ^ β k) / ∏ k, (ζ k - a k) ^ (α k + 1) =
      ∏ k, ((ζ k - a k) ^ β k / (ζ k - a k) ^ (α k + 1)) := fun ζ => by
    rw [Finset.prod_div_distrib]
  simp only [e]
  rw [torusIntegral_prod n a r (fun k => (hr k).le) (fun k z => (z - a k) ^ β k / (z - a k) ^ (α k + 1))]
  · simp only [circle_orth _ _ (hr _)]
    by_cases h : β = α
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, β k ≠ α k := by
        by_contra hcon
        push Not at hcon
        exact h (funext hcon)
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  · intro k
    have : ∀ z ∈ sphere (a k) (r k), (z - a k) ^ (α k + 1) ≠ 0 := by
      intro z hz
      refine pow_ne_zero _ (fun h0 => ?_)
      have : z = a k := sub_eq_zero.1 h0
      rw [mem_sphere, this, dist_self] at hz
      linarith [hr k]
    exact (continuousOn_id.sub continuousOn_const).pow _ |>.div
      ((continuousOn_id.sub continuousOn_const).pow _) this


theorem norm_term {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a z : Fin n → ℂ) (β : Fin n → ℕ) :
    ‖LeblSCV.Holomorphic.powerSeriesTerm c a β z‖ = ‖c β‖ * ∏ k, ‖z k - a k‖ ^ β k := by
  simp [LeblSCV.Holomorphic.powerSeriesTerm, norm_mul, norm_prod, norm_pow]

theorem coeff_torus' {n : ℕ} (a : Fin n → ℂ) (ρ r : Fin n → ℝ) (hr : ∀ k, 0 < r k)
    (hrρ : ∀ k, r k < ρ k) (c : (Fin n → ℕ) → ℂ) (f : (Fin n → ℂ) → ℂ)
    (hconv : ∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K →
      LeblSCV.Holomorphic.ConvergesUniformlyAbsolutelyOn c a K)
    (hsum : ∀ z ∈ LeblSCV.Shared.polydisc a ρ,
      HasSum (fun β => LeblSCV.Holomorphic.powerSeriesTerm c a β z) (f z)) (α : Fin n → ℕ) :
    torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - a k) ^ (α k + 1)) a r = (2 * Real.pi * I) ^ n * c α := by
  classical
  let zr : Fin n → ℂ := fun k => a k + (r k : ℂ)
  have hzr : zr ∈ LeblSCV.Shared.polydisc a ρ := by
    intro k
    simpa [zr, abs_of_pos (hr k)] using hrρ k
  obtain ⟨S, hS⟩ := hconv {zr} (Set.singleton_subset_iff.2 hzr) isCompact_singleton
  have hsumm0 : Summable (fun β => ‖LeblSCV.Holomorphic.powerSeriesTerm c a β zr‖) :=
    ⟨_, hS.tendsto_at (Set.mem_singleton _)⟩
  have hnorm0 : ∀ β, ‖LeblSCV.Holomorphic.powerSeriesTerm c a β zr‖ =
      ‖c β‖ * ∏ k, r k ^ β k := by
    intro β
    rw [norm_term]
    congr 1
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [zr, abs_of_pos (hr k)]
  have hsumm : Summable (fun β : Fin n → ℕ => ‖c β‖ * ∏ k, r k ^ β k) := by
    simpa only [hnorm0] using hsumm0
  -- objects on the torus
  let ζ : (Fin n → ℝ) → Fin n → ℂ := torusMap a r
  let X : (Fin n → ℝ) → ℂ := fun θ => ∏ i, (r i : ℂ) * exp (θ i * I) * I
  let Pα : (Fin n → ℂ) → ℂ := fun w => ∏ k, (w k - a k) ^ (α k + 1)
  let F : (Fin n → ℕ) → (Fin n → ℝ) → ℂ := fun β θ =>
    X θ * (LeblSCV.Holomorphic.powerSeriesTerm c a β (ζ θ) / Pα (ζ θ))
  have hζ_norm : ∀ θ k, ‖ζ θ k - a k‖ = r k := fun θ k => by
    simp [ζ, torusMap, abs_of_pos (hr k)]
  have hζΔ : ∀ θ, ζ θ ∈ LeblSCV.Shared.polydisc a ρ := fun θ k => by
    rw [hζ_norm]; exact hrρ k
  have hPne : ∀ θ, Pα (ζ θ) ≠ 0 := fun θ => by
    refine Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ ?_)
    intro h0
    have := hζ_norm θ k
    rw [sub_eq_zero.1 h0] at this
    simp at this
    linarith [hr k]
  have hζc : Continuous ζ := SCVOrth.continuous_torusMap' a r
  have hXc : Continuous X := by
    refine continuous_finsetProd _ (fun j _ => ?_)
    fun_prop
  have hPc : Continuous fun θ => Pα (ζ θ) := by
    refine continuous_finsetProd _ (fun j _ => ?_)
    exact (((continuous_apply j).comp hζc).sub continuous_const).pow _
  have hFc : ∀ β, Continuous (F β) := by
    intro β
    refine hXc.mul (Continuous.div ?_ hPc hPne)
    unfold LeblSCV.Holomorphic.powerSeriesTerm
    refine continuous_const.mul (continuous_finsetProd _ (fun j _ => ?_))
    exact (((continuous_apply j).comp hζc).sub continuous_const).pow _
  have hFint : ∀ β, Integrable (F β) (volume.restrict (Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi)) :=
    fun β => (hFc β).integrableOn_Icc
  have hXnorm : ∀ θ, ‖X θ‖ = ∏ k, r k := fun θ => by
    simp only [X, norm_prod, norm_mul, Complex.norm_real, norm_I, mul_one]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [abs_of_pos (hr k)]
  have hFnorm : ∀ β θ, ‖F β θ‖ = (∏ k, r k) * ((‖c β‖ * ∏ k, r k ^ β k) / ∏ k, r k ^ (α k + 1)) := by
    intro β θ
    simp only [F, norm_mul, norm_div, hXnorm, norm_term, Pα, norm_prod, norm_pow, hζ_norm]
  have hFsum : Summable fun β => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), ‖F β θ‖ := by
    simp only [hFnorm, integral_const]
    exact (hsumm.div_const _).mul_left _ |>.mul_left _
  have hHas := hasSum_integral_of_summable_integral_norm hFint hFsum
  have htsum : ∀ θ, ∑' β, F β θ = X θ * (f (ζ θ) / Pα (ζ θ)) := by
    intro θ
    have := (((hsum _ (hζΔ θ)).div_const (Pα (ζ θ))).mul_left (X θ))
    exact this.tsum_eq
  have hint : ∀ β, ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F β θ =
      c β * (if β = α then (2 * Real.pi * I) ^ n else 0) := by
    intro β
    have h1 : ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F β θ =
        torusIntegral (fun w : Fin n → ℂ => c β * ((∏ k, (w k - a k) ^ β k) /
          ∏ k, (w k - a k) ^ (α k + 1))) a r := by
      unfold torusIntegral
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [F, smul_eq_mul, LeblSCV.Holomorphic.powerSeriesTerm, Pα, ζ]
      ring
    rw [h1, torusIntegral_const_mul, SCVOrth.torus_orth a r hr β α]
  simp only [htsum] at hHas
  simp only [hint] at hHas
  have hsingle : HasSum (fun β : Fin n → ℕ => c β * (if β = α then (2 * Real.pi * I) ^ n else 0))
      (c α * (2 * Real.pi * I) ^ n) := by
    convert hasSum_ite_eq α (c α * (2 * Real.pi * I) ^ n) using 1
    funext β
    by_cases h : β = α
    · subst h; simp
    · simp [h]
  have hfin := hHas.unique hsingle
  have hfin2 : torusIntegral (fun w : Fin n → ℂ => f w / ∏ k, (w k - a k) ^ (α k + 1)) a r =
      ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), X θ * (f (ζ θ) / Pα (ζ θ)) := by
    unfold torusIntegral
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp [X, Pα, ζ, smul_eq_mul]
  rw [hfin2, hfin, mul_comm]

end SCVOrth

namespace SCVDeriv

def cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ k, ‖z k - a k‖ ≤ r k}

theorem cpoly_eq_pi {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    cpoly a r = Set.univ.pi (fun k => closedBall (a k) (r k)) := by
  ext z; simp [cpoly, mem_closedBall, dist_eq_norm]

theorem isCompact_cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : IsCompact (cpoly a r) := by
  rw [cpoly_eq_pi]
  exact isCompact_univ_pi (fun k => isCompact_closedBall _ _)

theorem torusMap_mem_cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (θ : Fin n → ℝ) : torusMap a r θ ∈ cpoly a r := by
  intro k
  simp [torusMap, abs_of_nonneg (hr k)]

theorem continuous_torusMap {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap a r) := by
  unfold torusMap
  fun_prop

/-- On the torus, the coordinates stay away from an interior point. -/
theorem torus_sub_norm {n : ℕ} (a z : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (hz : ∀ k, ‖z k - a k‖ < ρ k) (θ : Fin n → ℝ) (k : Fin n) :
    ρ k - ‖z k - a k‖ ≤ ‖torusMap a ρ θ k - z k‖ := by
  have h1 : ‖torusMap a ρ θ k - a k‖ = ρ k := by
    simp [torusMap, abs_of_pos (hρ k)]
  have h2 := norm_sub_norm_le (torusMap a ρ θ k - a k) (z k - a k)
  have h3 : torusMap a ρ θ k - a k - (z k - a k) = torusMap a ρ θ k - z k := by ring
  rw [h3, h1] at h2
  exact h2

/-- Differentiation under the integral sign for a kernel `(c θ - ξ)^{-m}`. -/
theorem hasDerivAt_param_integral {n : ℕ} (W c : (Fin n → ℝ) → ℂ) (hW : Continuous W)
    (hc : Continuous c) (ε : ℝ) (hε : 0 < ε) (hcε : ∀ θ, 2 * ε ≤ ‖c θ‖) (m : ℕ) :
    HasDerivAt (fun ξ : ℂ => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi),
        W θ * ((c θ - ξ) ^ m)⁻¹)
      (∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), W θ * ((m : ℂ) / (c θ) ^ (m + 1))) 0 := by
  set μ : Measure (Fin n → ℝ) := volume.restrict (Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi)) with hμ
  have hfin : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hne : ∀ θ, ∀ ξ : ℂ, ξ ∈ ball (0 : ℂ) ε → c θ - ξ ≠ 0 := by
    intro θ ξ hξ h0
    have h1 : c θ = ξ := sub_eq_zero.1 h0
    have h2 := hcε θ
    rw [h1] at h2
    have h3 : ‖ξ‖ < ε := by simpa using hξ
    linarith [norm_nonneg ξ]
  let F : ℂ → (Fin n → ℝ) → ℂ := fun ξ θ => W θ * ((c θ - ξ) ^ m)⁻¹
  let F' : ℂ → (Fin n → ℝ) → ℂ := fun ξ θ => W θ * ((m : ℂ) / (c θ - ξ) ^ (m + 1))
  have hcont_ξ : ∀ ξ : ℂ, ξ ∈ ball (0 : ℂ) ε → Continuous (F ξ) := by
    intro ξ hξ
    refine hW.mul (Continuous.inv₀ ?_ ?_)
    · exact (hc.sub continuous_const).pow m
    · intro θ; exact pow_ne_zero _ (hne θ ξ hξ)
  have hcont_ξ' : ∀ ξ : ℂ, ξ ∈ ball (0 : ℂ) ε → Continuous (F' ξ) := by
    intro ξ hξ
    refine hW.mul (Continuous.div continuous_const ((hc.sub continuous_const).pow _) ?_)
    intro θ; exact pow_ne_zero _ (hne θ ξ hξ)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ε := mem_ball_self hε
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := (0 : ℂ)) (s := ball (0 : ℂ) ε)
    (bound := fun θ => ‖W θ‖ * (m * (ε ^ (m + 1))⁻¹)) (ball_mem_nhds _ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [F, F'] using key.2
  · filter_upwards [ball_mem_nhds (0 : ℂ) hε] with ξ hξ
    exact (hcont_ξ ξ hξ).aestronglyMeasurable
  · exact (hcont_ξ 0 h0).integrableOn_Icc
  · exact (hcont_ξ' 0 h0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun θ ξ hξ => ?_)
    have h1 : ε ≤ ‖c θ - ξ‖ := by
      have := norm_sub_norm_le (c θ) ξ
      have h3 : ‖ξ‖ < ε := by simpa using hξ
      linarith [hcε θ]
    have h2 : ε ^ (m + 1) ≤ ‖c θ - ξ‖ ^ (m + 1) := pow_le_pow_left₀ hε.le h1 _
    simp only [F', norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact inv_anti₀ (pow_pos hε _) h2
  · have hb : Continuous fun θ : Fin n → ℝ => ‖W θ‖ * ((m : ℝ) * (ε ^ (m + 1))⁻¹) :=
      hW.norm.mul continuous_const
    exact hb.integrableOn_Icc
  · refine Filter.Eventually.of_forall (fun θ ξ hξ => ?_)
    have hnz := hne θ ξ hξ
    have hu : HasDerivAt (fun ξ : ℂ => c θ - ξ) (-1) ξ := by
      simpa using (hasDerivAt_id ξ).const_sub (c θ)
    have hp : HasDerivAt (fun ξ : ℂ => (c θ - ξ) ^ m) ((m : ℂ) * (c θ - ξ) ^ (m - 1) * (-1)) ξ :=
      hu.pow m
    have hi := hp.inv (pow_ne_zero _ hnz)
    have hm := hi.const_mul (W θ)
    refine hm.congr_deriv ?_
    show _ = W θ * ((m : ℂ) / (c θ - ξ) ^ (m + 1))
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      field_simp
      ring


theorem torus_sub_ne {n : ℕ} (a z : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (hz : ∀ k, ‖z k - a k‖ < ρ k) (θ : Fin n → ℝ) (k : Fin n) :
    torusMap a ρ θ k - z k ≠ 0 := by
  intro h
  have := torus_sub_norm a z ρ hρ hz θ k
  rw [h] at this
  simp at this
  linarith [hz k]

theorem aux_div (x g A B : ℂ) : x * (g / (A * B)) = x * (g / B) * A⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv]; ring

theorem torus_hasDerivAt {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (g : (Fin n → ℂ) → ℂ) (hg : ContinuousOn g (cpoly a ρ)) (z : Fin n → ℂ)
    (hz : ∀ j, ‖z j - a j‖ < ρ j) (k : Fin n) (β : Fin n → ℕ) :
    HasDerivAt (fun ξ : ℂ => torusIntegral
        (fun ζ => g ζ / ∏ j, (ζ j - Function.update z k (z k + ξ) j) ^ (β j + 1)) a ρ)
      (((β k : ℂ) + 1) * torusIntegral
        (fun ζ => g ζ / ∏ j, (ζ j - z j) ^ (Function.update β k (β k + 1) j + 1)) a ρ) 0 := by
  classical
  let P : (Fin n → ℂ) → ℂ := fun ζ => ∏ j ∈ Finset.univ.erase k, (ζ j - z j) ^ (β j + 1)
  let X : (Fin n → ℝ) → ℂ := fun θ => ∏ i, (ρ i : ℂ) * exp (θ i * I) * I
  let W : (Fin n → ℝ) → ℂ := fun θ => X θ * (g (torusMap a ρ θ) / P (torusMap a ρ θ))
  let c : (Fin n → ℝ) → ℂ := fun θ => torusMap a ρ θ k - z k
  have hcont_tm := continuous_torusMap a ρ
  have hsub : ∀ θ, torusMap a ρ θ ∈ cpoly a ρ := torusMap_mem_cpoly a ρ (fun k => (hρ k).le)
  have hPc : Continuous fun θ => P (torusMap a ρ θ) := by
    refine continuous_finsetProd _ (fun j _ => ?_)
    exact (((continuous_apply j).comp hcont_tm).sub continuous_const).pow _
  have hPne : ∀ θ, P (torusMap a ρ θ) ≠ 0 := fun θ =>
    Finset.prod_ne_zero_iff.2 (fun j _ => pow_ne_zero _ (torus_sub_ne a z ρ hρ hz θ j))
  have hX : Continuous X := by
    refine continuous_finsetProd _ (fun j _ => ?_)
    fun_prop
  have hW : Continuous W :=
    hX.mul ((hg.comp_continuous hcont_tm hsub).div hPc hPne)
  have hc : Continuous c := ((continuous_apply k).comp hcont_tm).sub continuous_const
  set ε : ℝ := (ρ k - ‖z k - a k‖) / 2 with hε
  have hεpos : 0 < ε := by have := hz k; simp only [hε]; linarith
  have hcε : ∀ θ, 2 * ε ≤ ‖c θ‖ := fun θ => by
    have := torus_sub_norm a z ρ hρ hz θ k
    simp only [hε, c]; linarith
  have key := SCVDeriv.hasDerivAt_param_integral W c hW hc ε hεpos hcε (β k + 1)
  have hrew : ∀ (ξ : ℂ) (θ : Fin n → ℝ),
      (∏ i, (ρ i : ℂ) * exp (θ i * I) * I) •
        ((fun ζ : Fin n → ℂ => g ζ / ∏ j, (ζ j - Function.update z k (z k + ξ) j) ^ (β j + 1))
          (torusMap a ρ θ)) = W θ * ((c θ - ξ) ^ (β k + 1))⁻¹ := by
    intro ξ θ
    have hprod : ∏ j, (torusMap a ρ θ j - Function.update z k (z k + ξ) j) ^ (β j + 1) =
        (c θ - ξ) ^ (β k + 1) * P (torusMap a ρ θ) := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
      congr 1
      · simp only [c, Function.update_self]
        ring_nf
      · refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    simp only [W, X, hprod, smul_eq_mul]
    exact aux_div _ _ _ _
  have hfun : (fun ξ : ℂ => torusIntegral
        (fun ζ => g ζ / ∏ j, (ζ j - Function.update z k (z k + ξ) j) ^ (β j + 1)) a ρ) =
      fun ξ : ℂ => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi),
        W θ * ((c θ - ξ) ^ (β k + 1))⁻¹ := by
    funext ξ
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => hrew ξ θ)
  rw [hfun]
  refine key.congr_deriv ?_
  unfold torusIntegral
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  have hprod : ∏ j, (torusMap a ρ θ j - z j) ^ (Function.update β k (β k + 1) j + 1) =
      (c θ) ^ (β k + 1 + 1) * P (torusMap a ρ θ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    congr 1
    · simp [c]
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [W, X, hprod, smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The Wirtinger operator is the complex derivative along the `k`-th coordinate. -/
theorem wirtinger_eq_of_hasDerivAt {n : ℕ} (h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) (k : Fin n)
    (d : ℂ) (hd : HasDerivAt (fun ξ : ℂ => h (Function.update z k (z k + ξ))) d 0) :
    LeblSCV.Holomorphic.wirtinger k h z = d := by
  unfold LeblSCV.Holomorphic.wirtinger
  have h1 : HasDerivAt (fun t : ℝ => h (Function.update z k (z k + (t : ℂ)))) d 0 := by
    have := hd.comp_ofReal (z := 0)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => h (Function.update z k (z k + (t : ℂ) * I))) (I • d) 0 := by
    have hI : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I (0 : ℝ) := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I
    have hd' : HasDerivAt (fun ξ : ℂ => h (Function.update z k (z k + ξ))) d ((fun t : ℝ => (t : ℂ) * I) 0) := by
      simpa using hd
    exact HasDerivAt.scomp (0 : ℝ) hd' hI
  rw [h1.deriv, h2.deriv]
  simp only [smul_eq_mul]
  have : (I : ℂ) * (I * d) = -d := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [this]
  ring

theorem isOpen_polydisc' {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) :
    IsOpen (LeblSCV.Shared.polydisc a ρ) := by
  have : LeblSCV.Shared.polydisc a ρ = Set.univ.pi (fun k => ball (a k) (ρ k)) := by
    ext z; simp [LeblSCV.Shared.polydisc, mem_ball, dist_eq_norm]
  rw [this]
  exact isOpen_set_pi Set.finite_univ (fun k _ => isOpen_ball)

/-- The Cauchy-integral candidate for `∂^β f`. -/
noncomputable def Efun {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (f : (Fin n → ℂ) → ℂ)
    (β : Fin n → ℕ) : (Fin n → ℂ) → ℂ := fun z =>
  ((2 * Real.pi * I) ^ n)⁻¹ * torusIntegral (fun ζ =>
    ((∏ k : Fin n, (β k).factorial : ℕ) : ℂ) * f ζ / ∏ k : Fin n, (ζ k - z k) ^ (β k + 1)) a ρ

theorem factorial_update {n : ℕ} (β : Fin n → ℕ) (k : Fin n) :
    (∏ j : Fin n, (Function.update β k (β k + 1) j).factorial) =
      (β k + 1) * ∏ j : Fin n, (β j).factorial := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => (β j).factorial) (Finset.mem_univ k)]
  have : ∏ j ∈ Finset.univ.erase k, (Function.update β k (β k + 1) j).factorial =
      ∏ j ∈ Finset.univ.erase k, (β j).factorial :=
    Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this]
  simp only [Function.update_self, Nat.factorial_succ]
  ring

theorem Efun_hasDerivAt {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (cpoly a ρ)) (z : Fin n → ℂ)
    (hz : ∀ j, ‖z j - a j‖ < ρ j) (k : Fin n) (β : Fin n → ℕ) :
    HasDerivAt (fun ξ : ℂ => Efun a ρ f β (Function.update z k (z k + ξ)))
      (Efun a ρ f (Function.update β k (β k + 1)) z) 0 := by
  have hg : ContinuousOn (fun ζ => ((∏ k : Fin n, (β k).factorial : ℕ) : ℂ) * f ζ) (cpoly a ρ) :=
    continuousOn_const.mul hf
  have h := (torus_hasDerivAt a ρ hρ _ hg z hz k β).const_mul (((2 * Real.pi * I) ^ n)⁻¹)
  refine h.congr_deriv ?_
  unfold Efun
  congr 1
  rw [← torusIntegral_const_mul]
  congr 1
  funext ζ
  rw [factorial_update]
  push_cast
  ring

theorem Efun_wirtinger {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (cpoly a ρ)) (h : (Fin n → ℂ) → ℂ) (k : Fin n)
    (β : Fin n → ℕ) (hh : Set.EqOn h (Efun a ρ f β) (LeblSCV.Shared.polydisc a ρ)) :
    Set.EqOn (LeblSCV.Holomorphic.wirtinger k h) (Efun a ρ f (Function.update β k (β k + 1)))
      (LeblSCV.Shared.polydisc a ρ) := by
  intro z hz
  have hz' : ∀ j, ‖z j - a j‖ < ρ j := fun j => by simpa [LeblSCV.Shared.polydisc] using hz j
  refine wirtinger_eq_of_hasDerivAt h z k _ ?_
  refine (Efun_hasDerivAt a ρ hρ f hf z hz' k β).congr_of_eventuallyEq ?_
  have hcont : Continuous fun ξ : ℂ => Function.update z k (z k + ξ) :=
    continuous_const.update k (continuous_const.add continuous_id)
  have hmem : ∀ᶠ ξ in 𝓝 (0 : ℂ), Function.update z k (z k + ξ) ∈ LeblSCV.Shared.polydisc a ρ := by
    have := (isOpen_polydisc' a ρ).mem_nhds (by simpa using hz)
    exact hcont.continuousAt.eventually (by simpa using this)
  filter_upwards [hmem] with ξ hξ using hh hξ

theorem iterate_eqOn {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (cpoly a ρ)) (k : Fin n) (m : ℕ) :
    ∀ (β : Fin n → ℕ) (h : (Fin n → ℂ) → ℂ),
      Set.EqOn h (Efun a ρ f β) (LeblSCV.Shared.polydisc a ρ) →
      Set.EqOn ((LeblSCV.Holomorphic.wirtinger k)^[m] h) (Efun a ρ f (Function.update β k (β k + m)))
        (LeblSCV.Shared.polydisc a ρ) := by
  induction m with
  | zero => intro β h hh; simpa using hh
  | succ m ih =>
    intro β h hh
    rw [Function.iterate_succ_apply']
    have := Efun_wirtinger a ρ hρ f hf _ k _ (ih β h hh)
    simpa [Function.update_idem, Nat.add_assoc] using this

theorem foldr_eqOn {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (cpoly a ρ)) (α : Fin n → ℕ) :
    ∀ (L : List (Fin n)), L.Nodup → ∀ (β : Fin n → ℕ) (h : (Fin n → ℂ) → ℂ),
      Set.EqOn h (Efun a ρ f β) (LeblSCV.Shared.polydisc a ρ) →
      Set.EqOn (L.foldr (fun k g => (LeblSCV.Holomorphic.wirtinger k)^[α k] g) h)
        (Efun a ρ f (fun j => β j + if j ∈ L then α j else 0)) (LeblSCV.Shared.polydisc a ρ) := by
  classical
  intro L
  induction L with
  | nil => intro _ β h hh; simpa using hh
  | cons k L ih =>
    intro hnd β h hh
    have hk : k ∉ L := (List.nodup_cons.1 hnd).1
    have := iterate_eqOn a ρ hρ f hf k (α k) _ _ (ih (List.nodup_cons.1 hnd).2 β h hh)
    simp only [List.foldr_cons]
    convert this using 2
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [hk]
    · simp [Function.update_of_ne hjk, hjk]

theorem polydisc_eq_pi' {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) :
    LeblSCV.Shared.polydisc a ρ = Set.univ.pi (fun k => ball (a k) (ρ k)) := by
  ext z; simp [LeblSCV.Shared.polydisc, mem_ball, dist_eq_norm]

theorem closure_polydisc {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k) :
    closure (LeblSCV.Shared.polydisc a ρ) = cpoly a ρ := by
  rw [polydisc_eq_pi', closure_pi_set, cpoly_eq_pi]
  congr 1
  funext k
  exact closure_ball _ (hρ k).ne'

theorem polydisc_subset_cpoly {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) :
    LeblSCV.Shared.polydisc a ρ ⊆ cpoly a ρ := fun z hz k => (hz k).le

theorem cpoly_mono {n : ℕ} (a : Fin n → ℂ) {r ρ : Fin n → ℝ} (h : ∀ k, r k ≤ ρ k) :
    cpoly a r ⊆ cpoly a ρ := fun z hz k => (hz k).trans (h k)

theorem polydisc_mono {n : ℕ} (a : Fin n → ℂ) {r ρ : Fin n → ℝ} (h : ∀ k, r k ≤ ρ k) :
    LeblSCV.Shared.polydisc a r ⊆ LeblSCV.Shared.polydisc a ρ :=
  fun z hz k => lt_of_lt_of_le (hz k) (h k)

/-- The multi-index Wirtinger derivative of a function that is continuous on a closed polydisc
and separately differentiable in the open polydisc is given by the Cauchy integral. -/
theorem deriv_formula {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hcont : ContinuousOn f (cpoly a ρ))
    (hdiff : ∀ w ∈ LeblSCV.Shared.polydisc a ρ, ∀ k, DifferentiableAt ℂ
      (fun ξ : ℂ => f (Function.update w k (w k + ξ))) 0)
    (α : Fin n → ℕ) :
    Set.EqOn (LeblSCV.Holomorphic.wirtingerIter α f) (Efun a ρ f α) (LeblSCV.Shared.polydisc a ρ) := by
  classical
  have hhol : LeblSCV.Holomorphic.IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ) := by
    refine ⟨?_, hdiff⟩
    obtain ⟨C, hC⟩ := (isCompact_cpoly a ρ).exists_bound_of_continuousOn hcont
    intro p hp
    refine ⟨LeblSCV.Shared.polydisc a ρ, (isOpen_polydisc' a ρ).mem_nhds hp, C, fun w hw => ?_⟩
    exact hC w (polydisc_subset_cpoly a ρ hw.2)
  have hcl : ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)) := by
    rw [closure_polydisc a ρ hρ]; exact hcont
  have h0 : Set.EqOn f (Efun a ρ f 0) (LeblSCV.Shared.polydisc a ρ) := by
    intro z hz
    have := LeblSCV.Holomorphic.cauchy_integral_formula_polydisc a ρ hρ hcl hhol hz
    rw [this]
    simp [Efun]
  have := foldr_eqOn a ρ hρ f hcont α (List.finRange n) (List.nodup_finRange n) 0 f h0
  unfold LeblSCV.Holomorphic.wirtingerIter
  convert this using 2
  funext j
  simp

end SCVDeriv

theorem estimate_aux {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (c : ℂ) (α : Fin n → ℕ) (M : ℝ)
    (hM : ∀ ζ ∈ LeblSCV.Holomorphic.distinguishedBoundary a ρ, ‖f ζ‖ ≤ M)
    (hcα : c = ((2 * Real.pi * I) ^ n)⁻¹ *
        torusIntegral (fun ζ => f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) a ρ) :
    ‖c‖ ≤ M / ∏ k : Fin n, ρ k ^ α k := by
  have hρprod : 0 < ∏ k : Fin n, ρ k := Finset.prod_pos (fun k _ => hρ k)
  have hQ : 0 < ∏ k : Fin n, ρ k ^ (α k + 1) := Finset.prod_pos (fun k _ => pow_pos (hρ k) _)
  have hQα : 0 < ∏ k : Fin n, ρ k ^ α k := Finset.prod_pos (fun k _ => pow_pos (hρ k) _)
  have hbd := norm_torusIntegral_le_of_norm_le_const (f := fun ζ : Fin n → ℂ =>
      f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) (c := a) (R := ρ)
    (C := M / ∏ k : Fin n, ρ k ^ (α k + 1)) (fun θ => by
      have hmem : torusMap a ρ θ ∈ LeblSCV.Holomorphic.distinguishedBoundary a ρ := fun k => by
        simp [torusMap, abs_of_pos (hρ k)]
      have hden : ∏ k : Fin n, ‖(torusMap a ρ θ k - a k) ^ (α k + 1)‖ = ∏ k : Fin n, ρ k ^ (α k + 1) := by
        refine Finset.prod_congr rfl (fun k _ => ?_)
        rw [norm_pow, hmem k]
      show ‖f (torusMap a ρ θ) / ∏ k : Fin n, (torusMap a ρ θ k - a k) ^ (α k + 1)‖ ≤ _
      rw [norm_div, norm_prod, hden]
      exact div_le_div_of_nonneg_right (hM _ hmem) hQ.le)
  have hn2 : ‖(2 * (Real.pi : ℂ) * I) ^ n‖ = (2 * Real.pi) ^ n := by
    rw [norm_pow]; congr 1; simp [abs_of_pos Real.pi_pos]
  have habs : ∏ i : Fin n, |ρ i| = ∏ k : Fin n, ρ k :=
    Finset.prod_congr rfl (fun k _ => abs_of_pos (hρ k))
  rw [habs] at hbd
  have h2pi : (0 : ℝ) < (2 * Real.pi) ^ n := by positivity
  have hQeq : ∏ k : Fin n, ρ k ^ (α k + 1) = (∏ k : Fin n, ρ k ^ α k) * ∏ k : Fin n, ρ k := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun k _ => pow_succ _ _)
  rw [hcα, norm_mul, norm_inv, hn2]
  calc ((2 * Real.pi) ^ n)⁻¹ * ‖torusIntegral (fun ζ : Fin n → ℂ => f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) a ρ‖
      ≤ ((2 * Real.pi) ^ n)⁻¹ * (((2 * Real.pi) ^ n * ∏ k : Fin n, ρ k) * (M / ∏ k : Fin n, ρ k ^ (α k + 1))) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 h2pi.le)
    _ = M / ∏ k : Fin n, ρ k ^ α k := by
        rw [hQeq]
        field_simp

theorem fact_prod_ne_zero {n : ℕ} (α : Fin n → ℕ) : ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun k _ => (Nat.factorial_pos _).ne'))

open SCVDeriv in
theorem solution {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) {f : (Fin n → ℂ) → ℂ}
    (hcont : ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)))
    (hf : LeblSCV.Holomorphic.IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ)) :
    (∀ z ∈ LeblSCV.Shared.polydisc a ρ, ∀ α : Fin n → ℕ,
      LeblSCV.Holomorphic.wirtingerIter α f z = ((2 * Real.pi * I) ^ n)⁻¹ *
        torusIntegral (fun ζ => ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * f ζ /
          ∏ k : Fin n, (ζ k - z k) ^ (α k + 1)) a ρ) ∧
    (∀ c : (Fin n → ℕ) → ℂ,
      (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K →
        LeblSCV.Holomorphic.ConvergesUniformlyAbsolutelyOn c a K) →
      (∀ z ∈ LeblSCV.Shared.polydisc a ρ,
        HasSum (fun α => LeblSCV.Holomorphic.powerSeriesTerm c a α z) (f z)) →
      (∀ α : Fin n → ℕ,
        c α = (((∏ k : Fin n, (α k).factorial : ℕ) : ℂ))⁻¹ *
          LeblSCV.Holomorphic.wirtingerIter α f a) ∧
      (∀ M : ℝ, (∀ ζ ∈ LeblSCV.Holomorphic.distinguishedBoundary a ρ, ‖f ζ‖ ≤ M) →
        ∀ α : Fin n → ℕ, ‖c α‖ ≤ M / ∏ k : Fin n, ρ k ^ α k)) := by
  rw [closure_polydisc a ρ hρ] at hcont
  have hdiff := hf.2
  refine ⟨fun z hz α => deriv_formula a ρ hρ f hcont hdiff α hz, ?_⟩
  intro c hconv hsum
  have haΔ : a ∈ LeblSCV.Shared.polydisc a ρ := fun k => by simpa using hρ k
  have hid : ∀ α : Fin n → ℕ, LeblSCV.Holomorphic.wirtingerIter α f a =
      ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * c α := by
    intro α
    set r : Fin n → ℝ := fun k => ρ k / 2 with hrdef
    have hr : ∀ k, 0 < r k := fun k => by simp only [hrdef]; linarith [hρ k]
    have hrρ : ∀ k, r k < ρ k := fun k => by simp only [hrdef]; linarith [hρ k]
    have har : a ∈ LeblSCV.Shared.polydisc a r := fun k => by simpa using hr k
    have h1 := deriv_formula a r hr f (hcont.mono (cpoly_mono a (fun k => (hrρ k).le)))
      (fun w hw k => hdiff w (polydisc_mono a (fun k => (hrρ k).le) hw) k) α har
    rw [h1]
    unfold Efun
    have h2 := SCVOrth.coeff_torus' a ρ r hr hrρ c f hconv hsum α
    have h3 : ∀ ζ : Fin n → ℂ, ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * f ζ /
        ∏ k : Fin n, (ζ k - a k) ^ (α k + 1) =
        ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * (f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) :=
      fun ζ => mul_div_assoc _ _ _
    simp only [h3]
    rw [torusIntegral_const_mul, h2]
    have hne : (2 * Real.pi * I : ℂ) ^ n ≠ 0 :=
      pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
    field_simp
  refine ⟨fun α => ?_, ?_⟩
  · rw [hid α]
    exact (inv_mul_cancel_left₀ (fact_prod_ne_zero α) (c α)).symm
  · intro M hM α
    have h1 := deriv_formula a ρ hρ f hcont hdiff α haΔ
    have hcα : c α = ((2 * Real.pi * I) ^ n)⁻¹ *
        torusIntegral (fun ζ => f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) a ρ := by
      have h4 := hid α
      rw [h1] at h4
      unfold Efun at h4
      have h3 : ∀ ζ : Fin n → ℂ, ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * f ζ /
          ∏ k : Fin n, (ζ k - a k) ^ (α k + 1) =
          ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * (f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) :=
        fun ζ => mul_div_assoc _ _ _
      simp only [h3] at h4
      rw [torusIntegral_const_mul] at h4
      have hF := fact_prod_ne_zero α
      have : ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * c α =
          ((∏ k : Fin n, (α k).factorial : ℕ) : ℂ) * (((2 * Real.pi * I) ^ n)⁻¹ *
            torusIntegral (fun ζ => f ζ / ∏ k : Fin n, (ζ k - a k) ^ (α k + 1)) a ρ) := by
        rw [← h4]; ring
      exact mul_left_cancel₀ hF this
    exact estimate_aux a ρ hρ f (c α) α M hM hcα
