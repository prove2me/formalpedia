-- Prove2me | solution 1 for LeblSCV.Holomorphic.cauchy_integral_formula_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:46:09.001191+00:00
-- url     : https://prove2.me/submissions/b0edef3e-9c24-45ff-ad5c-ca86231a03ad

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn

set_option autoImplicit false
open Complex MeasureTheory Set Metric Filter Topology

namespace SCVCauchy

/-- closed polydisc -/
def cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ k, ‖z k - a k‖ ≤ r k}

theorem torusMap_mem_cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (θ : Fin n → ℝ) : torusMap a r θ ∈ cpoly a r := by
  intro k
  simp [torusMap, norm_mul, abs_of_nonneg (hr k)]

theorem continuous_torusMap {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap a r) := by
  unfold torusMap
  fun_prop

theorem polydisc_eq_pi {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) :
    LeblSCV.Shared.polydisc a ρ = Set.univ.pi (fun k => ball (a k) (ρ k)) := by
  ext z; simp [LeblSCV.Shared.polydisc, mem_ball, dist_eq_norm]

theorem cpoly_eq_pi {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    cpoly a r = Set.univ.pi (fun k => closedBall (a k) (r k)) := by
  ext z; simp [cpoly, mem_closedBall, dist_eq_norm]

theorem closure_polydisc {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k) :
    closure (LeblSCV.Shared.polydisc a ρ) = cpoly a ρ := by
  rw [polydisc_eq_pi, closure_pi_set, cpoly_eq_pi]
  congr 1
  funext k
  exact closure_ball _ (hρ k).ne'

theorem isCompact_cpoly {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : IsCompact (cpoly a r) := by
  rw [cpoly_eq_pi]
  exact isCompact_univ_pi (fun k => isCompact_closedBall _ _)

/-- Torus integrability of a function continuous on the closed polydisc. -/
theorem torusIntegrable_of_continuousOn {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ k, 0 ≤ r k) {F : (Fin n → ℂ) → ℂ} (hF : ContinuousOn F (cpoly a r)) :
    TorusIntegrable F a r := by
  unfold TorusIntegrable
  refine ContinuousOn.integrableOn_Icc ?_
  exact hF.comp (continuous_torusMap a r).continuousOn
    (fun θ _ => torusMap_mem_cpoly a r hr θ)

theorem cauchy_closed : ∀ (n : ℕ) (a : Fin n → ℂ) (r : Fin n → ℝ), (∀ k, 0 < r k) →
    ∀ (f : (Fin n → ℂ) → ℂ), ContinuousOn f (cpoly a r) →
    (∀ w ∈ cpoly a r, ∀ k, DifferentiableAt ℂ
      (fun ξ : ℂ => f (Function.update w k (w k + ξ))) 0) →
    ∀ z : Fin n → ℂ, (∀ k, ‖z k - a k‖ < r k) →
    f z = ((2 * Real.pi * I) ^ n)⁻¹ * torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a r := by
  intro n
  induction n with
  | zero =>
    intro a r hr f hf hd z hz
    simp [Subsingleton.elim z a]
  | succ n ih =>
    intro a r hr f hf hd z hz
    have hz0 : ‖z 0 - a 0‖ < r 0 := hz 0
    set zt : Fin n → ℂ := Fin.tail z with hzt
    let g : ℂ → ℂ := fun ξ => f (Fin.cons ξ zt)
    have hcons_mem : ∀ ξ : ℂ, ‖ξ - a 0‖ ≤ r 0 → (Fin.cons ξ zt : Fin (n + 1) → ℂ) ∈ cpoly a r := by
      intro ξ hξ k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using hξ
      · simpa [hzt, Fin.tail] using (hz j.succ).le
    have hg_cont : ContinuousOn g (closedBall (a 0) (r 0)) := by
      refine hf.comp (by fun_prop : Continuous fun ξ : ℂ => (Fin.cons ξ zt : Fin (n + 1) → ℂ)).continuousOn ?_
      intro ξ hξ
      exact hcons_mem ξ (by simpa [dist_eq_norm] using hξ)
    have hg_diff : DifferentiableOn ℂ g (ball (a 0) (r 0)) := by
      intro ξ0 hξ0
      have h1 := hd (Fin.cons ξ0 zt) (hcons_mem ξ0 (by simpa [dist_eq_norm] using (mem_ball.1 hξ0).le)) 0
      have h2 : (fun ξ : ℂ => f (Function.update (Fin.cons ξ0 zt : Fin (n + 1) → ℂ) 0
          ((Fin.cons ξ0 zt : Fin (n + 1) → ℂ) 0 + ξ))) = fun ξ => g (ξ0 + ξ) := by
        funext ξ
        simp [g, Fin.update_cons_zero]
      rw [h2] at h1
      have h3 : DifferentiableAt ℂ g (ξ0 + 0) := by
        have := (differentiableAt_comp_add_left (f := g) (a := ξ0) (x := 0)).1 h1
        simpa using this
      simpa using h3.differentiableWithinAt
    have hg : DiffContOnCl ℂ g (ball (a 0) (r 0)) :=
      ⟨hg_diff, hg_cont.mono (by rw [closure_ball _ (hr 0).ne'])⟩
    have hmem : z 0 ∈ ball (a 0) (r 0) := by simpa [dist_eq_norm] using hz0
    have h1 := hg.circleIntegral_sub_inv_smul hmem
    have hz_tail : ∀ j : Fin n, ‖zt j - (a ∘ Fin.succ) j‖ < (r ∘ Fin.succ) j := fun j => hz j.succ
    -- inner Cauchy formula on the sphere
    have hinner : ∀ x : ℂ, ‖x - a 0‖ = r 0 →
        torusIntegral (fun y : Fin n → ℂ => f (Fin.cons x y) / ∏ j, (y j - zt j))
          (a ∘ Fin.succ) (r ∘ Fin.succ) = (2 * Real.pi * I) ^ n * g x := by
      intro x hx
      have hxm : (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) '' cpoly (a ∘ Fin.succ) (r ∘ Fin.succ) ⊆
          cpoly a r := by
        rintro _ ⟨y, hy, rfl⟩ k
        refine Fin.cases ?_ (fun j => ?_) k
        · simpa [hx] using le_rfl
        · simpa using hy j
      have hcont : ContinuousOn (fun y : Fin n → ℂ => f (Fin.cons x y))
          (cpoly (a ∘ Fin.succ) (r ∘ Fin.succ)) := by
        refine hf.comp (by fun_prop : Continuous fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)).continuousOn ?_
        intro y hy
        exact hxm ⟨y, hy, rfl⟩
      have hdiff : ∀ w ∈ cpoly (a ∘ Fin.succ) (r ∘ Fin.succ), ∀ k : Fin n,
          DifferentiableAt ℂ (fun ξ : ℂ => (fun y : Fin n → ℂ => f (Fin.cons x y))
            (Function.update w k (w k + ξ))) 0 := by
        intro w hw k
        have := hd (Fin.cons x w) (hxm ⟨w, hw, rfl⟩) k.succ
        have e : (fun ξ : ℂ => (fun y : Fin n → ℂ => f (Fin.cons x y))
            (Function.update w k (w k + ξ))) = fun ξ => f (Function.update (Fin.cons x w : Fin (n + 1) → ℂ)
              k.succ ((Fin.cons x w : Fin (n + 1) → ℂ) k.succ + ξ)) := by
          funext ξ
          simp [Fin.cons_update]
        rw [e]
        exact this
      have key := ih (a ∘ Fin.succ) (r ∘ Fin.succ) (fun j => hr j.succ) _ hcont hdiff zt hz_tail
      have key' : f (Fin.cons x zt) = ((2 * Real.pi * I) ^ n)⁻¹ *
          torusIntegral (fun y : Fin n → ℂ => f (Fin.cons x y) / ∏ j, (y j - zt j))
            (a ∘ Fin.succ) (r ∘ Fin.succ) := key
      have hne : (2 * Real.pi * I : ℂ) ^ n ≠ 0 := by
        apply pow_ne_zero; simp [Real.pi_ne_zero, I_ne_zero]
      show _ = (2 * Real.pi * I) ^ n * f (Fin.cons x zt)
      rw [key']
      field_simp
    -- integrability of the full integrand
    have hden : ∀ θ : Fin (n + 1) → ℝ, ∀ k, torusMap a r θ k - z k ≠ 0 := by
      intro θ k hk
      have h1 : ‖torusMap a r θ k - a k‖ = r k := by
        simp [torusMap, abs_of_pos (hr k)]
      have h2 : torusMap a r θ k = z k := sub_eq_zero.1 hk
      have := hz k
      rw [← h2, h1] at this
      exact lt_irrefl _ this
    have hFint : TorusIntegrable (fun ζ : Fin (n + 1) → ℂ => f ζ / ∏ k, (ζ k - z k)) a r := by
      unfold TorusIntegrable
      refine Continuous.integrableOn_Icc ?_
      have h1 : Continuous fun θ : Fin (n + 1) → ℝ => f (torusMap a r θ) :=
        hf.comp_continuous (continuous_torusMap a r) (fun θ => torusMap_mem_cpoly a r (fun k => (hr k).le) θ)
      have h2 : Continuous fun θ : Fin (n + 1) → ℝ => ∏ k, (torusMap a r θ k - z k) := by
        refine continuous_finsetProd _ (fun k _ => ?_)
        have := (continuous_apply k).comp (continuous_torusMap a r)
        exact this.sub continuous_const
      exact h1.div h2 (fun θ => Finset.prod_ne_zero_iff.2 (fun k _ => hden θ k))
    rw [torusIntegral_succ hFint]
    have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hcong : ∮ x in C(a 0, r 0), torusIntegral
          (fun y : Fin n → ℂ => (fun ζ : Fin (n + 1) → ℂ => f ζ / ∏ k, (ζ k - z k)) (Fin.cons x y))
          (a ∘ Fin.succ) (r ∘ Fin.succ) =
        ∮ x in C(a 0, r 0), ((2 * Real.pi * I) ^ n) • ((x - z 0)⁻¹ • g x) := by
      refine circleIntegral.integral_congr (hr 0).le (fun x hx => ?_)
      have hx' : ‖x - a 0‖ = r 0 := by simpa [dist_eq_norm] using hx
      have e : ∀ y : Fin n → ℂ,
          (fun ζ : Fin (n + 1) → ℂ => f ζ / ∏ k, (ζ k - z k)) (Fin.cons x y) =
          (x - z 0)⁻¹ * (f (Fin.cons x y) / ∏ j, (y j - zt j)) := by
        intro y
        simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hzt, Fin.tail]
        field_simp
      simp only [e]
      rw [torusIntegral_const_mul, hinner x hx']
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    rw [hcong]
    have h3 : ∮ x in C(a 0, r 0), ((2 * Real.pi * I) ^ n) • ((x - z 0)⁻¹ • g x) =
        ((2 * Real.pi * I) ^ n) • ∮ x in C(a 0, r 0), (x - z 0)⁻¹ • g x := by
      exact circleIntegral.integral_smul _ _ _ _
    rw [h3, h1]
    have hgz : g (z 0) = f z := by simp [g, hzt, Fin.cons_self_tail]
    rw [hgz]
    simp only [smul_eq_mul, pow_succ]
    have hne' : (2 * Real.pi * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ hne
    field_simp


theorem cauchy_polydisc {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hcont : ContinuousOn f (cpoly a ρ))
    (hdiff : ∀ w ∈ LeblSCV.Shared.polydisc a ρ, ∀ k, DifferentiableAt ℂ
      (fun ξ : ℂ => f (Function.update w k (w k + ξ))) 0)
    (z : Fin n → ℂ) (hz : ∀ k, ‖z k - a k‖ < ρ k) :
    f z = ((2 * Real.pi * I) ^ n)⁻¹ * torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a ρ := by
  classical
  set c : ℂ := ((2 * Real.pi * I) ^ n)⁻¹ with hc
  let rr : ℝ → Fin n → ℝ := fun s k => s * ρ k
  let Ts : ℝ → ℂ := fun s => torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a (rr s)
  -- eventual properties of s near 1
  have hev1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), 0 < s ∧ s < 1 := by
    have : Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT zero_lt_one
    filter_upwards [this] with s hs using hs
  have hev2 : ∀ᶠ s in 𝓝[<] (1 : ℝ), ∀ k, ‖z k - a k‖ < s * ρ k := by
    rw [Filter.eventually_all]
    intro k
    have hcts : Continuous fun s : ℝ => s * ρ k := continuous_id.mul continuous_const
    have : ∀ᶠ s in 𝓝 (1 : ℝ), ‖z k - a k‖ < s * ρ k :=
      hcts.continuousAt.eventually (lt_mem_nhds (by simpa using hz k))
    exact nhdsWithin_le_nhds this
  have hev3 : ∀ᶠ s in 𝓝[<] (1 : ℝ), f z = c * Ts s := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    have hsub : cpoly a (rr s) ⊆ cpoly a ρ := by
      intro w hw k
      exact (hw k).trans (by simpa [rr] using mul_le_of_le_one_left (hρ k).le hs1.2.le)
    refine cauchy_closed n a (rr s) (fun k => mul_pos hs1.1 (hρ k)) f (hcont.mono hsub) ?_ z hs2
    intro w hw k
    refine hdiff w ?_ k
    intro j
    exact lt_of_le_of_lt (hw j) (by
      simpa [rr] using mul_lt_of_lt_one_left (hρ j) hs1.2)
  -- the limit of the integrals
  have hT : Tendsto Ts (𝓝[<] (1 : ℝ)) (𝓝 (torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a ρ)) := by
    let F : ℝ → (Fin n → ℝ) → ℂ := fun s θ =>
      (∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I) •
        (f (torusMap a (rr s) θ) / ∏ k, (torusMap a (rr s) θ k - z k))
    have hTs : ∀ s, Ts s = ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F s θ := fun s => rfl
    have hrr1 : rr 1 = ρ := by funext k; simp [rr]
    have hT1 : torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a ρ =
        ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F 1 θ := by
      have : torusIntegral (fun ζ => f ζ / ∏ k, (ζ k - z k)) a (rr 1) =
          ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F 1 θ := rfl
      rwa [hrr1] at this
    rw [hT1]
    change Tendsto (fun s => ∫ θ in Icc (0 : Fin n → ℝ) (fun _ => 2 * Real.pi), F s θ) _ _
    obtain ⟨C, hC⟩ := (isCompact_cpoly a ρ).exists_bound_of_continuousOn hcont
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a (fun k => by simpa using (hρ k).le))
    let δ : Fin n → ℝ := fun k => (ρ k - ‖z k - a k‖) / 2
    have hδ : ∀ k, 0 < δ k := fun k => by have := hz k; simp only [δ]; linarith
    have hev4 : ∀ᶠ s in 𝓝[<] (1 : ℝ), ∀ k, ‖z k - a k‖ + δ k < s * ρ k := by
      rw [Filter.eventually_all]
      intro k
      have hcts : Continuous fun s : ℝ => s * ρ k := continuous_id.mul continuous_const
      have : ∀ᶠ s in 𝓝 (1 : ℝ), ‖z k - a k‖ + δ k < s * ρ k :=
        hcts.continuousAt.eventually (lt_mem_nhds (by simp only [δ, one_mul]; linarith [hz k]))
      exact nhdsWithin_le_nhds this
    have hden : ∀ s : ℝ, 0 < s → (∀ k, ‖z k - a k‖ + δ k < s * ρ k) → ∀ θ k,
        δ k ≤ ‖torusMap a (rr s) θ k - z k‖ := by
      intro s hs hsk θ k
      have h1 : ‖torusMap a (rr s) θ k - a k‖ = s * ρ k := by
        simp [torusMap, rr, abs_of_pos hs, abs_of_pos (hρ k)]
      have h2 := norm_sub_norm_le (torusMap a (rr s) θ k - a k) (z k - a k)
      have h3 : torusMap a (rr s) θ k - a k - (z k - a k) = torusMap a (rr s) θ k - z k := by ring
      rw [h3, h1] at h2
      linarith [hsk k]
    have hδprod : 0 < ∏ k, δ k := Finset.prod_pos (fun k _ => hδ k)
    have hρprod : 0 ≤ ∏ k, ρ k := Finset.prod_nonneg (fun k _ => (hρ k).le)
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (∏ k, ρ k) * (C / ∏ k, δ k)) ?_ ?_ ?_ ?_
    · filter_upwards [hev1, hev4] with s hs1 hs4
      refine Continuous.aestronglyMeasurable ?_
      have hne : ∀ θ : Fin n → ℝ, ∏ k, (torusMap a (rr s) θ k - z k) ≠ 0 := by
        intro θ
        refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_)
        intro h0
        have := hden s hs1.1 hs4 θ k
        rw [h0] at this
        simp at this
        exact absurd this (not_le.2 (hδ k))
      have hsub : ∀ θ, torusMap a (rr s) θ ∈ cpoly a ρ := by
        intro θ k
        have := torusMap_mem_cpoly a (rr s) (fun k => (mul_pos hs1.1 (hρ k)).le) θ k
        exact this.trans (by simpa [rr] using mul_le_of_le_one_left (hρ k).le hs1.2.le)
      have h1 : Continuous fun θ : Fin n → ℝ => f (torusMap a (rr s) θ) :=
        hcont.comp_continuous (continuous_torusMap a (rr s)) hsub
      have h2 : Continuous fun θ : Fin n → ℝ => ∏ k, (torusMap a (rr s) θ k - z k) := by
        refine continuous_finsetProd _ (fun k _ => ?_)
        exact ((continuous_apply k).comp (continuous_torusMap a (rr s))).sub continuous_const
      have h3 : Continuous fun θ : Fin n → ℝ =>
          ∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I := by
        refine continuous_finsetProd _ (fun k _ => ?_)
        fun_prop
      exact h3.smul (h1.div h2 hne)
    · filter_upwards [hev1, hev4] with s hs1 hs4
      refine Filter.Eventually.of_forall (fun θ => ?_)
      have hsub : torusMap a (rr s) θ ∈ cpoly a ρ := by
        intro k
        have := torusMap_mem_cpoly a (rr s) (fun k => (mul_pos hs1.1 (hρ k)).le) θ k
        exact this.trans (by simpa [rr] using mul_le_of_le_one_left (hρ k).le hs1.2.le)
      have hfb := hC _ hsub
      have hd := hden s hs1.1 hs4 θ
      have hn1 : ‖∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I‖ ≤ ∏ k, ρ k := by
        rw [norm_prod]
        refine Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => ?_)
        simp [rr, abs_of_pos hs1.1, abs_of_pos (hρ k)]
        exact mul_le_of_le_one_left (hρ k).le hs1.2.le
      have hn2 : ‖f (torusMap a (rr s) θ) / ∏ k, (torusMap a (rr s) θ k - z k)‖ ≤ C / ∏ k, δ k := by
        rw [norm_div, norm_prod]
        refine div_le_div₀ hC0 hfb hδprod ?_
        exact Finset.prod_le_prod (fun k _ => (hδ k).le) (fun k _ => hd k)
      calc ‖F s θ‖ = ‖∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I‖ *
            ‖f (torusMap a (rr s) θ) / ∏ k, (torusMap a (rr s) θ k - z k)‖ := norm_smul _ _
        _ ≤ (∏ k, ρ k) * (C / ∏ k, δ k) :=
          mul_le_mul hn1 hn2 (norm_nonneg _) hρprod
    · haveI : IsFiniteMeasure (volume.restrict (Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      exact integrable_const _
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      have hζc : Continuous fun s : ℝ => torusMap a (rr s) θ := by
        unfold torusMap rr
        fun_prop
      have hmem1 : torusMap a (rr 1) θ ∈ cpoly a ρ := by
        rw [hrr1]; exact torusMap_mem_cpoly a ρ (fun k => (hρ k).le) θ
      have hlim_in : Tendsto (fun s : ℝ => torusMap a (rr s) θ) (𝓝[<] (1 : ℝ))
          (𝓝[cpoly a ρ] (torusMap a (rr 1) θ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨(hζc.tendsto 1).mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [hev1] with s hs1 k
        have := torusMap_mem_cpoly a (rr s) (fun k => (mul_pos hs1.1 (hρ k)).le) θ k
        exact this.trans (by simpa [rr] using mul_le_of_le_one_left (hρ k).le hs1.2.le)
      have hf_lim : Tendsto (fun s : ℝ => f (torusMap a (rr s) θ)) (𝓝[<] (1 : ℝ))
          (𝓝 (f (torusMap a (rr 1) θ))) :=
        (hcont _ hmem1).tendsto.comp hlim_in
      have hden_lim : Tendsto (fun s : ℝ => ∏ k, (torusMap a (rr s) θ k - z k)) (𝓝[<] (1 : ℝ))
          (𝓝 (∏ k, (torusMap a (rr 1) θ k - z k))) := by
        have hc : Continuous fun s : ℝ => ∏ k, (torusMap a (rr s) θ k - z k) := by
          refine continuous_finsetProd _ (fun k _ => ?_)
          exact ((continuous_apply k).comp hζc).sub continuous_const
        exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      have hne1 : ∏ k, (torusMap a (rr 1) θ k - z k) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_)
        intro h0
        have h1 : ‖torusMap a (rr 1) θ k - a k‖ = ρ k := by
          simp [torusMap, rr, abs_of_pos (hρ k)]
        have h2 : torusMap a (rr 1) θ k = z k := sub_eq_zero.1 h0
        have := hz k
        rw [← h2, h1] at this
        exact lt_irrefl _ this
      have hsc : Tendsto (fun s : ℝ => ∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I) (𝓝[<] (1 : ℝ))
          (𝓝 (∏ i, ((rr 1 i : ℝ) : ℂ) * exp (θ i * I) * I)) := by
        have hc : Continuous fun s : ℝ => ∏ i, ((rr s i : ℝ) : ℂ) * exp (θ i * I) * I := by
          refine continuous_finsetProd _ (fun k _ => ?_)
          simp only [rr]
          fun_prop
        exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
      exact hsc.smul (hf_lim.div hden_lim hne1)
  have hT' := hT.const_mul c
  have hconst : Tendsto (fun _ : ℝ => f z) (𝓝[<] (1 : ℝ)) (𝓝 (f z)) := tendsto_const_nhds
  have := tendsto_nhds_unique (hconst.congr' (by
    filter_upwards [hev3] with s hs using hs)) hT'
  exact this

end SCVCauchy

open SCVCauchy in
theorem solution {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) {f : (Fin n → ℂ) → ℂ}
    (hcont : ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)))
    (hf : LeblSCV.Holomorphic.IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ))
    {z : Fin n → ℂ} (hz : z ∈ LeblSCV.Shared.polydisc a ρ) :
    f z = ((2 * Real.pi * I) ^ n)⁻¹ *
      torusIntegral (fun ζ => f ζ / ∏ k : Fin n, (ζ k - z k)) a ρ := by
  rw [closure_polydisc a ρ hρ] at hcont
  exact cauchy_polydisc a ρ hρ f hcont hf.2 z (fun k => by simpa [LeblSCV.Shared.polydisc] using hz k)
