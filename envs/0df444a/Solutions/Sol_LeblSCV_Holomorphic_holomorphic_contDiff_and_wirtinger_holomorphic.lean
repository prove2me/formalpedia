-- Prove2me | solution 1 for LeblSCV.Holomorphic.holomorphic_contDiff_and_wirtinger_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:32:39.997853+00:00
-- url     : https://prove2.me/submissions/fd37af26-b139-4237-a338-637fc7281bf0

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm
import Definitions.Def_LeblSCV_Holomorphic_wirtinger
import Definitions.Def_LeblSCV_Holomorphic_wirtingerIter
import Definitions.Def_LeblSCV_Holomorphic_distinguishedBoundary
import Theorems.Thm_LeblSCV_Holomorphic_cauchy_derivative_formula_and_estimates

set_option autoImplicit false
open Complex MeasureTheory Set Metric Filter Topology

namespace SCVCont

open LeblSCV.Holomorphic

/-- One-coordinate Lipschitz estimate for a locally bounded separately holomorphic function. -/
theorem line_lipschitz {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hdiff : ∀ z ∈ U, ∀ k : Fin n, DifferentiableAt ℂ (fun ξ : ℂ => f (Function.update z k (z k + ξ))) 0)
    (p : Fin n → ℂ) (R M : ℝ) (hR : 0 < R)
    (hball : ball p (2 * R) ⊆ U) (hM : ∀ w ∈ ball p (2 * R), ‖f w‖ ≤ M)
    (y : Fin n → ℂ) (hy : y ∈ ball p R) (k : Fin n) (h : ℂ) (hh : ‖h‖ < R / 2) :
    ‖f (Function.update y k (y k + h)) - f y‖ ≤ (2 * M / R) * ‖h‖ := by
  classical
  let φ : ℂ → ℂ := fun ξ => f (Function.update y k (y k + ξ))
  have hmem : ∀ ξ : ℂ, ‖ξ‖ < R → Function.update y k (y k + ξ) ∈ ball p (2 * R) := by
    intro ξ hξ
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [Function.update_self, dist_eq_norm]
      have h1 : ‖y j - p j‖ < R := by
        have := (dist_pi_lt_iff hR).1 (mem_ball.1 hy) j
        simpa [dist_eq_norm] using this
      calc ‖y j + ξ - p j‖ = ‖(y j - p j) + ξ‖ := by ring_nf
        _ ≤ ‖y j - p j‖ + ‖ξ‖ := norm_add_le _ _
        _ < 2 * R := by linarith
    · rw [Function.update_of_ne hj, dist_eq_norm]
      have := (dist_pi_lt_iff hR).1 (mem_ball.1 hy) j
      simp only [dist_eq_norm] at this
      linarith
  have hφd : DifferentiableOn ℂ φ (ball 0 R) := by
    intro ξ hξ
    have hξ' : ‖ξ‖ < R := by simpa using hξ
    have hU' := hball (hmem ξ hξ')
    have h1 := hdiff _ hU' k
    have e : (fun ξ' : ℂ => f (Function.update (Function.update y k (y k + ξ)) k
        ((Function.update y k (y k + ξ)) k + ξ'))) = fun ξ' => φ (ξ + ξ') := by
      funext ξ'
      simp [φ, add_assoc]
    rw [e] at h1
    have := (differentiableAt_comp_add_left (f := φ) (a := ξ) (x := 0)).1 h1
    simpa using this.differentiableWithinAt
  have hφb : ∀ ξ ∈ ball (0 : ℂ) R, ‖φ ξ‖ ≤ M := fun ξ hξ =>
    hM _ (hmem ξ (by simpa using hξ))
  -- derivative bound on ball (0, R/2)
  have hder : ∀ ξ ∈ ball (0 : ℂ) (R / 2), ‖deriv φ ξ‖ ≤ 2 * M / R := by
    intro ξ hξ
    have hξ' : ‖ξ‖ < R / 2 := by simpa using hξ
    have hsub : closedBall ξ (R / 2) ⊆ ball (0 : ℂ) R := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      calc ‖w‖ = ‖(w - ξ) + ξ‖ := by ring_nf
        _ ≤ ‖w - ξ‖ + ‖ξ‖ := norm_add_le _ _
        _ < R := by linarith
    have hdc : DiffContOnCl ℂ φ (ball ξ (R / 2)) :=
      hφd.diffContOnCl_ball hsub
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < R / 2) hdc
      (fun w hw => hφb w (hsub (sphere_subset_closedBall hw))) 
    calc ‖deriv φ ξ‖ ≤ M / (R / 2) := this
      _ = 2 * M / R := by field_simp
  have hconv : Convex ℝ (ball (0 : ℂ) (R / 2)) := convex_ball _ _
  have := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun ξ hξ => (hφd.differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith) hξ))))
    hder (mem_ball_self (by linarith)) (by simpa using hh)
  simpa [φ] using this

theorem holo_continuousAt {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {f : (Fin n → ℂ) → ℂ}
    (hf : IsHolomorphicOn f U) {p : Fin n → ℂ} (hp : p ∈ U) : ContinuousAt f p := by
  classical
  obtain ⟨N, hN, M, hM⟩ := hf.1 p hp
  have hNU : N ∩ U ∈ 𝓝 p := Filter.inter_mem hN (hU.mem_nhds hp)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hNU
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := by simp only [hRdef]; linarith
  have hεb : ∀ w ∈ ball p (2 * R), w ∈ ball p ε := fun w hw => by
    rw [mem_ball] at hw ⊢; simp only [hRdef] at hw; linarith
  have hball : ball p (2 * R) ⊆ U := fun w hw => (hεsub (hεb w hw)).2
  have hMb : ∀ w ∈ ball p (2 * R), ‖f w‖ ≤ M := fun w hw =>
    hM w ⟨(hεsub (hεb w hw)).1, (hεsub (hεb w hw)).2⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hMb p (mem_ball_self (by linarith)))
  set L : ℝ := 2 * M / R with hL
  have hL0 : 0 ≤ L := by positivity
  -- Lipschitz estimate near p
  have key : ∀ z ∈ ball p (R / 2), ‖f z - f p‖ ≤ n * (L * dist z p) := by
    intro z hz
    set d : ℝ := dist z p with hd
    have hdR : d < R / 2 := by simpa using hz
    let y : ℕ → Fin n → ℂ := fun m j => if (j : ℕ) < m then z j else p j
    have hcoord : ∀ j, ‖z j - p j‖ ≤ d := fun j => by
      have := norm_le_pi_norm (z - p) j
      simpa [hd, dist_eq_norm] using this
    have hy : ∀ m, y m ∈ ball p R := by
      intro m
      rw [mem_ball, dist_pi_lt_iff hR]
      intro j
      simp only [y]
      split_ifs
      · rw [dist_eq_norm]; linarith [hcoord j]
      · simp [hR]
    have claim : ∀ m, m ≤ n → ‖f (y m) - f p‖ ≤ m * (L * d) := by
      intro m
      induction m with
      | zero =>
        intro _
        have : y 0 = p := by funext j; simp [y]
        simp [this]
      | succ m ih =>
        intro hm
        have hmn : m < n := hm
        let k : Fin n := ⟨m, hmn⟩
        have hyk : y m k = p k := by simp [y, k]
        have hup : y (m + 1) = Function.update (y m) k (y m k + (z k - p k)) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [y, hyk, k]
          · rw [Function.update_of_ne hj]
            have : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
            simp only [y]
            by_cases h1 : (j : ℕ) < m
            · simp [h1, show (j : ℕ) < m + 1 by omega]
            · simp [h1, show ¬ (j : ℕ) < m + 1 by omega]
        have hstep := line_lipschitz (U := U) hf.2 p R M hR hball hMb (y m) (hy m) k (z k - p k)
          (by have := hcoord k; linarith)
        rw [← hup] at hstep
        have h1 : ‖f (y (m + 1)) - f p‖ ≤ ‖f (y (m + 1)) - f (y m)‖ + ‖f (y m) - f p‖ := by
          calc ‖f (y (m + 1)) - f p‖ = ‖(f (y (m + 1)) - f (y m)) + (f (y m) - f p)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        have h2 : L * ‖z k - p k‖ ≤ L * d := mul_le_mul_of_nonneg_left (hcoord k) hL0
        have h3 := ih (by omega)
        push_cast
        nlinarith
    have hyn : y n = z := by funext j; simp [y]
    have := claim n le_rfl
    rwa [hyn] at this
  rw [Metric.continuousAt_iff]
  intro η hη
  refine ⟨min (R / 2) (η / (n * L + 1)), by positivity, fun x hx => ?_⟩
  have hx1 : dist x p < R / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : dist x p < η / (n * L + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (key x (by simpa using hx1)) ?_
  have hpos : 0 < (n : ℝ) * L + 1 := by positivity
  calc (n : ℝ) * (L * dist x p) = ((n : ℝ) * L) * dist x p := by ring
    _ ≤ ((n : ℝ) * L + 1) * dist x p := by nlinarith [dist_nonneg (x := x) (y := p)]
    _ < ((n : ℝ) * L + 1) * (η / ((n : ℝ) * L + 1)) := by
        exact mul_lt_mul_of_pos_left hx2 hpos
    _ = η := by field_simp

theorem holo_continuousOn {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {f : (Fin n → ℂ) → ℂ}
    (hf : IsHolomorphicOn f U) : ContinuousOn f U :=
  fun p hp => (holo_continuousAt hU hf hp).continuousWithinAt

end SCVCont

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

theorem wirtingerIter_single {n : ℕ} (k : Fin n) (f : (Fin n → ℂ) → ℂ) :
    LeblSCV.Holomorphic.wirtingerIter (Pi.single k 1) f = LeblSCV.Holomorphic.wirtinger k f := by
  classical
  have key : ∀ L : List (Fin n), L.Nodup →
      L.foldr (fun j g => (LeblSCV.Holomorphic.wirtinger j)^[(Pi.single k 1 : Fin n → ℕ) j] g) f =
        if k ∈ L then LeblSCV.Holomorphic.wirtinger k f else f := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons j L ih =>
      intro hnd
      have hnd' := List.nodup_cons.1 hnd
      simp only [List.foldr_cons]
      by_cases hj : j = k
      · subst hj
        rw [ih hnd'.2, if_neg hnd'.1]
        simp
      · rw [ih hnd'.2, Pi.single_eq_of_ne hj]
        simp [Ne.symm hj]
  unfold LeblSCV.Holomorphic.wirtingerIter
  rw [key _ (List.nodup_finRange n)]
  simp

theorem torus_integral_bound {n : ℕ} (a z : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (hz : ∀ j, ‖z j - a j‖ ≤ ρ j / 2) (g : (Fin n → ℂ) → ℂ) (C : ℝ)
    (hC : ∀ θ, ‖g (torusMap a ρ θ)‖ ≤ C) (β : Fin n → ℕ) :
    ‖torusIntegral (fun ζ => g ζ / ∏ j, (ζ j - z j) ^ (β j + 1)) a ρ‖ ≤
      ((2 * Real.pi) ^ n * ∏ j, |ρ j|) * (C / ∏ j, (ρ j / 2) ^ (β j + 1)) := by
  refine norm_torusIntegral_le_of_norm_le_const (fun θ => ?_)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC θ)
  have hden : ∏ j, (ρ j / 2) ^ (β j + 1) ≤ ∏ j, ‖(torusMap a ρ θ j - z j) ^ (β j + 1)‖ := by
    refine Finset.prod_le_prod (fun j _ => by have := hρ j; positivity) (fun j _ => ?_)
    rw [norm_pow]
    refine pow_le_pow_left₀ (by have := hρ j; positivity) ?_ _
    have := torus_sub_norm a z ρ hρ (fun j => lt_of_le_of_lt (hz j) (by linarith [hρ j])) θ j
    linarith [hz j]
  have hpos : 0 < ∏ j, (ρ j / 2) ^ (β j + 1) :=
    Finset.prod_pos (fun j _ => pow_pos (by have := hρ j; positivity) _)
  show ‖g (torusMap a ρ θ) / ∏ j, (torusMap a ρ θ j - z j) ^ (β j + 1)‖ ≤ _
  rw [norm_div, norm_prod]
  exact div_le_div₀ hC0 (hC θ) hpos hden

/-- A closed polydisc around a point of an open set, contained in the set. -/
theorem exists_cpoly_subset {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {p : Fin n → ℂ}
    (hp : p ∈ U) : ∃ ρ : Fin n → ℝ, (∀ k, 0 < ρ k) ∧ cpoly p ρ ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU p hp
  refine ⟨fun _ => ε / 2, fun _ => by linarith, fun z hz => hsub ?_⟩
  rw [mem_ball, dist_pi_lt_iff hε]
  intro j
  rw [dist_eq_norm]
  have := hz j
  simp only at this
  linarith

theorem factorial_single_prod {n : ℕ} (k : Fin n) :
    (∏ j : Fin n, ((Pi.single k 1 : Fin n → ℕ) j).factorial) = 1 := by
  refine Finset.prod_eq_one (fun j _ => ?_)
  by_cases hj : j = k
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

theorem holomorphic_restrict {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (f : (Fin n → ℂ) → ℂ)
    (hcont : ContinuousOn f (cpoly a ρ))
    (hdiff : ∀ w ∈ LeblSCV.Shared.polydisc a ρ, ∀ k, DifferentiableAt ℂ
      (fun ξ : ℂ => f (Function.update w k (w k + ξ))) 0) :
    LeblSCV.Holomorphic.IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ) := by
  refine ⟨?_, hdiff⟩
  obtain ⟨C, hC⟩ := (isCompact_cpoly a ρ).exists_bound_of_continuousOn hcont
  intro p hp
  refine ⟨LeblSCV.Shared.polydisc a ρ, (isOpen_polydisc' a ρ).mem_nhds hp, C, fun w hw => ?_⟩
  exact hC w (polydisc_subset_cpoly a ρ hw.2)

theorem wirtinger_holomorphic {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ℂ} (hf : LeblSCV.Holomorphic.IsHolomorphicOn f U) (k : Fin n) :
    LeblSCV.Holomorphic.IsHolomorphicOn (LeblSCV.Holomorphic.wirtinger k f) U := by
  classical
  have hcontU : ContinuousOn f U := SCVCont.holo_continuousOn hU hf
  let α : Fin n → ℕ := Pi.single k 1
  -- formula on a polydisc around a point
  have hform : ∀ p ∈ U, ∀ ρ : Fin n → ℝ, (∀ j, 0 < ρ j) → cpoly p ρ ⊆ U →
      ∀ z ∈ LeblSCV.Shared.polydisc p ρ, LeblSCV.Holomorphic.wirtinger k f z =
        ((2 * Real.pi * I) ^ n)⁻¹ * torusIntegral (fun ζ => f ζ /
          ∏ j : Fin n, (ζ j - z j) ^ (α j + 1)) p ρ := by
    intro p hp ρ hρ hsub z hz
    have hcont : ContinuousOn f (cpoly p ρ) := hcontU.mono hsub
    have hhol := holomorphic_restrict p ρ f hcont
      (fun w hw j => hf.2 w (hsub (polydisc_subset_cpoly p ρ hw)) j)
    have hcl : ContinuousOn f (closure (LeblSCV.Shared.polydisc p ρ)) := by
      rw [closure_polydisc p ρ hρ]; exact hcont
    have := (LeblSCV.Holomorphic.cauchy_derivative_formula_and_estimates p ρ hρ hcl hhol).1 z hz α
    rw [← wirtingerIter_single k f] at *
    rw [show (Pi.single k 1 : Fin n → ℕ) = α from rfl, this, factorial_single_prod]
    simp
  refine ⟨?_, ?_⟩
  · -- local boundedness
    intro p hp
    obtain ⟨ρ, hρ, hsub⟩ := exists_cpoly_subset hU hp
    obtain ⟨C, hC⟩ := (isCompact_cpoly p ρ).exists_bound_of_continuousOn (hcontU.mono hsub)
    refine ⟨LeblSCV.Shared.polydisc p (fun j => ρ j / 2),
      (isOpen_polydisc' p _).mem_nhds (fun j => by simpa using hρ j),
      ‖((2 * Real.pi * I) ^ n)⁻¹‖ * (((2 * Real.pi) ^ n * ∏ j, |ρ j|) *
        (C / ∏ j : Fin n, (ρ j / 2) ^ (α j + 1))), fun w hw => ?_⟩
    have hw' : w ∈ LeblSCV.Shared.polydisc p ρ := fun j => lt_of_lt_of_le (hw.1 j) (by linarith [hρ j])
    rw [hform p hp ρ hρ hsub w hw', norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact torus_integral_bound p w ρ hρ (fun j => (hw.1 j).le) f C
      (fun θ => hC _ (torusMap_mem_cpoly p ρ (fun j => (hρ j).le) θ)) α
  · -- separate differentiability
    intro z hz j
    obtain ⟨ρ, hρ, hsub⟩ := exists_cpoly_subset hU hz
    have hcont : ContinuousOn f (cpoly z ρ) := hcontU.mono hsub
    have hz' : ∀ i, ‖z i - z i‖ < ρ i := fun i => by simpa using hρ i
    have hd := (torus_hasDerivAt z ρ hρ f hcont z hz' j α).const_mul (((2 * Real.pi * I) ^ n)⁻¹)
    have hcontj : Continuous fun ξ : ℂ => Function.update z j (z j + ξ) :=
      continuous_const.update j (continuous_const.add continuous_id)
    have hmem : ∀ᶠ ξ in 𝓝 (0 : ℂ), Function.update z j (z j + ξ) ∈ LeblSCV.Shared.polydisc z ρ := by
      have := (isOpen_polydisc' z ρ).mem_nhds (show z ∈ LeblSCV.Shared.polydisc z ρ from hz')
      exact hcontj.continuousAt.eventually (by simpa using this)
    refine hd.differentiableAt.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with ξ hξ
    exact hform z hz ρ hρ hsub _ hξ

end SCVDeriv

namespace SCVStrict

theorem hasDerivAt_of_line {G : ℂ → ℂ} {v d : ℂ} (h : HasDerivAt (fun ξ : ℂ => G (v + ξ)) d 0) :
    HasDerivAt G d v := by
  have h' : HasDerivAt (fun ξ : ℂ => G (v + ξ)) d (v - v) := by simpa using h
  have := h'.comp_sub_const v v
  simpa using this

theorem strict_of_partials : ∀ (n : ℕ) (U : Set (Fin n → ℂ)), IsOpen U →
    ∀ (g : (Fin n → ℂ) → ℂ) (d : Fin n → (Fin n → ℂ) → ℂ),
    (∀ y ∈ U, ∀ k, HasDerivAt (fun ξ : ℂ => g (Function.update y k (y k + ξ))) (d k y) 0) →
    (∀ k, ContinuousOn (d k) U) →
    ∀ y ∈ U, HasStrictFDerivAt g
      (∑ k, (d k y) • (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)) y := by
  intro n
  induction n with
  | zero =>
    intro U hU g d hd hdc y hy
    have : g = fun _ => g y := funext fun w => by rw [Subsingleton.elim w y]
    rw [this]
    simpa using hasStrictFDerivAt_const (g y) y
  | succ n ih =>
    intro U hU g d hd hdc y hy
    -- the splitting map and its inverse
    let L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ × (Fin n → ℂ) :=
      (ContinuousLinearMap.proj 0).prod (ContinuousLinearMap.pi fun j : Fin n => ContinuousLinearMap.proj j.succ)
    let C : ℂ × (Fin n → ℂ) → (Fin (n + 1) → ℂ) := fun v => Fin.cons v.1 v.2
    have hC : Continuous C := by
      unfold C
      exact Continuous.finCons continuous_fst continuous_snd
    have hLC : ∀ w, C (L w) = w := fun w => by
      show (Fin.cons (w 0) (fun i => w i.succ) : Fin (n + 1) → ℂ) = w
      exact Fin.cons_self_tail w
    have hcc : ∀ x : ℂ, Continuous fun z : Fin n → ℂ => (Fin.cons x z : Fin (n + 1) → ℂ) :=
      fun x => Continuous.finCons continuous_const continuous_id
    let f : ℂ → (Fin n → ℂ) → ℂ := fun x z => g (Fin.cons x z)
    let f₁ : ℂ → (Fin n → ℂ) → ℂ →L[ℂ] ℂ := fun x z =>
      (d 0 (Fin.cons x z)) • (ContinuousLinearMap.id ℂ ℂ)
    let f₂ : ℂ → (Fin n → ℂ) → (Fin n → ℂ) →L[ℂ] ℂ := fun x z =>
      ∑ j : Fin n, (d j.succ (Fin.cons x z)) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)
    set u : ℂ × (Fin n → ℂ) := L y with hu
    have hUC : IsOpen (C ⁻¹' U) := hU.preimage hC
    have huU : u ∈ C ⁻¹' U := by
      show C (L y) ∈ U
      rw [hLC]; exact hy
    have hev : ∀ᶠ v in 𝓝 u, v ∈ C ⁻¹' U := hUC.mem_nhds huU
    have df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (↿f₁ v) v.1 := by
      filter_upwards [hev] with v hv
      have h1 := hd (Fin.cons v.1 v.2) hv 0
      have e : (fun ξ : ℂ => g (Function.update (Fin.cons v.1 v.2 : Fin (n + 1) → ℂ) 0
          ((Fin.cons v.1 v.2 : Fin (n + 1) → ℂ) 0 + ξ))) = fun ξ => f (v.1 + ξ) v.2 := by
        funext ξ; simp [f, Fin.update_cons_zero]
      rw [e] at h1
      have h2 := hasDerivAt_of_line (G := fun x => f x v.2) h1
      have h3 := h2.hasFDerivAt
      have e2 : (↿f₁ v) = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (d 0 (Fin.cons v.1 v.2)) := by
        show f₁ v.1 v.2 = _
        ext; simp [f₁]
      rw [e2]
      exact h3
    have df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (↿f₂ v) v.2 := by
      filter_upwards [hev] with v hv
      have hUx : IsOpen {z : Fin n → ℂ | (Fin.cons v.1 z : Fin (n + 1) → ℂ) ∈ U} :=
        hU.preimage (hcc v.1)
      have := ih {z : Fin n → ℂ | (Fin.cons v.1 z : Fin (n + 1) → ℂ) ∈ U} hUx (f v.1)
        (fun j z => d j.succ (Fin.cons v.1 z)) (fun z hz j => by
          have h1 := hd (Fin.cons v.1 z) hz j.succ
          have e : (fun ξ : ℂ => g (Function.update (Fin.cons v.1 z : Fin (n + 1) → ℂ) j.succ
              ((Fin.cons v.1 z : Fin (n + 1) → ℂ) j.succ + ξ))) =
              fun ξ => f v.1 (Function.update z j (z j + ξ)) := by
            funext ξ; simp [f, Fin.cons_update]
          rw [e] at h1
          simpa using h1)
        (fun j => (hdc j.succ).comp (hcc v.1).continuousOn (fun z hz => hz)) v.2 hv
      exact this.hasFDerivAt
    have hCu : ContinuousAt C u := hC.continuousAt
    have hdcA : ∀ k, ContinuousAt (d k) (C u) := fun k => (hdc k).continuousAt (hU.mem_nhds huU)
    have hcf₁ : ContinuousAt ↿f₁ u :=
      ((hdcA 0).comp hCu).smul continuousAt_const
    have hcf₂ : ContinuousAt ↿f₂ u := by
      have hj : ∀ j : Fin n, ContinuousAt (fun v : ℂ × (Fin n → ℂ) =>
          (d j.succ (C v)) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)) u :=
        fun j => ((hdcA j.succ).comp hCu).smul continuousAt_const
      show Tendsto (fun v : ℂ × (Fin n → ℂ) => ∑ j : Fin n, (d j.succ (C v)) •
          (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)) (𝓝 u)
        (𝓝 (∑ j : Fin n, (d j.succ (C u)) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)))
      exact tendsto_finsetSum Finset.univ (fun j _ => hj j)
    have hstrict := hasStrictFDerivAt_uncurry_coprod df₁ df₂ hcf₁ hcf₂
    have hcomp := hstrict.comp y L.hasStrictFDerivAt
    have hgeq : (fun x => ↿f (L x)) = g := by
      funext w
      show g (C (L w)) = g w
      rw [hLC]
    rw [hgeq] at hcomp
    refine hcomp.congr_fderiv ?_
    have hCy : C u = y := hLC y
    have h1 : (↿f₁ u) = (d 0 y) • (ContinuousLinearMap.id ℂ ℂ) := by
      show f₁ u.1 u.2 = _
      simp only [f₁]
      have : (Fin.cons u.1 u.2 : Fin (n + 1) → ℂ) = y := hCy
      rw [this]
    have h2 : (↿f₂ u) = ∑ j : Fin n, (d j.succ y) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ) := by
      show f₂ u.1 u.2 = _
      simp only [f₂]
      have : (Fin.cons u.1 u.2 : Fin (n + 1) → ℂ) = y := hCy
      rw [this]
    rw [h1, h2]
    ext w
    simp [L, Fin.sum_univ_succ, ContinuousLinearMap.sum_apply]

end SCVStrict


open SCVDeriv SCVStrict in
theorem frechet_of_holomorphic {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ℂ} (hf : LeblSCV.Holomorphic.IsHolomorphicOn f U) :
    ∀ y ∈ U, HasStrictFDerivAt f
      (∑ k : Fin n, (LeblSCV.Holomorphic.wirtinger k f y) •
        (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)) y := by
  classical
  refine strict_of_partials n U hU f (fun k => LeblSCV.Holomorphic.wirtinger k f) ?_ ?_
  · intro y hy k
    have hd := (hf.2 y hy k).hasDerivAt
    have := wirtinger_eq_of_hasDerivAt f y k _ hd
    rw [this]
    exact hd
  · intro k
    exact SCVCont.holo_continuousOn hU (wirtinger_holomorphic hU hf k)

open SCVDeriv SCVStrict in
theorem contDiffOn_of_holomorphic {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) :
    ∀ (m : ℕ) (f : (Fin n → ℂ) → ℂ), LeblSCV.Holomorphic.IsHolomorphicOn f U →
      ContDiffOn ℂ m f U := by
  intro m
  induction m with
  | zero =>
    intro f hf
    exact contDiffOn_zero.2 (SCVCont.holo_continuousOn hU hf)
  | succ m ih =>
    intro f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨?_, by simp, ?_⟩
    · intro y hy
      exact ((frechet_of_holomorphic hU hf y hy).hasFDerivAt.differentiableAt).differentiableWithinAt
    · have hEq : Set.EqOn (fun y => fderiv ℂ f y)
          (fun y => ∑ k : Fin n, (LeblSCV.Holomorphic.wirtinger k f y) •
            (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)) U := by
        intro y hy
        exact (frechet_of_holomorphic hU hf y hy).hasFDerivAt.fderiv
      refine ContDiffOn.congr ?_ hEq
      refine ContDiffOn.sum (fun k _ => ?_)
      exact (ih _ (wirtinger_holomorphic hU hf k)).smul contDiffOn_const

open scoped ContDiff in
theorem solution {n : ℕ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) {f : (Fin n → ℂ) → ℂ} (hf : LeblSCV.Holomorphic.IsHolomorphicOn f U) :
    ContDiffOn ℝ ∞ f U ∧ ∀ k : Fin n, LeblSCV.Holomorphic.IsHolomorphicOn
      (LeblSCV.Holomorphic.wirtinger k f) U := by
  refine ⟨?_, fun k => SCVDeriv.wirtinger_holomorphic hU hf k⟩
  have : ContDiffOn ℂ ∞ f U := contDiffOn_infty.2 (fun m => contDiffOn_of_holomorphic hU m f hf)
  exact this.restrict_scalars ℝ
