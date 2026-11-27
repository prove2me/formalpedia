-- Prove2me | solution 1 for MasulloRH.common_rational_gaussian_fit_on_every_finite_frequency_band
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:30:35.535849+00:00
-- url     : https://prove2.me/submissions/d5109a50-cc14-450e-b9d9-74ca8cf9d2ea

import Definitions.Def_MasulloRH_FiniteMellinBands
import Theorems.Thm_MasulloRH_simultaneous_rational_theta_polynomials_on_two_finite_segments
import Theorems.Thm_MasulloRH_arbitrary_precision_gaussian_approximation_at_each_single_slope
import Theorems.Thm_MasulloRH_window_energy_sandwiched_by_endpoint_mellin_errors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.RationalThetaGrid
open MasulloRH.VerticalThetaApproximation MasulloRH.FiniteMellinBands

private theorem cheapAt (c τ : ℝ) (hc : 0<c) (hc' : c<1) (hτ : 0<τ) :
    ∃ (m : ℕ) (a : Fin m → ℚ×ℚ) (y : Fin m → ℚ), mass c a y < τ := by
  have hp : 0 < 2*Real.pi := by positivity
  obtain ⟨_,m,a,y,δ,hδ,_,_,h⟩ :=
    arbitrary_precision_gaussian_approximation_at_each_single_slope c (τ/(2*Real.pi)) hc hc'
      (div_pos hτ hp)
  have h0 := h c 0 le_rfl (by simpa using hδ.le)
  have h0' := (lt_div_iff₀' hp).mp h0
  refine ⟨m,a,y,?_⟩
  rw [((window_energy_sandwiched_by_endpoint_mellin_errors a y).1 c hc hc').2]
  exact h0'

private noncomputable def weight (c : ℝ) : ℝ := ∫ t : ℝ, ‖thetaMultiplier (pointAt c t)‖^2

private lemma localTransfer (c T δ : ℝ) (hc : 0<c) (hc' : c<1)
    {l m : ℕ} (a : Fin l → ℚ×ℚ) (x : Fin l → ℚ) (d : Fin m → ℚ×ℚ) (v : Fin m → ℚ)
    (h : ∀ t : ℝ, |t|≤T → ‖poly d v (pointAt c t)-poly a x (pointAt c t)‖ < δ) :
    ∫ t in Icc (-T) T, ‖VerticalThetaApproximation.spectrum c d v t‖^2 ≤
      2*mass c a x + 2*δ^2*weight c := by
  let F := VerticalThetaApproximation.spectrum c d v
  let G := VerticalThetaApproximation.spectrum c a x
  let H := fun t => thetaMultiplier (pointAt c t)
  have hiF := ((window_energy_sandwiched_by_endpoint_mellin_errors d v).1 c hc hc').1
  have hiG := ((window_energy_sandwiched_by_endpoint_mellin_errors a x).1 c hc hc').1
  have hH := (arbitrary_precision_gaussian_approximation_at_each_single_slope c 1 hc hc' one_pos).1
  have hiH := (memLp_two_iff_integrable_sq_norm hH.1).mp hH
  let f := fun t => 2*‖G t‖^2 + (2*δ^2)*‖H t‖^2
  have hi : Integrable f := (hiG.const_mul 2).add (hiH.const_mul (2*δ^2))
  have bound (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖F t‖^2 ≤ f t := by
    have eq : F t = G t - H t*(poly d v (pointAt c t)-poly a x (pointAt c t)) := by
      dsimp [F,G,H,VerticalThetaApproximation.spectrum,poly];ring
    have hn : ‖F t‖ ≤ ‖G t‖ + ‖H t‖*δ := by
      rw [eq]
      apply (norm_sub_le _ _).trans
      rw [norm_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (h t (abs_le.mpr ht)).le (norm_nonneg (H t)))
    have hs := mul_self_le_mul_self (norm_nonneg _) hn
    dsimp [f]
    nlinarith only [hs,sq_nonneg (‖G t‖-‖H t‖*δ)]
  have h1 := setIntegral_mono_on hiF.integrableOn hi.integrableOn measurableSet_Icc bound
  have h2 := setIntegral_le_integral (s:=Icc (-T) T) hi (Filter.Eventually.of_forall (fun t => by dsimp [f]; positivity))
  apply (h1.trans h2).trans_eq
  change ∫ t : ℝ, 2*‖G t‖^2 + (2*δ^2)*‖H t‖^2 = _
  rw [integral_add (hiG.const_mul _) (hiH.const_mul _), integral_const_mul, integral_const_mul]
  rfl

theorem solution (L U T ε : ℝ) (hL : 0<L) (hLU : L<U) (hU : U<1) (hε : 0<ε) :
    ∃ (m : ℕ) (d : Fin m → ℚ×ℚ) (v : Fin m → ℚ), band L U T d v < ε := by
  have W0 (c : ℝ) : 0≤weight c := integral_nonneg fun _ => sq_nonneg _
  let W := weight L+weight U
  have hW : 0≤W := add_nonneg (W0 _) (W0 _)
  let δ := Real.sqrt (ε/(8*(W+1)))
  have hδ : 0<δ := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨l,a,x,ha⟩ := cheapAt L (ε/8) hL (hLU.trans hU) (by positivity)
  obtain ⟨r,b,y,hb⟩ := cheapAt U (ε/8) (hL.trans hLU) hU (by positivity)
  obtain ⟨m,d,v,h⟩ := simultaneous_rational_theta_polynomials_on_two_finite_segments L U T δ hLU hδ a x b y
  have left := localTransfer L T δ hL (hLU.trans hU) a x d v (fun t ht => (h t ht).1)
  have right := localTransfer U T δ (hL.trans hLU) hU b y d v (fun t ht => (h t ht).2)
  have dl := ((window_energy_sandwiched_by_endpoint_mellin_errors d v).1 L hL (hLU.trans hU)).1
  have du := ((window_energy_sandwiched_by_endpoint_mellin_errors d v).1 U (hL.trans hLU) hU).1
  have calcδ : δ^2*(8*(W+1))=ε := by
    rw [show δ^2 = _ from Real.sq_sqrt (show 0≤ε/(8*(W+1)) by positivity)]
    exact div_mul_cancel₀ _ (by positivity)
  refine ⟨m,d,v,?_⟩
  unfold band errorDensity
  rw [integral_add dl.integrableOn du.integrableOn]
  dsimp [W] at calcδ
  nlinarith only [ha,hb,left,right,calcδ,sq_nonneg δ,hε]
