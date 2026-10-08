-- Prove2me | solution 1 for ImplicitCalculus.smooth_fixed_point_of_uniform_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T22:03:05.506243+00:00
-- url     : https://prove2.me/submissions/1eb1b0f9-3b2a-4881-8884-c3742d2a4276

import Theorems.Thm_ImplicitCalculus_contDiffAt_continuous_solution
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology ContDiff NNReal
set_option autoImplicit false

theorem solution {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Φ : P × V → V) (hΦ : ContDiff ℝ ∞ Φ)
    (K : ℝ≥0) (hK : K < 1)
    (hLip : ∀ p, LipschitzWith K (fun z => Φ (p,z)))
    (r : P → V) (hr : ∀ p, Φ (p,r p) = r p) : ContDiff ℝ ∞ r := by
  have hKr : (K : ℝ) < 1 := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < 1 - K := sub_pos.mpr hKr
  have hrc : Continuous r := by
    apply continuous_iff_continuousAt.mpr
    intro p₀
    have hbound : ∀ p, dist (r p) (r p₀) ≤
        dist (Φ (p,r p₀)) (Φ (p₀,r p₀)) / (1 - K) := by
      intro p
      have htri := dist_triangle (Φ (p,r p)) (Φ (p,r p₀)) (Φ (p₀,r p₀))
      have hl := (hLip p).dist_le_mul (r p) (r p₀)
      rw [hr p, hr p₀] at htri
      rw [hr p] at hl
      rw [hr p₀]
      apply (le_div_iff₀ hKpos).mpr
      nlinarith
    have he : Tendsto (fun p => dist (Φ (p,r p₀)) (Φ (p₀,r p₀)) / (1 - K))
        (𝓝 p₀) (𝓝 (0 : ℝ)) := by
      have hp : Tendsto (fun p => Φ (p,r p₀)) (𝓝 p₀) (𝓝 (Φ (p₀,r p₀))) :=
        (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto
      have hh : Tendsto (fun p => dist (Φ (p,r p₀)) (Φ (p₀,r p₀))) (𝓝 p₀) (𝓝 (0 : ℝ)) := by
        simpa using hp.dist (tendsto_const_nhds : Tendsto (fun _ : P => Φ (p₀,r p₀))
          (𝓝 p₀) (𝓝 (Φ (p₀,r p₀))))
      simpa using hh.div_const (1 - (K : ℝ))
    exact tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun _ => dist_nonneg) hbound he)
  apply contDiff_iff_contDiffAt.mpr
  intro p
  let D : V →L[ℝ] V := (fderiv ℝ Φ (p,r p)).comp (ContinuousLinearMap.inr ℝ P V)
  have hpd : HasFDerivAt (fun z => Φ (p,z)) D (r p) := by
    exact (hΦ.differentiable (by simp) (p,r p)).hasFDerivAt.comp (r p)
      (hasFDerivAt_prodMk_right p (r p))
  have hnorm : ‖D‖ < 1 := lt_of_le_of_lt (hpd.le_of_lipschitz (hLip p)) (by exact_mod_cast hK)
  let u : (V →L[ℝ] V)ˣ := Units.oneSub D hnorm
  have hi : (ContinuousLinearMap.id ℝ V - D).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
    change (u : V →L[ℝ] V) = ContinuousLinearMap.id ℝ V - D
    exact Units.val_oneSub D hnorm
  let G : P × V → V := fun q => q.2 - Φ q
  have hG : ContDiff ℝ ∞ G := contDiff_snd.sub hΦ
  have hD : (fderiv ℝ G (p,r p)).comp (ContinuousLinearMap.inr ℝ P V) =
      ContinuousLinearMap.id ℝ V - D := by
    have hg := (hasFDerivAt_snd (p := (p,r p))).sub
      (hΦ.differentiable (by simp) (p,r p)).hasFDerivAt
    change HasFDerivAt G (ContinuousLinearMap.snd ℝ P V - fderiv ℝ Φ (p,r p)) (p,r p) at hg
    rw [hg.fderiv]
    ext z
    simp [D]
  apply ImplicitCalculus.contDiffAt_continuous_solution ∞ (by simp) G r p
    hG.contDiffAt (hrc.continuousAt) (hD ▸ hi)
  apply Filter.Eventually.of_forall
  intro q
  simp [G, hr]
