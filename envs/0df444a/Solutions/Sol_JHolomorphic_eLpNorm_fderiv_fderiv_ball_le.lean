-- Prove2me | solution 1 for JHolomorphic.eLpNorm_fderiv_fderiv_ball_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:30:01.118729+00:00
-- url     : https://prove2.me/submissions/9da44e67-bd8c-4d2c-8757-2cb842062093

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Theorems.Thm_JHolomorphic_norm_le_norm_apply_one_add_norm_apply_I
import Theorems.Thm_JHolomorphic_eLpNorm_fderiv_smul_fderiv_apply_le



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 1000000 in
theorem eLpNorm_fderiv_fderiv_ball_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (CF CK : ℝ) (hCF : 0 ≤ CF) (hCK : 0 ≤ CK)
    (J₀ : E →L[ℝ] E)
    (hF : ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CF *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume)
    (hK : ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (CK * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume))
    (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u U)
    (Jc : E → E →L[ℝ] E)
    (heq : ∀ e : ℂ, ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (hβ1 : ∀ z ∈ ball z₀ (r / 2), β z = 1) (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (ball z₀ (r / 2))) ≤
      ENNReal.ofReal (4 * (CF * (Bβ * (1 + A + η) * M))) := by
  have hdir : ∀ e : ℂ, ‖e‖ ≤ 1 → _ := fun e he =>
    eLpNorm_fderiv_smul_fderiv_apply_le p hp CF CK hCF hCK J₀ hF hK U hU u hu Jc e he (heq e) z₀ r hr
      hball β hβ hβs Bβ hBβ η Λ A M hη0 hΛ0 hM0 hη hΛ hA hM hs1 hs2
  have h1 := hdir 1 (by simp)
  have hI := hdir Complex.I (by simp)
  have hBβ0 : 0 ≤ Bβ := (norm_nonneg _).trans (hBβ 0)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  set q := ENNReal.ofReal p with hqdef
  set μ := volume.restrict (ball z₀ (r / 2)) with hμ
  set k : ℝ := CF * (Bβ * (1 + A + η) * M) with hk
  have hk0 : 0 ≤ k := by positivity
  set G : ℂ → ℂ → ℂ → ℝ := fun e a z => ‖fderiv ℝ (fun y => β y • fderiv ℝ u y e) z a‖ with hG
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU
      (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))
  have hloc : ∀ e : ℂ, ∀ z ∈ ball z₀ (r / 2), ∀ a : ℂ,
      fderiv ℝ (fun y => β y • fderiv ℝ u y e) z a = fderiv ℝ (fderiv ℝ u) z a e := by
    intro e z hz a
    have hev : (fun y => β y • fderiv ℝ u y e) =ᶠ[𝓝 z] (fun y => fderiv ℝ u y e) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      rw [hβ1 y hy, one_smul]
    rw [hev.fderiv_eq]
    have hzU : z ∈ U := hball (ball_subset_ball (by linarith) hz)
    have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
      (hDu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hzU)
    rw [fderiv_clm_apply hd (differentiableAt_const e)]
    simp
  have hpt : ∀ z ∈ ball z₀ (r / 2), ‖fderiv ℝ (fderiv ℝ u) z‖ ≤
      G 1 1 z + G 1 Complex.I z + G Complex.I 1 z + G Complex.I Complex.I z := by
    intro z hz
    have a1 := norm_le_norm_apply_one_add_norm_apply_I (fderiv ℝ (fderiv ℝ u) z)
    have a2 := norm_le_norm_apply_one_add_norm_apply_I (fderiv ℝ (fderiv ℝ u) z 1)
    have a3 := norm_le_norm_apply_one_add_norm_apply_I (fderiv ℝ (fderiv ℝ u) z Complex.I)
    simp only [hG, hloc _ z hz]
    linarith
  have hm : ∀ e a : ℂ, AEStronglyMeasurable (G e a) μ := by
    intro e a
    borelize E
    exact (measurable_fderiv_apply_const ℝ (fun y => β y • fderiv ℝ u y e) a).norm.aestronglyMeasurable
  have hle : ∀ e a : ℂ, eLpNorm (G e a) q μ ≤
      eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z a) q volume := by
    intro e a
    show eLpNorm (fun z => ‖fderiv ℝ (fun y => β y • fderiv ℝ u y e) z a‖) q μ ≤ _
    exact (eLpNorm_norm (f := fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z a)).le.trans
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  calc eLpNorm (fderiv ℝ (fderiv ℝ u)) q μ
      ≤ eLpNorm (fun z => G 1 1 z + G 1 Complex.I z + G Complex.I 1 z +
          G Complex.I Complex.I z) q μ := by
        refine eLpNorm_mono_ae_real (F := ℂ →L[ℝ] ℂ →L[ℝ] E) (f := fderiv ℝ (fderiv ℝ u)) ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hpt z hz
    _ ≤ eLpNorm (G 1 1) q μ + eLpNorm (G 1 Complex.I) q μ + eLpNorm (G Complex.I 1) q μ +
          eLpNorm (G Complex.I Complex.I) q μ := by
        refine (eLpNorm_add_le (((hm _ _).add (hm _ _)).add (hm _ _)) (hm _ _) hq1).trans ?_
        gcongr
        refine (eLpNorm_add_le ((hm _ _).add (hm _ _)) (hm _ _) hq1).trans ?_
        gcongr
        exact eLpNorm_add_le (hm _ _) (hm _ _) hq1
    _ ≤ ENNReal.ofReal (2 * k) + ENNReal.ofReal (2 * k) := by
        have e1 := hle 1 1
        have e2 := hle 1 Complex.I
        have e3 := hle Complex.I 1
        have e4 := hle Complex.I Complex.I
        calc eLpNorm (G 1 1) q μ + eLpNorm (G 1 Complex.I) q μ + eLpNorm (G Complex.I 1) q μ +
              eLpNorm (G Complex.I Complex.I) q μ
            = (eLpNorm (G 1 1) q μ + eLpNorm (G 1 Complex.I) q μ) +
                (eLpNorm (G Complex.I 1) q μ + eLpNorm (G Complex.I Complex.I) q μ) := by ring
          _ ≤ _ := add_le_add ((add_le_add e1 e2).trans h1) ((add_le_add e3 e4).trans hI)
    _ = ENNReal.ofReal (4 * k) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (CF CK : ℝ) (hCF : 0 ≤ CF) (hCK : 0 ≤ CK)
    (J₀ : E →L[ℝ] E)
    (hF : ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CF *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume)
    (hK : ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (CK * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume))
    (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u U)
    (Jc : E → E →L[ℝ] E)
    (heq : ∀ e : ℂ, ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (hβ1 : ∀ z ∈ ball z₀ (r / 2), β z = 1) (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict (ball z₀ (r / 2))) ≤
      ENNReal.ofReal (4 * (CF * (Bβ * (1 + A + η) * M))) :=
  eLpNorm_fderiv_fderiv_ball_le_aux p hp CF CK hCF hCK J₀ hF hK U hU u hu Jc heq z₀ r hr hball β hβ hβs hβ1 Bβ hBβ η Λ A M hη0 hΛ0 hM0 hη hΛ hA hM hs1 hs2
