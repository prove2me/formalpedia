-- Prove2me | solution 1 for JHolomorphic.eLpNorm_fderiv_smul_fderiv_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:26:36.041919+00:00
-- url     : https://prove2.me/submissions/81111747-e041-4598-a0ac-f36277e20068

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

set_option maxHeartbeats 1000000 in
theorem eLpNorm_fderiv_smul_fderiv_apply_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
    (Jc : E → E →L[ℝ] E) (e : ℂ) (he : ‖e‖ ≤ 1)
    (heq : ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z 1) (ENNReal.ofReal p) volume +
        eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z Complex.I)
          (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * (CF * (Bβ * (1 + A + η) * M))) := by
  have hp0 : 0 < p := by linarith
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hBβ0 : 0 ≤ Bβ := (norm_nonneg _).trans (hBβ 0)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  set q := ENNReal.ofReal p with hqdef
  set ξ : ℂ → E := fun y => fderiv ℝ u y e with hξdef
  set g : ℂ → E := fun y => β y • ξ y with hgdef
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU
      (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))
  have hξ : ContDiffOn ℝ ∞ ξ U := hDu.clm_apply contDiffOn_const
  have hgU : tsupport g ⊆ ball z₀ r := (tsupport_smul_subset_left _ _).trans hβs
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact ((hβ.contDiffAt.smul (hξ.contDiffAt (hU.mem_nhds hy))).of_le
        (by exact_mod_cast le_top))
    · have hyg : y ∉ tsupport g := fun h => hy (hball (hgU h))
      rw [notMem_tsupport_iff_eventuallyEq] at hyg
      exact contDiffAt_const.congr_of_eventuallyEq hyg
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z₀ r)
      ((subset_tsupport g).trans (hgU.trans ball_subset_closedBall))
  -- the derivative of `g` inside `U`
  have hdg : ∀ y ∈ U, ∀ a : ℂ, fderiv ℝ g y a = β y • fderiv ℝ ξ y a + fderiv ℝ β y a • ξ y := by
    intro y hy a
    have hξd : DifferentiableAt ℝ ξ y :=
      (hξ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
    have hβd : DifferentiableAt ℝ β y := hβ.differentiable (by simp) y
    rw [show fderiv ℝ g y = β y • fderiv ℝ ξ y + (fderiv ℝ β y).smulRight (ξ y) from
      (hβd.hasFDerivAt.smul hξd.hasFDerivAt).fderiv]
    simp
  -- vanishing outside the disc
  have hdg0 : ∀ y ∉ ball z₀ r, fderiv ℝ g y = 0 := by
    intro y hy
    have : y ∉ tsupport (fderiv ℝ g) := fun h => hy (hgU (tsupport_fderiv_subset ℝ h))
    exact image_eq_zero_of_notMem_tsupport this
  -- finiteness of `X`
  set Xs := eLpNorm (fun z => fderiv ℝ g z 1) q volume with hXs
  set Xt := eLpNorm (fun z => fderiv ℝ g z Complex.I) q volume with hXt
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hXs_top : Xs ≠ ⊤ := ((hDg.clm_apply continuous_const).memLp_of_hasCompactSupport
    (hgc.fderiv_apply (𝕜 := ℝ) 1)).eLpNorm_lt_top.ne
  have hXt_top : Xt ≠ ⊤ := ((hDg.clm_apply continuous_const).memLp_of_hasCompactSupport
    (hgc.fderiv_apply (𝕜 := ℝ) Complex.I)).eLpNorm_lt_top.ne
  set Xr : ℝ := (Xs + Xt).toReal with hXr
  have hX : Xs + Xt = ENNReal.ofReal Xr := (ENNReal.ofReal_toReal (by finiteness)).symm
  have hXr0 : 0 ≤ Xr := ENNReal.toReal_nonneg
  -- the sup bound
  set G : ℝ := CK * r ^ (1 - 2 / p) * Xr with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hgG : ∀ z, ‖g z‖ ≤ G := by
    intro z
    have h := hK z₀ r hr g hg hgU z
    rw [hX, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  -- pointwise bound
  set c : ℝ := Bβ * (1 + A + η) + Λ * G with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ z ∈ ball z₀ r, ‖fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)‖ ≤
      c * ‖fderiv ℝ u z‖ + η * ‖fderiv ℝ g z Complex.I‖ := by
    intro z hz
    have hzU := hball hz
    have hs := hdg z hzU 1
    have ht := hdg z hzU Complex.I
    have hE := heq z hzU
    set bs := fderiv ℝ β z 1
    set bt := fderiv ℝ β z Complex.I
    set ξs := fderiv ℝ ξ z 1
    set ξt := fderiv ℝ ξ z Complex.I
    set ut := fderiv ℝ u z Complex.I
    set D := fderiv ℝ Jc (u z)
    have hξs : ξs = -(Jc (u z) ξt + D (ξ z) ut) := eq_neg_of_add_eq_zero_left hE
    have hid : fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I) =
        bs • ξ z + bt • J₀ (ξ z) + (J₀ - Jc (u z)) (fderiv ℝ g z Complex.I) -
          bt • (J₀ - Jc (u z)) (ξ z) - D (g z) ut := by
      rw [hs, ht, hξs]
      simp only [hgdef, map_add, map_smul, map_neg, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      module
    have hbs : |bs| ≤ Bβ := by
      have := (fderiv ℝ β z).le_opNorm 1
      rw [norm_one, mul_one, Real.norm_eq_abs] at this
      exact this.trans (hBβ z)
    have hbt : |bt| ≤ Bβ := by
      have := (fderiv ℝ β z).le_opNorm Complex.I
      rw [Complex.norm_I, mul_one, Real.norm_eq_abs] at this
      exact this.trans (hBβ z)
    have hξn : ‖ξ z‖ ≤ ‖fderiv ℝ u z‖ := by
      have := (fderiv ℝ u z).le_opNorm e
      nlinarith [norm_nonneg (fderiv ℝ u z)]
    have hut : ‖ut‖ ≤ ‖fderiv ℝ u z‖ := by
      have := (fderiv ℝ u z).le_opNorm Complex.I
      rwa [Complex.norm_I, mul_one] at this
    have hηz := hη z hz
    have hΛz := hΛ z hz
    have hJ₀ξ : ‖J₀ (ξ z)‖ ≤ A * ‖ξ z‖ :=
      (J₀.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    have hdiff1 : ‖(J₀ - Jc (u z)) (fderiv ℝ g z Complex.I)‖ ≤
        η * ‖fderiv ℝ g z Complex.I‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hηz (norm_nonneg _))
    have hdiff2 : ‖(J₀ - Jc (u z)) (ξ z)‖ ≤ η * ‖ξ z‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hηz (norm_nonneg _))
    have hDn : ‖D (g z) ut‖ ≤ Λ * G * ‖fderiv ℝ u z‖ := by
      refine (D.le_opNorm₂ _ _).trans ?_
      have := hgG z
      calc ‖D‖ * ‖g z‖ * ‖ut‖ ≤ Λ * G * ‖fderiv ℝ u z‖ := by gcongr
        _ = _ := rfl
    rw [hid]
    have t1 : ‖bs • ξ z‖ ≤ Bβ * ‖ξ z‖ := by
      rw [norm_smul, Real.norm_eq_abs]; gcongr
    have t2 : ‖bt • J₀ (ξ z)‖ ≤ Bβ * (A * ‖ξ z‖) := by
      rw [norm_smul, Real.norm_eq_abs]; gcongr
    have t4 : ‖bt • (J₀ - Jc (u z)) (ξ z)‖ ≤ Bβ * (η * ‖ξ z‖) := by
      rw [norm_smul, Real.norm_eq_abs]; gcongr
    have tri : ‖bs • ξ z + bt • J₀ (ξ z) + (J₀ - Jc (u z)) (fderiv ℝ g z Complex.I) -
          bt • (J₀ - Jc (u z)) (ξ z) - D (g z) ut‖ ≤
        ‖bs • ξ z‖ + ‖bt • J₀ (ξ z)‖ + ‖(J₀ - Jc (u z)) (fderiv ℝ g z Complex.I)‖ +
          ‖bt • (J₀ - Jc (u z)) (ξ z)‖ + ‖D (g z) ut‖ := by
      have h1 := norm_sub_le (bs • ξ z + bt • J₀ (ξ z) +
        (J₀ - Jc (u z)) (fderiv ℝ g z Complex.I) - bt • (J₀ - Jc (u z)) (ξ z)) (D (g z) ut)
      have h2 := norm_sub_le (bs • ξ z + bt • J₀ (ξ z) +
        (J₀ - Jc (u z)) (fderiv ℝ g z Complex.I)) (bt • (J₀ - Jc (u z)) (ξ z))
      have h3 := norm_add_le (bs • ξ z + bt • J₀ (ξ z))
        ((J₀ - Jc (u z)) (fderiv ℝ g z Complex.I))
      have h4 := norm_add_le (bs • ξ z) (bt • J₀ (ξ z))
      linarith
    have hξ1 : Bβ * (1 + A + η) * ‖ξ z‖ ≤ Bβ * (1 + A + η) * ‖fderiv ℝ u z‖ := by gcongr
    rw [hcdef]
    nlinarith
  -- the right-hand side is supported in the disc
  set Φ : ℂ → E := fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I) with hΦ
  have hΦsupp : Function.support Φ ⊆ ball z₀ r := by
    intro z hz
    by_contra h
    apply hz
    simp only [hΦ, hdg0 z h, ContinuousLinearMap.zero_apply, map_zero, add_zero]
  have hmeas1 : AEStronglyMeasurable (fun z => c * ‖fderiv ℝ u z‖)
      (volume.restrict (ball z₀ r)) :=
    ((measurable_fderiv ℝ u).norm.const_mul c).aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun z => η * ‖fderiv ℝ g z Complex.I‖)
      (volume.restrict (ball z₀ r)) :=
    (continuous_const.mul (hDg.clm_apply continuous_const).norm).aestronglyMeasurable
  have hY : eLpNorm Φ q volume ≤ ENNReal.ofReal c * ENNReal.ofReal M + ENNReal.ofReal η * Xt := by
    rw [← eLpNorm_restrict_eq_of_support_subset hΦsupp]
    calc eLpNorm Φ q (volume.restrict (ball z₀ r))
        ≤ eLpNorm (fun z => c * ‖fderiv ℝ u z‖ + η * ‖fderiv ℝ g z Complex.I‖) q
            (volume.restrict (ball z₀ r)) := by
          refine eLpNorm_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hpt z hz
      _ ≤ eLpNorm (fun z => c * ‖fderiv ℝ u z‖) q (volume.restrict (ball z₀ r)) +
            eLpNorm (fun z => η * ‖fderiv ℝ g z Complex.I‖) q (volume.restrict (ball z₀ r)) :=
          eLpNorm_add_le hmeas1 hmeas2 hq1
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal M + ENNReal.ofReal η * Xt := by
          gcongr ?_ + ?_
          · rw [show (fun z => c * ‖fderiv ℝ u z‖) = c • fun z => ‖fderiv ℝ u z‖ from rfl,
              eLpNorm_const_smul, eLpNorm_norm (fderiv ℝ u), Real.enorm_eq_ofReal hc0]
            gcongr
          · rw [show (fun z => η * ‖fderiv ℝ g z Complex.I‖) =
                η • fun z => ‖fderiv ℝ g z Complex.I‖ from rfl,
              eLpNorm_const_smul, eLpNorm_norm (fun z => fderiv ℝ g z Complex.I),
              Real.enorm_eq_ofReal hη0]
            gcongr
            exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hXle : Xs + Xt ≤
      ENNReal.ofReal CF * (ENNReal.ofReal c * ENNReal.ofReal M + ENNReal.ofReal η * Xt) :=
    (hF g hg hgc).trans (by gcongr)
  have hXt_le : Xt ≤ ENNReal.ofReal Xr := hX ▸ le_add_self
  have key : ENNReal.ofReal Xr ≤ ENNReal.ofReal (CF * (c * M + η * Xr)) := by
    have hR : ENNReal.ofReal (CF * (c * M + η * Xr)) = ENNReal.ofReal CF *
        (ENNReal.ofReal c * ENNReal.ofReal M + ENNReal.ofReal η * ENNReal.ofReal Xr) := by
      have h1 : 0 ≤ c * M := by positivity
      have h2 : 0 ≤ η * Xr := by positivity
      rw [ENNReal.ofReal_mul hCF, ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_mul hη0]
    rw [hR, ← hX]
    exact hXle.trans (by gcongr <;> exact le_add_self)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  have e1 : CF * (c * M + η * Xr) = CF * (Bβ * (1 + A + η) * M) +
      (CF * Λ * (CK * r ^ (1 - 2 / p)) * M) * Xr + (CF * η) * Xr := by
    rw [hcdef, hGdef]; ring
  have h1 : (CF * Λ * (CK * r ^ (1 - 2 / p)) * M) * Xr ≤ 1 / 4 * Xr :=
    mul_le_mul_of_nonneg_right hs2 hXr0
  have h2 : (CF * η) * Xr ≤ 1 / 4 * Xr := mul_le_mul_of_nonneg_right hs1 hXr0
  have hfin : Xr ≤ 2 * (CF * (Bβ * (1 + A + η) * M)) := by linarith
  rw [hX]
  exact ENNReal.ofReal_le_ofReal hfin



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
    (Jc : E → E →L[ℝ] E) (e : ℂ) (he : ‖e‖ ≤ 1)
    (heq : ∀ z ∈ U, fderiv ℝ (fun y => fderiv ℝ u y e) z 1 +
      (Jc (u z) (fderiv ℝ (fun y => fderiv ℝ u y e) z Complex.I) +
        fderiv ℝ Jc (u z) (fderiv ℝ u z e) (fderiv ℝ u z Complex.I)) = 0)
    (z₀ : ℂ) (r : ℝ) (hr : 0 < r) (hball : ball z₀ r ⊆ U)
    (β : ℂ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβs : tsupport β ⊆ ball z₀ r)
    (Bβ : ℝ) (hBβ : ∀ z, ‖fderiv ℝ β z‖ ≤ Bβ)
    (η Λ A M : ℝ) (hη0 : 0 ≤ η) (hΛ0 : 0 ≤ Λ) (hM0 : 0 ≤ M)
    (hη : ∀ z ∈ ball z₀ r, ‖J₀ - Jc (u z)‖ ≤ η)
    (hΛ : ∀ z ∈ ball z₀ r, ‖fderiv ℝ Jc (u z)‖ ≤ Λ) (hA : ‖J₀‖ ≤ A)
    (hM : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ r)) ≤
      ENNReal.ofReal M)
    (hs1 : CF * η ≤ 1 / 4) (hs2 : CF * Λ * (CK * r ^ (1 - 2 / p)) * M ≤ 1 / 4) :
    eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z 1) (ENNReal.ofReal p) volume +
        eLpNorm (fun z => fderiv ℝ (fun y => β y • fderiv ℝ u y e) z Complex.I)
          (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * (CF * (Bβ * (1 + A + η) * M))) :=
  eLpNorm_fderiv_smul_fderiv_apply_le_aux p hp CF CK hCF hCK J₀ hF hK U hU u hu Jc e he heq z₀ r hr hball β hβ hβs Bβ hBβ η Λ A M hη0 hΛ0 hM0 hη hΛ hA hM hs1 hs2
