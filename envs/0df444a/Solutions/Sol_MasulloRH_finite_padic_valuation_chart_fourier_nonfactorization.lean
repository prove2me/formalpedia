-- Prove2me | solution 1 for MasulloRH.finite_padic_valuation_chart_fourier_nonfactorization
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:57:59.222724+00:00
-- url     : https://prove2.me/submissions/074c031b-304d-4c91-adbe-a888cecb7005

import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
section

open MeasureTheory Set Metric

namespace MasulloRH

/-- An arbitrary nonzero-radius annulus has positive finite Haar mass; its Fourier transform
on the reciprocal ball is precisely that mass for a character trivial on the unit ball. -/
theorem padic_annulus_fourier_plateau (p : ℕ) [Fact p.Prime]
    [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]] (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure]
    (ψ : AddChar ℚ_[p] ℂ) (hψ : ∀ z : ℚ_[p], ‖z‖ ≤ 1 → ψ z = 1)
    (y₀ : ℚ_[p]) (hy₀ : y₀ ≠ 0) :
    let Ω := sphere (0 : ℚ_[p]) ‖y₀‖
    let F := Ω.indicator (fun _ : ℚ_[p] => (1:ℂ))
    0 < μ.real Ω ∧ ∀ u : ℚ_[p], ‖u‖ * ‖y₀‖ ≤ 1 →
      (∫ y, ψ (y*u) * F y ∂μ) = (μ.real Ω : ℂ) := by
  intro Ω F
  have hopen : IsOpen Ω := IsUltrametricDist.isOpen_sphere 0 (norm_ne_zero_iff.mpr hy₀)
  have hcompact : IsCompact Ω := isCompact_sphere _ _
  have hmem : Ω.Nonempty := ⟨y₀, by simp [Ω]⟩
  refine ⟨ENNReal.toReal_pos (hopen.measure_pos μ hmem).ne' hcompact.measure_lt_top.ne, ?_⟩
  intro u hu
  have hpoint (y : ℚ_[p]) : ψ (y*u) * F y = F y := by
    by_cases hy : y ∈ Ω
    · have hy' : ‖y‖ = ‖y₀‖ := by simpa [Ω] using hy
      rw [hψ _ (by simpa [norm_mul,hy',mul_comm] using hu), one_mul]
    · simp [F, indicator_of_notMem hy]
  simp_rw [hpoint]
  dsimp only [F]
  rw [integral_indicator_const _ hopen.measurableSet, Complex.real_smul, mul_one]


end MasulloRH
end

section

open MeasureTheory Set Filter
open scoped FourierTransform Topology
namespace MasulloRH

private noncomputable def realGauss (x : ℝ) : ℂ := Real.exp (-(Real.pi*x^2))

private theorem realGauss_fourier : 𝓕 realGauss = realGauss := by
  have h := fourier_gaussian_pi (b := (1:ℂ)) (by norm_num)
  simp only [Complex.one_cpow, div_one, mul_one, one_mul] at h
  have he : realGauss = fun x : ℝ => Complex.exp (-(Real.pi:ℂ)*(x:ℂ)^2) := by
    funext x
    simp [realGauss,Complex.ofReal_exp]
  simpa only [he] using h

private theorem scales_hit_annulus (p : ℕ) [Fact p.Prime] (L j : ℤ) (u : ℚ_[p])
    (hu : ‖u‖ = 1) : ‖(p:ℚ_[p])^j*u‖ = ‖(p:ℚ_[p])^L‖ ↔ j=L := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [norm_mul,hu,mul_one,Padic.norm_p_zpow,Padic.norm_p_zpow,zpow_right_inj₀ (by positivity) hp.ne']
  exact neg_inj

private theorem orbit_hits_single_valuation (p : ℕ) [Fact p.Prime] (L j : ℤ)
    {y : ℚ_[p]} (hy : y ≠ 0) : ‖(p:ℚ_[p])^j*y‖ = ‖(p:ℚ_[p])^L‖ ↔ j = L-y.valuation := by
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [norm_mul,Padic.norm_p_zpow,Padic.norm_p_zpow,Padic.norm_eq_zpow_neg_valuation hy,
    ← zpow_add₀ (zero_lt_one.trans hp).ne',zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne']
  omega

private theorem periodize_single_valuation (p : ℕ) [Fact p.Prime] (L : ℤ)
    (g : ℝ → ℚ_[p] → ℂ) (h : ∀ x y, ‖y‖ ≠ ‖(p:ℚ_[p])^L‖ → g x y = 0)
    (s : ℝ) (y : ℚ_[p]) (hy : y ≠ 0) :
    let j := L - y.valuation
    HasSum (fun k : ℤ => g ((p:ℝ)^k*s) ((p:ℚ_[p])^k*y))
      (g ((p:ℝ)^j*s) ((p:ℚ_[p])^j*y)) := by
  dsimp only
  convert hasSum_ite_eq (L-y.valuation) (g ((p:ℝ)^(L-y.valuation)*s) ((p:ℚ_[p])^(L-y.valuation)*y)) using 1
  funext k
  by_cases hk : k = L-y.valuation
  · simp [hk]
  · rw [if_neg hk]
    exact h _ _ (fun he => hk ((orbit_hits_single_valuation p L k hy).mp he))

private theorem shell_fourier_general (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) (ψ : AddChar ℚ_[p] ℂ) (Ω : Set ℚ_[p]) (g : ℝ → ℂ) (s : ℝ) (u : ℚ_[p]) :
    (∫ y : ℚ_[p], ψ (y*u) * (𝓕 (fun x : ℝ => Ω.indicator (fun _ => g x) y)) s ∂μ) =
    (∫ y : ℚ_[p], ψ (y*u) * Ω.indicator (fun _ => (1:ℂ)) y ∂μ) * (𝓕 g) s := by
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Ω
  · simp only [indicator_of_mem hy,mul_one]
  · simp only [indicator_of_notMem hy,mul_zero,zero_mul]
    simp [Real.fourier_real_eq_integral_exp_smul]

private theorem shell_fourier_in_place (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) (ψ : AddChar ℚ_[p] ℂ) (Ω : Set ℚ_[p]) (s : ℝ) (u : ℚ_[p]) :
    (∫ y : ℚ_[p], ψ (y*u) * (𝓕 (fun x : ℝ => Ω.indicator (fun _ => realGauss x) y)) s ∂μ) =
    (∫ y : ℚ_[p], ψ (y*u) * Ω.indicator (fun _ => (1:ℂ)) y ∂μ) * realGauss s := by
  simpa only [realGauss_fourier] using shell_fourier_general p μ ψ Ω realGauss s u

end MasulloRH
end

section

open Set MeasureTheory Filter
open scoped Topology FourierTransform

namespace MasulloRH

/-- A single smooth positive-frequency test works on every finite list after a common scaling. -/
theorem exists_bump_fourier_positive_on_scaled_finite_sets :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ x : ℝ, x ≤ 1 ∨ 2 ≤ x → g x = 0) ∧
      ∀ T : Finset ℝ, ∃ s : ℝ, 0 < s ∧ ∀ c ∈ T, 0 < (𝓕 g (c*s)).re := by
  let b : ContDiffBump (3/2 : ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let g (x : ℝ) := (b x : ℂ)
  have hD : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hC : HasCompactSupport g := b.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hI : Integrable g volume := hD.continuous.integrable_of_hasCompactSupport hC
  have hF : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hI
  have hb0 : 0 < ∫ t : ℝ, b t := by
    apply b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero b.hasCompactSupport (fun _ => b.nonneg)
      (x := (3/2 : ℝ))
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero
  have hF0 : 0 < (𝓕 g 0).re := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    change 0 < (∫ t : ℝ, (b t:ℂ)).re
    have he := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := fun t : ℝ => b t)
    have hre : (∫ t : ℝ, (b t:ℂ)).re = ∫ t : ℝ, b t := congrArg Complex.re he
    rw [hre]
    exact hb0
  refine ⟨g,hD,hC,?_,?_⟩
  · intro x hx
    apply Complex.ofReal_eq_zero.mpr
    apply b.zero_of_le_dist
    change 1/4 ≤ dist x (3/2)
    rw [Real.dist_eq]
    rcases hx with hx | hx
    · linarith [neg_le_abs (x-3/2)]
    · linarith [le_abs_self (x-3/2)]
  · intro T
    have hpos (c : ℝ) : ∀ᶠ s : ℝ in 𝓝 0, 0 < (𝓕 g (c*s)).re := by
      have hcont : Continuous (fun s : ℝ => (𝓕 g (c*s)).re) :=
        Complex.continuous_re.comp (hF.comp (continuous_const.mul continuous_id))
      exact (isOpen_lt continuous_const hcont).mem_nhds (by simpa using hF0)
    have hall : ∀ᶠ s : ℝ in 𝓝 0, ∀ c ∈ T, 0 < (𝓕 g (c*s)).re := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert c T hc ih => filter_upwards [hpos c, ih] with s hs hT using by simpa [hs] using hT
    have hall' := hall.filter_mono (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Ioi 0))
    have hright : ∀ᶠ s : ℝ in 𝓝[Ioi (0:ℝ)] 0, 0 < s := self_mem_nhdsWithin
    exact (hright.and hall').exists

end MasulloRH
end

section
open MeasureTheory Set Filter
open scoped FourierTransform Topology

theorem solution (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p]] [BorelSpace ℚ_[p]]
    (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[p] ℂ)
    (hψ : ∀ z : ℚ_[p], ‖z‖ ≤ 1 → ψ z = 1) (K : Finset ℤ) (hK : K.Nonempty) :
    let G (s : ℝ) : ℂ := Real.exp (-(Real.pi*s^2))
    let FT (f : ℝ → ℚ_[p] → ℂ) (s : ℝ) (u : ℚ_[p]) :=
      ∫ y : ℚ_[p], ψ (y*u) * (𝓕 (fun x : ℝ => f x y)) s ∂μ
    let stage (f : ℝ → ℚ_[p] → ℂ) (s : ℝ) (u : ℚ_[p]) :=
      ∑ j ∈ K, f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u)
    (∀ (ℓ : ℤ) (g : ℝ → ℚ_[p] → ℂ),
      (∀ x y, ‖y‖ ≠ ‖(p:ℚ_[p])^ℓ‖ → g x y = 0) →
      ∀ (s : ℝ) (y : ℚ_[p]), y ≠ 0 → let j := ℓ-y.valuation
      HasSum (fun k : ℤ => g ((p:ℝ)^k*s) ((p:ℚ_[p])^k*y))
        (g ((p:ℝ)^j*s) ((p:ℚ_[p])^j*y))) ∧
    ∃ L : ℤ,
      let Ω := Metric.sphere (0:ℚ_[p]) ‖(p:ℚ_[p])^L‖
      let f (x : ℝ) (y : ℚ_[p]) := Ω.indicator (fun _ => G x) y
      (∀ k ∈ K, k < L ∧ 0 ≤ k+L) ∧ 0 < μ.real Ω ∧
      (∀ s : ℝ, ∀ u : ℚ_[p], ‖u‖=1 →
        HasSum (fun j : ℤ => f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u)) (G ((p:ℝ)^L*s))) ∧
      (∀ s : ℝ, ∀ u : ℚ_[p], ‖u‖=1 → stage f s u = 0 ∧
        stage (FT f) s u = (μ.real Ω:ℂ) * ∑ j ∈ K, G ((p:ℝ)^j*s) ∧
        0 < (stage (FT f) s u).re) ∧
      (∃ b : ℝ → ℂ, ContDiff ℝ (⊤:ℕ∞) b ∧ HasCompactSupport b ∧
        (∀ x : ℝ, x≤1 ∨ 2≤x → b x=0) ∧
        let h (x : ℝ) (y : ℚ_[p]) := Ω.indicator (fun _ => b x) y
        (∀ t : ℝ, ∀ u : ℚ_[p], ‖u‖=1 → stage h t u=0) ∧
        ∃ s : ℝ, 0<s ∧ ∀ u : ℚ_[p], ‖u‖=1 → 0<(stage (FT h) s u).re) := by
  classical
  constructor
  · exact MasulloRH.periodize_single_valuation p
  let L : ℤ := (∑ k ∈ K, |k|) + 1
  have hL (k : ℤ) (hk : k∈K) : k<L ∧ 0≤k+L := by
    have hb : |k| ≤ ∑ i ∈ K, |i| := Finset.single_le_sum (fun i _ => abs_nonneg i) hk
    dsimp [L]
    constructor <;> linarith [le_abs_self k,neg_le_abs k]
  let Ω := Metric.sphere (0:ℚ_[p]) ‖(p:ℚ_[p])^L‖
  let f (x : ℝ) (y : ℚ_[p]) := Ω.indicator (fun _ => MasulloRH.realGauss x) y
  have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ)<p := zero_lt_one.trans hp
  have hpQ : (p:ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨hmass,hFT⟩ := MasulloRH.padic_annulus_fourier_plateau p μ ψ hψ ((p:ℚ_[p])^L) (zpow_ne_zero _ hpQ)
  have hcell (j : ℤ) (u : ℚ_[p]) (hu : ‖u‖=1) : (p:ℚ_[p])^j*u ∈ Ω ↔ j=L := by
    simpa only [Ω,Metric.mem_sphere,dist_zero_right] using MasulloRH.scales_hit_annulus p L j u hu
  have horbit (s : ℝ) (u : ℚ_[p]) (hu : ‖u‖=1) (j : ℤ) :
      f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u) = if j=L then MasulloRH.realGauss ((p:ℝ)^L*s) else 0 := by
    by_cases h : j=L
    · subst j
      simp [f, indicator_of_mem ((hcell L u hu).mpr rfl)]
    · simp only [f,indicator_of_notMem (fun hx => h ((hcell j u hu).mp hx)),if_neg h]
  have hnorm (u : ℚ_[p]) (hu : ‖u‖=1) (j : ℤ) (hj : j∈K) :
      ‖(p:ℚ_[p])^j*u‖ * ‖(p:ℚ_[p])^L‖ ≤ 1 := by
    rw [norm_mul,hu,mul_one,Padic.norm_p_zpow,Padic.norm_p_zpow,← zpow_add₀ hp0.ne']
    exact zpow_le_one_of_nonpos₀ hp.le (by linarith [(hL j hj).2])
  have hcoeff (b : ℝ → ℂ) (s : ℝ) (u : ℚ_[p]) (hu : ‖u‖=1) (j : ℤ) (hj : j∈K) :
      (∫ y : ℚ_[p], ψ (y*((p:ℚ_[p])^j*u)) *
        (𝓕 (fun x : ℝ => Ω.indicator (fun _ => b x) y)) ((p:ℝ)^j*s) ∂μ) =
      (μ.real Ω:ℂ) * (𝓕 b) ((p:ℝ)^j*s) :=
    (MasulloRH.shell_fourier_general p μ ψ Ω b _ _).trans (congrArg (fun z => z*_) (hFT _ (hnorm u hu j hj)))
  have hzero (b : ℝ → ℂ) (s : ℝ) (u : ℚ_[p]) (hu : ‖u‖=1) :
      (∑ j ∈ K, Ω.indicator (fun _ => b ((p:ℝ)^j*s)) ((p:ℚ_[p])^j*u))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact indicator_of_notMem (fun h => (hL j hj).1.ne ((hcell j u hu).mp h)) _
  refine ⟨L,hL,hmass,?_,?_,?_⟩
  · intro s u hu
    change HasSum (fun j : ℤ => f ((p:ℝ)^j*s) ((p:ℚ_[p])^j*u)) (MasulloRH.realGauss ((p:ℝ)^L*s))
    convert hasSum_ite_eq L (MasulloRH.realGauss ((p:ℝ)^L*s)) using 1
    funext j
    exact horbit s u hu j
  · intro s u hu
    have hG (j : ℤ) (hj : j∈K) := hcoeff MasulloRH.realGauss s u hu j hj
    simp only [MasulloRH.realGauss_fourier] at hG
    refine ⟨hzero MasulloRH.realGauss s u hu,?_,?_⟩
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hG
    · rw [Complex.re_sum]
      apply Finset.sum_pos _ hK
      intro j hj
      change 0 < (∫ y : ℚ_[p], ψ (y*((p:ℚ_[p])^j*u)) * (𝓕 (fun x : ℝ => f x y)) ((p:ℝ)^j*s) ∂μ).re
      rw [hG j hj]
      simpa only [MasulloRH.realGauss,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero] using mul_pos hmass (Real.exp_pos (-(Real.pi*(((p:ℝ)^j*s)^2))))
  · obtain ⟨b,hb,hbc,hcut,hpos⟩ := MasulloRH.exists_bump_fourier_positive_on_scaled_finite_sets
    obtain ⟨s,hs,hsval⟩ := hpos (K.image (fun j : ℤ => (p:ℝ)^j))
    refine ⟨b,hb,hbc,hcut,hzero b,s,hs,?_⟩
    intro u hu
    rw [Complex.re_sum]
    apply Finset.sum_pos _ hK
    intro j hj
    change 0 < (∫ y : ℚ_[p], ψ (y*((p:ℚ_[p])^j*u)) *
      (𝓕 (fun t : ℝ => Ω.indicator (fun _ => b t) y)) ((p:ℝ)^j*s) ∂μ).re
    rw [hcoeff b s u hu j hj,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_pos hmass (hsval _ (Finset.mem_image_of_mem _ hj))
end
