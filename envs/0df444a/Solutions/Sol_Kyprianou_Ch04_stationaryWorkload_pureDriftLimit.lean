-- Prove2me | solution 1 for Kyprianou.Ch04.stationaryWorkload_pureDriftLimit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:13:26.133167+00:00
-- url     : https://prove2.me/submissions/4a3fcca5-4535-4ec7-bddd-ca4317405cb8

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace PDAux

variable {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}

lemma nu_zero (L : SpectrallyNegativeLevy P F) (hd : 0 < L.drift)
    (hrho : (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) / ENNReal.ofReal L.drift = 0) :
    L.ν = 0 := by
  rw [ENNReal.div_eq_zero_iff] at hrho
  rcases hrho with h | h
  · have hm : Measurable (fun y : ℝ => ENNReal.ofReal (-y)) := by fun_prop
    rw [lintegral_eq_zero_iff hm] at h
    have h1 : L.ν (Set.Iio 0) = 0 := by
      rw [Filter.EventuallyEq, ae_iff] at h
      refine measure_mono_null ?_ h
      intro y hy
      simp only [Set.mem_Iio] at hy
      show ¬ (ENNReal.ofReal (-y) = (0 : ℝ → ℝ≥0∞) y)
      rw [Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have h2 := L.ν_Ici
    have : L.ν Set.univ = 0 := by
      rw [← Set.Iio_union_Ici (a := (0:ℝ))]
      exact measure_union_null h1 h2
    exact Measure.measure_univ_eq_zero.1 this
  · exact absurd h ENNReal.ofReal_ne_top

lemma psi_lin (L : SpectrallyNegativeLevy P F) (hσ : L.σ = 0) (hν : L.ν = 0) (θ : ℝ) :
    L.ψ θ = L.c * θ := by
  simp [SpectrallyNegativeLevy.ψ, laplaceExponent, hσ, hν]

lemma drift_eq (L : SpectrallyNegativeLevy P F) (hν : L.ν = 0) : L.drift = L.c := by
  simp [SpectrallyNegativeLevy.drift, hν]

lemma ae_eq_lin (L : SpectrallyNegativeLevy P F) (hσ : L.σ = 0) (hν : L.ν = 0) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, L.X t ω = L.c * t := by
  haveI := L.isProbability
  have h1 := L.laplace t 1 zero_le_one
  have h2 := L.laplace t 2 zero_le_two
  have hpl : ∀ θ, laplaceExponent L.c L.σ L.ν θ = L.c * θ := psi_lin L hσ hν
  rw [hpl] at h1 h2
  set Y : Omega → ℝ := fun ω => Real.exp (L.X t ω - L.c * t) with hY
  have hY1 : Y = fun ω => Real.exp (-(L.c * t)) * Real.exp (1 * L.X t ω) := by
    funext ω; simp only [hY, one_mul]; rw [← Real.exp_add]; ring_nf
  have hY2 : (fun ω => Y ω ^ 2) = fun ω => Real.exp (-(2 * (L.c * t))) * Real.exp (2 * L.X t ω) := by
    funext ω; simp only [hY]; rw [← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  have iY : Integrable Y P := by rw [hY1]; exact h1.1.const_mul _
  have iY2 : Integrable (fun ω => Y ω ^ 2) P := by rw [hY2]; exact h2.1.const_mul _
  have eY : ∫ ω, Y ω ∂P = 1 := by
    rw [hY1, integral_const_mul, h1.2, ← Real.exp_add]; ring_nf; simp
  have eY2 : ∫ ω, Y ω ^ 2 ∂P = 1 := by
    rw [hY2, integral_const_mul, h2.2, ← Real.exp_add]; ring_nf; simp
  have hsq : (fun ω => (Y ω - 1) ^ 2) = fun ω => Y ω ^ 2 - 2 * Y ω + 1 := by
    funext ω; ring
  have iZ : Integrable (fun ω => (Y ω - 1) ^ 2) P := by
    rw [hsq]; exact (iY2.sub (iY.const_mul 2)).add (integrable_const 1)
  have eZ : ∫ ω, (Y ω - 1) ^ 2 ∂P = 0 := by
    rw [hsq, integral_add (f := fun ω => Y ω ^ 2 - 2 * Y ω) (g := fun _ => (1:ℝ))
      (iY2.sub (iY.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun ω => Y ω ^ 2) (g := fun ω => 2 * Y ω) iY2 (iY.const_mul 2),
      integral_const_mul, eY, eY2]
    simp; norm_num
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (Y ω - 1)) iZ).1 eZ
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    sub_eq_zero, hY] at hω
  have := Real.exp_eq_one_iff _ |>.1 hω
  linarith

lemma ae_all (L : SpectrallyNegativeLevy P F) (hσ : L.σ = 0) (hν : L.ν = 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, L.X s ω = L.c * s := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, L.X (Real.toNNReal q) ω = L.c * (Real.toNNReal q : ℝ) := by
    rw [ae_all_iff]; intro q; exact ae_eq_lin L hσ hν _
  filter_upwards [hq] with ω hω
  intro s
  -- rational sequence decreasing to s
  have hseq : ∀ n : ℕ, ∃ q : ℚ, (s : ℝ) < q ∧ (q : ℝ) < s + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    exact exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hseq
  let u : ℕ → ℝ≥0 := fun n => Real.toNNReal (q n)
  have hu_ge : ∀ n, s ≤ u n := by
    intro n
    have : (s : ℝ) ≤ (u n : ℝ) := by
      simp only [u, Real.coe_toNNReal _ (le_trans s.2 (hq1 n).le)]; exact (hq1 n).le
    exact_mod_cast this
  have hu_real : Tendsto (fun n => (u n : ℝ)) atTop (nhds (s : ℝ)) := by
    have hlim : Tendsto (fun n : ℕ => (s : ℝ) + 1 / ((n : ℝ) + 1)) atTop (nhds (s : ℝ)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this.const_add (s : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim ?_ ?_
    · intro n; exact_mod_cast hu_ge n
    · intro n
      simp only [u, Real.coe_toNNReal _ (le_trans s.2 (hq1 n).le)]; exact (hq2 n).le
  have hu : Tendsto u atTop (nhdsWithin s (Set.Ici s)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall hu_ge⟩
    exact (NNReal.tendsto_coe.1 hu_real)
  have h1 : Tendsto (fun n => L.X (u n) ω) atTop (nhds (L.X s ω)) :=
    (L.rightCont ω s).tendsto.comp hu
  have h2 : Tendsto (fun n => L.X (u n) ω) atTop (nhds (L.c * s)) := by
    have : (fun n => L.X (u n) ω) = fun n => L.c * (u n : ℝ) := by
      funext n; exact hω (q n)
    rw [this]
    exact hu_real.const_mul _
  exact tendsto_nhds_unique h1 h2

end PDAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift) :
    let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    let eta : Measure Real :=
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun x : Real =>
          L.ν (Set.Iio (-x)) /
            (ENNReal.ofReal L.drift * rho))
    let convPow : Nat → Measure Real :=
      Nat.rec (Measure.dirac (0 : Real))
        (fun _ mu => mu.conv eta)
    (rho = 0 →
      ∀ w : Real, 0 ≤ w →
        let supX : NNReal → Omega → Real := fun t omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)
        let W : NNReal → Omega → Real := fun t omega =>
          max w (supX t omega) - L.X t omega
        ∀ f : BoundedContinuousFunction Real Real,
          Tendsto
            (fun t : NNReal =>
              ∫ omega, f (W t omega) ∂P)
            atTop (nhds (f 0))) := by
  intro rho eta convPow hrho w hw supX W f
  haveI := L.isProbability
  have hν := PDAux.nu_zero L hd hrho
  have hσ := hBV.1
  have hc : L.drift = L.c := PDAux.drift_eq L hν
  have hcpos : 0 < L.c := hc ▸ hd
  have hall := PDAux.ae_all L hσ hν
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ᶠ t : ℝ≥0 in atTop, w ≤ L.c * t := by
    have : Tendsto (fun t : ℝ≥0 => L.c * (t : ℝ)) atTop atTop :=
      (NNReal.tendsto_coe_atTop.2 tendsto_id).const_mul_atTop hcpos
    exact this.eventually_ge_atTop w
  filter_upwards [hev] with t ht
  symm
  have : (fun ω => f (W t ω)) =ᵐ[P] fun _ => f 0 := by
    filter_upwards [hall] with ω hω
    have hsup : supX t ω = L.c * t := by
      show sSup ((fun s : NNReal => L.X s ω) '' Set.Iic t) = L.c * t
      apply IsGreatest.csSup_eq
      refine ⟨⟨t, Set.mem_Iic.2 le_rfl, hω t⟩, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hω s]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hcpos.le
    show f (max w (supX t ω) - L.X t ω) = f 0
    rw [hsup, hω t, max_eq_right ht, sub_self]
  rw [integral_congr_ae this]
  simp
