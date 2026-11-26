-- Prove2me | solution 1 for NullConeGravity.graviton_pair_uv_log_divergence
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:30:04.764729+00:00
-- url     : https://prove2.me/submissions/d1d101f0-ff62-4205-b909-9a2393429093

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

private lemma third_quadratic_mul (a : ℂ) {F : ℝ → ℂ} (hF : ContDiffAt ℝ 3 F 0) :
    iteratedDeriv 3 (fun x : ℝ => (x ^ 2 • a) * F x) 0 = 6 * a * deriv F 0 := by
  have hquadratic (i : ℕ) :
      iteratedDeriv i (fun x : ℝ => x ^ 2 • a) 0 = (if i = 2 then (2 : ℝ) else 0) • a := by
    rw [iteratedDeriv_smul_const (by fun_prop) a, iteratedDeriv_fun_pow_zero]
    norm_num
  have hsmooth : ContDiffAt ℝ 3 (fun x : ℝ => x ^ 2 • a) 0 := by fun_prop
  rw [iteratedDeriv_fun_mul hsmooth hF]
  simp_rw [hquadratic]
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_one, Complex.real_smul]
  ring_nf
  simp

private lemma cutoff_derivative (c : ℝ) (N : ℕ) :
    iteratedDeriv 3
        (fun g : ℝ => ((c^2 * g^2 / 2 : ℝ) : ℂ) *
            Finset.sum (Finset.range N) (fun k : ℕ =>
                Complex.exp (-2 * Complex.I * (k + 1 : ℂ) * (c : ℂ) * (g : ℂ)) / (k + 1 : ℂ)^2)) 0
        = -6 * Complex.I * (c : ℂ)^3 * Finset.sum (Finset.range N) (fun k : ℕ => 1 / (k + 1 : ℂ)) := by
  let rate (k : ℕ) : ℂ := -2 * Complex.I * (k + 1 : ℂ) * (c : ℂ)
  let F (g : ℝ) : ℂ := ∑ k ∈ Finset.range N,
    Complex.exp (rate k * (g : ℂ)) / (k + 1 : ℂ) ^ 2
  have hF : ContDiffAt ℝ 3 F 0 := by
    have hcastSmooth : ContDiffAt ℝ 3 (fun g : ℝ => (g : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt
    apply ContDiffAt.sum
    intro k _
    exact (contDiffAt_const.mul hcastSmooth).cexp.div_const _
  have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hd : HasDerivAt F (∑ k ∈ Finset.range N, rate k / (k + 1 : ℂ) ^ 2) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    simpa using ((hcast.const_mul (rate k)).cexp.div_const ((k + 1 : ℂ) ^ 2))
  have hpref (g : ℝ) : ((c ^ 2 * g ^ 2 / 2 : ℝ) : ℂ) =
      g ^ 2 • ((c : ℂ) ^ 2 / 2) := by
    rw [Complex.real_smul]
    push_cast
    ring
  change iteratedDeriv 3 (fun g : ℝ => ((c ^ 2 * g ^ 2 / 2 : ℝ) : ℂ) * F g) 0 = _
  simp_rw [hpref]
  rw [third_quadratic_mul _ hF, hd.deriv, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  dsimp only [rate]
  field_simp [hk]

private lemma harmonic_ratio :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)) / Real.log N)
      atTop (𝓝 1) := by
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)) = (harmonic N : ℝ) := by
    simp [harmonic, Rat.cast_sum, one_div]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n) / Real.log n)
      atTop (𝓝 0) := Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hlimit : Tendsto (fun n : ℕ => 1 + ((harmonic n : ℝ) - Real.log n) / Real.log n)
      atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add herr
  apply hlimit.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  rw [hsum]
  field_simp [ne_of_gt hn]
  ring

theorem solution (c : ℝ) :
    (∀ N : ℕ, iteratedDeriv 3
        (fun g : ℝ => ((c^2 * g^2 / 2 : ℝ) : ℂ) *
            Finset.sum (Finset.range N) (fun k : ℕ =>
                Complex.exp (-2 * Complex.I * (k + 1 : ℂ) * (c : ℂ) * (g : ℂ)) / (k + 1 : ℂ)^2)) 0
        = -6 * Complex.I * (c : ℂ)^3 * Finset.sum (Finset.range N) (fun k : ℕ => 1 / (k + 1 : ℂ))) ∧
    Filter.Tendsto (fun N : ℕ => Finset.sum (Finset.range N) (fun k : ℕ => (1 : ℝ) / (k + 1)) / Real.log N)
        Filter.atTop (nhds 1) :=
  ⟨cutoff_derivative c, harmonic_ratio⟩
