-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_geometric_renewal_from_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:47:41.970427+00:00
-- url     : https://prove2.me/submissions/f1be06d9-bb0b-4d97-be3c-9616c7386516
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_conv_support_atomless_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_rho_laplace_pos_le_one_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_gap_kappa_lt_one_of_rho_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_laplace_series_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_renewal_gap_algebra_identity_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_laplace_finite_implies_locally_finite_public
import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s) (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ) (hsupp : ρ (Iio (0:ℝ)) = 0) (heq : ∀ s : ℝ, 0 < s → (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal = f d * (1 - s / d)) (κ : Measure ℝ) [SFinite κ] (hκsupp : κ (Iio (0:ℝ)) = 0) (hκatom : ∀ x : ℝ, κ {x} = 0) (hκgen : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s) (hκform : ∀ s : ℝ, 0 < s → s ≠ d → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s)))) (L : ℝ → ℝ≥0∞) (hL : ∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) = L s) (s0 : ℝ) (hs0 : 0 < s0) (hr : L s0 < 1) : ∃ ν : Measure ℝ, ν (Iio (0:ℝ)) = 0 ∧ (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧ (∀ s : ℝ, 0 < s → (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s)) ∧ (∀ x : ℝ, 0 < x → ν {x} = ENNReal.ofReal (d / f d) * ρ {x}) := by
  have hfd : 0 < f d := hpos d hd
  haveI := hprob
  obtain ⟨m, hm0, hmsucc, hsf⟩ := AvramDividend.Classical.exists_sfinite_convolution_power_sequence κ
  haveI : ∀ n, SFinite (m n) := hsf
  have hsupp_pair := Kyprianou.Ch08.StageB.p2m81_renewal_conv_support_atomless_public
  have hmsupp : ∀ n, m n (Iio (0:ℝ)) = 0 := by
    intro n
    induction n with
    | zero =>
        rw [hm0]
        simp
    | succ n ih =>
        rw [hmsucc n]
        exact (hsupp_pair κ (m n)).1 hκsupp ih
  have hR := Kyprianou.Ch08.StageB.p2m81_rho_laplace_pos_le_one_public ρ hprob hsupp
  have hκlt := Kyprianou.Ch08.StageB.p2m81_gap_kappa_lt_one_of_rho_public f hpos d hd ρ heq κ hκgen hκform hR
  have hRtrpos : ∀ s : ℝ, 0 < s → 0 < (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal := by intro s hs; have h1 := (hR s hs).1; have h2 := (hR s hs).2; have ht : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h2 ENNReal.one_lt_top); exact ENNReal.toReal_pos (ne_of_gt h1) ht
  have hRtle : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal ≤ 1 := by intro s hs; have h2 := (hR s hs).2; have h1t : (1:ℝ≥0∞) ≠ ⊤ := ne_of_lt ENNReal.one_lt_top; have ht : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h2 ENNReal.one_lt_top); have hle : (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal ≤ (1:ℝ≥0∞).toReal := (ENNReal.toReal_le_toReal ht h1t).mpr h2; simpa [ENNReal.toReal_one] using hle
  set cR : ℝ := d / f d with hcRdef
  set c : ℝ≥0∞ := ENNReal.ofReal cR with hcdef
  set ν : Measure ℝ := Measure.sum (fun n : ℕ => c • (ρ.conv (m n))) with hνdef
  have hνsupp : ν (Iio (0:ℝ)) = 0 := by rw [hνdef, Measure.sum_apply_eq_zero]; intro n; rw [Measure.smul_apply, (hsupp_pair ρ (m n)).1 hsupp (hmsupp n)]; simp
  have hconv_atom : ∀ (μ ν : Measure ℝ) [SFinite μ] [SFinite ν], (∀ y, ν {y} = 0) → ∀ x, (μ.conv ν) {x} = 0 := fun μ ν _ _ hν => (hsupp_pair μ ν).2 hν
  have hconv1 : ∀ (μ ν : Measure ℝ) [SFinite μ] [SFinite ν], (∀ y, μ {y} = 0) → ∀ x, (μ.conv ν) {x} = 0 := by intro μ ν _ _ hμ x; rw [Measure.conv_comm]; exact hconv_atom ν μ hμ x
  have hmatom : ∀ n, 0 < n → ∀ x, m n {x} = 0 := by intro n hn x; cases n with | zero => exact absurd hn (lt_irrefl 0) | succ k => have hrec : m (k + 1) = κ.conv (m k) := hmsucc k; rw [hrec]; exact hconv1 κ (m k) hκatom x
  have hρmatom : ∀ n, 0 < n → ∀ x, (ρ.conv (m n)) {x} = 0 := by intro n hn x; exact hconv_atom ρ (m n) (hmatom n hn) x
  have hνdef_eq : ν = Measure.sum (fun n : ℕ => c • (ρ.conv (m n))) := rfl
  have hseries := Kyprianou.Ch08.StageB.p2m81_renewal_laplace_series_public ρ hprob κ m hm0 hmsucc hsf c ν hνdef_eq hκlt
  have hνLap : ∀ s : ℝ, 0 < s → (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) = ENNReal.ofReal (s / f s) := by
    intro s hs
    rw [hseries s hs]
    have hc : c = ENNReal.ofReal (d / f d) := by rw [hcdef, hcRdef]
    rw [hc]
    exact Kyprianou.Ch08.StageB.p2m81_renewal_gap_algebra_identity_public f hpos d hd ρ heq κ hκgen hκform hRtrpos hRtle s hs
  have hLap1 : (∫⁻ y, ENNReal.ofReal (Real.exp (-(1:ℝ) * y)) ∂ν) = ENNReal.ofReal ((1:ℝ) / f 1) := hνLap 1 one_pos
  have hfin1 : (∫⁻ y, ENNReal.ofReal (Real.exp (-(1:ℝ) * y)) ∂ν) < ⊤ := by rw [hLap1]; exact ENNReal.ofReal_lt_top
  have hνfin : ∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤ := Kyprianou.Ch08.StageB.p2m81_laplace_finite_implies_locally_finite_public ν hfin1
  have hνatom : ∀ x : ℝ, 0 < x → ν {x} = ENNReal.ofReal (d / f d) * ρ {x} := by
    intro x _
    have hsing : MeasurableSet ({x} : Set ℝ) := measurableSet_singleton x
    rw [hνdef, Measure.sum_apply _ hsing]
    have h0 : (c • (ρ.conv (m 0))) {x} = c * ρ {x} := by simp [hm0, Measure.conv_dirac_zero, Measure.smul_apply, smul_eq_mul]
    have hrest : ∀ n, n ≠ 0 → (fun n : ℕ => (c • (ρ.conv (m n))) {x}) n = 0 := by
      intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [Measure.smul_apply, smul_eq_mul, hρmatom n hnpos x]
    rw [tsum_eq_single 0 hrest]
    rw [h0, hcdef, hcRdef]
  exact ⟨ν, hνsupp, hνfin, hνLap, hνatom⟩
