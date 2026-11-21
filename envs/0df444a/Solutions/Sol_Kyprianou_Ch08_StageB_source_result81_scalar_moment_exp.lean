-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scalar_moment_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:34:06.497309+00:00
-- url     : https://prove2.me/submissions/89428df4-1db0-4755-8e64-4b8fddc26c17

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem additive_at_nat_mul (g : ℝ≥0 → ℝ) (hg0 : g 0 = 0)
    (hgadd : ∀ s u, g (s + u) = g s + g u) :
    ∀ n : ℕ, ∀ s, g (n * s) = n * g s := by
  intro n s
  induction n with
  | zero => simp [hg0]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ≥0) * s = n * s + s by push_cast; ring, hgadd, ih]
    push_cast
    ring

private theorem additive_at_positive_grid (g : ℝ≥0 → ℝ)
    (hgnat : ∀ n : ℕ, ∀ s, g (n * s) = n * g s) (k m : ℕ) :
    g ((k : ℝ≥0) / ((m : ℝ≥0) + 1)) = ((k : ℝ) / ((m : ℝ) + 1)) * g 1 := by
  have h1 := hgnat (m + 1) ((k : ℝ≥0) / ((m : ℝ≥0) + 1))
  have h2 := hgnat k 1
  rw [show ((m + 1 : ℕ) : ℝ≥0) * ((k : ℝ≥0) / ((m : ℝ≥0) + 1)) = k by
    push_cast; field_simp] at h1
  rw [mul_one] at h2
  rw [h2] at h1
  push_cast at h1
  field_simp
  linarith

private theorem log_moment_le_of_right_fatou (G : ℝ≥0 → ℝ≥0∞) (g : ℝ≥0 → ℝ)
    (hfin : ∀ s, G s ≠ ⊤) (hGg : ∀ s, (G s).toReal = Real.exp (g s))
    (hright : ∀ (s : ℝ≥0) (sn : ℕ → ℝ≥0),
      (∀ n, s ≤ sn n) → Tendsto sn atTop (nhds s) →
        G s ≤ Filter.liminf (fun n => G (sn n)) atTop)
    (hgrid : ∀ k m : ℕ,
      g ((k : ℝ≥0) / ((m : ℝ≥0) + 1)) = ((k : ℝ) / ((m : ℝ) + 1)) * g 1)
    (s : ℝ≥0) : g s ≤ s * g 1 := by
  let sn : ℕ → ℝ≥0 := fun n => (⌈((n : ℝ≥0) + 1) * s⌉₊ : ℝ≥0) / ((n : ℝ≥0) + 1)
  have hge : ∀ n, s ≤ sn n := by
    intro n
    simp only [sn]
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact Nat.le_ceil _
  have hle : ∀ n, sn n ≤ s + 1 / ((n : ℝ≥0) + 1) := by
    intro n
    have e : (s + 1 / ((n : ℝ≥0) + 1)) * ((n : ℝ≥0) + 1) = ((n : ℝ≥0) + 1) * s + 1 := by
      field_simp
    simp only [sn]
    rw [div_le_iff₀ (by positivity), e]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hsn : Tendsto sn atTop (nhds s) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hge hle
    have ht : Tendsto (fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
    simpa using tendsto_const_nhds.add ht
  have hGsn (n : ℕ) : G (sn n) = ENNReal.ofReal (Real.exp ((sn n : ℝ) * g 1)) := by
    rw [← ENNReal.ofReal_toReal (hfin (sn n)), hGg]
    congr 2
    simp only [sn]
    rw [hgrid]
    push_cast
    ring
  have hlim : Tendsto (fun n => G (sn n)) atTop (nhds (ENNReal.ofReal (Real.exp (s * g 1)))) := by
    simp_rw [hGsn]
    have hc : Continuous fun x : ℝ≥0 => ENNReal.ofReal (Real.exp ((x : ℝ) * g 1)) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (NNReal.continuous_coe.mul continuous_const))
    exact (hc.tendsto s).comp hsn
  have hbound : G s ≤ ENNReal.ofReal (Real.exp (s * g 1)) := by
    rw [← hlim.liminf_eq]
    exact hright s sn hge hsn
  have hh := (ENNReal.toReal_le_toReal (hfin s) ENNReal.ofReal_ne_top).2 hbound
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hGg] at hh
  exact Real.exp_le_exp.1 hh

theorem solution
    (G : ℝ≥0 → ℝ≥0∞) (hG0 : G 0 = 1)
    (hmul : ∀ s u, G (s + u) = G s * G u)
    (hne : ∀ s, G s ≠ 0) (hfin : ∀ s, G s ≠ ⊤)
    (hright : ∀ (s : ℝ≥0) (sn : ℕ → ℝ≥0),
      (∀ n, s ≤ sn n) → Tendsto sn atTop (nhds s) →
        G s ≤ Filter.liminf (fun n => G (sn n)) atTop)
    (t : ℝ≥0) :
    (G t).toReal = Real.exp ((t : ℝ) * Real.log (G 1).toReal) := by
  set g : ℝ≥0 → ℝ := fun s => Real.log (G s).toReal with hgdef
  have hpos : ∀ s, 0 < (G s).toReal := fun s => ENNReal.toReal_pos (hne s) (hfin s)
  have hGg : ∀ s, (G s).toReal = Real.exp (g s) := fun s => (Real.exp_log (hpos s)).symm
  have hgadd : ∀ s u, g (s + u) = g s + g u := by
    intro s u
    simp only [hgdef, hmul, ENNReal.toReal_mul]
    exact Real.log_mul (hpos s).ne' (hpos u).ne'
  have hg0 : g 0 = 0 := by simp [hgdef, hG0]
  have hgnat := additive_at_nat_mul g hg0 hgadd
  have hup := log_moment_le_of_right_fatou G g hfin hGg hright (additive_at_positive_grid g hgnat)
  have hgt : g t = t * g 1 := by
    refine le_antisymm (hup t) ?_
    let N : ℝ≥0 := ⌈t⌉₊
    have htN : t ≤ N := Nat.le_ceil t
    have h1 := hgadd t (N - t)
    rw [add_tsub_cancel_of_le htN] at h1
    have h2 := hup (N - t)
    have h3 : g N = N * g 1 := by
      simpa [N] using hgnat ⌈t⌉₊ 1
    rw [NNReal.coe_sub htN] at h2
    nlinarith
  rw [hGg, hgt]
