-- Prove2me | solution 1 for NetworkControl.UtilityFairness.lemma_lyapunov_drift
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:05:25.911999+00:00
-- url     : https://prove2.me/submissions/24e5b19b-e08a-4ab1-b1e0-032da191d8a7

import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift

namespace NetworkControl.UtilityFairness

open MeasureTheory

theorem aux_lld_sum_odd (t : ℕ) :
    ∑ τ ∈ Finset.range t, (2 * (τ : ℝ) + 1) = (t : ℝ) ^ 2 := by
  induction t with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem aux_lld_avg_y (t : ℕ) :
    (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, (2 * (τ : ℝ) + 1) = (t : ℝ) := by
  rw [aux_lld_sum_odd]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp
  · have : (t : ℝ) ≠ 0 := by positivity
    field_simp

theorem aux_lld_limsup_y :
    Filter.limsup (fun t : ℕ => (t : ℝ)) Filter.atTop = 0 :=
  Real.limsup_of_not_isBoundedUnder
    (Filter.not_isBoundedUnder_of_tendsto_atTop tendsto_natCast_atTop_atTop)

theorem aux_lld_limsup_x :
    Filter.limsup (fun t : ℕ => (1 / (t : ℝ)) * ∑ _τ ∈ Finset.range t, (1 : ℝ)) Filter.atTop
      = 1 := by
  apply Filter.Tendsto.limsup_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with t ht
  have : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  simp [this]

end NetworkControl.UtilityFairness

open NetworkControl.UtilityFairness
open MeasureTheory

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (x y : ℕ → Ω → ℝ)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => L (U 0 ω)) P)
    (hIntegLdrift : ∀ t : ℕ, Integrable (fun ω => L (U (t + 1) ω) - L (U t ω)) P)
    (hIntegX : ∀ t : ℕ, Integrable (x t) P)
    (hIntegY : ∀ t : ℕ, Integrable (y t) P)
    (hdrift : ∀ t : ℕ,
      drift P L U t
        ≤ᵐ[P] ((P[y t | MeasurableSpace.comap (U t) inferInstance])
                - (P[x t | MeasurableSpace.comap (U t) inferInstance]))),
    (Filter.limsup (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P)
        Filter.atTop
      ≤ Filter.limsup (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P)
        Filter.atTop) ∧
    (Filter.liminf (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, x τ ω ∂P)
        Filter.atTop
      ≤ Filter.liminf (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, y τ ω ∂P)
        Filter.atTop)) := by
  intro H
  have hm : ∀ t : ℕ, MeasurableSpace.comap ((fun _ _ _ => (0 : ℝ)) t : Unit → Fin 0 → ℝ)
      inferInstance ≤ (inferInstance : MeasurableSpace Unit) :=
    fun t => (measurable_const).comap_le
  have h1 := (H (Ω := Unit) (P := Measure.dirac ()) (N := 0) (fun _ => 0) (fun _ => le_rfl)
    (fun _ _ _ => 0) (fun _ _ => 1) (fun t _ => 2 * (t : ℝ) + 1)
    (fun _ _ => measurable_const) (integrable_const _) (fun _ => by simp)
    (fun _ => integrable_const _) (fun _ => integrable_const _)
    (fun t => by
      simp only [drift, sub_self]
      rw [condExp_const (hm t), condExp_const (hm t), condExp_const (hm t)]
      exact Filter.Eventually.of_forall (fun _ => by simp))).1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  rw [aux_lld_limsup_x] at h1
  simp only [aux_lld_avg_y, aux_lld_limsup_y] at h1
  norm_num at h1
