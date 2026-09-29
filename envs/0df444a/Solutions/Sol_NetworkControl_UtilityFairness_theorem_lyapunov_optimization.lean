-- Prove2me | solution 1 for NetworkControl.UtilityFairness.theorem_lyapunov_optimization
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:09:54.1618+00:00
-- url     : https://prove2.me/submissions/3958c241-4602-40d9-8171-2ea6edff8812

import Mathlib
import Definitions.Def_NetworkControl_UtilityFairness_drift

namespace NetworkControl.UtilityFairness

open MeasureTheory

/-- Closed form of the partial sums `∑_{τ < t} (2τ + 100) = t (t + 99)`. -/
theorem aux_lyo_sum (t : ℕ) :
    ∑ τ ∈ Finset.range t, (2 * (τ : ℝ) + 100) = (t : ℝ) * ((t : ℝ) + 99) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The Cesàro averages of `2τ + 100` are eventually `t + 99`, hence unbounded above. -/
theorem aux_lyo_not_bdd :
    ¬ Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, (2 * (τ : ℝ) + 100)) := by
  apply Filter.not_isBoundedUnder_of_tendsto_atTop
  have h1 : Filter.Tendsto (fun t : ℕ => (t : ℝ) + 99) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with t ht
  rw [aux_lyo_sum]
  have : (t : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  field_simp

end NetworkControl.UtilityFairness

open NetworkControl.UtilityFairness
open MeasureTheory

theorem solution : ¬ (∀
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N K : ℕ} (L : (Fin N → ℝ) → ℝ) (hLnn : ∀ u, 0 ≤ L u)
    (U : ℕ → Ω → Fin N → ℝ) (R : ℕ → Ω → Fin K → ℝ) (g : (Fin K → ℝ) → ℝ) (gstar : ℝ)
    (hgConcave : ConcaveOn ℝ Set.univ g)
    (V ε B : ℝ) (hV : 0 < V) (hε : 0 < ε) (hB : 0 < B)
    (hMeasU : ∀ t : ℕ, ∀ i : Fin N, Measurable (fun ω => U t ω i))
    (hIntegL0 : Integrable (fun ω => L (U 0 ω)) P)
    (hIntegLdrift : ∀ t : ℕ, Integrable (fun ω => L (U (t + 1) ω) - L (U t ω)) P)
    (hIntegG : ∀ t : ℕ, Integrable (fun ω => g (R t ω)) P)
    (hIntegU : ∀ t : ℕ, ∀ i : Fin N, Integrable (fun ω => U t ω i) P)
    (hIntegR : ∀ t : ℕ, ∀ k : Fin K, Integrable (fun ω => R t ω k) P)
    (hdrift : ∀ t : ℕ,
      ((fun ω => drift P L U t ω - V * (P[(fun ω => g (R t ω)) | MeasurableSpace.comap (U t) inferInstance]) ω))
        ≤ᵐ[P] (fun ω => B - ε * ∑ i : Fin N, U t ω i - V * gstar)),
    (Filter.limsup
        (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin N, ∫ ω, U τ ω i ∂P)
        Filter.atTop
      ≤ (B + V * (Filter.limsup
            (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, g (R τ ω) ∂P)
            Filter.atTop
          - gstar)) / ε) ∧
    (Filter.liminf
        (fun t : ℕ => g (fun k : Fin K => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω k ∂P))
        Filter.atTop
      ≥ gstar - B / V)) := by
  intro hall
  -- Counterexample: Ω = Unit, P = δ_(), N = 0, K = 1, L = 0, g v = v 0,
  -- R t = 2t + 100 (deterministic), V = ε = B = 1, g* = 100.
  have hm : ∀ t : ℕ, MeasurableSpace.comap (fun (_ : Unit) (i : Fin 0) => Fin.elim0 i :
      Unit → Fin 0 → ℝ) inferInstance ≤ (inferInstance : MeasurableSpace Unit) := by
    intro t
    exact Measurable.comap_le (Subsingleton.measurable)
  have hconc : ConcaveOn ℝ Set.univ (fun v : Fin 1 → ℝ => v 0) :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).concaveOn convex_univ
  have key := @hall Unit _ (Measure.dirac ()) _ 0 1 (fun _ => 0) (fun _ => le_refl 0)
    (fun _ _ i => Fin.elim0 i) (fun t _ _ => 2 * (t : ℝ) + 100) (fun v => v 0) 100 hconc
    1 1 1 one_pos one_pos one_pos
    (fun _ i => Fin.elim0 i) (integrable_const _) (fun _ => integrable_const _)
    (fun _ => integrable_const _) (fun _ i => Fin.elim0 i) (fun _ _ => integrable_const _)
    (by
      intro t
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have h1 : drift (Measure.dirac ()) (fun _ => (0 : ℝ))
          (fun (_ : ℕ) (_ : Unit) (i : Fin 0) => Fin.elim0 i) t = 0 := by
        unfold drift
        simp only [sub_self]
        exact condExp_const (hm t) (0 : ℝ)
      have h2 : (Measure.dirac ())[(fun _ : Unit => 2 * (t : ℝ) + 100) |
          MeasurableSpace.comap (fun (_ : Unit) (i : Fin 0) => Fin.elim0 i :
            Unit → Fin 0 → ℝ) inferInstance] = fun _ => 2 * (t : ℝ) + 100 :=
        condExp_const (hm t) _
      simp only [h1, h2, Pi.zero_apply]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero]
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      linarith)
  have ha := key.1
  have hlhs : Filter.limsup
      (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, ∑ i : Fin 0,
        ∫ ω, (fun (_ : ℕ) (_ : Unit) (i : Fin 0) => (Fin.elim0 i : ℝ)) τ ω i ∂(Measure.dirac ()))
      Filter.atTop = 0 := by
    simp
  have hg : (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t,
      ∫ ω, (fun v : Fin 1 → ℝ => v 0) ((fun (t : ℕ) (_ : Unit) (_ : Fin 1) =>
        2 * (t : ℝ) + 100) τ ω) ∂(Measure.dirac ())) =
      (fun t : ℕ => (1 / (t : ℝ)) * ∑ τ ∈ Finset.range t, (2 * (τ : ℝ) + 100)) := by
    funext t
    simp
  rw [hlhs, hg, Real.limsup_of_not_isBoundedUnder aux_lyo_not_bdd] at ha
  norm_num at ha
