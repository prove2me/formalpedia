-- Prove2me | solution 1 for MDPFinance.IndifferencePricing.one_period_indifference_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:22:59.667387+00:00
-- url     : https://prove2.me/submissions/50686903-1d18-4e08-8d3d-b1ab2a6156b3

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_OnePeriodMarket

open MeasureTheory ProbabilityTheory
open MDPFinance.IndifferencePricing

namespace OPIAux

theorem integral_four {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E1 E2 E3 E4 : Set Ω) (m1 : MeasurableSet E1) (m2 : MeasurableSet E2) (m3 : MeasurableSet E3)
    (m4 : MeasurableSet E4) (d12 : Disjoint E1 E2) (d13 : Disjoint E1 E3) (d14 : Disjoint E1 E4)
    (d23 : Disjoint E2 E3) (d24 : Disjoint E2 E4) (d34 : Disjoint E3 E4)
    (p1 p2 p3 p4 : ℝ) (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)
    (hsum : p1 + p2 + p3 + p4 = 1)
    (h1 : μ E1 = ENNReal.ofReal p1) (h2 : μ E2 = ENNReal.ofReal p2)
    (h3 : μ E3 = ENNReal.ofReal p3) (h4 : μ E4 = ENNReal.ofReal p4)
    (f : Ω → ℝ) (c1 c2 c3 c4 : ℝ) (hf1 : ∀ ω ∈ E1, f ω = c1) (hf2 : ∀ ω ∈ E2, f ω = c2)
    (hf3 : ∀ ω ∈ E3, f ω = c3) (hf4 : ∀ ω ∈ E4, f ω = c4) :
    ∫ ω, f ω ∂μ = p1 * c1 + p2 * c2 + p3 * c3 + p4 * c4 := by
  have hU : μ (E1 ∪ E2 ∪ E3 ∪ E4) = 1 := by
    rw [measure_union (Disjoint.union_left (Disjoint.union_left d14 d24) d34) m4,
      measure_union (Disjoint.union_left d13 d23) m3, measure_union d12 m2, h1, h2, h3, h4,
      ← ENNReal.ofReal_add hp1 hp2, ← ENNReal.ofReal_add (by positivity) hp3,
      ← ENNReal.ofReal_add (by positivity) hp4, hsum, ENNReal.ofReal_one]
  have hmU : MeasurableSet (E1 ∪ E2 ∪ E3 ∪ E4) := ((m1.union m2).union m3).union m4
  have hS : μ (E1 ∪ E2 ∪ E3 ∪ E4)ᶜ = 0 := by
    rw [measure_compl hmU (measure_ne_top _ _), hU, measure_univ, tsub_self]
  let g : Ω → ℝ := E1.indicator (fun _ => c1) + E2.indicator (fun _ => c2) +
    E3.indicator (fun _ => c3) + E4.indicator (fun _ => c4)
  have hfg : f =ᵐ[μ] g := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hS
    intro ω hne hmem
    apply hne
    simp only [g, Pi.add_apply]
    rcases hmem with ((hm | hm) | hm) | hm
    · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.disjoint_left.1 d12 hm),
        Set.indicator_of_notMem (Set.disjoint_left.1 d13 hm),
        Set.indicator_of_notMem (Set.disjoint_left.1 d14 hm), hf1 ω hm]; ring
    · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.disjoint_right.1 d12 hm),
        Set.indicator_of_notMem (Set.disjoint_left.1 d23 hm),
        Set.indicator_of_notMem (Set.disjoint_left.1 d24 hm), hf2 ω hm]; ring
    · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.disjoint_right.1 d13 hm),
        Set.indicator_of_notMem (Set.disjoint_right.1 d23 hm),
        Set.indicator_of_notMem (Set.disjoint_left.1 d34 hm), hf3 ω hm]; ring
    · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem (Set.disjoint_right.1 d14 hm),
        Set.indicator_of_notMem (Set.disjoint_right.1 d24 hm),
        Set.indicator_of_notMem (Set.disjoint_right.1 d34 hm), hf4 ω hm]; ring
  rw [integral_congr_ae hfg]
  have i1 := (integrable_const c1).indicator m1 (μ := μ)
  have i2 := (integrable_const c2).indicator m2 (μ := μ)
  have i3 := (integrable_const c3).indicator m3 (μ := μ)
  have i4 := (integrable_const c4).indicator m4 (μ := μ)
  simp only [g]
  rw [integral_add' ((i1.add i2).add i3) i4, integral_add' (i1.add i2) i3, integral_add' i1 i2,
    integral_indicator_const _ m1, integral_indicator_const _ m2, integral_indicator_const _ m3,
    integral_indicator_const _ m4]
  simp only [measureReal_def, h1, h2, h3, h4, ENNReal.toReal_ofReal hp1, ENNReal.toReal_ofReal hp2,
    ENNReal.toReal_ofReal hp3, ENNReal.toReal_ofReal hp4, smul_eq_mul]

theorem sup_formula (E K1 K2 γ u d : ℝ) (hE : 0 < E) (hK1 : 0 < K1) (hK2 : 0 < K2) (hγ : 0 < γ)
    (hd1 : d < 1) (h1u : 1 < u) :
    let q := (1 - d) / (u - d)
    (⨆ a : ℝ, -E * (K1 * Real.exp (-γ * a * (u - 1)) + K2 * Real.exp (-γ * a * (d - 1)))) =
      -E * Real.exp (q * Real.log (K1 / q) + (1 - q) * Real.log (K2 / (1 - q))) := by
  intro q
  have hud : 0 < u - d := by linarith
  have hq0 : 0 < q := div_pos (by linarith) hud
  have hq1 : q < 1 := (div_lt_one hud).2 (by linarith)
  have h1q : 0 < 1 - q := by linarith
  have hkey : q * (u - 1) + (1 - q) * (d - 1) = 0 := by
    simp only [q]; field_simp; ring
  set L := q * Real.log (K1 / q) + (1 - q) * Real.log (K2 / (1 - q)) with hL
  have hsplit : ∀ a : ℝ, K1 * Real.exp (-γ * a * (u - 1)) + K2 * Real.exp (-γ * a * (d - 1)) =
      q * Real.exp (Real.log (K1 / q) + -γ * a * (u - 1)) +
        (1 - q) * Real.exp (Real.log (K2 / (1 - q)) + -γ * a * (d - 1)) := by
    intro a
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hK1 hq0), Real.exp_log (div_pos hK2 h1q)]
    field_simp
  have hlow : ∀ a : ℝ, Real.exp L ≤
      K1 * Real.exp (-γ * a * (u - 1)) + K2 * Real.exp (-γ * a * (d - 1)) := by
    intro a
    rw [hsplit a]
    have := convexOn_exp.2 (Set.mem_univ (Real.log (K1 / q) + -γ * a * (u - 1)))
      (Set.mem_univ (Real.log (K2 / (1 - q)) + -γ * a * (d - 1))) hq0.le h1q.le (by ring)
    simp only [smul_eq_mul] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    rw [hL]
    linear_combination (γ * a) * hkey
  set a0 := (Real.log (K1 / q) - Real.log (K2 / (1 - q))) / (γ * (u - d)) with ha0
  have heq : K1 * Real.exp (-γ * a0 * (u - 1)) + K2 * Real.exp (-γ * a0 * (d - 1)) = Real.exp L := by
    rw [hsplit a0]
    have hXY : Real.log (K1 / q) + -γ * a0 * (u - 1) = Real.log (K2 / (1 - q)) + -γ * a0 * (d - 1) := by
      have hc : γ * a0 * (u - d) = Real.log (K1 / q) - Real.log (K2 / (1 - q)) := by
        rw [ha0]; field_simp
      linear_combination -hc
    rw [hXY, ← add_mul, show q + (1 - q) = 1 by ring, one_mul]
    congr 1
    rw [hL]
    linear_combination (-q) * hXY - (γ * a0) * hkey
  apply le_antisymm
  · apply ciSup_le
    intro a
    have := hlow a
    nlinarith
  · have hbdd : BddAbove (Set.range fun a : ℝ =>
        -E * (K1 * Real.exp (-γ * a * (u - 1)) + K2 * Real.exp (-γ * a * (d - 1)))) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨a, rfl⟩
      have : 0 < K1 * Real.exp (-γ * a * (u - 1)) + K2 * Real.exp (-γ * a * (d - 1)) := by positivity
      nlinarith
    refine le_trans ?_ (le_ciSup hbdd a0)
    rw [heq]

theorem V0_eq {Ω : Type*} [MeasurableSpace Ω] (M : OnePeriodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ)
    (x s ŝ : ℝ) :
    M.V0 h x s ŝ = ⨆ a : ℝ, -Real.exp (-M.γ * x) * (M.hu h s ŝ * Real.exp (-M.γ * a * (M.u - 1)) +
      M.hd h s ŝ * Real.exp (-M.γ * a * (M.d - 1))) := by
  haveI := M.isProb
  unfold OnePeriodIndifferenceMarket.V0
  congr 1; funext a
  have hu_ne_d : M.u ≠ M.d := by linarith [M.hd1, M.h1u]
  have huh : M.uhat ≠ M.dhat := ne_of_gt M.hdhat_uhat
  obtain ⟨hp1, hp2, hp3, hp4⟩ := M.hp_pos
  have ms : ∀ r r', MeasurableSet {ω | M.Rtilde ω = r ∧ M.Rhat ω = r'} := fun r r' =>
    (M.hRtilde_meas (measurableSet_singleton r)).inter (M.hRhat_meas (measurableSet_singleton r'))
  have dj : ∀ r1 r1' r2 r2', (r1 ≠ r2 ∨ r1' ≠ r2') →
      Disjoint {ω | M.Rtilde ω = r1 ∧ M.Rhat ω = r1'} {ω | M.Rtilde ω = r2 ∧ M.Rhat ω = r2'} := by
    intro r1 r1' r2 r2' hne
    rw [Set.disjoint_left]
    rintro ω ⟨h1, h1'⟩ ⟨h2, h2'⟩
    rcases hne with hne | hne
    · exact hne (h1.symm.trans h2)
    · exact hne (h1'.symm.trans h2')
  rw [integral_four M.measIP _ _ _ _ (ms _ _) (ms _ _) (ms _ _) (ms _ _)
    (dj _ _ _ _ (Or.inr huh)) (dj _ _ _ _ (Or.inl hu_ne_d)) (dj _ _ _ _ (Or.inl hu_ne_d))
    (dj _ _ _ _ (Or.inl hu_ne_d)) (dj _ _ _ _ (Or.inl hu_ne_d)) (dj _ _ _ _ (Or.inr huh))
    M.p1 M.p2 M.p3 M.p4 hp1.le hp2.le hp3.le hp4.le M.hp_sum M.hlaw1 M.hlaw2 M.hlaw3 M.hlaw4
    (fun ω => -Real.exp (-M.γ * x - M.γ * a * (M.Rtilde ω - 1) +
      M.γ * h (s * M.Rtilde ω) (ŝ * M.Rhat ω)))
    (-Real.exp (-M.γ * x - M.γ * a * (M.u - 1) + M.γ * h (s * M.u) (ŝ * M.uhat)))
    (-Real.exp (-M.γ * x - M.γ * a * (M.u - 1) + M.γ * h (s * M.u) (ŝ * M.dhat)))
    (-Real.exp (-M.γ * x - M.γ * a * (M.d - 1) + M.γ * h (s * M.d) (ŝ * M.uhat)))
    (-Real.exp (-M.γ * x - M.γ * a * (M.d - 1) + M.γ * h (s * M.d) (ŝ * M.dhat)))
    (fun ω hω => by rw [hω.1, hω.2]) (fun ω hω => by rw [hω.1, hω.2])
    (fun ω hω => by rw [hω.1, hω.2]) (fun ω hω => by rw [hω.1, hω.2])]
  simp only [OnePeriodIndifferenceMarket.hu, OnePeriodIndifferenceMarket.hd,
    OnePeriodIndifferenceMarket.htilde, Real.exp_add, Real.exp_sub]
  have e1 : ∀ t : ℝ, Real.exp (-M.γ * a * t) = (Real.exp (M.γ * a * t))⁻¹ := by
    intro t; rw [← Real.exp_neg]; ring_nf
  rw [e1, e1]
  ring

end OPIAux

open OPIAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (M : OnePeriodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ) (hh : ∀ s1 ŝ1, 0 ≤ h s1 ŝ1)
    (x s ŝ : ℝ) (hs : 0 < s) (hŝ : 0 < ŝ) :
    M.V0 h x s ŝ = -Real.exp (-M.γ * x) * (M.hu h s ŝ / M.qrn) ^ M.qrn *
        (M.hd h s ŝ / (1 - M.qrn)) ^ (1 - M.qrn) ∧
      M.IsIndifferencePrice h s ŝ
        (M.qrn / M.γ * Real.log (M.hu h s ŝ / (M.p1 + M.p2)) +
          (1 - M.qrn) / M.γ * Real.log (M.hd h s ŝ / (M.p3 + M.p4))) := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := M.hp_pos
  have hud : 0 < M.u - M.d := by linarith [M.hd1, M.h1u]
  have hq0 : 0 < M.qrn := div_pos (by linarith [M.hd1]) hud
  have hq1 : M.qrn < 1 := (div_lt_one hud).2 (by linarith [M.h1u])
  have h1q : 0 < 1 - M.qrn := by linarith
  have hpos : ∀ g : ℝ → ℝ → ℝ, 0 < M.hu g s ŝ ∧ 0 < M.hd g s ŝ := by
    intro g
    simp only [OnePeriodIndifferenceMarket.hu, OnePeriodIndifferenceMarket.hd,
      OnePeriodIndifferenceMarket.htilde]
    constructor <;> positivity
  -- closed form for any claim
  have closed : ∀ (g : ℝ → ℝ → ℝ) (y : ℝ), M.V0 g y s ŝ = -Real.exp (-M.γ * y) *
      Real.exp (M.qrn * Real.log (M.hu g s ŝ / M.qrn) +
        (1 - M.qrn) * Real.log (M.hd g s ŝ / (1 - M.qrn))) := by
    intro g y
    rw [V0_eq]
    exact sup_formula _ _ _ _ _ _ (Real.exp_pos _) (hpos g).1 (hpos g).2 M.hγ M.hd1 M.h1u
  have hrp : ∀ (g : ℝ → ℝ → ℝ), (M.hu g s ŝ / M.qrn) ^ M.qrn *
      (M.hd g s ŝ / (1 - M.qrn)) ^ (1 - M.qrn) = Real.exp (M.qrn * Real.log (M.hu g s ŝ / M.qrn) +
        (1 - M.qrn) * Real.log (M.hd g s ŝ / (1 - M.qrn))) := by
    intro g
    rw [Real.rpow_def_of_pos (div_pos (hpos g).1 hq0), Real.rpow_def_of_pos (div_pos (hpos g).2 h1q),
      ← Real.exp_add]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [closed, mul_assoc, hrp]
  · intro y
    rw [closed, closed]
    have hu0 : M.hu (fun _ _ => 0) s ŝ = M.p1 + M.p2 := by
      simp [OnePeriodIndifferenceMarket.hu, OnePeriodIndifferenceMarket.htilde]
    have hd0 : M.hd (fun _ _ => 0) s ŝ = M.p3 + M.p4 := by
      simp [OnePeriodIndifferenceMarket.hd, OnePeriodIndifferenceMarket.htilde]
    rw [hu0, hd0]
    simp only [neg_mul, ← Real.exp_add, neg_inj]
    congr 1
    have hγ := M.hγ
    have a1 := (hpos h).1
    have a2 := (hpos h).2
    rw [Real.log_div a1.ne' hq0.ne', Real.log_div a2.ne' h1q.ne',
      Real.log_div (by positivity : M.p1 + M.p2 ≠ 0) hq0.ne',
      Real.log_div (by positivity : M.p3 + M.p4 ≠ 0) h1q.ne',
      Real.log_div a1.ne' (by positivity : M.p1 + M.p2 ≠ 0),
      Real.log_div a2.ne' (by positivity : M.p3 + M.p4 ≠ 0)]
    field_simp
    ring
