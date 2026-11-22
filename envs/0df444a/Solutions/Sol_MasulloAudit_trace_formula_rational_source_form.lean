-- Prove2me | solution 1 for MasulloAudit.trace_formula_rational_source_form
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:16:34.964819+00:00
-- url     : https://prove2.me/submissions/3666749a-5b2a-439d-abd7-3292db0de68c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_formula_inversion_even
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
import Theorems.Thm_MasulloRH_trace_formula_inversion_odd
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open MasulloRH MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem test_inv {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    IsRationalTraceTest (fun t => φ t⁻¹) := by
  let K := Inv.inv '' tsupport φ
  have hK : IsCompact K := hφ.2.1.image_of_continuousOn
    (continuousOn_id.inv₀ fun x hx => ne_of_gt (hφ.2.2.1 hx))
  have hs : tsupport (fun t => φ t⁻¹) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    exact ⟨x⁻¹, subset_tsupport φ hx, inv_inv x⟩
  have hpos : K ⊆ Ioi (0 : ℝ) := by
    rintro x ⟨y, hy, rfl⟩
    change 0 < y⁻¹
    exact inv_pos.mpr (show 0 < y from hφ.2.2.1 hy)
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hpos, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (fun t => φ t⁻¹)
    · exact hφ.1.contDiffAt.comp x (contDiffAt_inv ℝ (ne_of_gt (hpos (hs hx))))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hx)
  · simpa using hφ.2.2.2

private theorem test_add {φ ψ : ℝ → ℂ}
    (hφ : IsRationalTraceTest φ) (hψ : IsRationalTraceTest ψ) :
    IsRationalTraceTest (fun t => φ t + ψ t) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
    (tsupport_add φ ψ).trans (union_subset hφ.2.2.1 hψ.2.2.1), ?_⟩
  simp [hφ.2.2.2, hψ.2.2.2]

private theorem test_sub {φ ψ : ℝ → ℂ}
    (hφ : IsRationalTraceTest φ) (hψ : IsRationalTraceTest ψ) :
    IsRationalTraceTest (fun t => φ t - ψ t) := by
  refine ⟨hφ.1.sub hψ.1, hφ.2.1.sub hψ.2.1,
    (tsupport_sub φ ψ).trans (union_subset hφ.2.2.1 hψ.2.2.1), ?_⟩
  simp [hφ.2.2.2, hψ.2.2.2]

private theorem test_half {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    IsRationalTraceTest (fun t => φ t / 2) := by
  refine ⟨hφ.1.div_const 2, ?_, ?_, by simp [hφ.2.2.2]⟩
  · exact hφ.2.1.comp_left (g := fun z : ℂ => z / 2) (by simp)
  · exact (tsupport_comp_subset (g := fun z : ℂ => z / 2) (by simp) φ).trans hφ.2.2.1

private theorem test_mellin {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  let f := fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t
  have hs : tsupport f ⊆ tsupport φ := tsupport_mul_subset_right
  have hc : Continuous f := by
    apply continuous_of_tsupport
    intro t ht
    have hp : 0 < t := hφ.2.2.1 (hs ht)
    exact (Complex.continuousAt_ofReal_cpow_const t (s - 1)
      (Or.inr (ne_of_gt hp))).mul hφ.1.continuous.continuousAt
  have hk : HasCompactSupport f := hφ.2.1.mul_left
  exact (hc.integrable_of_hasCompactSupport hk).integrableOn

-- Linearity combines the even case with the already proved odd case.
theorem trace_formula_of_inversion_even
    (H : ∀ (α : ℝ), 0 < α → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      (∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ)
    (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  let e : ℝ → ℂ := fun t => (φ t + φ t⁻¹) / 2
  let o : ℝ → ℂ := fun t => φ t - e t
  have he : IsRationalTraceTest e := test_half (test_add hφ (test_inv hφ))
  have ho : IsRationalTraceTest o := test_sub hφ he
  have heven : ∀ t : ℝ, 0 < t → e t⁻¹ = e t := by
    intro t _; dsimp [e]; rw [inv_inv, add_comm]
  have hodd : ∀ t : ℝ, 0 < t → o t⁻¹ = -o t := by
    intro t _; dsimp [o, e]; rw [inv_inv]; ring
  obtain ⟨heI, heP, heZ, heq⟩ := H α hα e he heven
  obtain ⟨hoI, hoP, hoZ, hoq⟩ := trace_formula_inversion_odd α hα o ho hodd
  have hdecomp : φ = fun t => e t + o t := by funext t; dsimp [o]; ring
  have hI : realTraceIntegrand φ = fun t => realTraceIntegrand e t + realTraceIntegrand o t := by
    funext t; simp only [realTraceIntegrand, hdecomp]; ring
  have hP : primePowerTraceTerm φ = fun i => primePowerTraceTerm e i + primePowerTraceTerm o i := by
    funext i; simp only [primePowerTraceTerm, hdecomp]; ring
  have hM (s : ℂ) : mellin φ s = mellin e s + mellin o s := by
    rw [hdecomp]
    exact (hasMellin_add (test_mellin he s) (test_mellin ho s)).2
  have hZ : zetaTraceTerm φ α = fun ρ => zetaTraceTerm e α ρ + zetaTraceTerm o α ρ := by
    funext ρ; simp only [zetaTraceTerm, hM, mul_add]
  refine ⟨hI ▸ heI.add hoI, hP ▸ heP.add hoP, hZ ▸ heZ.add hoZ, ?_⟩
  rw [hI, hP, hZ, integral_add heI hoI, heP.tsum_add hoP, heZ.tsum_add hoZ,
    hM, hM]
  linear_combination heq + hoq

local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (zetaTraceTerm φ α) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  obtain ⟨hi, hp, _hfinite, hsum, _hpp, hgeo⟩ :=
    MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
  obtain ⟨_hi, _hp, hz, heq⟩ :=
    trace_formula_of_inversion_even MasulloRH.trace_formula_inversion_even α hα φ hφ
  exact ⟨hi, hp, hsum, hz, hgeo.trans heq⟩
