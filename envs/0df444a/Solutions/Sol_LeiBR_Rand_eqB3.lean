-- Prove2me | solution 1 for LeiBR.Rand.eqB3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:54:40.995801+00:00
-- url     : https://prove2.me/submissions/938fbd09-3bda-4a40-9dbe-88e8a270b4bd

import Mathlib
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants

open MeasureTheory ProbabilityTheory

open LeiBR.Rand in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (p : Fin N → ℝ) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1)
    (χ : Fin N → ℕ → Ω → ℕ) (hχ1 : ∀ i k ω, χ i k ω ≤ 1) (hχ_meas : ∀ i k, Measurable (χ i k))
    (hχ_prob : ∀ i k, P {ω | χ i k ω = 1} = ENNReal.ofReal (p i))
    (hχ_iid : ∀ i, iIndepFun (fun k => χ i k) P)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (i : Fin N) (k : ℕ) :
    ∫ ω, η ^ (2 * beta χ i k ω) ∂P = (1 - p i * (1 - η ^ 2)) ^ k ∧
    (1 - p i * (1 - η ^ 2)) ^ k ≤ (1 - pmin p * (1 - η ^ 2)) ^ k ∧
    (1 - pmin p * (1 - η ^ 2)) ^ k = etatil p η ^ (2 * k) := by
  have hη2 : 0 < η ^ 2 := by positivity
  have hη21 : η ^ 2 < 1 := by nlinarith
  have hpmin : pmin p ≤ p i := ciInf_le (Set.finite_range p).bddBelow i
  -- one factor
  have hfac : ∀ l, ∫ ω, (η ^ 2) ^ (χ i l ω) ∂P = 1 - p i * (1 - η ^ 2) := by
    intro l
    have hms : MeasurableSet {ω | χ i l ω = 1} := hχ_meas i l (measurableSet_singleton 1)
    have hpt : ∀ ω, (η ^ 2) ^ (χ i l ω) =
        Set.indicator {ω | χ i l ω = 1} (fun _ => η ^ 2 - 1) ω + 1 := by
      intro ω
      by_cases h : χ i l ω = 1
      · rw [Set.indicator_of_mem (show ω ∈ {ω | χ i l ω = 1} from h), h]
        ring
      · have h0 : χ i l ω = 0 := by have := hχ1 i l ω; omega
        rw [Set.indicator_of_notMem (show ω ∉ {ω | χ i l ω = 1} from h), h0]
        ring
    simp_rw [hpt]
    rw [integral_add ((integrable_const _).indicator hms) (integrable_const _),
      integral_indicator_const _ hms, integral_const]
    have hreal : P.real {ω | χ i l ω = 1} = p i := by
      rw [measureReal_def, hχ_prob, ENNReal.toReal_ofReal (hp i).le]
    rw [hreal]
    simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hrw : ∀ ω, η ^ (2 * beta χ i k ω) = ∏ l : Fin k, (η ^ 2) ^ (χ i l ω) := by
      intro ω
      rw [LeiBR.Rand.beta, pow_mul, ← Finset.prod_pow_eq_pow_sum, Finset.prod_range (fun l => (η ^ 2) ^ χ i l ω)]
    simp_rw [hrw]
    have hind : iIndepFun (fun l : Fin k => χ i l) P :=
      (hχ_iid i).precomp (g := fun l : Fin k => (l : ℕ)) Fin.val_injective
    rw [hind.integral_fun_prod_comp (f := fun _ c => (η ^ 2) ^ c)
      (fun l => (hχ_meas i l).aemeasurable)
      (fun l => (measurable_of_countable _).aestronglyMeasurable)]
    simp only [hfac]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · apply pow_le_pow_left₀
    · nlinarith [hp1 i]
    · nlinarith
  · unfold etatil
    have hnn : 0 ≤ 1 - pmin p * (1 - η ^ 2) := by nlinarith [hp1 i]
    rw [pow_mul, Real.sq_sqrt hnn]
