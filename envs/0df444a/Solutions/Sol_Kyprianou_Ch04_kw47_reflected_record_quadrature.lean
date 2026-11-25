-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_reflected_record_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:20:07.458617+00:00
-- url     : https://prove2.me/submissions/0bd810b7-2b8c-4a1b-a04f-a80edaf5a1f2

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_real_path
import Theorems.Thm_Kyprianou_Ch04_kw47_right_grid_integral_convergence
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The right-endpoint reflected exponential quadrature against
the record measure converges to the record increment. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      (runningSup L (u n (i+1)) w - runningSup L (u n i) w) *
        Z (u n (i+1))) atTop
        (nhds (runningSup L b w - runningSup L a w)) := by
  dsimp only
  let Z : NNReal → Real := fun r =>
    Real.exp (-alpha * (runningSup L r w - L.X r w))
  let f : Real → Real := fun r => Z r.toNNReal
  let mu := dividendMeasure (runningSup L) w
  obtain ⟨hf,hB,hRight⟩ :=
    Kyprianou.Ch04.kw47_reflected_exp_real_path L alpha hAlpha w
  have hmono (n : Nat) : Monotone (fun i => (u n i : Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  have h0r (n : Nat) : (u n 0 : Real) = (a : Real) := by rw [h0 n]
  have hNr (n : Nat) : (u n (N n) : Real) = (b : Real) := by rw [hN n]
  have hmass (r s : NNReal) (hrs : r ≤ s) :
      (mu (Ioc (r:Real) (s:Real))).toReal =
        runningSup L s w - runningSup L r w := by
    dsimp only [mu]
    rw [runningSup_dividendMeasure_Ioc_eq_record_increment,
      Real.toNNReal_coe, Real.toNNReal_coe, ENNReal.toReal_ofReal]
    exact sub_nonneg.mpr ((runningSup_monotone_and_path_le L w).1 hrs)
  letI : IsFiniteMeasure (mu.restrict (Ioc (a:Real) (b:Real))) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        dsimp only [mu]
        rw [runningSup_dividendMeasure_Ioc_eq_record_increment]
        exact ENNReal.ofReal_lt_top⟩
  have hconv := Kyprianou.Ch04.kw47_right_grid_integral_convergence
    mu (a:Real) (b:Real) f 1 hf hB hRight
    (fun n i => (u n i : Real)) N hmono h0r hNr delta hDelta hMesh
  let C : Set Real := {s | 0 ≤ s ∧
    L.X s.toNNReal w < runningSup L s.toNNReal w}
  have hNull : mu C = 0 := Kyprianou.Ch04.kw47_runningSup_contact_measure L w
  have hAe : ∀ᵐ s ∂mu, s ∉ C := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hNull
  have hContact :
      (∫ s in Ioc (a:Real) (b:Real), f s ∂mu) =
      (∫ _s in Ioc (a:Real) (b:Real), (1:Real) ∂mu) := by
    apply integral_congr_ae
    have hAeR := ae_restrict_le (s := Ioc (a:Real) (b:Real)) hAe
    filter_upwards [hAeR, ae_restrict_mem measurableSet_Ioc] with s hs hIn
    have hLe := (runningSup_monotone_and_path_le L w).2 s.toNNReal
    have hNot : ¬ L.X s.toNNReal w < runningSup L s.toNNReal w := by
      intro hLt
      exact hs ⟨(NNReal.coe_nonneg a).trans hIn.1.le, hLt⟩
    have heq := le_antisymm (le_of_not_gt hNot) hLe
    simp [f,Z,heq]
  have hTarget : (∫ s in Ioc (a:Real) (b:Real), f s ∂mu) =
        runningSup L b w - runningSup L a w := by
    rw [hContact, integral_const]
    simp only [Measure.real_def, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, smul_eq_mul, mul_one]
    exact hmass a b hab
  have hcell (n i : Nat) := hmass (u n i) (u n (i+1)) (hu n (Nat.le_succ i))
  simpa only [hcell, hTarget, f, Z, Real.toNNReal_coe] using hconv
