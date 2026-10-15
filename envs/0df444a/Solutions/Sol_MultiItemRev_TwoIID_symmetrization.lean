-- Prove2me | solution 1 for MultiItemRev.TwoIID.symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-15T09:58:35.621754+00:00
-- url     : https://prove2.me/submissions/4a55f3ae-2ead-4c11-b999-9eb0bb138e7d

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal BigOperators
open MultiItemRev.TwoIID

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (M : MultiItemRev.Decomp.Mechanism (Fin 2)) (hM : IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M) :
    IsAdmissible (symmetrize M) ∧ MultiItemRev.Decomp.IsNPT (symmetrize M) ∧
      IsSymmetric (symmetrize M) ∧
      expRevenue (Measure.pi (fun _ : Fin 2 => ν)) (symmetrize M) =
        expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M := by
  obtain ⟨⟨hFeas, hIC, hIR, hMeas⟩, hNPT⟩ := hM
  -- Basic unfolding facts for `symmetrize` and `swap2`.
  have hq : ∀ (x : Fin 2 → ℝ≥0) (i : Fin 2),
      (symmetrize M).q x i = (M.q x i + M.q (swap2 x) (Equiv.swap 0 1 i)) / 2 :=
    fun _ _ => rfl
  have hs : ∀ (x : Fin 2 → ℝ≥0),
      (symmetrize M).s x = (M.s x + M.s (swap2 x)) / 2 :=
    fun _ => rfl
  have hswap_invol : ∀ (x : Fin 2 → ℝ≥0), swap2 (swap2 x) = x := by
    intro x
    funext i
    show x (Equiv.swap 0 1 (Equiv.swap 0 1 i)) = x i
    rw [Equiv.swap_apply_self]
  have hmeas_swap2 : Measurable swap2 :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (Equiv.swap 0 1 i))
  -- The symmetrized allocation sum is the average of the two allocation sums.
  have hsum : ∀ (y x : Fin 2 → ℝ≥0),
      ∑ i, (symmetrize M).q y i * (x i : ℝ) =
        ((∑ i, M.q y i * (x i : ℝ)) +
          (∑ i, M.q (swap2 y) i * ((swap2 x) i : ℝ))) / 2 := by
    intro y x
    have hpt : ∀ i : Fin 2, (symmetrize M).q y i * (x i : ℝ) =
        (M.q y i * (x i : ℝ) + M.q (swap2 y) (Equiv.swap 0 1 i) * (x i : ℝ)) / 2 := by
      intro i
      rw [hq]
      ring
    have hre : (∑ i, M.q (swap2 y) (Equiv.swap 0 1 i) * (x i : ℝ)) =
        ∑ i, M.q (swap2 y) i * ((swap2 x) i : ℝ) := by
      calc (∑ i, M.q (swap2 y) (Equiv.swap 0 1 i) * (x i : ℝ))
          = ∑ i, (fun j => M.q (swap2 y) j * ((swap2 x) j : ℝ)) (Equiv.swap 0 1 i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [swap2, Function.comp_apply, Equiv.swap_apply_self]
        _ = ∑ i, M.q (swap2 y) i * ((swap2 x) i : ℝ) :=
          (Equiv.sum_comp (Equiv.swap (0 : Fin 2) 1)
            (fun j => M.q (swap2 y) j * ((swap2 x) j : ℝ)))
    calc ∑ i, (symmetrize M).q y i * (x i : ℝ)
        = ∑ i, (M.q y i * (x i : ℝ) +
            M.q (swap2 y) (Equiv.swap 0 1 i) * (x i : ℝ)) / 2 :=
          Finset.sum_congr rfl (fun i _ => hpt i)
      _ = ((∑ i, M.q y i * (x i : ℝ)) +
            (∑ i, M.q (swap2 y) (Equiv.swap 0 1 i) * (x i : ℝ))) / 2 := by
          rw [← Finset.sum_div, ← Finset.sum_add_distrib]
      _ = ((∑ i, M.q y i * (x i : ℝ)) +
            (∑ i, M.q (swap2 y) i * ((swap2 x) i : ℝ))) / 2 := by
          rw [hre]
  -- The buyer payoff of the symmetrized mechanism is the average of the two payoffs.
  have hBP : ∀ (x : Fin 2 → ℝ≥0),
      MultiItemRev.Decomp.buyerPayoff (symmetrize M) x =
        (MultiItemRev.Decomp.buyerPayoff M x +
          MultiItemRev.Decomp.buyerPayoff M (swap2 x)) / 2 := by
    intro x
    show (∑ i, (symmetrize M).q x i * (x i : ℝ)) - (symmetrize M).s x =
      (((∑ i, M.q x i * (x i : ℝ)) - M.s x) +
        ((∑ i, M.q (swap2 x) i * ((swap2 x) i : ℝ)) - M.s (swap2 x))) / 2
    rw [hsum x x, hs]
    ring
  -- The product measure is invariant under swapping the two coordinates.
  have hswap_int : ∀ F : (Fin 2 → ℝ≥0) → ℝ≥0∞, Measurable F →
      ∫⁻ x, F (swap2 x) ∂(Measure.pi (fun _ : Fin 2 => ν)) =
        ∫⁻ x, F x ∂(Measure.pi (fun _ : Fin 2 => ν)) := by
    intro F hF
    have hmp : MeasurePreserving
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℝ≥0) (Equiv.swap (0 : Fin 2) 1))
        (Measure.pi (fun _ : Fin 2 => ν)) (Measure.pi (fun _ : Fin 2 => ν)) :=
      MeasureTheory.measurePreserving_piCongrLeft (μ := fun _ : Fin 2 => ν)
        (f := Equiv.swap (0 : Fin 2) 1)
    have h := hmp.lintegral_comp hF
    have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℝ≥0)
        (Equiv.swap (0 : Fin 2) 1)) = swap2 := by
      funext x
      funext i
      have h2 := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap (0 : Fin 2) 1)
        (β := fun _ : Fin 2 => ℝ≥0) x (Equiv.swap 0 1 i)
      rw [Equiv.swap_apply_self] at h2
      exact h2
    rw [hfun] at h
    exact h
  -- Revenue: the negative parts vanish by NPT; the positive part averages two
  -- equal integrals (the second by swap-invariance).
  have hmeas1 : Measurable (fun x : Fin 2 → ℝ≥0 => ENNReal.ofReal (M.s x)) :=
    ENNReal.measurable_ofReal.comp hMeas
  have hmeas2 : Measurable (fun x : Fin 2 → ℝ≥0 => ENNReal.ofReal (M.s (swap2 x))) :=
    ENNReal.measurable_ofReal.comp (hMeas.comp hmeas_swap2)
  have hneg1 : (∫⁻ x, ENNReal.ofReal (-(symmetrize M).s x)
      ∂(Measure.pi (fun _ : Fin 2 => ν))) = 0 := by
    have h0 : ∀ x : Fin 2 → ℝ≥0, ENNReal.ofReal (-(symmetrize M).s x) = 0 := by
      intro x
      rw [ENNReal.ofReal_eq_zero, hs]
      have h1 := hNPT x
      have h2 := hNPT (swap2 x)
      linarith
    simp only [h0, MeasureTheory.lintegral_zero]
  have hneg2 : (∫⁻ x, ENNReal.ofReal (-M.s x)
      ∂(Measure.pi (fun _ : Fin 2 => ν))) = 0 := by
    have h0 : ∀ x : Fin 2 → ℝ≥0, ENNReal.ofReal (-M.s x) = 0 :=
      fun x => ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (hNPT x))
    simp only [h0, MeasureTheory.lintegral_zero]
  have hpos : (∫⁻ x, ENNReal.ofReal ((symmetrize M).s x)
      ∂(Measure.pi (fun _ : Fin 2 => ν))) =
      ∫⁻ x, ENNReal.ofReal (M.s x) ∂(Measure.pi (fun _ : Fin 2 => ν)) := by
    have hpt : ∀ x : Fin 2 → ℝ≥0, ENNReal.ofReal ((symmetrize M).s x) =
        (2⁻¹ : ℝ≥0∞) * (ENNReal.ofReal (M.s x) + ENNReal.ofReal (M.s (swap2 x))) := by
      intro x
      rw [hs, ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num),
        ENNReal.ofReal_add (hNPT x) (hNPT (swap2 x)), div_eq_mul_inv,
        ENNReal.ofReal_ofNat]
      ring
    have hmeas_sum : Measurable (fun x : Fin 2 → ℝ≥0 =>
        ENNReal.ofReal (M.s x) + ENNReal.ofReal (M.s (swap2 x))) :=
      hmeas1.add hmeas2
    calc (∫⁻ x, ENNReal.ofReal ((symmetrize M).s x)
          ∂(Measure.pi (fun _ : Fin 2 => ν)))
        = ∫⁻ x, (2⁻¹ : ℝ≥0∞) *
            (ENNReal.ofReal (M.s x) + ENNReal.ofReal (M.s (swap2 x)))
            ∂(Measure.pi (fun _ : Fin 2 => ν)) := by simp only [hpt]
      _ = (2⁻¹ : ℝ≥0∞) * (∫⁻ x, (ENNReal.ofReal (M.s x) +
            ENNReal.ofReal (M.s (swap2 x)))
            ∂(Measure.pi (fun _ : Fin 2 => ν))) :=
        MeasureTheory.lintegral_const_mul _ hmeas_sum
      _ = (2⁻¹ : ℝ≥0∞) * ((∫⁻ x, ENNReal.ofReal (M.s x)
            ∂(Measure.pi (fun _ : Fin 2 => ν))) +
          (∫⁻ x, ENNReal.ofReal (M.s (swap2 x))
            ∂(Measure.pi (fun _ : Fin 2 => ν)))) := by
        congr 1
        exact MeasureTheory.lintegral_add_left hmeas1 _
      _ = ∫⁻ x, ENNReal.ofReal (M.s x) ∂(Measure.pi (fun _ : Fin 2 => ν)) := by
        have hswap_s : (∫⁻ x, ENNReal.ofReal (M.s (swap2 x))
            ∂(Measure.pi (fun _ : Fin 2 => ν))) =
            ∫⁻ x, ENNReal.ofReal (M.s x) ∂(Measure.pi (fun _ : Fin 2 => ν)) :=
          hswap_int _ hmeas1
        rw [hswap_s, ← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- IsFeasible: averages of [0,1]-valued allocations stay in [0,1].
    intro x i
    rw [hq]
    have h1 := hFeas x i
    have h2 := hFeas (swap2 x) (Equiv.swap 0 1 i)
    refine ⟨?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · -- IsIC: average of the IC inequality at (x, x') and (swap2 x, swap2 x').
    intro x x'
    have h1 : (∑ i, M.q x' i * (x i : ℝ)) - M.s x' ≤
        MultiItemRev.Decomp.buyerPayoff M x := hIC x x'
    have h2 : (∑ i, M.q (swap2 x') i * ((swap2 x) i : ℝ)) - M.s (swap2 x') ≤
        MultiItemRev.Decomp.buyerPayoff M (swap2 x) := hIC (swap2 x) (swap2 x')
    rw [hsum x' x, hs, hBP x]
    linarith [h1, h2]
  · -- IsIR: average of two nonnegative payoffs.
    intro x
    have h1 : 0 ≤ MultiItemRev.Decomp.buyerPayoff M x := hIR x
    have h2 : 0 ≤ MultiItemRev.Decomp.buyerPayoff M (swap2 x) := hIR (swap2 x)
    rw [hBP x]
    linarith [h1, h2]
  · -- Measurability of the averaged payment.
    exact (hMeas.add (hMeas.comp hmeas_swap2)).div_const 2
  · -- IsNPT: average of two nonnegative payments.
    intro x
    rw [hs]
    have h1 := hNPT x
    have h2 := hNPT (swap2 x)
    linarith
  · -- IsSymmetric: swap-involution + add_comm.
    intro x
    refine ⟨?_, ?_⟩
    · rw [hq, hq, hswap_invol, Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    · rw [hs, hs, hswap_invol]
      ring
  · -- Same revenue.
    unfold MultiItemRev.TwoIID.expRevenue
    rw [hneg1, hneg2, hpos]

theorem symmetrization (ν : Measure ℝ≥0) [IsProbabilityMeasure ν]
    (M : MultiItemRev.Decomp.Mechanism (Fin 2)) (hM : IsAdmissible M ∧ MultiItemRev.Decomp.IsNPT M) :
    IsAdmissible (symmetrize M) ∧ MultiItemRev.Decomp.IsNPT (symmetrize M) ∧
      IsSymmetric (symmetrize M) ∧
      expRevenue (Measure.pi (fun _ : Fin 2 => ν)) (symmetrize M) =
        expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M := solution ν M hM
