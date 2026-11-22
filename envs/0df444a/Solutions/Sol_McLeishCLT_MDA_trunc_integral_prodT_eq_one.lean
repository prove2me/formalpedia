-- Prove2me | solution 1 for McLeishCLT.MDA.trunc_integral_prodT_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:08:34.812428+00:00
-- url     : https://prove2.me/submissions/02e4737a-4ee7-4e76-b5ff-30b9613399ef

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

set_option autoImplicit false

namespace McLeishCLT.MDA.TruncIntProof

open MeasureTheory Finset Complex

/-- `|1 + itz| ≤ exp(t²z²/2)`. -/
theorem norm_one_add_le (t z : ℝ) :
    ‖(1 : ℂ) + I * (t : ℂ) * (z : ℂ)‖ ≤ Real.exp (t ^ 2 * z ^ 2 / 2) := by
  have h1 : ‖(1 : ℂ) + I * (t : ℂ) * (z : ℂ)‖ ^ 2 = 1 + t ^ 2 * z ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have h2 : 1 + t ^ 2 * z ^ 2 ≤ Real.exp (t ^ 2 * z ^ 2 / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have := Real.add_one_le_exp (t ^ 2 * z ^ 2)
    have he : ((2 : ℕ) : ℝ) * (t ^ 2 * z ^ 2 / 2) = t ^ 2 * z ^ 2 := by push_cast; ring
    rw [he]
    linarith
  have hn := norm_nonneg ((1 : ℂ) + I * (t : ℂ) * (z : ℂ))
  have he := Real.exp_pos (t ^ 2 * z ^ 2 / 2)
  by_contra hcon
  push Not at hcon
  nlinarith

end McLeishCLT.MDA.TruncIntProof

open MeasureTheory Finset Complex McLeishCLT.MDA McLeishCLT.MDA.TruncIntProof

theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X) :
    ∀ (t : ℝ) (n : ℕ), ∫ ω, prodT k (trunc X) t n ω ∂P = 1 := by
  intro t n
  -- Partial sums of squares, partial products, and the stopped factor.
  set s : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ range m, X n i ω ^ 2 with hsdef
  set Q : ℕ → Ω → ℂ := fun m ω => ∏ j ∈ range m, (1 + I * (t : ℂ) * (trunc X n j ω : ℂ))
    with hQdef
  set Y : ℕ → Ω → ℂ := fun m ω => if s m ω ≤ 2 then Q m ω else 0 with hYdef
  -- Measurability with respect to the row filtration.
  have hxm : ∀ j m, j < k n → j < m → Measurable[ℱ n m] (X n j) := fun j m hjK hjm =>
    ((hmda n j hjK).1.mono ((ℱ n).mono (by omega))).measurable
  have hsm : ∀ m, m ≤ k n → Measurable[ℱ n m] (s m) := by
    intro m hm
    refine Finset.measurable_sum _ fun i hi => ?_
    rw [mem_range] at hi
    exact (hxm i m (by omega) hi).pow_const 2
  have hZm : ∀ j m, j < k n → j < m → Measurable[ℱ n m] (trunc X n j) := by
    intro j m hjK hjm
    have hset : MeasurableSet[ℱ n m] {ω | s j ω ≤ 2} :=
      measurableSet_le (((hsm j (by omega)).mono ((ℱ n).mono (by omega)) le_rfl))
        measurable_const
    have : trunc X n j = fun ω => X n j ω * (if s j ω ≤ 2 then 1 else 0) := rfl
    rw [this]
    exact (hxm j m hjK hjm).mul (Measurable.ite hset measurable_const measurable_const)
  have hQm : ∀ m, m ≤ k n → Measurable[ℱ n m] (Q m) := by
    intro m hm
    refine Finset.measurable_prod _ fun j hj => ?_
    rw [mem_range] at hj
    exact measurable_const.add (measurable_const.mul
      (Complex.measurable_ofReal.comp (hZm j m (by omega) hj)))
  have hYm : ∀ m, m ≤ k n → Measurable[ℱ n m] (Y m) := fun m hm =>
    Measurable.ite (measurableSet_le (hsm m hm) measurable_const) (hQm m hm) measurable_const
  -- `‖Q m‖ ≤ exp(t² s_m / 2)`, hence `‖Y m‖ ≤ exp(t²)`.
  have hQbound : ∀ m ω, ‖Q m ω‖ ≤ Real.exp (t ^ 2 / 2 * s m ω) := by
    intro m ω
    simp only [hQdef, hsdef]
    rw [norm_prod, mul_sum, Real.exp_sum]
    refine prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
    refine (norm_one_add_le t (trunc X n j ω)).trans (Real.exp_le_exp.mpr ?_)
    have hZ : trunc X n j ω ^ 2 ≤ X n j ω ^ 2 := by
      unfold trunc
      split_ifs <;> nlinarith [sq_nonneg (X n j ω)]
    nlinarith [sq_nonneg t]
  have hYbound : ∀ m ω, ‖Y m ω‖ ≤ Real.exp (t ^ 2) := by
    intro m ω
    simp only [hYdef]
    split_ifs with h
    · refine (hQbound m ω).trans (Real.exp_le_exp.mpr ?_)
      nlinarith [sq_nonneg t]
    · simp [(Real.exp_pos _).le]
  -- The induction on the row length.
  have hstep : ∀ m, m ≤ k n → Integrable (Q m) P ∧ ∫ ω, Q m ω ∂P = 1 := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Q 0 = fun _ => 1 := by funext ω; simp [hQdef]
      rw [this]
      exact ⟨integrable_const _, by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨hQi, hQint⟩ := ih (by omega)
      have hmK : m < k n := by omega
      obtain ⟨-, hxi, hce⟩ := hmda n m hmK
      have hxci : Integrable (fun ω => (X n m ω : ℂ)) P := hxi.ofReal
      have hYae : AEStronglyMeasurable (Y m) P :=
        ((hYm m (by omega)).mono ((ℱ n).le m) le_rfl).aestronglyMeasurable
      have hYx : Integrable (fun ω => Y m ω * (X n m ω : ℂ)) P :=
        hxci.bdd_mul hYae (Filter.Eventually.of_forall (hYbound m))
      -- `E[Y_m X_m] = E[Y_m E[X_m | ℱ_m]] = 0`.
      have hsmul_eq : (fun ω => Y m ω * (X n m ω : ℂ)) = fun ω => X n m ω • Y m ω := by
        funext ω
        rw [Complex.real_smul, mul_comm]
      have hzero : ∫ ω, Y m ω * (X n m ω : ℂ) ∂P = 0 := by
        rw [hsmul_eq]
        have hint : Integrable (fun ω => X n m ω • Y m ω) P := by rw [← hsmul_eq]; exact hYx
        have hpull := condExp_bilin_of_aestronglyMeasurable_left
          (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip) (m := ℱ n m)
          (f := Y m) (g := X n m)
          ((hYm m (by omega)).aestronglyMeasurable) hint hxi
        simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] at hpull
        rw [← integral_condExp ((ℱ n).le m), integral_congr_ae hpull]
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hce] with ω hω
        simp [hω]
      -- `Q_{m+1} = Q_m + i t Y_m X_m`.
      have hrec : Q (m + 1) = fun ω => Q m ω + I * (t : ℂ) * (Y m ω * (X n m ω : ℂ)) := by
        funext ω
        simp only [hQdef, hYdef, prod_range_succ]
        unfold trunc
        split_ifs with h
        · push_cast; ring
        · push_cast; ring
      rw [hrec]
      refine ⟨hQi.add (hYx.const_mul _), ?_⟩
      rw [integral_add hQi (hYx.const_mul _), integral_const_mul, hzero, hQint]
      ring
  exact (hstep (k n) le_rfl).2
