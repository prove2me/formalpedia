-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:01:03.615953+00:00
-- url     : https://prove2.me/submissions/d1cac8d1-c3c2-4626-b3cc-30d65984f3fc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_add_le
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_inner_aemeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The fixed point of the Picard step

The limit `picardLimit` of the Picard iterates is jointly measurable, progressively measurable and
of finite Bielecki norm, and the Bielecki distance between the step taken along it and the limit
itself vanishes, so the step and the limit agree almost surely at every time of the window. The
step contracts between two raw state processes and therefore respects almost sure equality of its
input, which promotes that agreement to the statement that the process built over the limit solves
the Picard equation along its own path.

## Main statements

* `picardLimit` — the limit of the Picard iterates.
* `bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero` — the limit is a fixed point in norm.
* `picardSelfMapRaw_picardLimit_ae_eq` — the fixed point is realised by a process of the space.
* `picardSelfMapRaw_isFixedPoint` — the fixed point solves its own Picard equation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)


omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference of two processes of the space is finite. -/
theorem bieleckiNorm_sub_lt_top {β : ℝ} (hβ : 0 ≤ β)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y.X t ω))
      = bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X.X t ω i - Y.X t ω i)
      = fun t (ω : Ω) => X.X t ω + (fun i => -(Y.X t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y.X t ω)) :=
    measurable_neg.comp Y.measurable_path
  have hadd := bieleckiNorm_add_le (P := P) 0 T X.X (fun t ω => -(Y.X t ω))
    (fun t => bieleckiNorm_inner_aemeasurable _ X.measurable_path t)
    (fun t => bieleckiNorm_inner_aemeasurable (fun t ω => -(Y.X t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨X.sup_L2, Y.sup_L2⟩

omit [ℱ'.IsRightContinuous] in
/-- The unweighted Bielecki norm is bounded by the weighted one, at the cost of `e^{βT}`. -/
theorem bieleckiNorm_zero_le_mul {β : ℝ} (hβ : 0 ≤ β) {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) 0 T Z
      ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z := by
  refine iSup₂_le fun t ht => ?_
  have hle : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z :=
    le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (β * t)) ≤ ENNReal.ofReal (Real.exp (β * T)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [ht.2, ht.1]))
  calc ENNReal.ofReal (Real.exp (-0 * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (β * t)) * (ENNReal.ofReal (Real.exp (-β * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z :=
        mul_le_mul' hexp hle

theorem _root_.solution {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) 0 T
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀) < ⊤ := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hbase : bieleckiNorm (P := P) β T X₀.X < ⊤ :=
    lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ.le T X₀.X) X₀.sup_L2
  have hsub := bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs
    hReg hLip x₀ hβ hT X₀ hq 0
  have hfin : ((1 - (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
      * bieleckiNorm (P := P) β T (fun t ω i =>
          (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
            - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i))
      ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hd : bieleckiNorm (P := P) β T (fun t ω i => X₀.X t ω i
      - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) < ⊤ := by
    refine lt_of_le_of_lt hsub ?_
    rw [pow_zero, one_mul]
    exact lt_top_iff_ne_top.mpr hfin
  refine lt_of_le_of_lt (bieleckiNorm_zero_le_mul (P := P) hβ.le _)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact bieleckiNorm_lt_top_of_approx β T
    (fun t i => measurable_slice_of_uncurry X₀.measurable_path t i)
    (fun t i => measurable_slice_of_uncurry hYm t i) hbase hd
