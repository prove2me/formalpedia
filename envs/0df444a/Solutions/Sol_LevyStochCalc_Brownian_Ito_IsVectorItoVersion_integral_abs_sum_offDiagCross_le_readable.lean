-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_offDiagCross_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:32.275374+00:00
-- url     : https://prove2.me/submissions/a8221874-f1e6-443f-a224-80462dbfa876

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_mul_and_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_weighted_crossSum_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_pow_four_le_readable
import Theorems.Thm_LevyStochCalc_integral_abs_le_sqrt_of_integral_sq_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section ThirdMoment
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)
end ThirdMoment
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
end VectorVersion
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section CrossSum
open LevyStochCalc.Brownian.Multidim
variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
/-- The cross increment is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_crossIncrement (i j : Fin d) (a b : ℝ) :
    Measurable (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) :=
  (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b).mul
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b)
variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)
include hCH0 hCH hCK0 hCK in
/-- **Second moment of a cross increment.** Both increments have fourth moments bounded through
the integrand bounds, and the square of a product is dominated by half the sum of the fourth
powers. -/
theorem LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Integrable (fun ω =>
        (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2) P
      ∧ ∫ ω, (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b ω) ^ 2 ∂P
        ≤ (6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (b - a) ^ 2 := by
  obtain ⟨hA4, hA4le⟩ :=
    integral_sub_pow_four_le_readable (W.W i) ℱ (hcoord i) H hHm hHp hHs hCH0 hCH ha hab
  obtain ⟨hB4, hB4le⟩ :=
    integral_sub_pow_four_le_readable (W.W j) ℱ (hcoord j) K hKm hKp hKs hCK0 hCK ha hab
  obtain ⟨hint, hle⟩ := integrable_sq_mul_and_le_readable
    (measurable_sub_stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a b)
    (measurable_sub_stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a b) hA4 hB4
  refine ⟨hint, le_trans hle ?_⟩
  linarith [hA4le, hB4le]
include hCH0 hCH hCK0 hCK in
/-- The cross increment lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_crossIncrement (i j : Fin d) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b) 2 P :=
  (memLp_two_iff_integrable_sq
      (measurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j a b).aestronglyMeasurable).2
    (integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j ha hab).1
end CrossSum
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section CellSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The squared cell lengths of the uniform grid sum to `T²/m`. -/
theorem LevyStochCalc.Brownian.Ito.sum_unifGrid_sq_diff {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = T ^ 2 / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hterm : ∀ i ∈ Finset.range m,
      (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = (T / (m : ℝ)) ^ 2 :=
    fun i _ => by rw [unifGrid_succ_sub hm0 i]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
end CellSums
section VectorQuadVar
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH in
/-- **The cross terms off the diagonal in the Brownian index sum to `O(m^{-1/2})`.** -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (p q : Fin n)
    {k l : Fin d} (hkl : k ≠ l)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
            k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
              k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.unifGrid T m 0 := le_of_eq (LevyStochCalc.Brownian.Ito.unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, LevyStochCalc.Brownian.Ito.unifGrid T m i < LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) := LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (LevyStochCalc.Brownian.Ito.unifGrid T m i))
      (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m i))
  have hζmem : ∀ i : ℕ, MemLp (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) 2 P := fun i =>
    LevyStochCalc.Brownian.Ito.memLp_two_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) hC0 (hCH p k) hC0 (hCH q l) k l (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) := fun i =>
    LevyStochCalc.Brownian.Ito.measurable_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) k l _ _
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
      * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
          k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le_readable W hcoord (hHm p k) (hHp p k) (hHs p k)
    (hHm q l) (hHp q l) (hHs q l) hC0 (hCH p k) hC0 (hCH q l) hkl (LevyStochCalc.Brownian.Ito.unifGrid T m) h0 hgrid
    (fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) hg hKφ0 (fun i ω => hφbd _) m
  rw [LevyStochCalc.Brownian.Ito.sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_readable ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩
