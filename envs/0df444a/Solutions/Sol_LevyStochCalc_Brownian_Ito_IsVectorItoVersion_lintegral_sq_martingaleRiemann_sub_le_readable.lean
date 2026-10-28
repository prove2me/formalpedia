-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:12.638186+00:00
-- url     : https://prove2.me/submissions/96f2d49e-5bd6-4703-9a20-a578a7d000de

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoRiemannIntegrand
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormula
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_sq_frozen_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_stochasticIntegral_mul_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_integralAgainst_readable

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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoRiemannIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Past the last partition point, the elementary integral of a simple integrand against a
process is the weighted sum of the process's increments across the cells. -/
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst_eq_sum {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) {t : ℝ} (ht : G.partition (Fin.last G.N) ≤ t) (ω : Ω) :
    G.integralAgainst M t ω
      = ∑ i : Fin G.N, G.ξ i ω
        * (M (G.partition i.succ) ω - M (G.partition i.castSucc) ω) := by
  unfold SimplePredictable.integralAgainst
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : G.partition i.succ ≤ t :=
    le_trans (G.partition_strictMono.monotone (Fin.le_last _)) ht
  have h2 : G.partition i.castSucc ≤ t :=
    le_of_lt ((G.partition_strictMono Fin.castSucc_lt_succ).trans_le h1)
  rw [min_eq_left h1, min_eq_left h2]
section Riemann
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt in
/-- **The weighted sum of the Itô integral's increments is an Itô integral.** -/
theorem LevyStochCalc.Brownian.Ito.sum_xi_mul_stochasticIntegral_sub_ae {t : ℝ} (ht : 0 < t)
    (hlast : G.partition (Fin.last G.N) ≤ t) :
    (fun ω => ∑ i : Fin G.N, G.ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (G.partition i.succ) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (G.partition i.castSucc) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t := by
  have hkey := stochasticIntegralBrownian_integralAgainst_readable W ℱ hℱ G h_adapt H hm hp hq
    hmm hmp hmq ht
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω => ?_) hkey
  exact (G.integralAgainst_eq_sum (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) hlast ω).symm
end Riemann
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormula.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section GridSum
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ in
/-- **The grid-weighted sum of the Itô integral's increments is an Itô integral.** For
coefficients `ξ i` measurable at the left endpoint of cell `i` of the uniform grid,

  `∑ᵢ ξᵢ · (M_{tᵢ₊₁} − M_{tᵢ}) = ∫_0^T G_m(s)·H_s dW_s`

almost surely, where `G_m` is the step process with value `ξ i` on `(tᵢ, tᵢ₊₁]`. -/
theorem LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    (fun ω => ∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
          (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
        (fun T' hT' =>
          (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
            hq T' hT') T := by
  have hlast : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition
      (Fin.last (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).N) ≤ T :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition_le_T
  exact sum_xi_mul_stochasticIntegral_sub_ae W ℱ hℱ
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas)
    (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) H hm hp hq _ _ _ hT hlast
end GridSum
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorFrozen
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
/-- **The martingale Riemann sum converges in `L²` at rate `√(T/m)`.** Freezing a bounded
`L`-Lipschitz `φ(X)` at the grid's left endpoints and pairing it with the increments of
`∫ G dWᵏ` approximates `∫_0^T φ(X_s) G_s dWᵏ_s` with squared `L²` error
`C_G²·L²·T·n(2B²(T/m)² + 2d²C²(T/m))`. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
    (hGp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ G)
    (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
    (hpg : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  set ξ : Fin m → Ω → ℝ := fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω) with hξdef
  have hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M := fun i => ⟨Kφ, fun ω => hφbd _⟩
  have hmeas : ∀ i : Fin m, Measurable (ξ i) := fun i =>
    hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ))) (ξ i) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hstep := LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae (W.W k) ℱ (hcoord k) G hGm hGp hGs hT hm0 ξ hbdd hmeas
    hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * G ω s)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hGm)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hGp)
          (fun T' hT' =>
            (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
              hGs T' hT') T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le_readable (W.W k) ℱ (hcoord k) G
    (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω)
    (fun ω s => φ (X s ω)) _ _ _ hmg hpg hqg hCG0 hCG hT) ?_
  gcongr _ * ?_
  exact h.lintegral_sq_frozen_sub_le_readable hC0 hCH hbm hB0 hB hL0 hφlip hT hm0 ξ hbdd hmeas
    fun i ω => rfl
