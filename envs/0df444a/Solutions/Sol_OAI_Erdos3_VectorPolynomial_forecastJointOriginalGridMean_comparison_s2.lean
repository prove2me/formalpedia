-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:11:53.593665+00:00
-- url     : https://prove2.me/submissions/41e2f7a0-d14d-4948-8a34-1d79a5067070

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_rationalInactive_translated_grid_comparison_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CompactSliceErrorIntegral
namespace OAI

section

namespace Erdos3
open MeasureTheory

variable {C J : Type*} [Fintype C] [Fintype J]

theorem compactProductDensity_integrable
    (g : (C → ℝ) × (J → ℝ) → ℝ) (hg : Continuous g) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    Integrable g ((volume : Measure (C → ℝ)).prod (volume : Measure (J → ℝ))) := by
  apply hg.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (C → ℝ) × (J → ℝ)) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  exact hx (hsupport x hn)

theorem compactSliceError_integral_norm_le
    (g : (C → ℝ) × (J → ℝ) → ℝ) (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {R A B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (err : (C → ℝ) → ℂ) (herr0 : ∀ c, R < ‖c‖ → err c = 0)
    (herr : ∀ c, ‖c‖ ≤ R → ‖err c‖ ≤ A + B * ∫ x, g (c, x)) :
    (∫ c, ‖err c‖) ≤ A * (2 * R) ^ Fintype.card C +
      B * ∫ x, g x ∂((volume : Measure (C → ℝ)).prod (volume : Measure (J → ℝ))) := by
  let s := Metric.closedBall (0 : C → ℝ) R
  have hs : MeasurableSet s := measurableSet_closedBall
  have hi : Integrable (s.indicator (fun _ : C → ℝ => A)) :=
    (integrableOn_const ((isCompact_closedBall (0 : C → ℝ) R).measure_lt_top.ne)).integrable_indicator hs
  have hgi := compactProductDensity_integrable g hg R hsupport
  have hm : Integrable (fun c : C → ℝ => B * ∫ x, g (c, x)) :=
    hgi.integral_prod_left.const_mul B
  have hb (c : C → ℝ) :
      ‖err c‖ ≤ s.indicator (fun _ : C → ℝ => A) c + B * ∫ x, g (c, x) := by
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc]
      exact herr c (by simpa only [s, Metric.mem_closedBall, dist_zero_right] using hc)
    · have hc' : R < ‖c‖ := by
        simpa only [s, Metric.mem_closedBall, dist_zero_right, not_le] using hc
      rw [herr0 c hc', norm_zero, Set.indicator_of_notMem hc, zero_add]
      exact mul_nonneg hB (integral_nonneg (fun x => hg0 (c, x)))
  have hv : volume.real s = (2 * R) ^ Fintype.card C := by
    rw [measureReal_def, Real.volume_pi_closedBall 0 hR, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ∫ c, s.indicator (fun _ : C → ℝ => A) c + B * ∫ x, g (c, x) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun c => norm_nonneg (err c)))
        (hi.add hm) (Filter.Eventually.of_forall hb)
    _ = _ := by
      rw [integral_add hi hm, integral_indicator_const A hs, hv,
        smul_eq_mul, integral_const_mul, ← integral_prod g hgi]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTsum
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem fiberMean_eq_zero_of_not_mem_image (F : X → R) (f : X → ℝ)
    (r : R) (hr : r ∉ Finset.univ.image F) : p.fiberMean F r f = 0 := by
  have hne : ∀ x, F x ≠ r := by
    intro x hx
    exact hr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  simp only [fiberMean, hne, ite_false, mean_const]

theorem complexMean_fiber_factor_sum_image (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r ∈ Finset.univ.image F, (p.fiberMean F r f : ℂ) * a r := by
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hx : F x ∈ Finset.univ.image F := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc, hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem compactBox_complex_integrable (f : (J → ℝ) → ℂ) (hf : Continuous f)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  exact hx (hsupport x hn)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UniformSumCoordinates
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniform_complexMean_sum_elim
    {A B R : Type*} [Fintype A] [Fintype B] [Fintype R] [Nonempty R]
    (f : ((A ⊕ B) → R) → ℂ) :
    (uniform (A → R)).complexMean (fun a =>
      (uniform (B → R)).complexMean (fun b => f (Sum.elim a b))) =
      (uniform ((A ⊕ B) → R)).complexMean f := by
  simp only [uniform_complexMean]
  calc
    _ = 𝔼 p : (A → R) × (B → R), f (Sum.elim p.1 p.2) := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (A → R))
          (Finset.univ : Finset (B → R)) (fun a b => f (Sum.elim a b))).symm
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi (fun _ : A ⊕ B => R)).symm
      intro p
      rfl

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.TranslatedPartialPeriodicGridIntegrability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C J : Type*} [Fintype C] [Fintype J]

theorem translatedPartialPeriodicIntegerGrid_integrable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r))
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Integrable (fun c : C → ℝ =>
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ)) := by
  have hzero (c : C → ℝ) (k : J → ℤ)
      (hk : k ∉ rectangularWeightIndices center T R) :
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j) = 0 := by
    have h := rectangularWeight_zero_off_indices
      (fun z => ‖f (fun j => (k j : ZMod q)) (c, z)‖) center T hT
      (fun z hz => by
        rw [hsupport _ _ (hz.trans_le (norm_snd_le (c, z))), norm_zero]) k hk
    change ‖f (fun j => (k j : ZMod q))
      (c, fun j => ((k j : ℝ) - center j) / T j)‖ = 0 at h
    exact norm_eq_zero.mp h
  have hsection (k : J → ℤ) : Integrable (fun c : C → ℝ =>
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) := by
    apply compactBox_complex_integrable _
      ((hf _).comp (continuous_id.prodMk continuous_const)) R
    intro c hc
    exact hsupport _ _ (hc.trans_le (norm_fst_le (c, fun j => ((k j : ℝ) - center j) / T j)))
  have heq : (fun c : C → ℝ => ∑' k : J → ℤ,
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) =
      (fun c => ∑ k ∈ rectangularWeightIndices center T R,
        f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) := by
    funext c
    exact tsum_eq_sum (hzero c)
  have hsum := integrable_finsetSum (rectangularWeightIndices center T R)
    (fun k _ => hsection k)
  rw [← heq] at hsum
  exact hsum.div_const _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]
variable (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N)
variable (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ b, Continuous (φ b))
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)

local notation "Domain" => (V → ℝ) × (J → ℝ)
local notation "rout" => rationalOutputDensity p Y N

include hg hφ hsupport

theorem rationalOutput_gridTest_integrable (b : J → ZMod qW) :
    Integrable (fun x : Domain => (g x : ℂ) * φ b x)
      ((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  apply ((Complex.continuous_ofReal.comp hg).mul (hφ b)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Domain) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  apply hx
  change (g x : ℂ) * φ b x = 0
  rw [hsupport x hn, Complex.ofReal_zero, zero_mul]

include hW in
theorem rationalOutput_partial_grid_integrable
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) :
    Integrable (fun c : V → ℝ =>
      (∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rout (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) := by
  let fN := fun (b : J → ZMod N) (x : Domain) =>
    (g x : ℂ) * (rout (Sum.elim aux b) : ℂ) * φ (zmodPiReduction hW b) x
  have hfN (b : J → ZMod N) : Continuous (fN b) :=
    ((Complex.continuous_ofReal.comp hg).mul continuous_const).mul (hφ _)
  have hsN (b : J → ZMod N) (x : Domain) (hx : R < ‖x‖) : fN b x = 0 := by
    simp only [fN, hsupport x hx, Complex.ofReal_zero, zero_mul]
  have hred (k : J → ℤ) :
      zmodPiReduction hW (fun j => (k j : ZMod N)) =
        (fun j => (k j : ZMod qW)) := by
    funext j
    exact map_intCast (ZMod.castHom hW (ZMod qW)) (k j)
  simpa only [fN, hred] using translatedPartialPeriodicIntegerGrid_integrable
    N fN hfN center T hT R hsN

theorem rationalOutput_partial_reference_integrable :
    Integrable (fun c : V → ℝ => 𝔼 b : J → ZMod N,
      (rout (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x)) := by
  simp only [Finset.expect_eq_sum_div_card]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro b _
  exact (rationalOutput_gridTest_integrable qW g φ hg hφ R hsupport
    (zmodPiReduction hW b)).integral_prod_left.const_mul _

theorem rationalOutput_partial_reference_integral :
    (∫ c : V → ℝ, 𝔼 b : J → ZMod N,
      (rout (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x)) =
      𝔼 b : J → ZMod N, (rout (Sum.elim aux b) : ℂ) *
        ∫ x : Domain, (g x : ℂ) * φ (zmodPiReduction hW b) x
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  have hi (b : J → ZMod N) := rationalOutput_gridTest_integrable qW g φ hg hφ R hsupport
    (zmodPiReduction hW b)
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _
    (fun b _ => (hi b).integral_prod_left.const_mul (rout (Sum.elim aux b) : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, ← integral_prod _ (hi b)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ControlledJointGrid
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedPeriodicGridQuadrature
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_zero_off_image {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  rw [rationalInactiveForecast,
    inactive.fiberMean_eq_zero_of_not_mem_image gridPoint _ z hz, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalInactivePartialReference
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I A Z O : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_pointwise_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : O → ZMod N) (test : Z → ℂ) :
    (∑' z, ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i)) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  exact (inactive.complexMean_fiber_factor_sum_image gridPoint
    (fun i => rationalOutputDensity (active i) (Y i) N b) test).symm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalInactiveForecast_partial_reference
    {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O] [Fintype K]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, 𝔼 k : K,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => 𝔼 k : K,
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  rw [← Finset.expect_sum_comm]
  have he (k : K) : (∑ z ∈ Finset.univ.image gridPoint,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
        test (gridPoint i) k) := by
    simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
    exact (inactive.complexMean_fiber_factor_sum_image gridPoint
      (fun i => rationalOutputDensity (active i) (Y i) N (b k)) (fun z => test z k)).symm
  simp_rw [he]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp only [Finset.mul_expect]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RationalInactiveLatticeContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I A Z O K : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O]

theorem rationalInactiveForecast_lattice_tsum_test
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      inactive.complexMean (fun i => ∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) := by
  let grid := Finset.univ.image gridPoint
  have hz (z : Z) (hz : z ∉ grid) (k : K) :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) = 0 :=
    rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz (b k)
  rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h, zero_div,
    Complex.ofReal_zero, mul_zero, zero_mul, tsum_zero])]
  have hk (z : Z) : (∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) =
      ∑ k ∈ sK, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hk]
  rw [Finset.sum_comm]
  have hzsum (k : K) :
      (∑ z ∈ grid, G k *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
          gridVolume : ℝ) : ℂ) * test z k) =
      G k * inactive.complexMean (fun i =>
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) := by
    rw [← rationalInactiveForecast_pointwise_tsum_test inactive active gridPoint Y N hV
      (b k) (fun z => test z k)]
    rw [tsum_eq_sum (s := grid) (fun z h => by simp only [hz z h k, zero_div,
      Complex.ofReal_zero, zero_mul])]
    simp only [Finset.mul_sum, mul_assoc]
  simp_rw [hzsum]
  have hi (i : I) : (∑' k, G k *
      (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k) =
      ∑ k ∈ sK, G k *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) * test (gridPoint i) k :=
    tsum_eq_sum (fun k h => by rw [hG k h, zero_mul, zero_mul])
  simp_rw [hi, FiniteProbabilityWeights.complexMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem rationalInactiveForecast_lattice_tsum_test_div
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (G : K → ℂ) (sK : Finset K) (hG : ∀ k ∉ sK, G k = 0)
    (b : K → O → ZMod N) (test : Z → K → ℂ) (v : ℂ) :
    (∑' z, ∑' k, G k *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / v =
      inactive.complexMean (fun i => (∑' k,
        G k * (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / v) := by
  rw [rationalInactiveForecast_lattice_tsum_test inactive active gridPoint Y N hV G sK hG b test]
  simp only [FiniteProbabilityWeights.complexMean, Finset.sum_div, mul_div_assoc]

theorem rationalInactiveForecast_compactGrid_tsum_test_div {J : Type*} [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ)
    (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (test : Z → (J → ℤ) → ℂ) :
    (∑' z, ∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (b k) /
        gridVolume : ℝ) : ℂ) * test z k) / ((∏ j, scale j : ℝ) : ℂ) =
      inactive.complexMean (fun i => (∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
        (rationalOutputDensity (active i) (Y i) N (b k) : ℂ) *
          test (gridPoint i) k) / ((∏ j, scale j : ℝ) : ℂ)) := by
  apply rationalInactiveForecast_lattice_tsum_test_div inactive active gridPoint Y N hV
    _ (rectangularWeightIndices center scale R) _ b test
  intro k hk
  have h := rectangularWeight_zero_off_indices g center scale hscale hsupport k hk
  unfold rectangularWeight rectangularLatticePoint at h
  rw [h, Complex.ofReal_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalInactiveGridIntegralComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {I A Z Aux J V : Type*}
variable [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]
variable (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
variable (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N) (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ z b, Continuous (φ z b))
variable (center T : J → ℝ) (hT : ∀ j, 0 < T j)
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)

local notation "Domain" => (V → ℝ) × (J → ℝ)
local notation "rational" => rationalInactiveForecast inactive active gridPoint Y N gridVolume
local notation "normk" => (fun (k : J → ℤ) (j : J) => ((k j : ℝ) - center j) / T j)
local notation "raw" => (fun c : V → ℝ =>
  (∑' z, ∑' k : J → ℤ, (g (c, normk k) : ℂ) *
    ((rational z (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (fun j => (k j : ZMod qW)) (c, normk k)) / ((∏ j, T j : ℝ) : ℂ))
local notation "reference" => (fun c : V → ℝ =>
  ∑' z, 𝔼 b : J → ZMod N,
    ((rational z (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))
local notation "fullReference" => (∑' z, 𝔼 b : J → ZMod N,
  ((rational z (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
    ∫ x : Domain, (g x : ℂ) * φ z (zmodPiReduction hW b) x
      ∂(Measure.prod (volume : Measure (V → ℝ)) (volume : Measure (J → ℝ))))
local notation "outGrid" => (fun (c : V → ℝ) (i : I) =>
  (∑' k : J → ℤ, (g (c, normk k) : ℂ) *
    (rationalOutputDensity (active i) (Y i) N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
      φ (gridPoint i) (fun j => (k j : ZMod qW)) (c, normk k)) / ((∏ j, T j : ℝ) : ℂ))
local notation "outRef" => (fun (c : V → ℝ) (i : I) =>
  𝔼 b : J → ZMod N,
    (rationalOutputDensity (active i) (Y i) N (Sum.elim aux b) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ (gridPoint i) (zmodPiReduction hW b) (c, x))

include hV hT hsupport in
theorem rationalInactive_partial_grid_conditional (c : V → ℝ) :
    raw c = inactive.complexMean (outGrid c) := by
  exact rationalInactiveForecast_compactGrid_tsum_test_div inactive active gridPoint Y N hV
    (fun x => g (c, x)) center T hT R
    (fun x hx => hsupport _ (hx.trans_le (norm_snd_le (c, x))))
    (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun z k => φ z (fun j => (k j : ZMod qW)) (c, normk k))

omit [Fintype V] in
include hV in
theorem rationalInactive_partial_reference_conditional (c : V → ℝ) :
    reference c = inactive.complexMean (outRef c) :=
  rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))

include hV hW hg hφ hT hsupport in
theorem rationalInactive_partial_grid_integrable : Integrable raw := by
  have he := rationalInactive_partial_grid_conditional inactive active gridPoint Y hV
    qW aux g φ center T hT R hsupport
  simp_rw [he]
  apply inactive.complexMean_integrable volume outGrid
  intro i
  exact rationalOutput_partial_grid_integrable (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport center T hT

include hV hg hφ hsupport in
theorem rationalInactive_partial_reference_integrable : Integrable reference := by
  simp_rw [rationalInactive_partial_reference_conditional inactive active gridPoint Y hV
    qW hW aux g φ]
  apply inactive.complexMean_integrable volume outRef
  intro i
  exact rationalOutput_partial_reference_integrable (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport

include hV hg hφ hsupport in
theorem rationalInactive_partial_reference_integral :
    (∫ c, reference c) = fullReference := by
  have hi (i : I) : Integrable (fun c => outRef c i) :=
    rationalOutput_partial_reference_integrable (active i) (Y i) qW hW aux g
      (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport
  simp_rw [rationalInactive_partial_reference_conditional inactive active gridPoint Y hV
    qW hW aux g φ]
  rw [inactive.integral_complexMean volume outRef hi]
  have he (i : I) := rationalOutput_partial_reference_integral (active i) (Y i) qW hW aux g
    (φ (gridPoint i)) hg (hφ (gridPoint i)) R hsupport
  simp_rw [he]
  exact (rationalInactiveForecast_partial_reference inactive active gridPoint Y N hV
    (fun b : J → ZMod N => Sum.elim aux b)
    (fun z b => ∫ x : Domain, (g x : ℂ) * φ z (zmodPiReduction hW b) x
      ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))).symm

include hV hg hφ hT hsupport in
theorem rationalInactive_partial_grid_sub_reference_integral :
    (∫ c, raw c - reference c) = (∫ c, raw c) - fullReference := by
  rw [integral_sub
    (rationalInactive_partial_grid_integrable inactive active gridPoint Y hV qW hW aux
      g φ hg hφ center T hT R hsupport)
    (rationalInactive_partial_reference_integrable inactive active gridPoint Y hV qW hW aux
      g φ hg hφ R hsupport),
    rationalInactive_partial_reference_integral inactive active gridPoint Y hV qW hW aux
      g φ hg hφ R hsupport]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_partial_grid_integral_norm_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ) (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    (∫ c : V → ℝ,
      ‖(∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))‖) ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  classical
  let err := fun c : V → ℝ =>
    (∑' z, ∑' k : J → ℤ,
      (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ) -
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ z (zmodPiReduction hW b) (c, x))
  have herr0 (c : V → ℝ) (hc : R < ‖c‖) : err c = 0 := by
    have hz (x : J → ℝ) : g (c, x) = 0 := hsupport _ (hc.trans_le (norm_fst_le (c, x)))
    simp only [err, hz, Complex.ofReal_zero, zero_mul, integral_zero, mul_zero,
      Finset.expect_const_zero, tsum_zero, zero_div, sub_self]
  have herr (c : V → ℝ) (_hc : ‖c‖ ≤ R) : ‖err c‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) +
          (2 * (D / cutoff)) * ∫ x, g (c, x) := by
    have hg' : LipschitzWith L (fun x : J → ℝ => g (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using hg.dist_le_mul (c, x) (c, y)
    have hφ' (z : Z) (b : J → ZMod qW) : LipschitzWith K (fun x : J → ℝ => φ z b (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using (hφ z b).dist_le_mul (c, x) (c, y)
    have he := rationalInactive_translated_grid_comparison_s2 inactive active gridPoint Y hV qW hW aux cutoff hcutoff hD hP hdecay
      (fun x => g (c, x)) (fun z b x => φ z b (c, x)) C L K hg' (fun x => hg0 _) hφ'
      (fun x => hcap _) (fun z b x => hbound _ _ _) center T hT hR hδ hδ1 hmesh
      (fun x hx => hsupport _ (hx.trans_le (norm_snd_le (c, x))))
    exact he.trans_eq (by ring)
  exact compactSliceError_integral_norm_le g hg.continuous hg0 hR
    (mul_nonneg (by norm_num) (div_nonneg hD (Nat.cast_nonneg _))) hsupport err herr0 herr

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_partial_grid_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ) (φ : Z → (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : J → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
        ∫ x : ((V → ℝ) × (J → ℝ)), (g x : ℂ) * φ z (zmodPiReduction hW b) x
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  have h := rationalInactive_partial_grid_integral_norm_comparison inactive active gridPoint Y
    hV qW hW aux cutoff hcutoff hD hP hdecay g φ C L K hg hg0 hφ hcap hbound
    center T hT hR hδ hδ1 hmesh hsupport
  have hn := (norm_integral_le_integral_norm _).trans h
  rw [rationalInactive_partial_grid_sub_reference_integral inactive active gridPoint Y
    hV qW hW aux g φ hg.continuous (fun z b => (hφ z b).continuous)
    center T hT R hsupport] at hn
  exact hn

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalInactiveJointComparisonInstances
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalInactiveForecast_auxiliary_reference
    {I A Z Aux J : Type*} [Fintype I] [Fintype A]
    [Fintype Aux] [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (test : Z → ((Aux ⊕ J) → ZMod N) → ℂ) :
    (𝔼 aux : Aux → ZMod N, ∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z (Sum.elim aux b) /
        gridVolume : ℝ) : ℂ) * test z (Sum.elim aux b)) =
    ∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
        gridVolume : ℝ) : ℂ) * test z b := by
  let f : Z → ((Aux ⊕ J) → ZMod N) → ℂ := fun z b =>
    ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
      gridVolume : ℝ) : ℂ) * test z b
  have hzero (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b) : f z b = 0 := by
    simp only [f, rationalInactiveForecast_zero_off_image inactive active gridPoint Y N
      gridVolume z hz, zero_div, Complex.ofReal_zero, zero_mul]
  have haux (aux : Aux → ZMod N) :
      (∑' z, 𝔼 b : J → ZMod N, f z (Sum.elim aux b)) =
        ∑ z ∈ Finset.univ.image gridPoint, 𝔼 b : J → ZMod N, f z (Sum.elim aux b) := by
    apply tsum_eq_sum
    intro z hz
    simp only [hzero z hz, Finset.expect_const_zero]
  have hfull : (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N, f z b) =
      ∑ z ∈ Finset.univ.image gridPoint, 𝔼 b : (Aux ⊕ J) → ZMod N, f z b := by
    apply tsum_eq_sum
    intro z hz
    simp only [hzero z hz, Finset.expect_const_zero]
  change (𝔼 aux : Aux → ZMod N, ∑' z, 𝔼 b : J → ZMod N, f z (Sum.elim aux b)) = _
  simp_rw [haux]
  rw [hfull, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [FiniteProbabilityWeights.uniform_complexMean] using
    FiniteProbabilityWeights.uniform_complexMean_sum_elim (f z)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

private theorem zmodPiReduction_sum_elim {Aux J : Type*} {N q : ℕ}
    (h : q ∣ N) (a : Aux → ZMod N) (b : J → ZMod N) :
    zmodPiReduction h (Sum.elim a b) =
      Sum.elim (zmodPiReduction h a) (zmodPiReduction h b) := by
  funext j
  cases j <;> rfl

variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalInactive_joint_grid_comparison
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ)
    (φ : Z → ((Aux ⊕ J) → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
          (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  classical
  let raw := fun aux : Aux → ZMod N => ∫ c : V → ℝ,
    (∑' z, ∑' k : J → ℤ,
      (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
      φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ)
  let ref := fun aux : Aux → ZMod N =>
    ∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (Sum.elim aux b) / gridVolume : ℝ) : ℂ) *
      ∫ y, (g y : ℂ) * φ z (Sum.elim (zmodPiReduction hW aux) (zmodPiReduction hW b)) y
        ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ)))
  let err : ℝ :=
    ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
      (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
        (2 * R) ^ Fintype.card V +
      (2 * (D / cutoff)) * ∫ y, g y
        ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ)))
  have he (aux : Aux → ZMod N) : ‖raw aux - ref aux‖ ≤ err := by
    exact rationalInactive_partial_grid_comparison inactive active gridPoint Y hV qW hW
      aux cutoff hcutoff hD hP hdecay g
      (fun z b => φ z (Sum.elim (zmodPiReduction hW aux) b)) C L K hg hg0
      (fun z b => hφ z _) hcap (fun z b x => hbound z _ x)
      center T hT hR hδ hδ1 hmesh hsupport
  have havg := (FiniteProbabilityWeights.uniform (Aux → ZMod N)).norm_complexMean_sub_le
    raw ref (fun _ => err) (fun aux _ => he aux)
  rw [FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.mean_const] at havg
  have href : (𝔼 aux : Aux → ZMod N, ref aux) =
      ∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
    simpa only [ref, zmodPiReduction_sum_elim] using
      rationalInactiveForecast_auxiliary_reference inactive active gridPoint Y N gridVolume
        (fun z b => ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))
  rw [href] at havg
  exact havg

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {I A Z Aux J V : Type*} [Fintype I] [Fintype A] [Fintype Aux] [Fintype J] [Fintype V]
variable [instAux : DecidableEq Aux] [instJ : DecidableEq J]

theorem rationalInactive_joint_grid_comparison_instances
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → (Aux ⊕ J) → ℤ)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ)
    (φ : Z → ((Aux ⊕ J) → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ z b, LipschitzWith K (φ z b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ z b x, ‖φ z b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : V → ℝ,
      (∑' z, ∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
          (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
        φ z (Sum.elim (zmodPiReduction hW aux) (fun j => (k j : ZMod qW)))
          (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) -
      (∑' z, 𝔼 b : (Aux ⊕ J) → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
          gridVolume : ℝ) : ℂ) *
        ∫ y, (g y : ℂ) * φ z (zmodPiReduction hW b) y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  cases Subsingleton.elim instAux (Classical.decEq Aux)
  cases Subsingleton.elim instJ (Classical.decEq J)
  exact rationalInactive_joint_grid_comparison inactive active gridPoint Y hV qW hW cutoff hcutoff
    hD hP hdecay g φ C L K hg hg0 hφ hcap hbound center T hT hR hδ hδ1 hmesh hsupport

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalOutputAxisReindex
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem rationalOutputDensity_axis_reindex {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) [NeZero N] (r : A → ZMod N) :
    rationalOutputDensity p Y N r =
      rationalOutputDensity p (fun ω b => Y ω (e.symm b)) N (fun b => r (e.symm b)) := by
  have hcard : Fintype.card (A → ZMod N) = Fintype.card (B → ZMod N) :=
    Fintype.card_congr (outputAxisReindexAddEquiv e (ZMod N)).toEquiv
  have heq (ω : Ω) :
      ((fun b : B => (Y ω (e.symm b) : ZMod N)) = fun b => r (e.symm b)) ↔
        ((fun a : A => (Y ω a : ZMod N)) = r) := by
    constructor
    · intro h
      funext a
      simpa only [Equiv.symm_apply_apply] using congrFun h (e a)
    · intro h
      exact congrArg (fun f : A → ZMod N => fun b => f (e.symm b)) h
  unfold rationalOutputDensity finiteImageMass
  simp only [hcard, heq]

theorem rationalInactiveForecast_axis_reindex {I Ω Z A B : Type*}
    [Fintype I] [Fintype Ω] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (inactive : FiniteProbabilityWeights I)
    (active : I → FiniteProbabilityWeights Ω) (gridPoint : I → Z)
    (Y : I → Ω → A → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (r : A → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z r =
      rationalInactiveForecast inactive active gridPoint
        (fun i ω b => Y i ω (e.symm b)) N gridVolume z (fun b => r (e.symm b)) := by
  unfold rationalInactiveForecast
  apply congrArg (gridVolume * ·)
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact rationalOutputDensity_axis_reindex e (active i) (Y i) N r

theorem outputAxisCharacterPullback_order {A B : Type*} (e : A ≃ B)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    orderOf (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) =
      orderOf χ :=
  characterPullback_order _ (outputAxisReindexAddEquiv e (ZMod N)).surjective χ

theorem finiteImageCharacteristic_axis_reindex {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) (χ : AddChar (B → ZMod N) ℂ) :
    finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ =
      finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N))
        (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ) := rfl

theorem finiteImageCharacteristic_axis_reindex_bound {Ω A B : Type*} [Fintype Ω]
    (e : A ≃ B) (p : FiniteProbabilityWeights Ω) (Y : Ω → A → ℤ)
    (N : ℕ) {D P : ℝ}
    (hdecay : ∀ χ : AddChar (A → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω a => (Y ω a : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P)) :
    ∀ χ : AddChar (B → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun ω b => (Y ω (e.symm b) : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P) := by
  intro χ
  rw [finiteImageCharacteristic_axis_reindex]
  simpa only [outputAxisCharacterPullback_order] using
    hdecay (characterPullback (outputAxisReindexAddEquiv e (ZMod N)).toAddMonoidHom χ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastActiveGridIntegralComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {X : Type*} [Fintype X]
variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "Cont" => (Σ j : Fin m, I j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoinEquiv_apply
    (p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) :
    forecastJointCoordinateJoinEquiv U basis L p =
      forecastJointCoordinateJoin U basis L p.1 p.2 := by
  apply Prod.ext
  · funext a
    simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
      forecastJointCoordinateJoin, forecastJointAxisEquiv]
  · funext a
    cases h : forecastActiveAxisEquiv U basis L a <;>
      simp [forecastJointCoordinateJoinEquiv, MeasurableEquiv.sumPiEquivProdPi,
        MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
        forecastJointCoordinateJoin, forecastJointAxisEquiv, forecastActiveCoordinateJoin, h]

theorem forecastJointCoordinateJoinEquiv_measurePreserving :
    MeasurePreserving (forecastJointCoordinateJoinEquiv (X := X) (I := I) U basis L)
      volume volume := by
  exact (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Spatial ⊕ Output => ℝ)).comp
      ((volume_measurePreserving_piCongrLeft (fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).comp
          (volume_measurePreserving_sumPiEquivProdPi_symm
            (fun _ : Cont ⊕ (X ⊕ IntAxis) => ℝ)))

theorem forecastJointCoordinateJoin_isometry :
    Isometry (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) := by
  let e : ((Cont → ℝ) × ((X ⊕ IntAxis) → ℝ)) ≃ᵢ
      ((Spatial → ℝ) × (Output → ℝ)) :=
    IsometryEquiv.sumArrowIsometryEquivProdArrow.symm.trans
      ((IsometryEquiv.piCongrLeft (Y := fun _ : Spatial ⊕ Output => ℝ)
        (forecastJointAxisEquiv (X := X) (I := I) U basis L).symm).trans
          IsometryEquiv.sumArrowIsometryEquivProdArrow)
  have he : (e : _ → _) = fun p => forecastJointCoordinateJoin U basis L p.1 p.2 := by
    funext p
    exact forecastJointCoordinateJoinEquiv_apply U basis L p
  rw [← he]
  exact e.isometry

theorem forecastJointCoordinateJoin_lipschitz :
    LipschitzWith 1 (fun p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ) =>
      forecastJointCoordinateJoin U basis L p.1 p.2) :=
  (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).lipschitz

omit [Fintype X] [∀ j, Fintype (I j)] in
theorem forecastJointCoordinateJoin_zero :
    forecastJointCoordinateJoin (X := X) (I := I) U basis L 0 0 = 0 := by
  apply Prod.ext <;> funext a
  · rfl
  · change Sum.elim (fun _ => (0 : ℝ)) (fun _ => 0)
      (forecastActiveAxisEquiv U basis L a) = 0
    cases forecastActiveAxisEquiv U basis L a <;> rfl

theorem forecastJointCoordinateJoin_norm (c : Cont → ℝ) (z : (X ⊕ IntAxis) → ℝ) :
    ‖forecastJointCoordinateJoin U basis L c z‖ = max ‖c‖ ‖z‖ := by
  have h := (forecastJointCoordinateJoin_isometry (X := X) (I := I) U basis L).dist_eq
    (c, z) (0, 0)
  simpa only [forecastJointCoordinateJoin_zero, Prod.dist_eq, dist_zero_right, Prod.norm_def] using h

theorem forecastJointCoordinateJoin_integral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : ((Spatial → ℝ) × (Output → ℝ)) → V) :
    (∫ y, F y) = ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
      F (forecastJointCoordinateJoin U basis L p.1 p.2) := by
  simpa only [forecastJointCoordinateJoinEquiv_apply] using
    ((forecastJointCoordinateJoinEquiv_measurePreserving (X := X) (I := I) U basis L).integral_comp (forecastJointCoordinateJoinEquiv U basis L).measurableEmbedding F).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L
local notation "Cont" => (Σ j : Fin m, I j)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Domain" => (Spatial → ℝ) × (Output → ℝ)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis L hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis L

theorem forecastJoint_rational_reference
    {P Ω Z : Type*} [Fintype P] [Fintype Ω]
    (inactive : FiniteProbabilityWeights P) (active : P → FiniteProbabilityWeights Ω)
    (gridPoint : P → Z) (Y : P → Ω → Out → ℤ)
    (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
    (density : Domain → ℝ) (hdensity : Measurable density)
    (hnonneg : ∀ y, 0 ≤ density y)
    (test : Z → (Out → ZMod q) → Domain → ℂ) :
    (∑' z, 𝔼 r : (Aux ⊕ (X ⊕ IntAxis)) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint
        (fun i ω a => Y i ω ((axis).symm a)) N gridVolume z r / gridVolume : ℝ) : ℂ) *
      ∫ p : (Cont → ℝ) × ((X ⊕ IntAxis) → ℝ),
        (density (join p.1 p.2) : ℂ) *
          test z (fun a => ZMod.castHom hq (ZMod q) (r (axis a))) (join p.1 p.2)) =
    ∑' z, 𝔼 r : Out → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
        ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
          ∂realDensityMeasure volume density := by
  apply tsum_congr
  intro z
  symm
  apply Fintype.expect_equiv (outputAxisReindexAddEquiv axis (ZMod N)).toEquiv
  intro r
  rw [rationalInactiveForecast_axis_reindex axis]
  congr 1
  rw [realDensityMeasure_integral_complex volume density hdensity hnonneg]
  rw [forecastJointCoordinateJoin_integral U basis L]
  apply integral_congr_ae
  filter_upwards [] with p
  congr 2
  funext a
  exact congrArg (ZMod.castHom hq (ZMod q)) (congrArg r ((axis).symm_apply_apply a).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

theorem forecastJointOriginalGridMean_reindexed :
    let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
    let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
      test z (fun a => r (axis a)) (join p.1 p.2)
    let Y' := fun i ω a => Y i ω ((axis).symm a)
    forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale =
      (𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) := by
  intro g φ Y'
  have hraw :
      rationalInactiveForecast inactive active gridPoint Y N gridVolume =
        fun z r => rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
          (fun a => r ((axis).symm a)) := by
    funext z r
    exact rationalInactiveForecast_axis_reindex axis inactive active gridPoint Y N gridVolume z r
  unfold forecastJointOriginalGridMean
  simp only [hraw, g, φ, Equiv.apply_symm_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis Lsize
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

variable [NeZero q]

private theorem forecastJointOriginalGridMean_reindexed_comparison
    (hV : gridVolume ≠ 0) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P radius δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (C L K : ℝ≥0) (hg : LipschitzWith L density) (hg0 : ∀ y, 0 ≤ density y)
    (htest : ∀ z r, LipschitzWith K (test z r))
    (hcap : ∀ y, |density y| ≤ C) (hbound : ∀ z r y, ‖test z r y‖ ≤ 1)
    (hscale : ∀ j, 0 < scale j) (hradius : 0 ≤ radius) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ)
    (hsupport : ∀ y, radius < ‖y‖ → density y = 0) :
    let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
    let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
      test z (fun a => r (axis a)) (join p.1 p.2)
    let Y' := fun i ω a => Y i ω ((axis).symm a)
    ‖(𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) -
      (∑' z, 𝔼 r : (Aux ⊕ Joint) → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z r / gridVolume : ℝ) : ℂ) *
      ∫ p : (Cont → ℝ) × (Joint → ℝ), (g p : ℂ) * φ z (zmodPiReduction hq r) p
        ∂((volume : Measure (Cont → ℝ)).prod (volume : Measure (Joint → ℝ))))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * (2 * radius + 2) ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * radius + 2) ^ Fintype.card Joint * (L : ℝ) * δ)) *
          (2 * radius) ^ Fintype.card Cont +
        (2 * (D / cutoff)) * ∫ y, density y := by
  intro g φ Y'
  have hcard : Fintype.card Out = Fintype.card (Aux ⊕ Joint) := Fintype.card_congr axis
  have hg' : LipschitzWith L g := by
    simpa only [g, Function.comp_def, mul_one] using
      hg.comp (forecastJointCoordinateJoin_lipschitz (X := X) (I := I) U basis Lsize)
  have hφ' (z) (r : (Aux ⊕ Joint) → ZMod q) : LipschitzWith K (φ z r) := by
    simpa only [φ, Function.comp_def, mul_one] using
      (htest z (fun a => r (axis a))).comp
        (forecastJointCoordinateJoin_lipschitz (X := X) (I := I) U basis Lsize)
  have hs' (p : (Cont → ℝ) × (Joint → ℝ)) (hp : radius < ‖p‖) : g p = 0 := by
    apply hsupport
    change radius < ‖join p.1 p.2‖
    rw [forecastJointCoordinateJoin_norm]
    exact hp
  have hp' : ((Fintype.card (Aux ⊕ Joint) + 2 : ℕ) : ℝ) ≤ P := by rwa [← hcard]
  have hd' := fun i => finiteImageCharacteristic_axis_reindex_bound axis (active i) (Y i) N (hdecay i)
  have h := rationalInactive_joint_grid_comparison_instances inactive active gridPoint Y' hV q hq cutoff hcutoff
    hD hp' hd' g φ C L K hg' (fun p => hg0 _) hφ' (fun p => hcap _)
      (fun z r p => hbound _ _ _) center scale hscale hradius hδ hδ1 hmesh hs'
  have hmass : (∫ p : (Cont → ℝ) × (Joint → ℝ), g p
      ∂((volume : Measure (Cont → ℝ)).prod (volume : Measure (Joint → ℝ)))) =
      ∫ y, density y := (forecastJointCoordinateJoin_integral U basis Lsize density).symm
  exact h.trans_eq (by rw [hmass, ← hcard])

theorem forecastJointOriginalGridMean_comparison_s2_oai
    (hV : gridVolume ≠ 0) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P radius δ : ℝ} (hD : 0 ≤ D)
    (hP : ((Fintype.card Out + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (Out → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (C L K : ℝ≥0) (hg : LipschitzWith L density) (hg0 : ∀ y, 0 ≤ density y)
    (htest : ∀ z r, LipschitzWith K (test z r))
    (hcap : ∀ y, |density y| ≤ C) (hbound : ∀ z r y, ‖test z r y‖ ≤ 1)
    (hscale : ∀ j, 0 < scale j) (hradius : 0 ≤ radius) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) / scale j ≤ δ)
    (hsupport : ∀ y, radius < ‖y‖ → density y = 0) :
    ‖forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale -
      (∑' z, 𝔼 r : Out → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z r / gridVolume : ℝ) : ℂ) *
          ∫ y, test z (fun a => ZMod.castHom hq (ZMod q) (r a)) y
            ∂realDensityMeasure volume density)‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card Out + 1) *
        (2 * (2 * radius + 2) ^ Fintype.card Joint * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * radius + 2) ^ Fintype.card Joint * (L : ℝ) * δ)) *
          (2 * radius) ^ Fintype.card Cont +
        (2 * (D / cutoff)) * ∫ y, density y := by
  let g := fun p : (Cont → ℝ) × (Joint → ℝ) => density (join p.1 p.2)
  let φ := fun z (r : (Aux ⊕ Joint) → ZMod q) (p : (Cont → ℝ) × (Joint → ℝ)) =>
    test z (fun a => r (axis a)) (join p.1 p.2)
  let Y' := fun i ω a => Y i ω ((axis).symm a)
  have h := forecastJointOriginalGridMean_reindexed_comparison U basis Lsize hm
    inactive active gridPoint Y N q hq gridVolume density test center scale hV cutoff hcutoff
    hD hP hdecay C L K hg hg0 htest hcap hbound hscale hradius hδ hδ1 hmesh hsupport
  have hmean : forecastJointOriginalGridMean U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale =
      (𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
        (∑' z, ∑' k : Joint → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
          ((rationalInactiveForecast inactive active gridPoint Y' N gridVolume z
            (Sum.elim aux (fun j => (k j : ZMod N))) / gridVolume : ℝ) : ℂ) *
          φ z (Sum.elim (zmodPiReduction hq aux) (fun j => (k j : ZMod q)))
            (c, fun j => ((k j : ℝ) - center j) / scale j)) /
            ((∏ j, scale j : ℝ) : ℂ)) :=
    forecastJointOriginalGridMean_reindexed U basis Lsize hm inactive active gridPoint Y N q hq
      gridVolume density test center scale
  rw [hmean]
  have href := forecastJoint_rational_reference U basis Lsize hm inactive active gridPoint Y N q hq
    gridVolume density hg.continuous.measurable hg0 test
  convert h using 1
  congr 2
  exact href.symm

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.forecastJointOriginalGridMean_comparison_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
