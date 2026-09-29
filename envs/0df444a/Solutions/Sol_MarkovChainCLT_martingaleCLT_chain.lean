-- Prove2me | solution 1 for MarkovChainCLT.martingaleCLT_chain
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:47:54.58103+00:00
-- url     : https://prove2.me/submissions/6339f9a6-c2ad-42d0-8457-6d6a17d3a6da

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing
import Theorems.Thm_MarkovChainCLT_chainMeasure_eq_comp_traj
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_chainMeasure
import Definitions.Def_MarkovErgodicity
import Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future
import Theorems.Thm_MarkovChainCLT_processSigma_Ici_eq_comap_shift
import Theorems.Thm_MarkovChainCLT_processSigma_Iic_eq_comap_restrict
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/- Complete proof components for the chain martingale CLT.
The five generic UI/MDS components retain the complete bodies from accepted
Prove2Me submission 5b366a5e-0a3b-46f3-ae2f-3689f4448c20. The full truncation
tail proof is from accepted 9bf13022-35a0-4f8f-b749-aa19388cce2a. HarrisAlpha
credits the accepted restart argument it adapts while removing its extra
countability assumption through measurable event deviations. -/

section ChainMartingaleComponent1

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace NumberChainSummableRhoUI

variable {Omega I : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_of_uniform_Lp_approximation
    {p : ENNReal} (hp : 1 <= p) {X : I -> Omega -> Real}
    (hX : forall i, MemLp (X i) p P)
    (happrox : forall eps : Real, 0 < eps ->
      exists G : I -> Omega -> Real, UniformIntegrable G p P /\
        forall i, eLpNorm (X i - G i) p P <= ENNReal.ofReal eps) :
    UniformIntegrable X p P := by
  refine And.intro (fun i => (hX i).aestronglyMeasurable) (And.intro ?_ ?_)
  · intro eps heps
    obtain ⟨G, hG, hdist⟩ := happrox (eps / 2) (half_pos heps)
    obtain ⟨delta, hdelta, hsmall⟩ := hG.unifIntegrable (half_pos heps)
    refine ⟨delta, hdelta, fun i s hs hPs => ?_⟩
    have hid : s.indicator (X i) =
        s.indicator (X i - G i) + s.indicator (G i) := by
      rw [<- indicator_add']
      congr 1
      exact (sub_add_cancel _ _).symm
    rw [hid]
    calc
      eLpNorm (s.indicator (X i - G i) + s.indicator (G i)) p P <=
          eLpNorm (s.indicator (X i - G i)) p P + eLpNorm (s.indicator (G i)) p P :=
        eLpNorm_add_le (((hX i).aestronglyMeasurable.sub
          (hG.aestronglyMeasurable i)).indicator hs)
          ((hG.aestronglyMeasurable i).indicator hs) hp
      _ <= ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) :=
        add_le_add ((eLpNorm_indicator_le _).trans (hdist i)) (hsmall i s hs hPs)
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_add (half_pos heps).le (half_pos heps).le, add_halves]
  · obtain ⟨G, hG, hdist⟩ := happrox 1 zero_lt_one
    obtain ⟨C, hC⟩ := hG.2.2
    refine ⟨C + 1, fun i => ?_⟩
    calc
      eLpNorm (X i) p P = eLpNorm (X i - G i + G i) p P := by rw [sub_add_cancel]
      _ <= eLpNorm (X i - G i) p P + eLpNorm (G i) p P :=
        eLpNorm_add_le ((hX i).aestronglyMeasurable.sub (hG.aestronglyMeasurable i))
          (hG.aestronglyMeasurable i) hp
      _ <= ENNReal.ofReal 1 + C := add_le_add (hdist i) (hC i)
      _ = (C + 1 : NNReal) := by simp [add_comm]

theorem uniformIntegrable_add
    {p : ENNReal} (hp : 1 <= p) {X Y : I -> Omega -> Real}
    (hX : UniformIntegrable X p P) (hY : UniformIntegrable Y p P) :
    UniformIntegrable (fun i x => X i x + Y i x) p P := by
  refine ⟨(fun i => (hX.1 i).add (hY.1 i)),
    hX.unifIntegrable.add hY.unifIntegrable hp hX.1 hY.1, ?_⟩
  obtain ⟨C, hC⟩ := hX.2.2
  obtain ⟨D, hD⟩ := hY.2.2
  refine ⟨C + D, fun i => ?_⟩
  exact (eLpNorm_add_le (hX.1 i) (hY.1 i) hp).trans (by exact_mod_cast add_le_add (hC i) (hD i))

theorem uniformIntegrable_comp
    {p : ENNReal} {X : I -> Omega -> Real} (hX : UniformIntegrable X p P)
    {J : Type*} (r : J -> I) : UniformIntegrable (fun j => X (r j)) p P := by
  refine ⟨fun j => hX.1 (r j), ?_, ?_⟩
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable heps
    exact ⟨d, hd, fun j => hsmall (r j)⟩
  · obtain ⟨C, hC⟩ := hX.2.2
    exact ⟨C, fun j => hC (r j)⟩

theorem uniformIntegrable_of_Lp_null
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X : Nat -> Omega -> Real} (hX : forall n, MemLp (X n) p P)
    (hnull : Tendsto (fun n => eLpNorm (X n) p P) atTop (𝓝 0)) :
    UniformIntegrable X p P := by
  refine ⟨fun n => (hX n).1, unifIntegrable_of_tendsto_Lp_zero hp hpt hX hnull, ?_⟩
  have ht : Tendsto (fun n => (eLpNorm (X n) p P).toReal) atTop (𝓝 (0 : Real)) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hnull
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨Real.toNNReal C, fun n => ?_⟩
  change eLpNorm (X n) p P <= ENNReal.ofReal C
  rw [<- ENNReal.ofReal_toReal (hX n).2.ne]
  exact ENNReal.ofReal_le_ofReal (hC ⟨n, rfl⟩)

theorem uniformIntegrable_add_Lp_null
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X R : Nat -> Omega -> Real} (hX : UniformIntegrable X p P)
    (hR : forall n, MemLp (R n) p P)
    (hnull : Tendsto (fun n => eLpNorm (R n) p P) atTop (𝓝 0)) :
    UniformIntegrable (fun n x => X n x + R n x) p P :=
  uniformIntegrable_add hp hX (uniformIntegrable_of_Lp_null hp hpt hR hnull)

theorem eLpNorm_square (f : Omega -> Real) (p : ENNReal) :
    eLpNorm (fun x => f x ^ 2) p P = eLpNorm f (p * 2) P ^ 2 := by
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
    ENNReal.rpow_two] using (eLpNorm_norm_rpow (p := p) (μ := P) f (by norm_num : (0 : Real) < 2))

theorem uniformIntegrable_square {X : I -> Omega -> Real}
    (hX : UniformIntegrable X 2 P) :
    UniformIntegrable (fun i x => X i x ^ 2) 1 P := by
  refine ⟨fun i => (hX.1 i).pow 2, ?_, ?_⟩
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable (Real.sqrt_pos.2 heps)
    refine ⟨d, hd, fun i s hs hPs => ?_⟩
    have hid : s.indicator (fun x => X i x ^ 2) = fun x => (s.indicator (X i) x) ^ 2 := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hid, eLpNorm_square, one_mul]
    calc
      eLpNorm (s.indicator (X i)) 2 P ^ 2 <= ENNReal.ofReal (Real.sqrt eps) ^ 2 :=
        pow_le_pow_left' (hsmall i s hs hPs) 2
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt heps.le]
  · obtain ⟨C, hC⟩ := hX.2.2
    refine ⟨C ^ 2, fun i => ?_⟩
    rw [eLpNorm_square, one_mul, ENNReal.coe_pow]
    exact pow_le_pow_left' (hC i) 2

theorem uniformIntegrable_bounded_mul
    {p : ENNReal} {X : I -> Omega -> Real} (hX : UniformIntegrable X p P)
    {a : I -> Real} (C : NNReal) (ha : forall i, |a i| <= C) :
    UniformIntegrable (fun i x => a i * X i x) p P := by
  have hnorm : forall i, ‖a i‖ₑ <= (C : ENNReal) := by
    intro i
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_of_le_toReal (by simpa using ha i)
  refine ⟨fun i => (hX.1 i).const_mul (a i), ?_, ?_⟩
  · intro eps heps
    have hCpos : (0 : Real) < C + 1 := by positivity
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable (div_pos heps hCpos)
    refine ⟨d, hd, fun i s hs hPs => ?_⟩
    have hid : s.indicator (fun x => a i * X i x) = a i • s.indicator (X i) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hid, eLpNorm_const_smul]
    calc
      ‖a i‖ₑ * eLpNorm (s.indicator (X i)) p P <=
          (C : ENNReal) * ENNReal.ofReal (eps / (C + 1)) :=
        mul_le_mul' (hnorm i) (hsmall i s hs hPs)
      _ <= ENNReal.ofReal (C + 1) * ENNReal.ofReal (eps / (C + 1)) := by
        gcongr
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_le_ofReal (show (C : Real) <= (C : Real) + 1 by linarith))
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_mul hCpos.le, mul_div_cancel₀ _ hCpos.ne']
  · obtain ⟨D, hD⟩ := hX.2.2
    refine ⟨C * D, fun i => ?_⟩
    change eLpNorm (a i • X i) p P <= _
    rw [eLpNorm_const_smul, ENNReal.coe_mul]
    exact mul_le_mul' (hnorm i) (hD i)

theorem uniformIntegrable_of_succ
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X : Nat -> Omega -> Real} (hzero : MemLp (X 0) p P)
    (htail : UniformIntegrable (fun n => X (n + 1)) p P) :
    UniformIntegrable X p P := by
  have hz : UniformIntegrable (fun _ : Unit => X 0) p P :=
    uniformIntegrable_const hp hpt hzero
  obtain ⟨C, hC⟩ := hz.2.2
  obtain ⟨D, hD⟩ := htail.2.2
  refine ⟨?_, ?_, max C D, ?_⟩
  · intro n
    cases n with
    | zero => exact hzero.1
    | succ n => exact htail.1 n
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hz.unifIntegrable heps
    obtain ⟨e, he, hsmall'⟩ := htail.unifIntegrable heps
    refine ⟨min d e, lt_min hd he, fun n s hs hPs => ?_⟩
    cases n with
    | zero => exact hsmall () s hs (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    | succ n => exact hsmall' n s hs (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  · intro n
    cases n with
    | zero => exact (hC ()).trans (by exact_mod_cast le_max_left C D)
    | succ n => exact (hD n).trans (by exact_mod_cast le_max_right C D)

end NumberChainSummableRhoUI

end ChainMartingaleComponent1

section ChainMartingaleComponent2

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace NumberChainSummableRhoUI

variable {Omega I : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_two_of_bounded_four
    [IsProbabilityMeasure P] {X : I -> Omega -> Real}
    (hX : forall i, AEStronglyMeasurable (X i) P)
    (C : NNReal) (hC : forall i, eLpNorm (X i) 4 P <= C) :
    UniformIntegrable X 2 P := by
  refine ⟨hX, ?_, C, fun i =>
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ENNReal) <= 4) (hX i)).trans (hC i)⟩
  intro eps heps
  have hCpos : (0 : Real) < C + 1 := by positivity
  let r : Real := eps / (C + 1)
  have hr : 0 < r := div_pos heps hCpos
  refine ⟨r ^ 4, pow_pos hr 4, fun i s hs hPs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hroot : (ENNReal.ofReal (r ^ 4)) ^ (1 / 4 : Real) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_pow hr.le, <- ENNReal.rpow_natCast,
      <- ENNReal.rpow_mul]
    norm_num
  calc
    eLpNorm (X i) 2 (P.restrict s) <=
        eLpNorm (X i) 4 (P.restrict s) * P s ^ (1 / 4 : Real) := by
      convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := P.restrict s) (by norm_num : (2 : ENNReal) <= 4) (hX i).restrict using 1
      norm_num
    _ <= (C : ENNReal) * (ENNReal.ofReal (r ^ 4)) ^ (1 / 4 : Real) :=
      mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i))
        (ENNReal.rpow_le_rpow hPs (by norm_num))
    _ = (C : ENNReal) * ENNReal.ofReal r := by rw [hroot]
    _ <= ENNReal.ofReal ((C : Real) + 1) * ENNReal.ofReal r := by
      gcongr
      simpa only [ENNReal.ofReal_coe_nnreal] using
        (ENNReal.ofReal_le_ofReal (show (C : Real) <= (C : Real) + 1 by linarith))
    _ = ENNReal.ofReal eps := by
      rw [<- ENNReal.ofReal_mul hCpos.le]
      congr 1
      exact mul_div_cancel₀ eps hCpos.ne'

theorem eLpNorm_fourth (f : Omega -> Real) :
    eLpNorm (fun x => f x ^ 4) 1 P = eLpNorm f 4 P ^ 4 := by
  have heq : (fun x => f x ^ 4) = fun x => (f x ^ 2) ^ 2 := by
    ext x
    ring
  rw [heq, eLpNorm_square, one_mul, eLpNorm_square]
  norm_num [<- pow_mul]

theorem uniformIntegrable_two_of_fourth_moment
    [IsProbabilityMeasure P] {X : I -> Omega -> Real}
    (hX : forall i, AEStronglyMeasurable (X i) P)
    (hint : forall i, Integrable (fun x => X i x ^ 4) P)
    (C : NNReal) (hC : forall i, (∫ x, X i x ^ 4 ∂P) <= C) :
    UniformIntegrable X 2 P := by
  have hpow : forall i, eLpNorm (X i) 4 P ^ 4 <= (C : ENNReal) := by
    intro i
    rw [<- eLpNorm_fourth]
    rw [eLpNorm_one_eq_lintegral_enorm]
    have heq : (fun x => ‖X i x ^ 4‖ₑ) = fun x => ENNReal.ofReal (X i x ^ 4) := by
      ext x
      rw [Real.enorm_eq_ofReal (by positivity)]
    rw [heq, <- ofReal_integral_eq_lintegral_ofReal (hint i) (by filter_upwards with x using by positivity)]
    exact ENNReal.ofReal_le_of_le_toReal (by simpa using hC i)
  apply uniformIntegrable_two_of_bounded_four hX (C + 1)
  intro i
  have hbig : (C : ENNReal) <= ((C + 1 : NNReal) : ENNReal) ^ 4 := by
    exact_mod_cast (show C <= (C + 1) ^ 4 by nlinarith [sq_nonneg C, sq_nonneg (C * C)])
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : Real) < 4)).1
  convert (hpow i).trans hbig using 1 <;> first | rfl | norm_num

end NumberChainSummableRhoUI

end ChainMartingaleComponent2

section ChainMartingaleComponent3

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace NumberChainSummableRhoUI

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_bounded_mul_of_tendsto
    {p : ENNReal} {X : Nat -> Omega -> Real} (hX : UniformIntegrable X p P)
    {a : Nat -> Real} {b : Real} (ha : Tendsto a atTop (𝓝 b)) :
    UniformIntegrable (fun n x => a n * X n x) p P := by
  obtain ⟨C, hC⟩ := ha.abs.bddAbove_range
  apply uniformIntegrable_bounded_mul hX (Real.toNNReal C)
  intro n
  exact (hC ⟨n, rfl⟩).trans (Real.le_coe_toNNReal C)

theorem uniformIntegrable_variance_normalized
    {S : Nat -> Omega -> Real} (hzero : S 0 = 0)
    (hUI : UniformIntegrable (fun n x => S (n + 1) x / Real.sqrt (n + 1)) 2 P)
    {v : Real} (hv : 0 < v)
    (hvar : Tendsto (fun n : Nat =>
      (∫ x, S (n + 1) x ^ 2 ∂P) / (n + 1 : Real)) atTop (𝓝 v)) :
    UniformIntegrable
      (fun n x => S n x ^ 2 / (∫ y, S n y ^ 2 ∂P)) 1 P := by
  apply uniformIntegrable_of_succ (by norm_num) (by simp)
  · simp [hzero]
  have ha : Tendsto (fun n : Nat => (n + 1 : Real) / (∫ x, S (n + 1) x ^ 2 ∂P))
      atTop (𝓝 v⁻¹) := by
    simpa only [inv_div] using hvar.inv₀ hv.ne'
  have h := uniformIntegrable_bounded_mul_of_tendsto (uniformIntegrable_square hUI) ha
  apply h.ae_eq
  intro n
  filter_upwards with x
  have hn : (0 : Real) < n + 1 := by positivity
  rw [div_pow, Real.sq_sqrt hn.le]
  by_cases hd : (∫ y, S (n + 1) y ^ 2 ∂P) = 0
  · simp [hd]
  · field_simp

end NumberChainSummableRhoUI

end ChainMartingaleComponent3

section ChainMartingaleComponent4

open MeasureTheory
open scoped ENNReal NNReal

namespace NumberChainSummableRhoUI

/- The following complete FourthRecurrence namespace is retained verbatim from
ryanshin's accepted submission b434e964-c658-411b-ab9f-bcba879ef869 for theorem
5909e9db-042a-4d8a-8050-d16e7bec2e97. Original source SHA256:
4feb5e7528ab36453533dc6816954ffb736c4e6ba2684769f71e4e5eed454629.
The selected byte interval [670,6847) has SHA256:
08903a629552b23fbbbcb9380353c959b5ace1bdabfb10c38847cd1b9c37ed92.
Only this enclosing namespace and focused imports are new. -/

namespace FourthRecurrence

variable {Ω : Type*} [MeasurableSpace Ω]

def partialSum (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, D k ω

omit [MeasurableSpace Ω] in
theorem partialSum_zero (D : ℕ → Ω → ℝ) (ω : Ω) : partialSum D 0 ω = 0 := by
  simp [partialSum]

omit [MeasurableSpace Ω] in
theorem partialSum_succ (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum D (n + 1) ω = partialSum D n ω + D n ω := by
  simp [partialSum, Finset.sum_range_succ]

theorem measurable_partialSum (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (n : ℕ) :
    Measurable (partialSum D n) := by
  unfold partialSum
  exact Finset.measurable_sum _ (fun n _ => hD n)

omit [MeasurableSpace Ω] in
theorem partialSum_bound (D : ℕ → Ω → ℝ) (c : ℝ)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n : ℕ) (ω : Ω) :
    |partialSum D n ω| ≤ (n : ℝ) * c := by
  unfold partialSum
  calc
    |∑ k ∈ Finset.range n, D k ω| ≤ ∑ k ∈ Finset.range n, |D k ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, c := Finset.sum_le_sum (fun k _ => hbound k ω)
    _ = (n : ℝ) * c := by simp

theorem integrable_monomial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n p q : ℕ) :
    Integrable (fun ω => partialSum D n ω ^ p * D n ω ^ q) μ := by
  apply Integrable.of_bound
    (((measurable_partialSum D hD n).pow_const p).mul ((hD n).pow_const q)).aestronglyMeasurable
    (((n : ℝ) * c) ^ p * c ^ q)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Pi.mul_apply, norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) (partialSum_bound D c hbound n ω) p)
    (pow_le_pow_left₀ (abs_nonneg _) (hbound n ω) q)
    (by positivity) (by positivity)

theorem integrable_fourth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => partialSum D n ω ^ 4) μ := by
  simpa only [pow_zero, mul_one] using integrable_monomial μ D hD c hc hbound n 4 0

theorem fourth_step_bound (m d c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hm : |m| ≤ t * c) (hd : |d| ≤ c) :
    (m + d) ^ 4 ≤ m ^ 4 + 4 * (m ^ 3 * d) +
      6 * c ^ 2 * m ^ 2 + (4 * t + 1) * c ^ 4 := by
  have hd2 : d ^ 2 ≤ c ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hd4 : d ^ 4 ≤ c ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg d) hd2 2
  have hmd3 : m * d ^ 3 ≤ t * c ^ 4 := by
    calc
      m * d ^ 3 ≤ |m * d ^ 3| := le_abs_self _
      _ = |m| * |d| ^ 3 := by rw [abs_mul, abs_pow]
      _ ≤ (t * c) * c ^ 3 :=
        mul_le_mul hm (pow_le_pow_left₀ (abs_nonneg d) hd 3) (by positivity) (by positivity)
      _ = t * c ^ 4 := by ring
  have hmd2 : m ^ 2 * d ^ 2 ≤ c ^ 2 * m ^ 2 := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd2 (sq_nonneg m)
  nlinarith

theorem integral_fourth_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c)
    (horth : ∀ n, ∫ ω, partialSum D n ω ^ 3 * D n ω ∂μ = 0)
    (hsecond : ∀ n, (∫ ω, partialSum D n ω ^ 2 ∂μ) ≤ (n : ℝ) * c ^ 2)
    (n : ℕ) :
    (∫ ω, partialSum D n ω ^ 4 ∂μ) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      have hi4 := integrable_fourth μ D hD c hc hbound n
      have hi3 : Integrable (fun ω => partialSum D n ω ^ 3 * D n ω) μ := by
        simpa only [pow_one] using integrable_monomial μ D hD c hc hbound n 3 1
      have hi2 : Integrable (fun ω => partialSum D n ω ^ 2) μ := by
        simpa only [pow_zero, mul_one] using integrable_monomial μ D hD c hc hbound n 2 0
      have hstep : (∫ ω, partialSum D (n + 1) ω ^ 4 ∂μ) ≤
          (∫ ω, partialSum D n ω ^ 4 ∂μ) +
          6 * c ^ 2 * (∫ ω, partialSum D n ω ^ 2 ∂μ) +
          (4 * (n : ℝ) + 1) * c ^ 4 := by
        calc
          (∫ ω, partialSum D (n + 1) ω ^ 4 ∂μ) ≤
              ∫ ω, partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω) +
                (6 * c ^ 2) * partialSum D n ω ^ 2 + (4 * (n : ℝ) + 1) * c ^ 4 ∂μ := by
            apply integral_mono (integrable_fourth μ D hD c hc hbound (n + 1))
              (((hi4.add (hi3.const_mul 4)).add (hi2.const_mul (6 * c ^ 2))).add
                (integrable_const ((4 * (n : ℝ) + 1) * c ^ 4)))
            intro ω
            dsimp only [Pi.add_apply]
            rw [partialSum_succ]
            exact fourth_step_bound _ _ c n hc (Nat.cast_nonneg n)
              (partialSum_bound D c hbound n ω) (hbound n ω)
          _ = _ := by
            rw [integral_add
                (f := fun ω => partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω) +
                  (6 * c ^ 2) * partialSum D n ω ^ 2)
                (g := fun _ => (4 * (n : ℝ) + 1) * c ^ 4)
                ((hi4.add (hi3.const_mul 4)).add (hi2.const_mul (6 * c ^ 2)))
                (integrable_const ((4 * (n : ℝ) + 1) * c ^ 4)),
              integral_add
                (f := fun ω => partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω))
                (g := fun ω => (6 * c ^ 2) * partialSum D n ω ^ 2)
                (hi4.add (hi3.const_mul 4)) (hi2.const_mul (6 * c ^ 2)),
              integral_add (f := fun ω => partialSum D n ω ^ 4)
                (g := fun ω => 4 * (partialSum D n ω ^ 3 * D n ω)) hi4 (hi3.const_mul 4)]
            simp only [integral_const_mul, integral_const, horth n, mul_zero, add_zero,
              probReal_univ, smul_eq_mul, one_mul]
      have hsecond' := mul_le_mul_of_nonneg_left (hsecond n) (by positivity : 0 ≤ 6 * c ^ 2)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hc4 : 0 ≤ c ^ 4 := by positivity
      push_cast
      nlinarith

end FourthRecurrence

abbrev mdsSum {Ω : Type*} (D : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  FourthRecurrence.partialSum D n

noncomputable def normalizedMdsSum {Ω : Type*} (D : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := mdsSum D n ω / Real.sqrt ((n : ℝ) + 1)

section

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

lemma integral_mul_eq_zero_of_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {U D : Ω → ℝ}
    (hU : AEStronglyMeasurable[m] U P) (hUD : Integrable (U * D) P)
    (hD : Integrable D P) (hzero : P[D | m] =ᵐ[P] 0) :
    (∫ ω, U ω * D ω ∂P) = 0 := by
  haveI : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  have hpull := condExp_mul_of_aestronglyMeasurable_left hU hUD hD
  calc
    (∫ ω, U ω * D ω ∂P) = ∫ ω, (P[U * D | m]) ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, U ω * (P[D | m]) ω ∂P := integral_congr_ae hpull
    _ = 0 := by
      calc
        _ = ∫ _ω : Ω, (0 : ℝ) ∂P := by
          apply integral_congr_ae
          filter_upwards [hzero] with ω hω
          simp only [hω, Pi.zero_apply, mul_zero]
        _ = 0 := by simp

lemma mdsSum_aestronglyMeasurable_past (P : Measure Ω) (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P) (n : ℕ) :
    AEStronglyMeasurable[F n] (mdsSum D n) P := by
  let G : ℕ → Ω → ℝ := fun i => (hD i).mk (D i)
  have hG : Measurable[F n] (fun ω => ∑ i ∈ Finset.range n, G i ω) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((hD i).stronglyMeasurable_mk.mono
      (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))).measurable
  refine ⟨_, hG.stronglyMeasurable, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => (hD i).ae_eq_mk)] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

lemma memLp_mdsSum (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (n : ℕ) : MemLp (mdsSum D n) 2 P :=
  memLp_finsetSum (Finset.range n) (fun i _ => hD i)

lemma memLp_normalizedMdsSum (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (n : ℕ) : MemLp (normalizedMdsSum D n) 2 P := by
  unfold normalizedMdsSum
  simpa only [div_eq_mul_inv] using
    (memLp_mdsSum P D hD n).mul_const (Real.sqrt ((n : ℝ) + 1))⁻¹

theorem integral_mdsSum_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    (∫ ω, mdsSum D n ω ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P := by
  induction n with
  | zero => simp [mdsSum, FourthRecurrence.partialSum]
  | succ n ih =>
      have hM := memLp_mdsSum P D hL2 n
      have hiM : Integrable (fun ω => mdsSum D n ω ^ 2) P :=
        (memLp_two_iff_integrable_sq hM.1).mp hM
      have hiD : Integrable (fun ω => D n ω ^ 2) P :=
        (memLp_two_iff_integrable_sq (hL2 n).1).mp (hL2 n)
      have hiMD : Integrable (fun ω => mdsSum D n ω * D n ω) P :=
        hM.integrable_mul (hL2 n)
      have hMD : (∫ ω, mdsSum D n ω * D n ω ∂P) = 0 :=
        integral_mul_eq_zero_of_condExp P (F.le n)
          (mdsSum_aestronglyMeasurable_past P F D hD n) hiMD
          ((hL2 n).integrable (by norm_num)) (hzero n)
      have hpoly : (fun ω => mdsSum D (n + 1) ω ^ 2) =
          (fun ω => mdsSum D n ω ^ 2 + 2 * (mdsSum D n ω * D n ω) + D n ω ^ 2) := by
        funext ω
        simp only [mdsSum, FourthRecurrence.partialSum_succ]
        ring
      rw [hpoly, integral_add
          (f := fun ω => mdsSum D n ω ^ 2 + 2 * (mdsSum D n ω * D n ω))
          (g := fun ω => D n ω ^ 2) (hiM.add (hiMD.const_mul 2)) hiD,
        integral_add (f := fun ω => mdsSum D n ω ^ 2)
          (g := fun ω => 2 * (mdsSum D n ω * D n ω)) hiM (hiMD.const_mul 2),
        integral_const_mul, hMD,
        mul_zero, add_zero, ih, Finset.sum_range_succ]

theorem integral_normalizedMdsSum_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    (∫ ω, normalizedMdsSum D n ω ^ 2 ∂P) =
      (∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P) / ((n : ℝ) + 1) := by
  simp only [normalizedMdsSum, div_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  rw [integral_div, integral_mdsSum_sq P F D hD hL2 hzero]

theorem integral_normalizedMdsSum_sq_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, (∫ ω, D i ω ^ 2 ∂P) ≤ B) (n : ℕ) :
    (∫ ω, normalizedMdsSum D n ω ^ 2 ∂P) ≤ B := by
  rw [integral_normalizedMdsSum_sq P F D hD hL2 hzero]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  calc
    _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (n : ℝ) * B := by simp
    _ ≤ B * ((n : ℝ) + 1) := by nlinarith

lemma mdsSum_congr_ae (P : Measure Ω) {D E : ℕ → Ω → ℝ}
    (hDE : ∀ n, D n =ᵐ[P] E n) (n : ℕ) :
    mdsSum D n =ᵐ[P] mdsSum E n := by
  filter_upwards [ae_all_iff.mpr hDE] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

theorem bounded_mds_fourth (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => mdsSum D n ω ^ 4) P ∧
      (∫ ω, mdsSum D n ω ^ 4 ∂P) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2 := by
  classical
  let E : ℕ → Ω → ℝ := fun i ω => max (-c) (min c ((hD i).mk (D i) ω))
  have hEm (i : ℕ) : Measurable[F (i + 1)] (E i) :=
    measurable_const.max (measurable_const.min (hD i).stronglyMeasurable_mk.measurable)
  have hEglobal (i : ℕ) : Measurable (E i) :=
    ((hEm i).stronglyMeasurable.mono (F.le (i + 1))).measurable
  have hEadapt (i : ℕ) : AEStronglyMeasurable[F (i + 1)] (E i) P :=
    (hEm i).stronglyMeasurable.aestronglyMeasurable
  have hEb (i : ℕ) (ω : Ω) : |E i ω| ≤ c := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hDE (i : ℕ) : D i =ᵐ[P] E i := by
    filter_upwards [(hD i).ae_eq_mk, hbound i] with ω hrep hb
    dsimp only [E]
    rw [← hrep, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  have hEL2 (i : ℕ) : MemLp (E i) 2 P :=
    MemLp.of_bound (hEglobal i).aestronglyMeasurable c
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hEb i ω)
  have hEzero (i : ℕ) : P[E i | F i] =ᵐ[P] 0 :=
    (condExp_congr_ae (hDE i).symm).trans (hzero i)
  have hsecond (i : ℕ) : (∫ ω, mdsSum E i ω ^ 2 ∂P) ≤ (i : ℝ) * c ^ 2 := by
    rw [integral_mdsSum_sq P F E hEadapt hEL2 hEzero]
    calc
      _ ≤ ∑ _j ∈ Finset.range i, c ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hi : Integrable (fun ω => E j ω ^ 2) P :=
          (memLp_two_iff_integrable_sq (hEL2 j).1).mp (hEL2 j)
        calc
          _ ≤ ∫ _ω : Ω, c ^ 2 ∂P := integral_mono hi (integrable_const _) (fun ω => by
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hEb j ω) 2)
          _ = c ^ 2 := by simp
      _ = _ := by simp
  have horth (i : ℕ) : (∫ ω, mdsSum E i ω ^ 3 * E i ω ∂P) = 0 := by
    have hi : Integrable (fun ω => mdsSum E i ω ^ 3 * E i ω) P := by
      simpa only [pow_one] using
        FourthRecurrence.integrable_monomial P E hEglobal c hc hEb i 3 1
    exact integral_mul_eq_zero_of_condExp P (F.le i)
      ((mdsSum_aestronglyMeasurable_past P F E hEadapt i).pow 3) hi
      ((hEL2 i).integrable (by norm_num)) (hEzero i)
  have hi4 := FourthRecurrence.integrable_fourth P E hEglobal c hc hEb n
  have hb4 := FourthRecurrence.integral_fourth_le P E hEglobal c hc hEb horth hsecond n
  have hsum : (fun ω => mdsSum D n ω ^ 4) =ᵐ[P]
      (fun ω => mdsSum E n ω ^ 4) := (mdsSum_congr_ae P hDE n).pow_const 4
  refine ⟨hi4.congr hsum.symm, ?_⟩
  rw [integral_congr_ae hsum]
  exact hb4

theorem bounded_normalizedMdsSum_fourth (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => normalizedMdsSum D n ω ^ 4) P ∧
      (∫ ω, normalizedMdsSum D n ω ^ 4 ∂P) ≤ 6 * c ^ 4 := by
  obtain ⟨hi, hb⟩ := bounded_mds_fourth P F D hD hzero c hc hbound n
  have hs : Real.sqrt ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 2 := by
    calc
      _ = (Real.sqrt ((n : ℝ) + 1) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  simp only [normalizedMdsSum, div_pow, hs]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  apply (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).mpr
  have hn : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact hb.trans (mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 6 * c ^ 4))

end

end NumberChainSummableRhoUI

end ChainMartingaleComponent4

section ChainMartingaleComponent5

open MeasureTheory
open scoped ENNReal NNReal

namespace NumberChainSummableRhoUI

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

lemma eLpNorm_two_sq_eq_integral (P : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    eLpNorm f 2 P ^ 2 = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  have hs : eLpNorm (fun ω => f ω ^ 2) 1 P = eLpNorm f 2 P ^ 2 := by
    simpa only [one_mul] using eLpNorm_square (P := P) f 1
  rw [← hs, eLpNorm_one_eq_lintegral_enorm]
  have heq : (fun ω => ‖f ω ^ 2‖ₑ) = fun ω => ENNReal.ofReal (f ω ^ 2) := by
    funext ω
    exact Real.enorm_eq_ofReal (sq_nonneg _)
  rw [heq]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq hf.1).mp hf)
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))).symm

lemma eLpNorm_two_le_iff_integral_sq_le (P : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 P) {B : ℝ} (hB : 0 ≤ B) :
    eLpNorm f 2 P ≤ ENNReal.ofReal B ↔ (∫ ω, f ω ^ 2 ∂P) ≤ B ^ 2 := by
  rw [← ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0),
    eLpNorm_two_sq_eq_integral P hf, ← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)]

noncomputable def centeredMdsApproximation (P : Measure Ω)
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  W n - P[W n | F n]

lemma centeredMdsApproximation_adapted (P : Measure Ω) (F : Filtration ℕ m0)
    (W : ℕ → Ω → ℝ)
    (hW : ∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) (n : ℕ) :
    AEStronglyMeasurable[F (n + 1)] (centeredMdsApproximation P F W n) P :=
  (hW n).sub ((stronglyMeasurable_condExp.mono (F.mono (Nat.le_succ n))).aestronglyMeasurable)

lemma centeredMdsApproximation_memLp (P : Measure Ω) (F : Filtration ℕ m0)
    (W : ℕ → Ω → ℝ) (hW : ∀ n, MemLp (W n) 2 P) (n : ℕ) :
    MemLp (centeredMdsApproximation P F W n) 2 P :=
  (hW n).sub ((hW n).condExp (by norm_num))

lemma centeredMdsApproximation_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Integrable (W n) P) (n : ℕ) :
    P[centeredMdsApproximation P F W n | F n] =ᵐ[P] 0 := by
  haveI : IsFiniteMeasure (P.trim (F.le n)) := isFiniteMeasure_trim (F.le n)
  have hsub := condExp_sub (hW n)
    (integrable_condExp (μ := P) (m := F n) (f := W n)) (F n)
  have htower := condExp_condExp_of_le (μ := P) (f := W n) le_rfl (F.le n)
  filter_upwards [hsub, htower] with ω hω ht
  simpa only [centeredMdsApproximation, Pi.sub_apply, ht, sub_self, Pi.zero_apply] using hω

lemma centeredMdsApproximation_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Integrable (W n) P) (B : ℝ)
    (hB : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B) (n : ℕ) :
    ∀ᵐ ω ∂P, |centeredMdsApproximation P F W n ω| ≤ 2 * B := by
  have hlo : (fun _ : Ω => -B) ≤ᵐ[P] W n := (hB n).mono fun _ h => (abs_le.mp h).1
  have hhi : W n ≤ᵐ[P] (fun _ : Ω => B) := (hB n).mono fun _ h => (abs_le.mp h).2
  have h₁ := condExp_mono (m := F n) (integrable_const (-B)) (hW n) hlo
  have h₂ := condExp_mono (m := F n) (hW n) (integrable_const B) hhi
  rw [condExp_const (F.le n) (-B)] at h₁
  rw [condExp_const (F.le n) B] at h₂
  filter_upwards [h₁, h₂, hB n] with ω h₁ h₂ hb
  have hce : |(P[W n | F n]) ω| ≤ B := abs_le.mpr ⟨h₁, h₂⟩
  exact (abs_sub (W n ω) ((P[W n | F n]) ω)).trans (by linarith)

lemma centeredMdsApproximation_error (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D W : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    eLpNorm (D n - centeredMdsApproximation P F W n) 2 P ≤
      2 * eLpNorm (D n - W n) 2 P := by
  have hsub := condExp_sub ((hD n).integrable (by norm_num))
    ((hW n).integrable (by norm_num)) (F n)
  have heq : D n - centeredMdsApproximation P F W n =ᵐ[P]
      (D n - W n) - P[D n - W n | F n] := by
    filter_upwards [hsub, hzero n] with ω hs hz
    simp only [Pi.sub_apply, Pi.zero_apply] at hs hz
    simp only [centeredMdsApproximation, Pi.sub_apply, hs, hz]
    ring
  rw [eLpNorm_congr_ae heq, two_mul]
  exact (eLpNorm_sub_le ((hD n).sub (hW n)).1
    (((hD n).sub (hW n)).condExp (by norm_num)).1 (by norm_num)).trans
      (add_le_add le_rfl (eLpNorm_condExp_le_eLpNorm _ (by norm_num)))

omit m0 in
lemma normalizedMdsSum_sub (D E : ℕ → Ω → ℝ) (n : ℕ) :
    normalizedMdsSum (fun i => D i - E i) n =
      normalizedMdsSum D n - normalizedMdsSum E n := by
  funext ω
  simp only [normalizedMdsSum, mdsSum, FourthRecurrence.partialSum,
    Pi.sub_apply, Finset.sum_sub_distrib, sub_div]

theorem eLpNorm_normalizedMdsSum_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n, eLpNorm (D n) 2 P ≤ ENNReal.ofReal B) (n : ℕ) :
    eLpNorm (normalizedMdsSum D n) 2 P ≤ ENNReal.ofReal B := by
  apply (eLpNorm_two_le_iff_integral_sq_le P (memLp_normalizedMdsSum P D hL2 n) hB).2
  exact integral_normalizedMdsSum_sq_le P F D hD hL2 hzero (B ^ 2)
    (sq_nonneg B) (fun i => (eLpNorm_two_le_iff_integral_sq_le P (hL2 i) hB).1 (hbound i)) n

theorem uniformIntegrable_normalizedMdsSum_of_bounded_approximation
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (B : ℝ) (_ : 0 ≤ B) (W : ℕ → Ω → ℝ),
      (∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B) ∧
      ∀ n, eLpNorm (D n - W n) 2 P ≤ ENNReal.ofReal ε) :
    UniformIntegrable (normalizedMdsSum D) 2 P := by
  apply uniformIntegrable_of_uniform_Lp_approximation (by norm_num)
    (memLp_normalizedMdsSum P D hL2)
  intro ε hε
  obtain ⟨B, hB, W, hWa, hWb, hWe⟩ := happrox (ε / 2) (half_pos hε)
  have hW : ∀ n, MemLp (W n) 2 P := fun n =>
    MemLp.of_bound (AEStronglyMeasurable.mono (F.le (n + 1)) (hWa n)) B
      ((hWb n).mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)
  have hWi : ∀ n, Integrable (W n) P := fun n => (hW n).integrable (by norm_num)
  let Z := centeredMdsApproximation P F W
  have hZa := centeredMdsApproximation_adapted P F W hWa
  have hZ2 := centeredMdsApproximation_memLp P F W hW
  have hZzero := centeredMdsApproximation_condExp P F W hWi
  have hZb := centeredMdsApproximation_bound P F W hWi B hWb
  have hUI : UniformIntegrable (normalizedMdsSum Z) 2 P := by
    apply uniformIntegrable_two_of_fourth_moment
      (fun n => (memLp_normalizedMdsSum P Z hZ2 n).1)
      (fun n => (bounded_normalizedMdsSum_fourth P F Z hZa hZzero
        (2 * B) (by positivity) hZb n).1)
      ⟨6 * (2 * B) ^ 4, by positivity⟩
    intro n
    exact (bounded_normalizedMdsSum_fourth P F Z hZa hZzero
      (2 * B) (by positivity) hZb n).2
  refine ⟨normalizedMdsSum Z, hUI, ?_⟩
  have hEa : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n - Z n) P :=
    fun n => (hD n).sub (hZa n)
  have hE2 : ∀ n, MemLp (D n - Z n) 2 P := fun n => (hL2 n).sub (hZ2 n)
  have hEzero : ∀ n, P[D n - Z n | F n] =ᵐ[P] 0 := by
    intro n
    filter_upwards [condExp_sub ((hL2 n).integrable (by norm_num))
      ((hZ2 n).integrable (by norm_num)) (F n), hzero n, hZzero n] with ω hs hd hz
    simpa only [Pi.sub_apply, hd, hz, Pi.zero_apply, sub_self] using hs
  have hEb : ∀ n, eLpNorm (D n - Z n) 2 P ≤ ENNReal.ofReal ε := by
    intro n
    calc
      _ ≤ 2 * eLpNorm (D n - W n) 2 P := centeredMdsApproximation_error P F D W hL2 hW hzero n
      _ ≤ 2 * ENNReal.ofReal (ε / 2) := mul_le_mul' le_rfl (hWe n)
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  intro n
  rw [← normalizedMdsSum_sub]
  exact eLpNorm_normalizedMdsSum_le P F (fun i => D i - Z i) hEa hE2 hEzero ε hε.le hEb n

end NumberChainSummableRhoUI

end ChainMartingaleComponent5

section ChainMartingaleComponent6

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem MeasureTheory.tendsto_integral_sq_sub_truncation {X : Type*} [MeasurableSpace X] (π : Measure X) [IsProbabilityMeasure π]
    (f : X → ℝ) (hf : Measurable f) (hL2 : Integrable (fun x => (f x) ^ 2) π) :
    Tendsto (fun K : ℕ => ∫ x, (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))) ^ 2 ∂π)
      atTop (𝓝 0) := by
  classical
  set F : ℕ → X → ℝ := fun K x => (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))) ^ 2 with hF
  -- pointwise bound on the truncation error
  have htrunc : ∀ (y : ℝ) (K : ℝ), 0 ≤ K → |y - max (min y K) (-K)| ≤ |y| := by
    intro y K hK
    rcases le_total y K with h1 | h1
    · rcases le_total (-K) y with h2 | h2
      · rw [min_eq_left h1, max_eq_left h2]
        simp
      · rw [min_eq_left h1, max_eq_right h2]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    · rw [min_eq_right h1, max_eq_left (by linarith)]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hFmeas : ∀ K : ℕ, AEStronglyMeasurable (F K) π := by
    intro K
    exact ((hf.sub (((hf.min measurable_const).max measurable_const))).pow_const
      2).aestronglyMeasurable
  have hFbd : ∀ K : ℕ, ∀ᵐ x ∂π, ‖F K x‖ ≤ (f x) ^ 2 := by
    intro K
    filter_upwards with x
    have h := htrunc (f x) (K : ℝ) (Nat.cast_nonneg K)
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : |f x - max (min (f x) (K : ℝ)) (-(K : ℝ))| ^ 2 ≤ |f x| ^ 2 := by
      nlinarith [abs_nonneg (f x - max (min (f x) (K : ℝ)) (-(K : ℝ))), abs_nonneg (f x), h]
    rwa [sq_abs, sq_abs] at h2
  have hFlim : ∀ᵐ x ∂π, Tendsto (fun K : ℕ => F K x) atTop (𝓝 0) := by
    filter_upwards with x
    obtain ⟨K0, hK0⟩ := exists_nat_gt |f x|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K0] with K hK
    have hKR : |f x| ≤ (K : ℝ) := by
      have : (K0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      linarith
    have h1 : f x ≤ (K : ℝ) := le_trans (le_abs_self _) hKR
    have h2 : -(K : ℝ) ≤ f x := by
      have := neg_abs_le (f x)
      linarith
    rw [hF]
    simp only
    rw [min_eq_left h1, max_eq_left h2]
    simp
  have := tendsto_integral_of_dominated_convergence (fun x => (f x) ^ 2) hFmeas hL2 hFbd hFlim
  simpa using this

end ChainMartingaleComponent6

section ChainMartingaleComponent7

open MeasureTheory ProbabilityTheory Filter NumberChainSummableRhoUI
open scoped ENNReal NNReal Topology

namespace StationaryMartingaleCLT

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

theorem uniformIntegrable_normalizedMdsSum_of_identDistrib
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (D n))
    (ha : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : MemLp (D 0) 2 P) (hid : ∀ n, IdentDistrib (D n) (D 0) P P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) :
    UniformIntegrable (normalizedMdsSum D) 2 P := by
  have hL2all (n : ℕ) : MemLp (D n) 2 P := (hid n).memLp_iff.mpr hL2
  apply uniformIntegrable_normalizedMdsSum_of_bounded_approximation P F D ha hL2all hzero
  intro ε hε
  have hlim := tendsto_integral_sq_sub_truncation P (D 0) (hm 0) hL2.integrable_sq
  obtain ⟨K, hK⟩ := (hlim.eventually_le_const (sq_pos_of_pos hε)).exists
  let W : ℕ → Ω → ℝ := fun n ω => max (min (D n ω) (K : ℝ)) (-(K : ℝ))
  have hWa (n : ℕ) : AEStronglyMeasurable[F (n + 1)] (W n) P :=
    ((continuous_id.min continuous_const).max continuous_const).comp_aestronglyMeasurable (ha n)
  have hWb (n : ℕ) (ω : Ω) : |W n ω| ≤ (K : ℝ) := by
    change |max (min (D n ω) (K : ℝ)) (-(K : ℝ))| ≤ (K : ℝ)
    apply abs_le.mpr
    exact ⟨le_max_right _ _, max_le (min_le_right _ _)
      (by linarith [show (0 : ℝ) ≤ (K : ℝ) from Nat.cast_nonneg K])⟩
  refine ⟨K, Nat.cast_nonneg K, W, hWa, fun n => ae_of_all _ (hWb n), ?_⟩
  intro n
  have hW2 : MemLp (W n) 2 P :=
    MemLp.of_bound ((hWa n).mono (F.le (n + 1))) K
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hWb n ω)
  apply (eLpNorm_two_le_iff_integral_sq_le P ((hL2all n).sub hW2) hε.le).2
  change (∫ ω, (D n ω - max (min (D n ω) (K : ℝ)) (-(K : ℝ))) ^ 2 ∂P) ≤ ε ^ 2
  have hmeas : Measurable (fun x : ℝ => (x - max (min x (K : ℝ)) (-(K : ℝ))) ^ 2) :=
    (measurable_id.sub ((measurable_id.min measurable_const).max measurable_const)).pow_const 2
  have heq := ((hid n).comp hmeas).integral_eq
  simp only [Function.comp_def] at heq
  exact heq.trans_le hK

theorem mdsSum_second_moment_identDistrib
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ)
    (ha : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : MemLp (D 0) 2 P) (hid : ∀ n, IdentDistrib (D n) (D 0) P P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    ∫ ω, mdsSum D n ω ^ 2 ∂P = (n : ℝ) * ∫ ω, D 0 ω ^ 2 ∂P := by
  rw [integral_mdsSum_sq P F D ha (fun i => (hid i).memLp_iff.mpr hL2) hzero]
  have heq (i : ℕ) : (∫ ω, D i ω ^ 2 ∂P) = ∫ ω, D 0 ω ^ 2 ∂P :=
    ((hid i).comp (measurable_id.pow_const 2)).integral_eq
  simp only [heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem uniformIntegrable_sqrt_normalizedMdsSum
    {P : Measure Ω} {D : ℕ → Ω → ℝ}
    (hUI : UniformIntegrable (normalizedMdsSum D) 2 P) :
    UniformIntegrable (fun n ω => mdsSum D n ω / Real.sqrt (n : ℝ)) 2 P := by
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).inv₀ (by norm_num)
  have ha : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1) / Real.sqrt (n : ℝ))
      atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hr
    simpa only [Function.comp_def, Real.sqrt_div' _ (Nat.cast_nonneg _), Real.sqrt_one] using h
  have h := uniformIntegrable_bounded_mul_of_tendsto hUI ha
  apply h.ae_eq
  intro n
  filter_upwards with ω
  dsimp only [normalizedMdsSum]
  have hs : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [div_mul_div_comm, mul_comm (Real.sqrt ((n : ℝ) + 1)) (mdsSum D n ω),
    mul_div_mul_right _ _ hs]

theorem uniformIntegrable_variance_normalizedMdsSum
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (D n))
    (ha : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : MemLp (D 0) 2 P) (hid : ∀ n, IdentDistrib (D n) (D 0) P P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (hv : 0 < ∫ ω, D 0 ω ^ 2 ∂P) :
    UniformIntegrable
      (fun n ω => mdsSum D n ω ^ 2 / ∫ ω', mdsSum D n ω' ^ 2 ∂P) 1 P := by
  have hUI := uniformIntegrable_sqrt_normalizedMdsSum
    (uniformIntegrable_normalizedMdsSum_of_identDistrib P F D hm ha hL2 hid hzero)
  apply uniformIntegrable_variance_normalized (by ext ω; simp [mdsSum, FourthRecurrence.partialSum])
    (by simpa only [Nat.cast_add, Nat.cast_one] using
      uniformIntegrable_comp hUI (fun n => n + 1)) hv
  have heq : (fun n : ℕ => (∫ ω, mdsSum D (n + 1) ω ^ 2 ∂P) / ((n : ℝ) + 1)) =
      fun _ => ∫ ω, D 0 ω ^ 2 ∂P := by
    funext n
    rw [mdsSum_second_moment_identDistrib P F D ha hL2 hid hzero]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [heq]
  exact tendsto_const_nhds

end StationaryMartingaleCLT

end ChainMartingaleComponent7

section ChainMartingaleComponent8

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace StationaryMartingaleCLT

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussian_limit_of_ae_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ) (hU : ∀ n, Measurable (U n))
    (hzero : ∀ n, U n =ᵐ[P] 0) :
    TendstoInDistribution U atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 0) := by
  have hmap (n : ℕ) : P.map (U n) = Measure.dirac 0 := by
    rw [Measure.map_congr (hzero n)]
    change P.map (fun _ : Ω => (0 : ℝ)) = Measure.dirac 0
    simp
  refine ⟨fun n => (hU n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  simp only [hmap, gaussianReal_zero_var, Measure.map_id]
  exact tendsto_const_nhds

theorem gaussian_limit_const_mul (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ)
    (h : TendstoInDistribution U atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1))
    (a : ℝ) (v : ℝ≥0) (hv : (v : ℝ) = a ^ 2) :
    TendstoInDistribution (fun n ω => a * U n ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 v) := by
  have hscaled := h.continuous_comp (g := fun x : ℝ => a * x) (by fun_prop)
  have hnn : NNReal.mk (a ^ 2) (sq_nonneg a) = v := by
    apply Subtype.ext
    exact hv.symm
  have hmap : (gaussianReal 0 1).map (fun x => a * x) = gaussianReal 0 v := by
    simpa only [mul_zero, mul_one, hnn] using
      (gaussianReal_map_const_mul (μ := 0) (v := 1) a)
  refine ⟨hscaled.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Function.comp_def, id_eq, hmap, Measure.map_id] using hscaled.tendsto

end StationaryMartingaleCLT

end ChainMartingaleComponent8

section ChainMartingaleComponent9

open MeasureTheory ProbabilityTheory Filter NumberChainSummableRhoUI MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace StationaryMartingaleCLT

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

theorem stationary_mds_clt
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (D n))
    (hstat : IsStrictlyStationary P D)
    (ha : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : MemLp (D 0) 2 P) (hid : ∀ n, IdentDistrib (D n) (D 0) P P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (hmix : Tendsto (fun n => alphaMixingCoef P D n) atTop (𝓝 0)) :
    ∃ v : ℝ≥0, TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ * mdsSum D n ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 v) := by
  let v : ℝ := ∫ ω, D 0 ω ^ 2 ∂P
  have hv : 0 ≤ v := integral_nonneg fun _ => sq_nonneg _
  have hSmeas (n : ℕ) : Measurable (mdsSum D n) :=
    Finset.measurable_sum _ fun i _ => hm i
  have hS2 (n : ℕ) : MemLp (mdsSum D n) 2 P :=
    memLp_mdsSum P D (fun i => (hid i).memLp_iff.mpr hL2) n
  have hsecond (n : ℕ) : (∫ ω, mdsSum D n ω ^ 2 ∂P) = (n : ℝ) * v :=
    mdsSum_second_moment_identDistrib P F D ha hL2 hid hzero n
  by_cases hvzero : v = 0
  · refine ⟨0, gaussian_limit_of_ae_zero P _ (fun n => measurable_const.mul (hSmeas n)) ?_⟩
    intro n
    have hint : (∫ ω, mdsSum D n ω ^ 2 ∂P) = 0 := by rw [hsecond, hvzero, mul_zero]
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (mdsSum D n ω))
      (hS2 n).integrable_sq).mp hint
    filter_upwards [hae] with ω hω
    have hs : mdsSum D n ω = 0 := sq_eq_zero_iff.mp hω
    simp only [hs, mul_zero, Pi.zero_apply]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvzero)
    haveI : IsFiniteMeasure (P.trim (F.le 0)) := isFiniteMeasure_trim (F.le 0)
    have hcent : (∫ ω, D 0 ω ∂P) = 0 := by
      calc
        _ = ∫ ω, (P[D 0 | F 0]) ω ∂P := (integral_condExp (F.le 0)).symm
        _ = ∫ _ω : Ω, (0 : ℝ) ∂P := integral_congr_ae (hzero 0)
        _ = 0 := by simp
    have hvar : Tendsto (fun n => ∫ ω, mdsSum D n ω ^ 2 ∂P) atTop atTop := by
      simp only [hsecond]
      exact Filter.Tendsto.atTop_mul_const hvpos tendsto_natCast_atTop_atTop
    have hUI := uniformIntegrable_variance_normalizedMdsSum P F D hm ha hL2 hid hzero hvpos
    have hdenker := (clt_iff_uniformlyIntegrable_of_alpha_mixing P D hm hstat hcent hL2
      hmix hvar).mpr hUI
    have hscaled := gaussian_limit_const_mul P _ hdenker (Real.sqrt v) ⟨v, hv⟩
      (Real.sq_sqrt hv).symm
    refine ⟨⟨v, hv⟩, hscaled.congr (fun n => ae_of_all _ fun ω => ?_) Filter.EventuallyEq.rfl⟩
    change Real.sqrt v * (mdsSum D n ω / Real.sqrt (∫ ω', mdsSum D n ω' ^ 2 ∂P)) = _
    rw [hsecond, Real.sqrt_mul (Nat.cast_nonneg n)]
    have hroot : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hvpos)
    rw [div_mul_eq_div_div_swap, ← mul_div_assoc, mul_div_cancel₀ _ hroot,
      div_eq_mul_inv, mul_comm]

end StationaryMartingaleCLT

end ChainMartingaleComponent9

section ChainMartingaleComponent10

open MeasureTheory ProbabilityTheory Filter Function Preorder
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace NumberChainMartingaleCLT

set_option maxHeartbeats 800000

variable {X : Type*} [MeasurableSpace X]

theorem traj_prefix_next (P : Kernel X X) [IsMarkovKernel P] (n : ℕ)
    (x : Finset.Iic n → X) :
    (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) n x).map
        (fun ω => (frestrictLe n ω, ω (n + 1))) =
      (P (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).map (Prod.mk x) := by
  have h := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => X) (κ := BanditAlgorithm.markovChainStep P)
    (a := n) (b := n) le_rfl (x₀ := x)
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h
  rw [← h]
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
  rw [lintegral_dirac']
  · rfl
  · exact Kernel.measurable_kernel_prodMk_left hs

theorem chain_prefix_next (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (n : ℕ) :
    (MarkovChainCLT.chainMeasure P π).map (fun ω => (frestrictLe n ω, ω (n + 1))) =
      ((MarkovChainCLT.chainMeasure P π).map (frestrictLe n)) ⊗ₘ
        BanditAlgorithm.markovChainStep P n := by
  let ν := (MarkovChainCLT.chainMeasure P π).map (frestrictLe n)
  have hdec := MarkovChainCLT.chainMeasure_eq_comp_traj P π n
  change MarkovChainCLT.chainMeasure P π =
    Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) n ∘ₘ ν at hdec
  change (MarkovChainCLT.chainMeasure P π).map
    (fun ω => (frestrictLe n ω, ω (n + 1))) = ν ⊗ₘ BanditAlgorithm.markovChainStep P n
  conv_lhs => rw [hdec, Measure.map_comp _ _ (by fun_prop)]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.compProd_apply hs]
  apply lintegral_congr
  intro x
  rw [Kernel.map_apply _ (by fun_prop), traj_prefix_next,
    Measure.map_apply measurable_prodMk_left hs]
  rfl

end NumberChainMartingaleCLT

end ChainMartingaleComponent10

section ChainMartingaleComponent11

open MeasureTheory ProbabilityTheory Filter Function Preorder
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace NumberChainMartingaleCLT

theorem condExp_of_joint_kernel {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hist : Ω → A) (step : Ω → B)
    (hp : Measurable hist) (hn : Measurable step)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hjoint : μ.map (fun ω => (hist ω, step ω)) = (μ.map hist) ⊗ₘ κ)
    (g : B → ℝ) (hg : Measurable g) (hi : Integrable (fun ω => g (step ω)) μ) :
    μ[fun ω => g (step ω) | MeasurableSpace.comap hist inferInstance] =ᵐ[μ]
      fun ω => ∫ y, g y ∂κ (hist ω) := by
  have hg2 : StronglyMeasurable (fun z : A × B => g z.2) :=
    hg.stronglyMeasurable.comp_measurable measurable_snd
  have hiJoint : Integrable (fun z : A × B => g z.2) ((μ.map hist) ⊗ₘ κ) := by
    rw [← hjoint]
    exact (integrable_map_measure hg2.aestronglyMeasurable (hp.prodMk hn).aemeasurable).mpr hi
  have hm : StronglyMeasurable (fun x => ∫ y, g y ∂κ x) := hg.stronglyMeasurable.integral_kernel
  have hiNorm := ((Measure.integrable_compProd_iff hiJoint.1).mp hiJoint).2
  have hiAvg : Integrable (fun x => ∫ y, g y ∂κ x) (μ.map hist) :=
    hiNorm.mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ => norm_integral_le_integral_norm _)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hp.comap_le hi
    (fun s _ _ => (hiAvg.comp_measurable hp).integrableOn) ?_ ?_).symm
  · rintro _ ⟨t, ht, rfl⟩ _
    calc
      (∫ ω in hist ⁻¹' t, ∫ y, g y ∂κ (hist ω) ∂μ) =
          ∫ x in t, ∫ y, g y ∂κ x ∂μ.map hist :=
        (setIntegral_map ht hiAvg.1 hp.aemeasurable).symm
      _ = ∫ z in t ×ˢ Set.univ, g z.2 ∂((μ.map hist) ⊗ₘ κ) := by
        simpa using (Measure.setIntegral_compProd ht MeasurableSet.univ hiJoint.integrableOn).symm
      _ = ∫ z in t ×ˢ Set.univ, g z.2 ∂μ.map (fun ω => (hist ω, step ω)) := by rw [hjoint]
      _ = ∫ ω in hist ⁻¹' t, g (step ω) ∂μ := by
        simpa only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ] using
          setIntegral_map (ht.prod MeasurableSet.univ) hg2.aestronglyMeasurable
            (hp.prodMk hn).aemeasurable
  · exact (hm.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

variable {X : Type*} [MeasurableSpace X]

theorem chain_condExp_next (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (g : X → ℝ) (hg : Measurable g)
    (n : ℕ) (hi : Integrable (fun ω : ℕ → X => g (ω (n + 1))) (MarkovChainCLT.chainMeasure P π)) :
    (MarkovChainCLT.chainMeasure P π)[fun ω => g (ω (n + 1)) | Filtration.piLE n] =ᵐ[
        MarkovChainCLT.chainMeasure P π] fun ω => ∫ y, g y ∂P (ω n) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_joint_kernel (MarkovChainCLT.chainMeasure P π) (frestrictLe n)
    (fun ω => ω (n + 1)) (measurable_frestrictLe n) (measurable_pi_apply (n + 1))
    (BanditAlgorithm.markovChainStep P n) (chain_prefix_next P π n) g hg hi

end NumberChainMartingaleCLT

end ChainMartingaleComponent11

section ChainMartingaleComponent12

open MeasureTheory ProbabilityTheory Filter Function MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace NumberChainMartingaleCLT

variable {X : Type*} [MeasurableSpace X]

noncomputable def increment (P : Kernel X X) (g : X → ℝ) (i : ℕ) (ω : ℕ → X) : ℝ :=
  g (ω (i + 1)) - ∫ y, g y ∂P (ω i)

theorem kernelMean_measurable (P : Kernel X X) [IsMarkovKernel P]
    (g : X → ℝ) (hg : Measurable g) : Measurable (fun x => ∫ y, g y ∂P x) :=
  hg.stronglyMeasurable.integral_kernel.measurable

theorem coord_measurable_piLE (i n : ℕ) (hin : i ≤ n) :
    @Measurable (ℕ → X) X (Filtration.piLE n) _ (fun ω => ω i) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_pi_apply (X := fun _ : Finset.Iic n => X)
    (⟨i, Finset.mem_Iic.mpr hin⟩ : Finset.Iic n)).comp
    (Measurable.of_comap_le le_rfl)

theorem increment_measurable (P : Kernel X X) [IsMarkovKernel P]
    (g : X → ℝ) (hg : Measurable g) (n : ℕ) : Measurable (increment P g n) :=
  (hg.comp (measurable_pi_apply (n + 1))).sub
    ((kernelMean_measurable P g hg).comp (measurable_pi_apply n))

theorem increment_stronglyMeasurable (P : Kernel X X) [IsMarkovKernel P]
    (g : X → ℝ) (hg : Measurable g) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (n + 1)] (increment P g n) :=
  ((hg.comp (coord_measurable_piLE (n + 1) (n + 1) le_rfl)).sub
    ((kernelMean_measurable P g hg).comp (coord_measurable_piLE n (n + 1) (by omega)))).stronglyMeasurable

theorem coord_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hgL2 : MemLp g 2 π) (n : ℕ) :
    MemLp (fun ω : ℕ → X => g (ω n)) 2 (chainMeasure P π) :=
  hgL2.comp_measurePreserving ⟨measurable_pi_apply n, map_coord_chainMeasure P π hinv n⟩

theorem kernelMean_coord_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (hgL2 : MemLp g 2 π) (n : ℕ) :
    MemLp (fun ω : ℕ → X => ∫ y, g y ∂P (ω n)) 2 (chainMeasure P π) := by
  have hnext := coord_memLp P π hinv g hgL2 (n + 1)
  exact MemLp.ae_eq (chain_condExp_next P π g hg n (hnext.integrable (by norm_num))) (hnext.condExp (by norm_num))

theorem increment_memLp (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (hgL2 : MemLp g 2 π) (n : ℕ) :
    MemLp (increment P g n) 2 (chainMeasure P π) :=
  (coord_memLp P π hinv g hgL2 (n + 1)).sub (kernelMean_coord_memLp P π hinv g hg hgL2 n)

theorem increment_condExp_zero (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (hgL2 : MemLp g 2 π) (n : ℕ) :
    (chainMeasure P π)[increment P g n | Filtration.piLE n] =ᵐ[chainMeasure P π] 0 := by
  have hiNext := (coord_memLp P π hinv g hgL2 (n + 1)).integrable (by norm_num)
  have hiMean := (kernelMean_coord_memLp P π hinv g hg hgL2 n).integrable (by norm_num)
  have hm : StronglyMeasurable[Filtration.piLE n] (fun ω : ℕ → X => ∫ y, g y ∂P (ω n)) :=
    ((kernelMean_measurable P g hg).comp (coord_measurable_piLE n n le_rfl)).stronglyMeasurable
  have hmean := condExp_of_stronglyMeasurable (Filtration.piLE.le n) hm hiMean
  have hsub := condExp_sub hiNext hiMean (Filtration.piLE n)
  unfold increment
  filter_upwards [hsub, chain_condExp_next P π g hg n hiNext] with ω hω hnext
  simpa only [Pi.sub_def, Pi.sub_apply, Pi.zero_apply, hnext, hmean, sub_self] using hω

theorem increment_stationary (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) :
    IsStrictlyStationary (chainMeasure P π) (increment P g) := by
  intro a
  let F : (ℕ → X) → (ℕ → ℝ) := fun ω n => increment P g n ω
  have hF : Measurable F := measurable_pi_lambda _ (increment_measurable P g hg)
  have hs := isStrictlyStationary_chainMeasure P π hinv a
  change (chainMeasure P π).map (fun ω : ℕ → X => fun n => ω (n + a)) =
    (chainMeasure P π).map id at hs
  rw [Measure.map_id] at hs
  have h := congrArg (Measure.map F) hs
  rw [Measure.map_map hF (measurable_pi_lambda _ (fun n => measurable_pi_apply (n + a)))] at h
  simpa only [F, Function.comp_def, increment, Nat.add_assoc, Nat.add_comm a 1] using h

theorem increment_identDistrib (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (n : ℕ) :
    IdentDistrib (increment P g n) (increment P g 0) (chainMeasure P π) (chainMeasure P π) := by
  refine ⟨(increment_measurable P g hg n).aemeasurable,
    (increment_measurable P g hg 0).aemeasurable, ?_⟩
  have h := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (increment_stationary P π hinv g hg n)
  rw [Measure.map_map (measurable_pi_apply 0)
    (measurable_pi_lambda _ (fun i => increment_measurable P g hg (i + n))),
    Measure.map_map (measurable_pi_apply 0)
    (measurable_pi_lambda _ (increment_measurable P g hg))] at h
  simpa only [Function.comp_def, Nat.zero_add] using h

end NumberChainMartingaleCLT

end ChainMartingaleComponent12

section ChainMartingaleComponent13

open Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

set_option maxHeartbeats 2000000

namespace HarrisAlpha

variable {X : Type*} [MeasurableSpace X]

-- The restart calculation adapts Zehao Jin's accepted cbc65707 proof.
-- The measurable event deviations below replace its measurable-TV hypothesis.
noncomputable def futureDeviation (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (n : ℕ) (B : Set (ℕ → X)) (x : X) : ℝ :=
  |(((BanditAlgorithm.markovChainKernel P ∘ₖ iterKernel P n) x) B).toReal -
    ((chainMeasure P π) B).toReal|

theorem futureDeviation_measurable (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (n : ℕ) {B : Set (ℕ → X)} (hB : MeasurableSet B) :
    Measurable (futureDeviation P π n B) :=
  ((Kernel.measurable_coe _ hB).ennreal_toReal.sub_const _).abs

theorem futureDeviation_nonneg (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    (n : ℕ) (B : Set (ℕ → X)) (x : X) : 0 ≤ futureDeviation P π n B x :=
  abs_nonneg _

theorem futureDeviation_le_one (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (n : ℕ) (B : Set (ℕ → X)) (x : X) :
    futureDeviation P π n B x ≤ 1 := by
  have h₁ : 0 ≤ (((BanditAlgorithm.markovChainKernel P ∘ₖ iterKernel P n) x) B).toReal :=
    ENNReal.toReal_nonneg
  have h₂ : (((BanditAlgorithm.markovChainKernel P ∘ₖ iterKernel P n) x) B).toReal ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one
  have h₃ : 0 ≤ ((chainMeasure P π) B).toReal := ENNReal.toReal_nonneg
  have h₄ : ((chainMeasure P π) B).toReal ≤ 1 := by
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one
  rw [futureDeviation, abs_le]
  constructor <;> linarith

theorem chain_bind_real (P : Kernel X X) [IsMarkovKernel P]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (B : Set (ℕ → X)) (hB : MeasurableSet B) :
    ((BanditAlgorithm.markovChainKernel P ∘ₘ ν) B).toReal =
      ∫ y, ((BanditAlgorithm.markovChainKernel P y) B).toReal ∂ν := by
  rw [Measure.bind_apply hB (Kernel.aemeasurable _)]
  refine (integral_toReal (Kernel.measurable_coe _ hB).aemeasurable ?_).symm
  filter_upwards with y
  exact measure_lt_top _ _

theorem futureDeviation_le_tv (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π]
    (n : ℕ) {B : Set (ℕ → X)} (hB : MeasurableSet B) (x : X) :
    futureDeviation P π n B x ≤ tvDist (iterKernel P n x) π := by
  rw [futureDeviation, Kernel.comp_apply, chainMeasure,
    chain_bind_real P _ B hB, chain_bind_real P π B hB]
  apply MarkovChainCLT.abs_integral_sub_le_tvDist _ π
    (fun y => ((BanditAlgorithm.markovChainKernel P y) B).toReal)
    (Kernel.measurable_coe _ hB).ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg)
  intro y
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  change (BanditAlgorithm.markovChainKernel P y) B ≤ ENNReal.ofReal 1
  rw [ENNReal.ofReal_one]
  exact prob_le_one (μ := BanditAlgorithm.markovChainKernel P y) (s := B)

theorem futureDeviation_integrable (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π]
    (n : ℕ) {B : Set (ℕ → X)} (hB : MeasurableSet B) :
    Integrable (futureDeviation P π n B) π := by
  apply Integrable.of_bound (futureDeviation_measurable P π n hB).aestronglyMeasurable 1
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (futureDeviation_nonneg P π n B x)] using
    futureDeviation_le_one P π n B x

theorem past_future_bound (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (n k : ℕ) (A B : Set (ℕ → X))
    (hA : MeasurableSet[processSigma (fun i (ω : ℕ → X) => ω i) (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma (fun i (ω : ℕ → X) => ω i) (Set.Ici (k + n))] B) :
    ∃ C : Set (ℕ → X), MeasurableSet C ∧
      |((chainMeasure P π) (A ∩ B)).toReal -
        ((chainMeasure P π) A).toReal * ((chainMeasure P π) B).toReal| ≤
          ∫ x, futureDeviation P π n C x ∂π := by
  set μ := chainMeasure P π with hμ
  set K := BanditAlgorithm.markovChainKernel P with hK
  rw [MarkovChainCLT.processSigma_Iic_eq_comap_restrict] at hA
  rw [MarkovChainCLT.processSigma_Ici_eq_comap_shift] at hB
  obtain ⟨A₀, hA₀, rfl⟩ := hA
  obtain ⟨B₀, hB₀, rfl⟩ := hB
  refine ⟨B₀, hB₀, ?_⟩
  have hfr : (fun (ω : ℕ → X) => fun i : Finset.Iic k => ω i.1)
      = frestrictLe (π := fun _ : ℕ => X) k := rfl
  have hsh : Measurable (fun (ω : ℕ → X) => fun l => ω (k + n + l)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  set lamk := μ.map (frestrictLe (π := fun _ : ℕ => X) k) with hlamk
  haveI : IsProbabilityMeasure lamk := by
    rw [hlamk]
    exact Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  have hstat : μ ((fun (ω : ℕ → X) => fun l => ω (k + n + l)) ⁻¹' B₀) = μ B₀ := by
    have hconv : (fun (ω : ℕ → X) => fun l => ω (k + n + l))
        = (fun (ω : ℕ → X) => fun l => ω (l + (k + n))) := by
      funext ω l
      rw [Nat.add_comm]
    rw [← Measure.map_apply hsh hB₀, hconv]
    have hs := MarkovChainCLT.isStrictlyStationary_chainMeasure P π hinv (k + n)
    simp only at hs
    rw [hs]
    have hid : (fun (ω : ℕ → X) => fun l => ω l) = id := rfl
    rw [hid, Measure.map_id]
  rw [hfr, hstat,
    MarkovChainCLT.chainMeasure_past_inter_future P π k n A₀ hA₀ B₀ hB₀,
    show μ (frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀) = lamk A₀ from
      (Measure.map_apply (measurable_frestrictLe k) hA₀).symm]
  set F : (Π _i : Finset.Iic k, X) → ℝ≥0∞ :=
    fun u => (K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀ with hF
  have hFm : Measurable F := by
    have h1 : Measurable (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀) := by
      have he : (fun x : X => (K ∘ₘ (iterKernel P n x)) B₀)
          = fun x : X => ((K ∘ₖ (iterKernel P n)) x) B₀ := by
        funext x
        rw [Kernel.comp_apply]
      rw [he]
      exact Kernel.measurable_coe _ hB₀
    exact h1.comp (measurable_pi_apply _)
  have hFlt : ∀ u, F u < ∞ := fun u => measure_lt_top _ _
  have hToReal : (∫⁻ u in A₀, F u ∂lamk).toReal = ∫ u in A₀, (F u).toReal ∂lamk :=
    (integral_toReal hFm.aemeasurable (Filter.Eventually.of_forall hFlt)).symm
  rw [hToReal]
  have hev : Measurable (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have hcoord : lamk.map (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩)
      = π := by
    rw [hlamk, Measure.map_map hev (measurable_frestrictLe k)]
    have hcomp : (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩)
        ∘ (frestrictLe (π := fun _ : ℕ => X) k) = fun ω : ℕ → X => ω k := rfl
    rw [hcomp, hμ]
    exact MarkovChainCLT.map_coord_chainMeasure P π hinv k
  set m := (μ B₀).toReal with hm
  have hdev : ∀ u, |(F u).toReal - m| =
      futureDeviation P π n B₀ (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) := by
    intro u
    rw [futureDeviation, Kernel.comp_apply]
  have hFint : Integrable (fun u => (F u).toReal) lamk := by
    apply Integrable.of_bound hFm.ennreal_toReal.aestronglyMeasurable 1
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa only [F, ENNReal.ofReal_one] using
      (prob_le_one (μ := K ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) (s := B₀))
  have hqintπ : Integrable (futureDeviation P π n B₀) π :=
    futureDeviation_integrable P π n hB₀
  have hqint : Integrable (fun u : Π _i : Finset.Iic k, X =>
      futureDeviation P π n B₀ (u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) lamk := by
    have hqmap : Integrable (futureDeviation P π n B₀)
        (lamk.map (fun u : Π _i : Finset.Iic k, X => u ⟨k, Finset.mem_Iic.2 le_rfl⟩)) := by
      rw [hcoord]
      exact hqintπ
    exact (integrable_map_measure hqmap.1 hev.aemeasurable).mp hqmap
  have hqval : (∫ u, futureDeviation P π n B₀ (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) ∂lamk)
      = ∫ x, futureDeviation P π n B₀ x ∂π := by
    rw [← hcoord, integral_map hev.aemeasurable]
    rw [hcoord]
    exact hqintπ.1
  have hcent : (∫ u in A₀, (F u).toReal ∂lamk) - (lamk A₀).toReal * m
      = ∫ u in A₀, ((F u).toReal - m) ∂lamk := by
    rw [integral_sub hFint.integrableOn (integrable_const m).restrict, integral_const,
      smul_eq_mul]
    congr 2
    simp [Measure.real]
  rw [hcent]
  calc
    |∫ u in A₀, ((F u).toReal - m) ∂lamk| ≤
        ∫ u in A₀, |(F u).toReal - m| ∂lamk := abs_integral_le_integral_abs
    _ = ∫ u in A₀, futureDeviation P π n B₀ (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) ∂lamk := by
      simp_rw [hdev]
    _ ≤ ∫ u, futureDeviation P π n B₀ (u ⟨k, Finset.mem_Iic.2 le_rfl⟩) ∂lamk :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun u => futureDeviation_nonneg P π n B₀ _) hqint
    _ = _ := hqval

theorem alpha_nonneg {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef μ Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _

theorem strongly_mixing_of_harris (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hP : HarrisErgodic P π) :
    Tendsto (fun n => alphaMixingCoef (chainMeasure P π) (fun i ω => ω i) n)
      atTop (𝓝 0) := by
  classical
  let μ := chainMeasure P π
  let α := fun n => alphaMixingCoef μ (fun i (ω : ℕ → X) => ω i) n
  have hnear : ∀ n : ℕ, ∃ C : Set (ℕ → X), MeasurableSet C ∧
      α n ≤ (∫ x, futureDeviation P π n C x ∂π) + 1 / ((n : ℝ) + 1) := by
    intro n
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hs : {r : ℝ | ∃ k : ℕ, ∃ A B : Set (ℕ → X),
        MeasurableSet[processSigma (fun i (ω : ℕ → X) => ω i) (Set.Iic k)] A ∧
        MeasurableSet[processSigma (fun i (ω : ℕ → X) => ω i) (Set.Ici (k + n))] B ∧
        r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|}.Nonempty :=
      ⟨0, 0, ∅, ∅, by simp, by simp, by simp⟩
    obtain ⟨r, ⟨k, A, B, hA, hB, rfl⟩, hr⟩ :=
      exists_lt_of_lt_csSup hs (show α n - 1 / ((n : ℝ) + 1) < α n by linarith)
    obtain ⟨C, hC, hbound⟩ := past_future_bound P π hP.1 n k A B hA hB
    refine ⟨C, hC, ?_⟩
    dsimp [μ] at hr
    linarith
  choose C hC hnear using hnear
  have hpoint : ∀ x, Tendsto (fun n => futureDeviation P π n (C n) x) atTop (𝓝 0) := by
    intro x
    exact squeeze_zero (fun n => futureDeviation_nonneg P π n (C n) x)
      (fun n => futureDeviation_le_tv P π n (hC n) x) (hP.2 x)
  have hint : Tendsto (fun n => ∫ x, futureDeviation P π n (C n) x ∂π) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := π)
      (fun _x : X => (1 : ℝ))
      (fun n => (futureDeviation_measurable P π n (hC n)).aestronglyMeasurable)
      (integrable_const 1)
      (fun n => ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (futureDeviation_nonneg P π n (C n) x)]
        exact futureDeviation_le_one P π n (C n) x))
      (ae_of_all _ hpoint)
    simpa using h
  have herr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero (fun n => alpha_nonneg μ (fun i (ω : ℕ → X) => ω i) n)
    hnear (by simpa using hint.add herr)

end HarrisAlpha

end ChainMartingaleComponent13

section ChainMartingaleComponent14

open Filter MeasurableSpace MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology

namespace HarrisAlpha

theorem probability_event_difference_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ 1 := by
  have hprob (C : Set Ω) : 0 ≤ (μ C).toReal ∧ (μ C).toReal ≤ 1 := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simpa using prob_le_one
  obtain ⟨hAB0, hAB1⟩ := hprob (A ∩ B)
  obtain ⟨hA0, hA1⟩ := hprob A
  obtain ⟨hB0, hB1⟩ := hprob B
  rw [abs_le]
  constructor <;> nlinarith

theorem event_difference_le_alpha {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ℕ → Ω → E)
    (n k : ℕ) (A B : Set Ω)
    (hA : MeasurableSet[processSigma Y (Set.Iic k)] A)
    (hB : MeasurableSet[processSigma Y (Set.Ici (k + n))] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixingCoef μ Y n := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro r ⟨k', A', B', hA', hB', rfl⟩
    exact probability_event_difference_le_one μ A' B'
  · exact ⟨k, A, B, hA, hB, rfl⟩

variable {X : Type*} [MeasurableSpace X]

theorem finite_window_sigma_le (g h : X → ℝ) (hg : Measurable g) (hh : Measurable h)
    (s t : Set ℕ) (hst : ∀ i ∈ s, i ∈ t ∧ i + 1 ∈ t) :
    processSigma (fun i (ω : ℕ → X) => g (ω (i + 1)) - h (ω i)) s ≤
      processSigma (fun i (ω : ℕ → X) => ω i) t := by
  unfold processSigma
  apply iSup₂_le
  intro i hi
  apply measurable_iff_comap_le.mp
  have hcoord (j : ℕ) (hj : j ∈ t) :
      Measurable[⨆ l ∈ t, MeasurableSpace.comap (fun (ω : ℕ → X) => ω l) inferInstance]
        (fun (ω : ℕ → X) => ω j) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  exact (hg.comp (hcoord (i + 1) (hst i hi).2)).sub (hh.comp (hcoord i (hst i hi).1))

theorem finite_window_alpha_le (μ : Measure (ℕ → X)) [IsProbabilityMeasure μ]
    (g h : X → ℝ) (hg : Measurable g) (hh : Measurable h) (n : ℕ) :
    alphaMixingCoef μ (fun i (ω : ℕ → X) => g (ω (i + 1)) - h (ω i)) (n + 1) ≤
      alphaMixingCoef μ (fun i (ω : ℕ → X) => ω i) n := by
  apply Real.sSup_le _ (alpha_nonneg μ (fun i (ω : ℕ → X) => ω i) n)
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  apply event_difference_le_alpha μ (fun i (ω : ℕ → X) => ω i) n (k + 1) A B
  · refine (finite_window_sigma_le g h hg hh (Set.Iic k) (Set.Iic (k + 1)) ?_) A hA
    intro i hi
    simp only [Set.mem_Iic] at *
    constructor <;> omega
  · refine (finite_window_sigma_le g h hg hh (Set.Ici (k + (n + 1)))
      (Set.Ici ((k + 1) + n)) ?_) B hB
    intro i hi
    simp only [Set.mem_Ici] at *
    constructor <;> omega

theorem finite_window_strongly_mixing (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π] (hP : HarrisErgodic P π)
    (g h : X → ℝ) (hg : Measurable g) (hh : Measurable h) :
    Tendsto (fun n => alphaMixingCoef (chainMeasure P π)
      (fun i (ω : ℕ → X) => g (ω (i + 1)) - h (ω i)) n) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact squeeze_zero
    (fun n => alpha_nonneg (chainMeasure P π)
      (fun i (ω : ℕ → X) => g (ω (i + 1)) - h (ω i)) (n + 1))
    (finite_window_alpha_le (chainMeasure P π) g h hg hh)
    (strongly_mixing_of_harris P π hP)

end HarrisAlpha

end ChainMartingaleComponent14

section ChainMartingaleComponent15

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT NumberChainMartingaleCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (g : X → ℝ) (hg : Measurable g) (hgL2 : MemLp g 2 π) :
    ∃ v : ℝ≥0, TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, (g (ω (i + 1)) - ∫ y, g y ∂(P (ω i))))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v) := by
  exact StationaryMartingaleCLT.stationary_mds_clt (chainMeasure P π) Filtration.piLE
    (increment P g) (increment_measurable P g hg) (increment_stationary P π hP.1 g hg)
    (fun n => (increment_stronglyMeasurable P g hg n).aestronglyMeasurable)
    (increment_memLp P π hP.1 g hg hgL2 0) (increment_identDistrib P π hP.1 g hg)
    (increment_condExp_zero P π hP.1 g hg hgL2)
    (HarrisAlpha.finite_window_strongly_mixing P π hP g
      (fun x => ∫ y, g y ∂P x) hg (kernelMean_measurable P g hg))

end ChainMartingaleComponent15

#print axioms solution
