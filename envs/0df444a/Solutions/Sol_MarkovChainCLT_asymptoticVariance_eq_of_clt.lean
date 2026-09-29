-- Prove2me | solution 1 for MarkovChainCLT.asymptoticVariance_eq_of_clt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-21T19:25:04.587814+00:00
-- url     : https://prove2.me/submissions/d21b0e49-8e1f-44fd-abb5-644ab68578f9

import Definitions.Def_MarkovAsymptoticVariance
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_pow_le
import Theorems.Thm_MarkovChainCLT_exists_lag_tvDist_le_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_integral_sq_scaled_sampleAvg_le
import Theorems.Thm_MarkovChainCLT_integrable_sq_scaled_sampleAvg
import Theorems.Thm_MarkovChainCLT_gaussian_variance_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_exp_variance_sub_le_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_abs_sub_le_exp_mul_abs_exp_neg_half_sub
import Theorems.Thm_MarkovChainCLT_asymptoticVariance_eq_of_clt_of_bounded

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace MarkovChainCLT

variable {X : Type*} [MeasurableSpace X]

lemma sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂μ := by
  have h := ProbabilityTheory.variance_nonneg g μ
  rw [ProbabilityTheory.variance_eq_sub hg] at h
  simp only [Pi.pow_apply] at h
  linarith

/-- Bochner version of the composition formula for a measure and a kernel. -/
lemma integral_comp_measure (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (f : X → ℝ) (hf : Integrable f (P ∘ₘ π)) :
    ∫ z, f z ∂(P ∘ₘ π) = ∫ x, ∫ y, f y ∂(P x) ∂π := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hf]
  simp

/-- Jensen: the transition operator does not increase the `L²(π)` norm when `π` is
invariant. -/
lemma integral_sq_step_le (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (g : X → ℝ) (hg : Measurable g) (hL2 : Integrable (fun x => (g x) ^ 2) π) :
    ∫ x, (∫ y, g y ∂(P x)) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
  have hcomp : (P ∘ₘ π) = π := hinv
  have hL2c : Integrable (fun x => (g x) ^ 2) (P ∘ₘ π) := by rw [hcomp]; exact hL2
  have hsplit := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := fun x => (g x) ^ 2)
    ((hg.pow_const 2).aestronglyMeasurable)).1 hL2c
  have hnormeq : (fun x => ∫ y, ‖(g y) ^ 2‖ ∂(P x)) = fun x => ∫ y, (g y) ^ 2 ∂(P x) := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hint2 : Integrable (fun x => ∫ y, (g y) ^ 2 ∂(P x)) π := by
    rw [← hnormeq]; exact hsplit.2
  have heq : ∫ x, (∫ y, (g y) ^ 2 ∂(P x)) ∂π = ∫ x, (g x) ^ 2 ∂π := by
    rw [← integral_comp_measure P π _ hL2c, hcomp]
  rw [← heq]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hint2 ?_
  filter_upwards [hsplit.1] with x hx
  exact sq_integral_le_integral_sq (P x) g
    ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hx)

lemma integrable_sq_step (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (g : X → ℝ) (hg : Measurable g)
    (hL2 : Integrable (fun x => (g x) ^ 2) π) (hinv : Kernel.Invariant P π) :
    Integrable (fun x => (∫ y, g y ∂(P x)) ^ 2) π := by
  have hcomp : (P ∘ₘ π) = π := hinv
  have hL2c : Integrable (fun x => (g x) ^ 2) (P ∘ₘ π) := by rw [hcomp]; exact hL2
  have hsplit := (Measure.integrable_comp_iff (κ := P) (μ := π) (f := fun x => (g x) ^ 2)
    ((hg.pow_const 2).aestronglyMeasurable)).1 hL2c
  have hnormeq : (fun x => ∫ y, ‖(g y) ^ 2‖ ∂(P x)) = fun x => ∫ y, (g y) ^ 2 ∂(P x) := by
    funext x
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hint2 : Integrable (fun x => ∫ y, (g y) ^ 2 ∂(P x)) π := by
    rw [← hnormeq]; exact hsplit.2
  refine Integrable.mono' hint2 ?_ ?_
  · exact ((StronglyMeasurable.integral_kernel (κ := P)
      hg.stronglyMeasurable).pow 2).aestronglyMeasurable
  · filter_upwards [hsplit.1] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_integral_le_integral_sq (P x) g
      ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hx)

@[simp] lemma iterKernel_one (P : Kernel X X) [IsMarkovKernel P] : iterKernel P 1 = P := by
  rw [iterKernel_succ, iterKernel_zero, Kernel.comp_id]

lemma iterKernel_add (P : Kernel X X) [IsMarkovKernel P] (a b : ℕ) :
    iterKernel P (a + b) = iterKernel P a ∘ₖ iterKernel P b := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hab : a + 1 + b = (a + b) + 1 := by omega
      rw [hab, iterKernel_succ, ih, iterKernel_succ, Kernel.comp_assoc]

lemma invariant_iterKernel (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (k : ℕ) :
    Kernel.Invariant (iterKernel P k) π := by
  induction k with
  | zero =>
      have hid : ⇑(iterKernel P 0) = (Measure.dirac : X → Measure X) := by
        funext x; rw [iterKernel_zero, Kernel.id_apply]
      show ⇑(iterKernel P 0) ∘ₘ π = π
      rw [hid]
      exact Measure.bind_dirac
  | succ k ih => rw [iterKernel_succ]; exact Kernel.Invariant.comp hinv ih

/-- The conditional-mean operator of the `k`-step kernel is an `L²(π)` contraction. -/
lemma iterMean_bound (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) :
    ∀ (k : ℕ) (g : X → ℝ), Measurable g → Integrable (fun x => (g x) ^ 2) π →
      Integrable (fun x => (∫ y, g y ∂(iterKernel P k x)) ^ 2) π ∧
      ∫ x, (∫ y, g y ∂(iterKernel P k x)) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
  intro k
  induction k with
  | zero =>
      intro g hg hL2
      have hd : ∀ x, ∫ y, g y ∂(iterKernel P 0 x) = g x := by
        intro x
        rw [iterKernel_zero, Kernel.id_apply]
        exact integral_dirac' _ x hg.stronglyMeasurable
      simp only [hd]
      exact ⟨hL2, le_rfl⟩
  | succ k ih =>
      intro g hg hL2
      have hgint : Integrable g π :=
        ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hL2).integrable (by norm_num)
      have hPg : Measurable (fun x => ∫ y, g y ∂(P x)) :=
        (StronglyMeasurable.integral_kernel (κ := P) hg.stronglyMeasurable).measurable
      have hPgL2 : Integrable (fun x => (∫ y, g y ∂(P x)) ^ 2) π :=
        integrable_sq_step P π g hg hL2 hinv
      have hstep := ih (fun x => ∫ y, g y ∂(P x)) hPg hPgL2
      -- rewrite the (k+1)-step mean as the k-step mean of the one-step mean
      have hae : ∀ᵐ x ∂π, ∫ y, g y ∂(iterKernel P (k + 1) x)
          = ∫ w, (∫ y, g y ∂(P w)) ∂(iterKernel P k x) := by
        have hinvk : Kernel.Invariant (iterKernel P (k + 1)) π :=
          invariant_iterKernel P π hinv (k + 1)
        have hgc : Integrable g ((iterKernel P (k + 1)) ∘ₘ π) := by
          rw [show ((iterKernel P (k + 1)) ∘ₘ π) = π from hinvk]; exact hgint
        have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P (k + 1)) (μ := π)
          (f := g) hg.aestronglyMeasurable).1 hgc
        filter_upwards [hsplit.1] with x hx
        rw [iterKernel_succ] at hx ⊢
        exact ProbabilityTheory.Kernel.integral_comp hx
      constructor
      · refine (hstep.1).congr' ?_ ?_
        · exact ((StronglyMeasurable.integral_kernel (κ := iterKernel P (k + 1))
            hg.stronglyMeasurable).pow 2).aestronglyMeasurable
        · filter_upwards [hae] with x hx; rw [hx]
      · rw [integral_congr_ae (g := fun x => (∫ w, (∫ y, g y ∂(P w)) ∂(iterKernel P k x)) ^ 2)
          (by filter_upwards [hae] with x hx; rw [hx])]
        exact le_trans hstep.2 (integral_sq_step_le P π hinv g hg hL2)

lemma iterMean_add_ae (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (g : X → ℝ) (hg : Measurable g)
    (hint : Integrable g π) (a b : ℕ) :
    ∀ᵐ x ∂π, ∫ y, g y ∂(iterKernel P (a + b) x)
      = ∫ w, (∫ y, g y ∂(iterKernel P a w)) ∂(iterKernel P b x) := by
  have hinvk : Kernel.Invariant (iterKernel P (a + b)) π := invariant_iterKernel P π hinv (a + b)
  have hgc : Integrable g ((iterKernel P (a + b)) ∘ₘ π) := by
    rw [show ((iterKernel P (a + b)) ∘ₘ π) = π from hinvk]; exact hint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P (a + b)) (μ := π)
    (f := g) hg.aestronglyMeasurable).1 hgc
  filter_upwards [hsplit.1] with x hx
  rw [iterKernel_add] at hx ⊢
  exact ProbabilityTheory.Kernel.integral_comp hx

/-- Geometric `L²` decay of the `k`-step conditional mean of a centred observable. -/
lemma integral_sq_iterKernel_geom_decay (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) (k : ℕ) :
    ∫ x, (∫ y, h y ∂(iterKernel P k x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ (k / N) * ∫ x, (h x) ^ 2 ∂π := by
  set j := k / N with hj
  set s := k % N with hs
  have hk : j * N + s = k := by
    rw [hj, hs, mul_comm]
    exact Nat.div_add_mod k N
  have hint : Integrable h π :=
    ((memLp_two_iff_integrable_sq hh.aestronglyMeasurable).2 hL2).integrable (by norm_num)
  set G : X → ℝ := fun w => ∫ y, h y ∂(iterKernel P (j * N) w) with hG
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P (j * N))
      hh.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv (j * N) h hh hL2
  have hGpow := integral_sq_iterKernel_pow_le P π hinv N ρ hρ0 hρ hrate h hh hL2 hmean j
  have hae := iterMean_add_ae P π hinv h hh hint (j * N) s
  have hrw : ∫ x, (∫ y, h y ∂(iterKernel P k x)) ^ 2 ∂π
      = ∫ x, (∫ w, G w ∂(iterKernel P s x)) ^ 2 ∂π := by
    rw [← hk]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
  rw [hrw]
  exact le_trans (iterMean_bound P π hinv s G hGmeas hGb.1).2 hGpow

lemma summable_half_pow_div (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k / N)) := by
  set r : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / N) with hr
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hbound : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k / N) ≤ 2 * r ^ k := by
    intro k
    have h1 : N * (k / N) + k % N = k := Nat.div_add_mod k N
    have h2 : k % N < N := Nat.mod_lt _ (by omega)
    have h3 : (k : ℝ) < (N : ℝ) * ((k / N : ℕ) : ℝ) + (N : ℝ) := by
      have : k < N * (k / N) + N := by omega
      exact_mod_cast this
    have hk : (k : ℝ) / N - 1 ≤ ((k / N : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hNpos]
      nlinarith [h3]
    have e1 : (1 / 2 : ℝ) ^ (k / N) = (1 / 2 : ℝ) ^ (((k / N : ℕ) : ℝ)) :=
      (Real.rpow_natCast _ _).symm
    have e2 : (1 / 2 : ℝ) ^ (((k / N : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ ((k : ℝ) / N - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hk
    have e3 : (1 / 2 : ℝ) ^ ((k : ℝ) / N - 1) = 2 * r ^ k := by
      have hkN : (k : ℝ) / N = (1 / (N:ℝ)) * (k:ℝ) := by ring
      have hpow : (1 / 2 : ℝ) ^ ((k : ℝ) / N) = r ^ k := by
        rw [hkN, Real.rpow_mul (by norm_num), ← hr, Real.rpow_natCast]
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, hpow]
      ring
    rw [e1]
    exact le_trans e2 (le_of_eq e3)
  refine Summable.of_nonneg_of_le (fun k => by positivity) hbound ?_
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_left 2


/-! ### Cauchy-Schwarz and the `L²(π)` norm -/

/-- Cauchy-Schwarz for the Bochner integral, via nonnegativity of the discriminant. -/
lemma abs_integral_mul_le (π : Measure X) [IsProbabilityMeasure π] (a b : X → ℝ)
    (ha : MemLp a 2 π) (hb : MemLp b 2 π) :
    |∫ x, a x * b x ∂π|
      ≤ Real.sqrt (∫ x, (a x) ^ 2 ∂π) * Real.sqrt (∫ x, (b x) ^ 2 ∂π) := by
  set A := ∫ x, (a x) ^ 2 ∂π with hA
  set B := ∫ x, (b x) ^ 2 ∂π with hB
  set C := ∫ x, a x * b x ∂π with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hAi : Integrable (fun x => (a x) ^ 2) π := (memLp_two_iff_integrable_sq
    ha.aestronglyMeasurable).1 ha
  have hBi : Integrable (fun x => (b x) ^ 2) π := (memLp_two_iff_integrable_sq
    hb.aestronglyMeasurable).1 hb
  have hCi : Integrable (fun x => a x * b x) π := MemLp.integrable_mul (p := 2) (q := 2) ha hb
  have hquad : ∀ lam : ℝ, 0 ≤ lam ^ 2 * A + 2 * lam * C + B := by
    intro lam
    have hexp : ∀ x, (lam * a x + b x) ^ 2
        = lam ^ 2 * (a x) ^ 2 + 2 * lam * (a x * b x) + (b x) ^ 2 := by
      intro x; ring
    have i1 : Integrable (fun x => lam ^ 2 * (a x) ^ 2) π := hAi.const_mul _
    have i2 : Integrable (fun x => 2 * lam * (a x * b x)) π := hCi.const_mul _
    have i12 : Integrable (fun x => lam ^ 2 * (a x) ^ 2 + 2 * lam * (a x * b x)) π := i1.fun_add i2
    have h0 : (0:ℝ) ≤ ∫ x, (lam * a x + b x) ^ 2 ∂π := integral_nonneg fun x => sq_nonneg _
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add i12 hBi, integral_add i1 i2,
      integral_const_mul, integral_const_mul] at h0
    exact h0
  have hdisc : C ^ 2 ≤ A * B := by
    rcases eq_or_lt_of_le hA0 with hA0' | hApos
    · -- A = 0 forces C = 0
      have hC0 : C = 0 := by
        by_contra hne
        have h := hquad (-(B + 1) / (2 * C))
        have hne2 : (2:ℝ) * C ≠ 0 := mul_ne_zero two_ne_zero hne
        have key : 2 * (-(B + 1) / (2 * C)) * C = -(B + 1) := by field_simp
        rw [← hA0', mul_zero, zero_add, key] at h
        linarith
      rw [hC0, ← hA0']; simp
    · have h := hquad (-C / A)
      have hAne : A ≠ 0 := ne_of_gt hApos
      have key : (-C / A) ^ 2 * A + 2 * (-C / A) * C + B = B - C ^ 2 / A := by
        field_simp; ring
      rw [key, sub_nonneg, div_le_iff₀ hApos] at h
      exact le_trans h (le_of_eq (mul_comm B A))
  have hfin : |C| ≤ Real.sqrt A * Real.sqrt B := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA0]
    exact Real.sqrt_le_sqrt hdisc
  exact hfin

/-- The `L²(π)` norm of a real observable. -/
noncomputable def l2NormAux (π : Measure X) (g : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (g x) ^ 2 ∂π)

lemma l2NormAux_nonneg (π : Measure X) (g : X → ℝ) : 0 ≤ l2NormAux π g := Real.sqrt_nonneg _

/-- The lagged covariance, written as an integral of the centred observable against the
`k`-step conditional mean of the centred observable. -/
lemma lagCovariance_eq_centred (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (φ ψ : X → ℝ) (hψ : Measurable ψ) (hψint : Integrable ψ π) (k : ℕ) :
    lagCovariance P π φ ψ k
      = ∫ x, (φ x - ∫ y, φ y ∂π)
          * (∫ y, (ψ y - ∫ z, ψ z ∂π) ∂(iterKernel P k x)) ∂π := by
  have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
  have hψc : Integrable ψ ((iterKernel P k) ∘ₘ π) := by
    rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]; exact hψint
  have hsplit := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
    (f := ψ) hψ.aestronglyMeasurable).1 hψc
  unfold lagCovariance
  refine integral_congr_ae ?_
  filter_upwards [hsplit.1] with x hx
  congr 1
  rw [integral_sub hx (integrable_const _), integral_const]
  simp

/-- **Geometric decay of the lagged covariance, bilinear form.** -/
lemma abs_lagCovariance_le_bilin (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) (k : ℕ) :
    |lagCovariance P π φ ψ k|
      ≤ l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
        * l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) * (1 / 2 : ℝ) ^ (k / N) := by
  set hφc : X → ℝ := fun x => φ x - ∫ y, φ y ∂π with hφcdef
  set hψc : X → ℝ := fun x => ψ x - ∫ y, ψ y ∂π with hψcdef
  have hφcm : Measurable hφc := hφ.sub measurable_const
  have hψcm : Measurable hψc := hψ.sub measurable_const
  have hφcL2 : MemLp hφc 2 π := hφ2.sub (memLp_const _)
  have hψcL2 : MemLp hψc 2 π := hψ2.sub (memLp_const _)
  have hψcsq : Integrable (fun x => (hψc x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hψcm.aestronglyMeasurable).1 hψcL2
  have hψcmean : ∫ x, hψc x ∂π = 0 := by
    rw [hψcdef]
    rw [integral_sub (hψ2.integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  set G : X → ℝ := fun x => ∫ y, hψc y ∂(iterKernel P k x) with hGdef
  have hGmeas : Measurable G :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hψcm.stronglyMeasurable).measurable
  have hGb := iterMean_bound P π hinv k hψc hψcm hψcsq
  have hGL2 : MemLp G 2 π := (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGb.1
  have hrw : lagCovariance P π φ ψ k = ∫ x, hφc x * G x ∂π :=
    lagCovariance_eq_centred P π hinv φ ψ hψ (hψ2.integrable (by norm_num)) k
  rw [hrw]
  refine le_trans (abs_integral_mul_le π hφc G hφcL2 hGL2) ?_
  have hGdecay := integral_sq_iterKernel_geom_decay P π hinv N hN (1 / 16) (by norm_num)
    (by norm_num) hrate hψc hψcm hψcsq hψcmean k
  have hGnorm : Real.sqrt (∫ x, (G x) ^ 2 ∂π)
      ≤ (1 / 2 : ℝ) ^ (k / N) * l2NormAux π hψc := by
    have hpow : (1 / 4 : ℝ) ^ (k / N) = ((1 / 2 : ℝ) ^ (k / N)) ^ 2 := by
      have h4 : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
      rw [h4, ← pow_mul, ← pow_mul, Nat.mul_comm 2 (k / N)]
    have h1 : Real.sqrt (∫ x, (G x) ^ 2 ∂π)
        ≤ Real.sqrt (((1 / 2 : ℝ) ^ (k / N)) ^ 2 * ∫ x, (hψc x) ^ 2 ∂π) := by
      refine Real.sqrt_le_sqrt ?_
      rw [← hpow]
      exact hGdecay
    refine le_trans h1 (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), l2NormAux]
  calc l2NormAux π hφc * Real.sqrt (∫ x, (G x) ^ 2 ∂π)
      ≤ l2NormAux π hφc * ((1 / 2 : ℝ) ^ (k / N) * l2NormAux π hψc) :=
        mul_le_mul_of_nonneg_left hGnorm (l2NormAux_nonneg _ _)
    _ = l2NormAux π hφc * l2NormAux π hψc * (1 / 2 : ℝ) ^ (k / N) := by ring

lemma summable_lagCovariance_succ (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) :
    Summable (fun k : ℕ => lagCovariance P π φ ψ (k + 1)) := by
  set M := l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
    * l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) with hM
  have hM0 : 0 ≤ M := mul_nonneg (l2NormAux_nonneg _ _) (l2NormAux_nonneg _ _)
  refine Summable.of_norm_bounded (g := fun k : ℕ => M * (1 / 2 : ℝ) ^ (k / N))
    ((summable_half_pow_div N hN).mul_left M) fun k => ?_
  rw [Real.norm_eq_abs]
  refine le_trans (abs_lagCovariance_le_bilin P π hinv N hN hrate φ ψ hφ hψ hφ2 hψ2 (k + 1)) ?_
  have hle : k / N ≤ (k + 1) / N := Nat.div_le_div_right (by omega)
  have hp : (1 / 2 : ℝ) ^ ((k + 1) / N) ≤ (1 / 2 : ℝ) ^ (k / N) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
  nlinarith [hM0, hp]

/-- Bilinearity of the lagged covariance, in the form needed to compare two observables. -/
lemma lagCovariance_diag_sub (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) (k : ℕ) :
    lagCovariance P π φ φ k - lagCovariance P π ψ ψ k
      = lagCovariance P π (fun x => φ x - ψ x) φ k
        + lagCovariance P π ψ (fun x => φ x - ψ x) k := by
  have hφi : Integrable φ π := hφ2.integrable (by norm_num)
  have hψi : Integrable ψ π := hψ2.integrable (by norm_num)
  have hdi : Integrable (fun x => φ x - ψ x) π := hφi.sub hψi
  set cφ := ∫ y, φ y ∂π with hcφ
  set cψ := ∫ y, ψ y ∂π with hcψ
  have hcd : ∫ y, (φ y - ψ y) ∂π = cφ - cψ := integral_sub hφi hψi
  set Hφ : X → ℝ := fun x => φ x - cφ with hHφ
  set Hψ : X → ℝ := fun x => ψ x - cψ with hHψ
  have hHφm : Measurable Hφ := hφ.sub measurable_const
  have hHψm : Measurable Hψ := hψ.sub measurable_const
  have hHφ2 : MemLp Hφ 2 π := hφ2.sub (memLp_const _)
  have hHψ2 : MemLp Hψ 2 π := hψ2.sub (memLp_const _)
  have hHφsq : Integrable (fun x => (Hφ x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hHφm.aestronglyMeasurable).1 hHφ2
  have hHψsq : Integrable (fun x => (Hψ x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hHψm.aestronglyMeasurable).1 hHψ2
  set Gφ : X → ℝ := fun x => ∫ y, Hφ y ∂(iterKernel P k x) with hGφ
  set Gψ : X → ℝ := fun x => ∫ y, Hψ y ∂(iterKernel P k x) with hGψ
  have hGφm : Measurable Gφ :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hHφm.stronglyMeasurable).measurable
  have hGψm : Measurable Gψ :=
    (StronglyMeasurable.integral_kernel (κ := iterKernel P k) hHψm.stronglyMeasurable).measurable
  have hGφ2 : MemLp Gφ 2 π := (memLp_two_iff_integrable_sq hGφm.aestronglyMeasurable).2
    (iterMean_bound P π hinv k Hφ hHφm hHφsq).1
  have hGψ2 : MemLp Gψ 2 π := (memLp_two_iff_integrable_sq hGψm.aestronglyMeasurable).2
    (iterMean_bound P π hinv k Hψ hHψm hHψsq).1
  -- the four lagged covariances as integrals
  have e1 : lagCovariance P π φ φ k = ∫ x, Hφ x * Gφ x ∂π :=
    lagCovariance_eq_centred P π hinv φ φ hφ hφi k
  have e2 : lagCovariance P π ψ ψ k = ∫ x, Hψ x * Gψ x ∂π :=
    lagCovariance_eq_centred P π hinv ψ ψ hψ hψi k
  have e3 : lagCovariance P π (fun x => φ x - ψ x) φ k
      = ∫ x, (Hφ x - Hψ x) * Gφ x ∂π := by
    rw [lagCovariance_eq_centred P π hinv (fun x => φ x - ψ x) φ hφ hφi k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    congr 1
    rw [hcd, hHφ, hHψ]; ring
  have e4 : lagCovariance P π ψ (fun x => φ x - ψ x) k
      = ∫ x, Hψ x * (Gφ x - Gψ x) ∂π := by
    have hdm : Measurable (fun x => φ x - ψ x) := hφ.sub hψ
    rw [lagCovariance_eq_centred P π hinv ψ (fun x => φ x - ψ x) hdm hdi k]
    have hinvk : Kernel.Invariant (iterKernel P k) π := invariant_iterKernel P π hinv k
    have hsplitφ := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
      (f := Hφ) hHφm.aestronglyMeasurable).1
      (by rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]
          exact hHφ2.integrable (by norm_num))
    have hsplitψ := (Measure.integrable_comp_iff (κ := iterKernel P k) (μ := π)
      (f := Hψ) hHψm.aestronglyMeasurable).1
      (by rw [show ((iterKernel P k) ∘ₘ π) = π from hinvk]
          exact hHψ2.integrable (by norm_num))
    refine integral_congr_ae ?_
    filter_upwards [hsplitφ.1, hsplitψ.1] with x hxφ hxψ
    congr 1
    have : ∀ y, (φ y - ψ y) - (cφ - cψ) = Hφ y - Hψ y := by intro y; rw [hHφ, hHψ]; ring
    rw [hcd]
    rw [integral_congr_ae (Filter.Eventually.of_forall this), integral_sub hxφ hxψ]
  -- combine
  have i1 : Integrable (fun x => Hφ x * Gφ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHφ2 hGφ2
  have i2 : Integrable (fun x => Hψ x * Gψ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHψ2 hGψ2
  have i3 : Integrable (fun x => Hψ x * Gφ x) π := MemLp.integrable_mul (p := 2) (q := 2) hHψ2 hGφ2
  have i4 : Integrable (fun x => (Hφ x - Hψ x) * Gφ x) π :=
    MemLp.integrable_mul (p := 2) (q := 2) (hHφ2.sub hHψ2) hGφ2
  have i5 : Integrable (fun x => Hψ x * (Gφ x - Gψ x)) π :=
    MemLp.integrable_mul (p := 2) (q := 2) hHψ2 (hGφ2.sub hGψ2)
  rw [e1, e2, e3, e4]
  have s1 : ∫ x, (Hφ x - Hψ x) * Gφ x ∂π
      = (∫ x, Hφ x * Gφ x ∂π) - ∫ x, Hψ x * Gφ x ∂π := by
    rw [← integral_sub i1 i3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have s2 : ∫ x, Hψ x * (Gφ x - Gψ x) ∂π
      = (∫ x, Hψ x * Gφ x ∂π) - ∫ x, Hψ x * Gψ x ∂π := by
    rw [← integral_sub i3 i2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [s1, s2]; ring

/-- **The asymptotic variance is `L²(π)`-continuous**, with an explicit modulus. -/
lemma abs_asymptoticVariance_sub_le (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (φ ψ : X → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ2 : MemLp φ 2 π) (hψ2 : MemLp ψ 2 π) :
    |asymptoticVariance P π φ - asymptoticVariance P π ψ|
      ≤ (l2NormAux π (fun x => φ x - ∫ y, φ y ∂π)
          + l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π))
        * l2NormAux π (fun x => (φ x - ψ x) - ∫ y, (φ y - ψ y) ∂π)
        * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by
  classical
  set D : X → ℝ := fun x => φ x - ψ x with hD
  have hDm : Measurable D := hφ.sub hψ
  have hD2 : MemLp D 2 π := hφ2.sub hψ2
  set Lφ := l2NormAux π (fun x => φ x - ∫ y, φ y ∂π) with hLφ
  set Lψ := l2NormAux π (fun x => ψ x - ∫ y, ψ y ∂π) with hLψ
  set LD := l2NormAux π (fun x => D x - ∫ y, D y ∂π) with hLD
  have hLφ0 : 0 ≤ Lφ := l2NormAux_nonneg _ _
  have hLψ0 : 0 ≤ Lψ := l2NormAux_nonneg _ _
  have hLD0 : 0 ≤ LD := l2NormAux_nonneg _ _
  set M := (Lφ + Lψ) * LD with hM
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) hLD0
  -- pointwise bound on the difference of the diagonal lagged covariances
  have hdiff : ∀ k : ℕ, |lagCovariance P π φ φ k - lagCovariance P π ψ ψ k|
      ≤ M * (1 / 2 : ℝ) ^ (k / N) := by
    intro k
    rw [lagCovariance_diag_sub P π hinv φ ψ hφ hψ hφ2 hψ2 k]
    refine le_trans (abs_add_le _ _) ?_
    have b1 := abs_lagCovariance_le_bilin P π hinv N hN hrate D φ hDm hφ hD2 hφ2 k
    have b2 := abs_lagCovariance_le_bilin P π hinv N hN hrate ψ D hψ hDm hψ2 hD2 k
    have hp0 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (k / N) := by positivity
    calc |lagCovariance P π D φ k| + |lagCovariance P π ψ D k|
        ≤ LD * Lφ * (1 / 2 : ℝ) ^ (k / N) + Lψ * LD * (1 / 2 : ℝ) ^ (k / N) :=
          add_le_add b1 b2
      _ = M * (1 / 2 : ℝ) ^ (k / N) := by rw [hM]; ring
  -- summability
  have hsumφ := summable_lagCovariance_succ P π hinv N hN hrate φ φ hφ hφ hφ2 hφ2
  have hsumψ := summable_lagCovariance_succ P π hinv N hN hrate ψ ψ hψ hψ hψ2 hψ2
  have hgeo := summable_half_pow_div N hN
  have hSnn : 0 ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N) :=
    tsum_nonneg fun k => by positivity
  have hbnd : ∀ k : ℕ, ‖lagCovariance P π φ φ (k + 1) - lagCovariance P π ψ ψ (k + 1)‖
      ≤ M * (1 / 2 : ℝ) ^ (k / N) := by
    intro k
    rw [Real.norm_eq_abs]
    refine le_trans (hdiff (k + 1)) ?_
    have hle : k / N ≤ (k + 1) / N := Nat.div_le_div_right (by omega)
    have hp : (1 / 2 : ℝ) ^ ((k + 1) / N) ≤ (1 / 2 : ℝ) ^ (k / N) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    nlinarith [hM0, hp]
  have hsumabs : Summable (fun k : ℕ =>
      ‖lagCovariance P π φ φ (k + 1) - lagCovariance P π ψ ψ (k + 1)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbnd (hgeo.mul_left M)
  have htail : |(∑' k : ℕ, lagCovariance P π φ φ (k + 1))
      - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)|
      ≤ M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N) := by
    rw [← Summable.tsum_sub hsumφ hsumψ]
    refine le_trans (by simpa using norm_tsum_le_tsum_norm hsumabs) ?_
    rw [← hgeo.tsum_mul_left M]
    exact hsumabs.tsum_le_tsum hbnd (hgeo.mul_left M)
  have hzero : |lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0| ≤ M := by
    have := hdiff 0
    simpa using this
  -- assemble
  have hexp : asymptoticVariance P π φ - asymptoticVariance P π ψ
      = (lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0)
        + 2 * ((∑' k : ℕ, lagCovariance P π φ φ (k + 1))
              - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)) := by
    simp only [asymptoticVariance, asymptoticCovariance]
    ring
  rw [hexp]
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_mul, abs_two]
  have : M + 2 * (M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N))
      = M * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by ring
  calc |lagCovariance P π φ φ 0 - lagCovariance P π ψ ψ 0|
        + 2 * |(∑' k : ℕ, lagCovariance P π φ φ (k + 1))
              - ∑' k : ℕ, lagCovariance P π ψ ψ (k + 1)|
      ≤ M + 2 * (M * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := by
        exact add_le_add hzero (by linarith [htail])
    _ = M * (1 + 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N)) := this

/-! ### Truncation -/

lemma sampleAvg_sub (f g : X → ℝ) (n : ℕ) (ω : ℕ → X) :
    sampleAvg f n ω - sampleAvg g n ω = sampleAvg (fun x => f x - g x) n ω := by
  unfold sampleAvg
  rw [← mul_sub, ← Finset.sum_sub_distrib]

/-- Truncation of an observable at level `K`. -/
noncomputable def truncAt (K : ℕ) (f : X → ℝ) : X → ℝ :=
  fun x => max (-(K : ℝ)) (min (K : ℝ) (f x))

lemma measurable_truncAt (K : ℕ) (f : X → ℝ) (hf : Measurable f) :
    Measurable (truncAt K f) := by
  unfold truncAt; fun_prop

lemma abs_truncAt_le (K : ℕ) (f : X → ℝ) (x : X) : |truncAt K f x| ≤ (K : ℝ) := by
  have hK : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  rw [abs_le, truncAt]
  refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma abs_sub_truncAt_le_abs (K : ℕ) (f : X → ℝ) (x : X) :
    |f x - truncAt K f x| ≤ |f x| := by
  have hK : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  by_cases h1 : f x ≤ -(K:ℝ)
  · have ht : truncAt K f x = -(K:ℝ) := by
      rw [truncAt, min_eq_right (by linarith), max_eq_left h1]
    rw [ht, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1' : -(K:ℝ) < f x := not_le.1 h1
    by_cases h2 : f x ≤ (K:ℝ)
    · have ht : truncAt K f x = f x := by
        rw [truncAt, min_eq_right h2, max_eq_right (le_of_lt h1')]
      rw [ht]; simp
    · have h2' : (K:ℝ) < f x := not_le.1 h2
      have ht : truncAt K f x = (K:ℝ) := by
        rw [truncAt, min_eq_left (le_of_lt h2'), max_eq_right (by linarith)]
      rw [ht, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma tendsto_sub_truncAt (f : X → ℝ) (x : X) :
    Filter.Tendsto (fun K : ℕ => f x - truncAt K f x) atTop (𝓝 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|f x|⌉₊) fun K hK => ?_
  have h1 : |f x| ≤ (K : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hK)
  obtain ⟨hl, hr⟩ := abs_le.1 h1
  have h2 : truncAt K f x = f x := by
    rw [truncAt, min_eq_right hr, max_eq_right hl]
  rw [h2]; ring

/-- The centred second moment never exceeds the second moment. -/
lemma integral_sq_sub_mean_le (π : Measure X) [IsProbabilityMeasure π] (g : X → ℝ)
    (hg : MemLp g 2 π) :
    ∫ x, (g x - ∫ y, g y ∂π) ^ 2 ∂π ≤ ∫ x, (g x) ^ 2 ∂π := by
  have hgi : Integrable g π := hg.integrable (by norm_num)
  have hgsq : Integrable (fun x => (g x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg
  set c := ∫ y, g y ∂π with hc
  have hexp : ∀ x, (g x - c) ^ 2 = ((g x) ^ 2 - (2 * c) * g x) + c ^ 2 := fun x => by ring
  have i2 : Integrable (fun x => (2 * c) * g x) π := hgi.const_mul _
  have i1 : Integrable (fun x => (g x) ^ 2 - (2 * c) * g x) π := hgsq.sub' i2
  have key : ∫ x, (g x - c) ^ 2 ∂π = (∫ x, (g x) ^ 2 ∂π) - c ^ 2 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add i1 (integrable_const _), integral_sub hgsq i2,
      integral_const_mul, integral_const, ← hc]
    simp
    ring
  rw [key]
  nlinarith [sq_nonneg c]

/-- For a probability measure, the `L¹` norm is dominated by the `L²` norm. -/
lemma integral_abs_le_sqrt_integral_sq (π : Measure X) [IsProbabilityMeasure π] (W : X → ℝ)
    (hW : MemLp W 2 π) :
    ∫ x, |W x| ∂π ≤ Real.sqrt (∫ x, (W x) ^ 2 ∂π) := by
  have h := abs_integral_mul_le π (fun x => |W x|) (fun _ => (1:ℝ)) hW.abs (memLp_const 1)
  have e1 : ∀ x, |W x| * (1:ℝ) = |W x| := by intro x; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e1)] at h
  have e2 : ∫ x, (|W x|) ^ 2 ∂π = ∫ x, (W x) ^ 2 ∂π :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs _)
  have e3 : ∫ (_ : X), (1:ℝ) ^ 2 ∂π = 1 := by simp
  rw [e2, e3, Real.sqrt_one, mul_one] at h
  exact le_trans (le_abs_self _) h

lemma abs_truncAt_le_abs (K : ℕ) (f : X → ℝ) (x : X) : |truncAt K f x| ≤ |f x| := by
  have hK : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  by_cases h1 : f x ≤ -(K:ℝ)
  · have ht : truncAt K f x = -(K:ℝ) := by
      rw [truncAt, min_eq_right (by linarith), max_eq_left h1]
    rw [ht, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1' : -(K:ℝ) < f x := not_le.1 h1
    by_cases h2 : f x ≤ (K:ℝ)
    · have ht : truncAt K f x = f x := by
        rw [truncAt, min_eq_right h2, max_eq_right (le_of_lt h1')]
      rw [ht]
    · have h2' : (K:ℝ) < f x := not_le.1 h2
      have ht : truncAt K f x = (K:ℝ) := by
        rw [truncAt, min_eq_left (le_of_lt h2'), max_eq_right (by linarith)]
      rw [ht, abs_of_nonneg hK, abs_of_nonneg (by linarith)]; linarith

lemma measurable_sampleAvg (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω : ℕ → X => sampleAvg f n ω) := by
  unfold sampleAvg
  exact (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply (i + 1))).const_mul _

/-- **Identification of the CLT limit variance, `L²` case, reduced to the bounded case.** -/
theorem asymptoticVariance_eq_of_clt_main (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    (v : ℝ) = asymptoticVariance P π f := by
  classical
  have hinv : Kernel.Invariant P π := hP.1
  obtain ⟨N, hN, hrate⟩ := exists_lag_tvDist_le_of_uniformlyErgodic P π huni
  have hNR : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  set μc := chainMeasure P π with hμc
  have hfi : Integrable f π := hL2.integrable (by norm_num)
  have hfsq : Integrable (fun x => (f x) ^ 2) π :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hL2
  have hf2nn : (0:ℝ) ≤ ∫ x, (f x) ^ 2 ∂π := integral_nonneg fun x => sq_nonneg _
  -- truncations
  set g : ℕ → X → ℝ := fun K => truncAt K f with hgdef
  have hgm : ∀ K, Measurable (g K) := fun K => measurable_truncAt K f hf
  have hgb : ∀ K x, |g K x| ≤ (K:ℝ) := fun K x => abs_truncAt_le K f x
  have hgL2 : ∀ K, MemLp (g K) 2 π := fun K =>
    MemLp.of_bound (hgm K).aestronglyMeasurable (K:ℝ)
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hgb K x)
  have hgsqle : ∀ K, ∫ x, (g K x) ^ 2 ∂π ≤ ∫ x, (f x) ^ 2 ∂π := by
    intro K
    refine integral_mono ((memLp_two_iff_integrable_sq (hgm K).aestronglyMeasurable).1 (hgL2 K))
      hfsq fun x => ?_
    have := abs_truncAt_le_abs K f x
    nlinarith [abs_nonneg (g K x), abs_nonneg (f x), sq_abs (g K x), sq_abs (f x)]
  -- remainders
  set r : ℕ → X → ℝ := fun K x => f x - g K x with hrdef
  have hrm : ∀ K, Measurable (r K) := fun K => hf.sub (hgm K)
  have hrL2 : ∀ K, MemLp (r K) 2 π := fun K => hL2.sub (hgL2 K)
  have hrsq : ∀ K, Integrable (fun x => (r K x) ^ 2) π := fun K =>
    (memLp_two_iff_integrable_sq (hrm K).aestronglyMeasurable).1 (hrL2 K)
  set E : ℕ → ℝ := fun K => ∫ x, (r K x - ∫ y, r K y ∂π) ^ 2 ∂π with hEdef
  have hE0 : ∀ K, 0 ≤ E K := fun K => integral_nonneg fun x => sq_nonneg _
  have hEle : ∀ K, E K ≤ ∫ x, (r K x) ^ 2 ∂π := fun K =>
    integral_sq_sub_mean_le π (r K) (hrL2 K)
  have hrto0 : Filter.Tendsto (fun K => ∫ x, (r K x) ^ 2 ∂π) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (F := fun K x => (r K x) ^ 2)
      (f := fun _ : X => (0:ℝ)) (bound := fun x => (f x) ^ 2)
      (fun K => ((hrm K).pow_const 2).aestronglyMeasurable) hfsq
      (fun K => Filter.Eventually.of_forall fun x => by
        have h := abs_sub_truncAt_le_abs K f x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [abs_nonneg (r K x), abs_nonneg (f x), sq_abs (r K x), sq_abs (f x)])
      (Filter.Eventually.of_forall fun x => by
        have h := tendsto_sub_truncAt f x
        simpa using (h.pow 2))
    simpa using this
  have hEto0 : Filter.Tendsto E atTop (𝓝 0) := squeeze_zero hE0 hEle hrto0
  -- CLT for each truncation, and its identified variance
  have hbclt : ∀ K, ∃ w : ℝ≥0, TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg (g K) n ω - ∫ x, g K x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => μc) (gaussianReal 0 w) := by
    intro K
    obtain ⟨w, hw⟩ := clt_of_bounded_of_uniformlyErgodic P π hinv huni (g K) (hgm K) (K:ℝ) (hgb K)
    exact ⟨w, hw π⟩
  choose w hw using hbclt
  have hwval : ∀ K, ((w K : ℝ≥0) : ℝ) = asymptoticVariance P π (g K) := fun K =>
    asymptoticVariance_eq_of_clt_of_bounded P π hP huni (g K) (hgm K) (K:ℝ) (hgb K) (w K) (hw K)
  -- uniform second-moment bound
  set Bnd : ℝ := 4 * (N:ℝ) * ∫ x, (f x) ^ 2 ∂π with hBnd
  set Y : ℕ → (ℕ → X) → ℝ :=
    fun n ω => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π) with hY
  set YK : ℕ → ℕ → (ℕ → X) → ℝ :=
    fun K n ω => Real.sqrt n * (sampleAvg (g K) n ω - ∫ x, g K x ∂π) with hYK
  have hYmeas : ∀ n, Measurable (Y n) := fun n =>
    ((measurable_sampleAvg f hf n).sub measurable_const).const_mul _
  have hYKmeas : ∀ K n, Measurable (YK K n) := fun K n =>
    ((measurable_sampleAvg (g K) (hgm K) n).sub measurable_const).const_mul _
  have hYint : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) μc := fun n =>
    integrable_sq_scaled_sampleAvg P π hinv f hf hfsq n
  have hYbd : ∀ n, ∫ ω, (Y n ω) ^ 2 ∂μc ≤ Bnd := by
    intro n
    refine le_trans (integral_sq_scaled_sampleAvg_le P π hinv N hN hrate f hf hfsq n) ?_
    have h := integral_sq_sub_mean_le π f hL2
    rw [hBnd]; nlinarith [hNR, h]
  have hvB : (v:ℝ) ≤ Bnd :=
    gaussian_variance_le_of_tendstoInDistribution μc Y v Bnd hYmeas hclt hYint hYbd
  have hwB : ∀ K, ((w K : ℝ≥0) : ℝ) ≤ Bnd := by
    intro K
    have hgsqK : Integrable (fun x => (g K x) ^ 2) π :=
      (memLp_two_iff_integrable_sq (hgm K).aestronglyMeasurable).1 (hgL2 K)
    refine gaussian_variance_le_of_tendstoInDistribution μc (YK K) (w K) Bnd (hYKmeas K)
      (hw K) (fun n => integrable_sq_scaled_sampleAvg P π hinv (g K) (hgm K) hgsqK n)
      (fun n => ?_)
    refine le_trans (integral_sq_scaled_sampleAvg_le P π hinv N hN hrate (g K) (hgm K) hgsqK n) ?_
    have h1 := integral_sq_sub_mean_le π (g K) (hgL2 K)
    have h2 := hgsqle K
    rw [hBnd]; nlinarith [hNR, h1, h2]
  -- L¹ closeness of the two CLT-scaled sequences
  have hdiffeq : ∀ K n, (fun ω => Y n ω - YK K n ω)
      = fun ω => Real.sqrt n * (sampleAvg (r K) n ω - ∫ x, r K x ∂π) := by
    intro K n
    funext ω
    have h1 : sampleAvg f n ω - sampleAvg (g K) n ω = sampleAvg (r K) n ω :=
      sampleAvg_sub f (g K) n ω
    have h2 : ∫ x, r K x ∂π = (∫ x, f x ∂π) - ∫ x, g K x ∂π :=
      integral_sub hfi ((hgL2 K).integrable (by norm_num))
    simp only [hY, hYK]
    rw [h2, ← h1]; ring
  have hWL2 : ∀ K n, MemLp (fun ω => Y n ω - YK K n ω) 2 μc := by
    intro K n
    rw [hdiffeq K n]
    refine (memLp_two_iff_integrable_sq ?_).2
      (integrable_sq_scaled_sampleAvg P π hinv (r K) (hrm K) (hrsq K) n)
    exact (((measurable_sampleAvg (r K) (hrm K) n).sub measurable_const).const_mul
      _).aestronglyMeasurable
  have hclose : ∀ K n, ∫ ω, |Y n ω - YK K n ω| ∂μc ≤ Real.sqrt (4 * (N:ℝ) * E K) := by
    intro K n
    refine le_trans (integral_abs_le_sqrt_integral_sq μc _ (hWL2 K n)) ?_
    refine Real.sqrt_le_sqrt ?_
    have hbase := integral_sq_scaled_sampleAvg_le P π hinv N hN hrate (r K) (hrm K) (hrsq K) n
    have heq : ∫ ω, (Y n ω - YK K n ω) ^ 2 ∂μc
        = ∫ ω, (Real.sqrt n * (sampleAvg (r K) n ω - ∫ x, r K x ∂π)) ^ 2 ∂μc :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [congrFun (hdiffeq K n) ω])
    rw [heq]
    exact hbase
  have hintdiff : ∀ K n, Integrable (fun ω => |Y n ω - YK K n ω|) μc := fun K n =>
    ((hWL2 K n).integrable (by norm_num)).abs
  have hexpvar : ∀ K, |(v:ℝ) - ((w K : ℝ≥0) : ℝ)|
      ≤ 2 * Real.exp (Bnd / 2) * Real.sqrt (4 * (N:ℝ) * E K) := by
    intro K
    have h1 := abs_exp_variance_sub_le_of_tendstoInDistribution μc Y (YK K) v (w K)
      (Real.sqrt (4 * (N:ℝ) * E K)) hYmeas (hYKmeas K) hclt (hw K) (hintdiff K) (hclose K)
    have h2 := abs_sub_le_exp_mul_abs_exp_neg_half_sub Bnd (v:ℝ) ((w K : ℝ≥0) : ℝ)
      v.coe_nonneg (w K).coe_nonneg hvB (hwB K)
    refine le_trans h2 ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  -- closeness of the asymptotic variances
  set S := ∑' k : ℕ, (1 / 2 : ℝ) ^ (k / N) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  set L0 := Real.sqrt (∫ x, (f x) ^ 2 ∂π) with hL0
  have hL00 : 0 ≤ L0 := Real.sqrt_nonneg _
  have hLf : l2NormAux π (fun x => f x - ∫ y, f y ∂π) ≤ L0 := by
    rw [l2NormAux, hL0]; exact Real.sqrt_le_sqrt (integral_sq_sub_mean_le π f hL2)
  have hLg : ∀ K, l2NormAux π (fun x => g K x - ∫ y, g K y ∂π) ≤ L0 := by
    intro K
    rw [l2NormAux, hL0]
    exact Real.sqrt_le_sqrt (le_trans (integral_sq_sub_mean_le π (g K) (hgL2 K)) (hgsqle K))
  have hLD : ∀ K, l2NormAux π (fun x => (f x - g K x) - ∫ y, (f y - g K y) ∂π)
      = Real.sqrt (E K) := fun K => rfl
  have hsig : ∀ K, |asymptoticVariance P π f - asymptoticVariance P π (g K)|
      ≤ 2 * L0 * (1 + 2 * S) * Real.sqrt (E K) := by
    intro K
    have h := abs_asymptoticVariance_sub_le P π hinv N hN hrate f (g K) hf (hgm K) hL2 (hgL2 K)
    rw [hLD K, ← hS] at h
    set A := l2NormAux π (fun x => f x - ∫ y, f y ∂π) with hAdef
    set B := l2NormAux π (fun x => g K x - ∫ y, g K y ∂π) with hBdef
    have hsq0 : 0 ≤ Real.sqrt (E K) := Real.sqrt_nonneg _
    have hpos : (0:ℝ) ≤ 1 + 2 * S := by linarith
    have hsum : A + B ≤ 2 * L0 := by have := hLg K; linarith [hLf]
    refine le_trans h ?_
    have h1 : (A + B) * Real.sqrt (E K) ≤ (2 * L0) * Real.sqrt (E K) :=
      mul_le_mul_of_nonneg_right hsum hsq0
    calc (A + B) * Real.sqrt (E K) * (1 + 2 * S)
        ≤ (2 * L0) * Real.sqrt (E K) * (1 + 2 * S) := mul_le_mul_of_nonneg_right h1 hpos
      _ = 2 * L0 * (1 + 2 * S) * Real.sqrt (E K) := by ring
  -- conclude
  have hfinal : ∀ K, |(v:ℝ) - asymptoticVariance P π f|
      ≤ 2 * Real.exp (Bnd / 2) * Real.sqrt (4 * (N:ℝ) * E K)
        + 2 * L0 * (1 + 2 * S) * Real.sqrt (E K) := by
    intro K
    have h1 := hexpvar K
    rw [hwval K] at h1
    have h2 := hsig K
    have h3 : |(v:ℝ) - asymptoticVariance P π f|
        ≤ |(v:ℝ) - asymptoticVariance P π (g K)|
          + |asymptoticVariance P π (g K) - asymptoticVariance P π f| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm (asymptoticVariance P π (g K))] at h3
    linarith
  have hato0 : Filter.Tendsto
      (fun K => 2 * Real.exp (Bnd / 2) * Real.sqrt (4 * (N:ℝ) * E K)
        + 2 * L0 * (1 + 2 * S) * Real.sqrt (E K)) atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun K => Real.sqrt (E K)) atTop (𝓝 0) := by
      have hcs := (Real.continuous_sqrt.tendsto 0).comp hEto0
      simpa only [Function.comp_def, Real.sqrt_zero] using hcs
    have hE' : Filter.Tendsto (fun K => 4 * (N:ℝ) * E K) atTop (𝓝 0) := by
      simpa using hEto0.const_mul (4 * (N:ℝ))
    have h2 : Filter.Tendsto (fun K => Real.sqrt (4 * (N:ℝ) * E K)) atTop (𝓝 0) := by
      have hcs := (Real.continuous_sqrt.tendsto 0).comp hE'
      simpa only [Function.comp_def, Real.sqrt_zero] using hcs
    have := (h2.const_mul (2 * Real.exp (Bnd / 2))).add (h1.const_mul (2 * L0 * (1 + 2 * S)))
    simpa using this
  have hle0 : |(v:ℝ) - asymptoticVariance P π f| ≤ 0 :=
    ge_of_tendsto hato0 (Filter.Eventually.of_forall hfinal)
  have := abs_nonneg ((v:ℝ) - asymptoticVariance P π f)
  have hz : (v:ℝ) - asymptoticVariance P π f = 0 :=
    abs_eq_zero.1 (le_antisymm hle0 this)
  linarith

end MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : MarkovChainCLT.HarrisErgodic P π)
    (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) =>
        Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => MarkovChainCLT.chainMeasure P π)
      (gaussianReal 0 v)) :
    (v : ℝ) = MarkovChainCLT.asymptoticVariance P π f :=
  MarkovChainCLT.asymptoticVariance_eq_of_clt_main P π hP huni f hf hL2 v hclt
