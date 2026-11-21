-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.uniform_wide_gaussian_initial_sampler
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:52:43.960207+00:00
-- url     : https://prove2.me/submissions/13e583c6-02da-49a8-b0be-9a892f68ba06

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_03
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_ShorAlgorithms_QFT_Circuit
set_option Elab.async true

set_option linter.all false

namespace AFT
end AFT

namespace AFT.BetaReference
end AFT.BetaReference

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace AFT.FiniteConvolutionProgram
end AFT.FiniteConvolutionProgram

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.PermutationProgram
end AFT.PermutationProgram

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace Hex.Matrix
end Hex.Matrix

namespace InfoLossLAR.WorstCase
end InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.GaussianProjection
end InfoLossLAR.WorstCase.GaussianProjection

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry
end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

namespace InfoLossLAR.WorstCase.RegevSketch
end InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT

namespace InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h05d99dd2bef78a64.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT

namespace InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h1076ff82614707e5.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT

namespace InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h18af7218e3ae5082.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT

namespace InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h2882c93186ab7cf8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT

namespace InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3497cf28d345cc71.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT

namespace InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h3827d5d7d51242c6.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT

namespace InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h41ae6c8d47a51d34.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT

namespace InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4b0b2c49d14fd209.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT

namespace InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h4f5add37bf40c2da.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT
end InfoLossLARNativeSupplements.h5a8ca90c605f85fc.AFT

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT

namespace InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5b3dd70c728d6348.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT

namespace InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h5f0d1be1226eed7f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT

namespace InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h6381918e2bfc67e4.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT

namespace InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h707562ec4bd11ae8.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT

namespace InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic
end InfoLossLARNativeSupplements.h7fd26e43562bbe30.AFT.BinaryArithmetic

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT

namespace InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h854528c9e123c6f3.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT

namespace InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h878260dd8e6c9a6e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT

namespace InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h8fac5110874b5cd9.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT

namespace InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h90032182500c2e77.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT

namespace InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics
end InfoLossLARNativeSupplements.h91d71a61f0497f7b.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT

namespace InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.ha562531658b7642e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT
end InfoLossLARNativeSupplements.had468f01f375d910.AFT

namespace InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics
end InfoLossLARNativeSupplements.had468f01f375d910.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT
end InfoLossLARNativeSupplements.hb0db73987b7b1eff.AFT

namespace InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT
end InfoLossLARNativeSupplements.hb6587a05bd2df660.AFT

namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT

namespace InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic
end InfoLossLARNativeSupplements.hbc5d2d237f3bc4c8.AFT.BinaryArithmetic

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT

namespace InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hc6ad092b2f522781.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT

namespace InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hca9f3ecea512145f.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT

namespace InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hdcd54a4fdf95f258.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT

namespace InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics
end InfoLossLARNativeSupplements.he7db6c4ee6224eee.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT

namespace InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hec331a1b1191da2d.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT

namespace InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics
end InfoLossLARNativeSupplements.hf2382f7ddc8e222e.AFT.RationalNumerics

namespace InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT
end InfoLossLARNativeSupplements.hf808c8dbbd952db7.AFT

namespace Integration9_9
end Integration9_9

namespace Integration9_9.LARPlatformEncoding
end Integration9_9.LARPlatformEncoding

namespace Integration9_9.TM2NativeFiniteDraw
end Integration9_9.TM2NativeFiniteDraw

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace Integration9_9.TM2NativeRootGroupProfiles
end Integration9_9.TM2NativeRootGroupProfiles

namespace Matrix
end Matrix

namespace OAI.MetricKMedian.Binary
end OAI.MetricKMedian.Binary

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace OAI.MetricKMedian.Binary.Automatic.Poly
end OAI.MetricKMedian.Binary.Automatic.Poly

namespace QAlgorithms.Complexity
end QAlgorithms.Complexity

namespace QMCNumericRuntime
end QMCNumericRuntime

namespace RegevLWE.GaussConv
end RegevLWE.GaussConv

/- Helper module AFT.TransportBound. -/
section P2MDyadicModule0

namespace AFT

namespace FiniteDist

open scoped BigOperators

open scoped Classical

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]

theorem event_nonneg (p : FiniteDist α) (s : Finset α) : 0 ≤ p.event s :=
  Finset.sum_nonneg (fun a _ => p.nonneg a)

theorem TVBound.symm {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) : TVBound q p error := by
  intro s
  rw [abs_sub_comm]
  exact h s

theorem TVBound.mono {p q : FiniteDist α} {error largerError : ℝ}
    (h : TVBound p q error) (hle : error ≤ largerError) :
    TVBound p q largerError := fun s => (h s).trans hle

theorem TVBound.triangle {p q r : FiniteDist α} {firstError secondError : ℝ}
    (hfirst : TVBound p q firstError) (hsecond : TVBound q r secondError) :
    TVBound p r (firstError + secondError) := by
  intro s
  calc
    |p.event s - r.event s| ≤ |p.event s - q.event s| + |q.event s - r.event s| :=
      abs_sub_le _ _ _
    _ ≤ firstError + secondError := add_le_add (hfirst s) (hsecond s)

theorem event_map (p : FiniteDist α) (f : α → β) (s : Finset β) :
    (p.map f).event s = ∑ a, if f a ∈ s then p.weight a else 0 := by
  classical
  simp only [event, map_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

/-- Deterministic data processing, including a canonical endpoint pullback. -/
theorem TVBound.map {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) (f : α → β) : TVBound (p.map f) (q.map f) error := by
  classical
  intro s
  rw [event_map, event_map]
  simpa only [event, Finset.sum_filter] using
    h (Finset.univ.filter (fun a => f a ∈ s))

end FiniteDist

end AFT

end P2MDyadicModule0

/- Helper module AFT.TotalVariation. -/
section P2MDyadicModule1

namespace AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

/-- A bounded test cannot distinguish a zero-mass signed measure better than
its positive mass. -/
theorem signed_test_bound (weight test : α → ℝ)
    (hzero : signedMass weight = 0) (htest : ∀ a, 0 ≤ test a ∧ test a ≤ 1) :
    |∑ a, weight a * test a| ≤ positiveMass weight := by
  have hpoint (a : α) :
      -max (-weight a) 0 ≤ weight a * test a ∧
        weight a * test a ≤ max (weight a) 0 := by
    obtain ⟨ht0, ht1⟩ := htest a
    by_cases hw : 0 ≤ weight a
    · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
      constructor <;> nlinarith
    · have hw' : weight a ≤ 0 := le_of_not_ge hw
      rw [max_eq_right hw', max_eq_left (neg_nonneg.mpr hw')]
      constructor <;> nlinarith
  have hmass : positiveMass weight = negativeMass weight := by
    simpa [hzero] using positiveMass_eq weight
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => (hpoint a).1)
    rw [hmass]
    simpa only [Finset.sum_neg_distrib, negativeMass] using h
  · exact Finset.sum_le_sum (fun a _ => (hpoint a).2)

namespace FiniteDist

theorem signedMass_difference (p q : FiniteDist α) :
    signedMass (fun a => p.weight a - q.weight a) = 0 := by
  simp [signedMass, Finset.sum_sub_distrib, p.sum_one, q.sum_one]

/-- The eventwise definition used by V7 equals the positive-mass definition. -/
theorem tvBound_iff_totalVariation_le (p q : FiniteDist α) (error : ℝ) :
    TVBound p q error ↔ totalVariation p q ≤ error := by
  classical
  constructor
  · intro h
    let s := Finset.univ.filter (fun a => 0 ≤ p.weight a - q.weight a)
    have hevent : p.event s - q.event s = totalVariation p q := by
      simp only [event, s, Finset.sum_filter, ← Finset.sum_sub_distrib,
        totalVariation, positiveMass]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 ≤ p.weight a - q.weight a
      · simp [ha]
      · simp [ha, max_eq_right (le_of_not_ge ha)]
    have hn : 0 ≤ totalVariation p q :=
      Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have he := h s
    rwa [hevent, abs_of_nonneg hn] at he
  · intro h s
    have ht : ∀ a : α, 0 ≤ (if a ∈ s then (1 : ℝ) else 0) ∧
        (if a ∈ s then (1 : ℝ) else 0) ≤ 1 := by
      intro a
      split_ifs <;> norm_num
    have hb := signed_test_bound (fun a => p.weight a - q.weight a)
      (fun a => if a ∈ s then 1 else 0) (signedMass_difference p q) ht
    have he : (∑ a, (p.weight a - q.weight a) * (if a ∈ s then (1 : ℝ) else 0)) =
        p.event s - q.event s := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      simp [event, Finset.sum_sub_distrib]
    rw [he] at hb
    exact hb.trans h

/-- Conventional half-`L¹` formula, proved from the normalized weights. -/
theorem totalVariation_eq_half_l1 (p q : FiniteDist α) :
    totalVariation p q = (∑ a, |p.weight a - q.weight a|) / 2 := by
  let weight := fun a => p.weight a - q.weight a
  have hmass : positiveMass weight = negativeMass weight := by
    have hz : signedMass weight = 0 := signedMass_difference p q
    simpa only [hz, zero_add] using positiveMass_eq weight
  have habs (a : α) : |weight a| = max (weight a) 0 + max (-weight a) 0 := by
    by_cases ha : 0 ≤ weight a
    · simp [abs_of_nonneg ha, max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
    · have ha' : weight a ≤ 0 := le_of_not_ge ha
      simp [abs_of_nonpos ha', max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
  change positiveMass weight = (∑ a, |weight a|) / 2
  simp_rw [habs]
  rw [Finset.sum_add_distrib]
  change positiveMass weight = (positiveMass weight + negativeMass weight) / 2
  rw [← hmass]
  ring

theorem event_le_one (p : FiniteDist α) (s : Finset α) : p.event s ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => p.nonneg a)

theorem event_mix (p : FiniteDist α) (kernel : α → FiniteDist β) (s : Finset β) :
    (p.mix kernel).event s = ∑ a, p.weight a * (kernel a).event s := by
  simp only [event, mix_weight, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteDist

end AFT

end P2MDyadicModule1

/- Helper module AFT.Histogram. -/
section P2MDyadicModule2

namespace AFT

open scoped BigOperators

open scoped Classical

variable {dimension : ℕ} {Color : Type*}

variable [Fintype Color]

namespace FiniteDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem map_const_weight (distribution : FiniteDist α) (value output : β) :
    (distribution.map (fun _ => value)).weight output = if value = output then 1 else 0 := by
  rw [map_weight]
  split_ifs <;> simp [distribution.sum_one]

end FiniteDist

section HistogramKernel

variable [Nonempty Color]

end HistogramKernel

section ZeroSumReference

variable [AddCommMonoid Color]

end ZeroSumReference

end AFT

end P2MDyadicModule2

/- Helper module AFT.GaussianConvolution. -/
section P2MDyadicModule3

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable def shiftedWeight (width center : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ((z : ℝ) - center) ^ 2)

noncomputable def theta (width center : ℝ) : ℝ :=
  ∑' z : ℤ, shiftedWeight width center z

noncomputable def thetaFourier (width center : ℝ) (z : ℤ) : ℂ :=
  Complex.exp (-Real.pi * (width : ℂ) ^ 2 * (z : ℂ) ^ 2 +
    2 * Real.pi * Complex.I * center * z)

/-- Poisson summation for an arbitrarily shifted integer lattice. -/
theorem theta_poisson (width center : ℝ) (hw : 0 < width) :
    (theta width center : ℂ) / width = ∑' z : ℤ, thetaFourier width center z := by
  have hs : ((width : ℂ) ^ 2) ^ (1 / 2 : ℂ) = width := by
    have hr : (width ^ 2) ^ (1 / 2 : ℝ) = width := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hw.le]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    rw [Complex.ofReal_cpow (sq_nonneg width)] at hc
    simpa using hc
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (width : ℂ) ^ 2) (by simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using sq_pos_of_pos hw)
    (Complex.I * center)
  rw [hs] at hp
  have hleft : (∑' z : ℤ, Complex.exp (-Real.pi * (width : ℂ) ^ 2 * z ^ 2 +
      2 * Real.pi * (Complex.I * center) * z)) =
      ∑' z : ℤ, thetaFourier width center z := by
    apply tsum_congr
    intro z
    congr 1
    ring
  have hright : (∑' z : ℤ, Complex.exp
      (-Real.pi / (width : ℂ) ^ 2 * (z + Complex.I * (Complex.I * center)) ^ 2)) =
      (theta width center : ℂ) := by
    rw [theta, Complex.ofReal_tsum]
    apply tsum_congr
    intro z
    rw [shiftedWeight, Complex.ofReal_exp]
    congr 1
    push_cast
    have hI : Complex.I * (Complex.I * (center : ℂ)) = -(center : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hI]
    ring
  rw [hleft, hright] at hp
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hp.symm

theorem thetaFourier_norm (width center : ℝ) (hw : 0 < width) (z : ℤ) :
    ‖thetaFourier width center z‖ = weight (1 / width) z := by
  rw [thetaFourier, Complex.norm_exp]
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.neg_re ]
  unfold weight
  congr 1
  field_simp

theorem summable_thetaFourier (width center : ℝ) (hw : 0 < width) :
    Summable (thetaFourier width center) := by
  apply Summable.of_norm
  simpa only [thetaFourier_norm width center hw] using summable_weight (1 / width) (by positivity)

/-- The nonzero Fourier modes control the entire relative error, uniformly
in the center, by the zero-centered dual Gaussian mass. -/
theorem theta_relative_error (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ realNormalizer (1 / width) - 1 := by
  let f := thetaFourier width center
  have hf := summable_thetaFourier width center hw
  have hnorm : Summable (fun z : ℤ => ‖if z = 0 then (0 : ℂ) else f z‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (summable_weight (1 / width) (by positivity))
    intro z
    split_ifs
    · exact (show ‖(0 : ℂ)‖ = 0 by norm_num).symm ▸ (weight_pos (1 / width) z).le
    · exact le_of_eq (thetaFourier_norm width center hw z)
  have hzero : f 0 = 1 := by simp [f, thetaFourier]
  have heq := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  change (∑' z : ℤ, f z) = f 0 + ∑' z : ℤ, if z = 0 then 0 else f z at heq
  rw [hzero] at heq
  have hdual := (summable_weight (1 / width) (by positivity)).tsum_eq_add_tsum_ite (0 : ℤ)
  change realNormalizer (1 / width) = weight (1 / width) 0 + _ at hdual
  have hwzero : weight (1 / width) 0 = 1 := by simp [weight]
  rw [hwzero] at hdual
  have hnormsum : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
      realNormalizer (1 / width) - 1 := by
    have heq' : (∑' z : ℤ, ‖if z = 0 then (0 : ℂ) else f z‖) =
        ∑' z : ℤ, if z = 0 then 0 else weight (1 / width) z := by
      apply tsum_congr
      intro z
      split_ifs
      · exact norm_zero
      · exact thetaFourier_norm width center hw z
    rw [heq']
    linarith
  have hcomplex : ((theta width center / width - 1 : ℝ) : ℂ) =
      ∑' z : ℤ, if z = 0 then 0 else f z := by
    push_cast
    rw [theta_poisson width center hw]
    change (∑' z : ℤ, f z) - 1 = _
    rw [heq]
    ring
  have h := norm_tsum_le_tsum_norm hnorm
  rw [← hcomplex, Complex.norm_real, Real.norm_eq_abs, hnormsum] at h
  exact h

/-- Explicit exponentially small theta error. -/
noncomputable def thetaError (width : ℝ) : ℝ :=
  2 * (Real.exp (-Real.pi * width ^ 2) / (1 - Real.exp (-Real.pi * width ^ 2)))

theorem thetaError_nonneg (width : ℝ) (hw : 0 < width) : 0 ≤ thetaError width := by
  have h : Real.exp (-Real.pi * width ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hw])
  exact mul_nonneg (by norm_num) (div_nonneg (Real.exp_pos _).le (by linarith))

theorem theta_relative_error_exp (width center : ℝ) (hw : 0 < width) :
    |theta width center / width - 1| ≤ thetaError width := by
  apply (theta_relative_error width center hw).trans
  have h := realNormalizer_le_geometric (1 / width) (by positivity)
  have heq : Real.pi / (1 / width) ^ 2 = Real.pi * width ^ 2 := by field_simp
  rw [heq, ← neg_mul] at h
  unfold thetaError
  linarith

theorem summable_shiftedWeight (width center : ℝ) (hw : 0 < width) :
    Summable (shiftedWeight width center) := by
  let coefficient := Real.pi / width ^ 2
  have hc : 0 < coefficient := div_pos Real.pi_pos (sq_pos_of_pos hw)
  have hw' : 0 < Real.sqrt 2 * width := by positivity
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _
    ((summable_weight (Real.sqrt 2 * width) hw').mul_left
      (Real.exp (coefficient * center ^ 2)))
  intro z
  unfold weight
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := mul_nonneg hc.le (sq_nonneg ((z : ℝ) - 2 * center))
  change -coefficient * ((z : ℝ) - center) ^ 2 ≤ _
  have heq : coefficient * center ^ 2 + -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
      coefficient * center ^ 2 - coefficient * (z : ℝ) ^ 2 / 2 := by
    dsimp [coefficient]
    ring
  rw [heq]
  nlinarith

theorem theta_pos (width center : ℝ) (hw : 0 < width) : 0 < theta width center := by
  have hzero := (summable_shiftedWeight width center hw).le_tsum (0 : ℤ)
    (fun z _ => (Real.exp_pos _).le)
  change shiftedWeight width center 0 ≤ theta width center at hzero
  exact (show 0 < shiftedWeight width center 0 by
    unfold shiftedWeight
    positivity).trans_le hzero

/-- The theta error decreases with the Gaussian width. -/
theorem thetaError_antitone (left right : ℝ) (hl : 0 < left) (h : left ≤ right) :
    thetaError right ≤ thetaError left := by
  have hr : 0 < right := hl.trans_le h
  have hl1 : Real.exp (-Real.pi * left ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hl])
  have hr1 : Real.exp (-Real.pi * right ^ 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sq_pos_of_pos hr])
  have hsq : left ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hl.le hr.le).mpr h
  have he : Real.exp (-Real.pi * right ^ 2) ≤ Real.exp (-Real.pi * left ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  unfold thetaError
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi * right ^ 2))
    (by linarith : 0 < 1 - Real.exp (-Real.pi * left ^ 2))).mpr
  nlinarith

theorem thetaError_le_four_exp (width : ℝ) (hw : 1 ≤ width) :
    thetaError width ≤ 4 * Real.exp (-Real.pi * width ^ 2) := by
  have hw0 : 0 < width := zero_lt_one.trans_le hw
  have hcoef : 1 ≤ Real.pi * width ^ 2 := by
    have hsq : 1 ≤ width ^ 2 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have he : 2 ≤ Real.exp (Real.pi * width ^ 2) :=
    (by linarith : 2 ≤ Real.pi * width ^ 2 + 1).trans (Real.add_one_le_exp _)
  have hhalf : Real.exp (-Real.pi * width ^ 2) ≤ 1 / 2 := by
    rw [neg_mul, Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by simpa using he)
  have hden : 0 < 1 - Real.exp (-Real.pi * width ^ 2) := by linarith
  unfold thetaError
  have hquot : Real.exp (-Real.pi * width ^ 2) /
      (1 - Real.exp (-Real.pi * width ^ 2)) ≤ 2 * Real.exp (-Real.pi * width ^ 2) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.exp_pos (-Real.pi * width ^ 2)]
  linarith

end AFT.GaussianSource

end P2MDyadicModule3

/- Helper module AFT.FiniteTicketSampler. -/
section P2MDyadicModule4

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

/-- Exactly the declared number of tickets selects each table entry,
including zero-count entries and indices beyond the end of the table. -/
theorem bucket_count (counts : List ℕ) (index : ℕ) :
    (∑ ticket ∈ Finset.range counts.sum, if bucket counts ticket = index then 1 else 0) =
      counts[index]?.getD 0 := by
  induction counts generalizing index with
  | nil => simp
  | cons count rest ih =>
    rw [List.sum_cons, Finset.sum_range_add]
    have hfirst (ticket : ℕ) (ht : ticket ∈ Finset.range count) :
        bucket (count :: rest) ticket = 0 := by
      simp only [bucket, if_pos (Finset.mem_range.mp ht)]
    have hsecond (ticket : ℕ) : bucket (count :: rest) (count + ticket) = 1 + bucket rest ticket := by
      simp only [bucket, show ¬count + ticket < count by omega, if_false, Nat.add_sub_cancel_left]
    simp_rw [hsecond]
    cases index with
    | zero =>
      have hf : (∑ ticket ∈ Finset.range count, if bucket (count :: rest) ticket = 0 then 1 else 0) = count := by
        calc
          _ = ∑ _ticket ∈ Finset.range count, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro ticket ht
            rw [hfirst ticket ht]
            simp
          _ = _ := by simp
      simp [hf]
    | succ index =>
      have hf : (∑ ticket ∈ Finset.range count,
          if bucket (count :: rest) ticket = index + 1 then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ticket ht
        rw [hfirst ticket ht]
        simp
      simp only [hf, zero_add, Nat.add_comm 1, Nat.add_right_cancel_iff,
        List.getElem?_cons_succ, ih]

end AFT.FiniteTicketSampler

end P2MDyadicModule4

/- Helper module AFT.QuantizedSampling. -/
section P2MDyadicModule5

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

theorem drawFin_law {n : ℕ} (counts : Fin n → ℕ) (hpositive : 0 < ∑ index, counts index)
    (index : Fin n) :
    (by
      letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
      exact ((FiniteDist.uniform (Fin (∑ index, counts index))).map (drawFin counts)).weight index) =
      (counts index : ℝ) / (∑ index, counts index) := by
  letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
  have hc := bucket_count (List.ofFn counts) index.val
  simp only [List.sum_ofFn, List.getElem?_ofFn, dif_pos index.isLt, Option.getD_some] at hc
  have hreal : (∑ ticket ∈ Finset.range (∑ index, counts index),
      if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0) = counts index := by
    exact_mod_cast hc
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin,
    drawFin, Fin.ext_iff]
  simp_rw [show ∀ ticket : Fin (∑ index, counts index),
    (if bucket (List.ofFn counts) ticket.val = index.val then ((∑ index, counts index : ℕ) : ℝ)⁻¹ else 0) =
      ((∑ index, counts index : ℕ) : ℝ)⁻¹ *
        (if bucket (List.ofFn counts) ticket.val = index.val then 1 else 0) from
          fun ticket => by split_ifs <;> simp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun ticket => if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0)
      (∑ index, counts index), hreal]
  ring

end FiniteTicketSampler

namespace FiniteQuantization

open scoped BigOperators Classical

noncomputable section

end

end FiniteQuantization

end AFT

end P2MDyadicModule5

/- Helper module AFT.FairBitSampling. -/
section P2MDyadicModule6

namespace AFT.FiniteTicketSampler

open scoped BigOperators Classical

theorem independent_fair_bits_uniform (bits : ℕ) :
    FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2)) =
      FiniteDist.uniform (Fin bits → Fin 2) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]

theorem bitTicket_uniform (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map (bitTicket bits) =
      FiniteDist.uniform (Fin (2 ^ bits)) := by
  rw [independent_fair_bits_uniform]
  exact FiniteDist.uniform_map_equiv finFunctionFinEquiv

theorem drawBitTable_law {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ index, counts index = 2 ^ bits) (index : Fin n) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (drawBitTable bits counts htotal)).weight index = (counts index : ℝ) / (2 : ℝ) ^ bits := by
  have hpos : 0 < ∑ index, counts index := by rw [htotal]; positivity
  letI : NeZero (∑ index, counts index) := ⟨hpos.ne'⟩
  have hu := bitTicket_uniform bits
  have ht := FiniteDist.uniform_map_equiv (finCongr htotal.symm)
  have hm := congrArg (fun p : FiniteDist (Fin (2 ^ bits)) =>
    p.map (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) hu
  rw [FiniteDist.map_map] at hm
  have hc := congrArg (fun p : FiniteDist (Fin (∑ index, counts index)) => p.map (drawFin counts)) ht
  rw [FiniteDist.map_map] at hc
  change ((FiniteDist.uniform (Fin (2 ^ bits))).map
    (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) = _ at hc
  change ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
    (fun word => drawFin counts (Fin.cast htotal.symm (bitTicket bits word)))).weight index = _
  rw [hm, hc]
  exact (drawFin_law counts hpos index).trans (by simp only [htotal, Nat.cast_pow, Nat.cast_ofNat])

end FiniteTicketSampler

end AFT

end P2MDyadicModule6

/- Helper module AFT.Rejection. -/
section P2MDyadicModule7

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]

/-- Exact finite retry semantics, including the exhaustion fallback. -/
theorem cappedRejection_weight (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) (a : A) :
    (cappedRejection proposal coin hcoin fallback count).weight a =
      (1 - (1 - acceptance proposal coin) ^ count) *
        (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept).weight a +
          (1 - acceptance proposal coin) ^ count * fallback.weight a := by
  induction count with
  | zero => simp [cappedRejection]
  | succ count ih =>
    simp only [cappedRejection, rejectionStep, ih, pow_succ, acceptedLaw]
    field_simp
    ring

/-- No factor depending on the size of the sample space is paid on retry
exhaustion. -/
theorem cappedRejection_tv (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      ((1 - acceptance proposal coin) ^ count) := by
  intro event
  let accepted := acceptedLaw proposal coin (fun a => (hcoin a).1) haccept
  have hfailure : 0 ≤ (1 - acceptance proposal coin) ^ count :=
    pow_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) _
  have hid : (cappedRejection proposal coin hcoin fallback count).event event - accepted.event event =
      (1 - acceptance proposal coin) ^ count * (fallback.event event - accepted.event event) := by
    simp only [FiniteDist.event, cappedRejection_weight proposal coin hcoin haccept fallback count, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [accepted]
    ring
  change |(cappedRejection proposal coin hcoin fallback count).event event - accepted.event event| ≤ _
  rw [hid, abs_mul, abs_of_nonneg hfailure]
  have hdiff : |fallback.event event - accepted.event event| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [event_nonneg fallback event, event_le_one fallback event,
      event_nonneg accepted event, event_le_one accepted event]
  exact (mul_le_mul_of_nonneg_left hdiff hfailure).trans_eq (mul_one _)

theorem cappedRejection_exp_bound (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      (Real.exp (-(count : ℝ) * acceptance proposal coin)) := by
  apply (cappedRejection_tv proposal coin hcoin haccept fallback count).mono
  have hbase : 1 - acceptance proposal coin ≤ Real.exp (-acceptance proposal coin) := by
    linarith [Real.add_one_le_exp (-acceptance proposal coin)]
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) hbase count
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using hh

end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A : Type*} [Fintype A]

end

end AFT.FiniteDist

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {A S : Type*} [Fintype A] [Fintype S]

end

end AFT.FiniteDist

end P2MDyadicModule7

/- Helper module AFT.SignedConditioning. -/
section P2MDyadicModule8

namespace AFT.SignedConditioning

open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

theorem mass_difference_le_l1 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Normalizing a signed mass loses at most twice its L1 error divided by
its actual positive mass. Only the reference mass needs pointwise positivity. -/
theorem normalized_signed_l1 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using mass_difference_le_l1 signed reference
  have hpoint (color) : |signed color / total - reference color / referenceTotal| ≤
      |signed color - reference color| / total +
        reference color * |referenceTotal - total| / (total * referenceTotal) := by
    have heq : signed color / total - reference color / referenceTotal =
        (signed color - reference color) / total +
          reference color * (referenceTotal - total) / (total * referenceTotal) := by
      dsimp only [total, referenceTotal]
      field_simp
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hsigned,
        abs_of_pos (mul_pos hsigned hreference), abs_of_nonneg (href color)])
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hh
  have heq : (∑ color, |signed color - reference color|) / total +
      (∑ color, reference color) * |referenceTotal - total| / (total * referenceTotal) =
        (error + |referenceTotal - total|) / total := by
    dsimp only [error, total, referenceTotal]
    field_simp
  rw [heq] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hsigned.le
  linarith

end

end AFT.SignedConditioning

end P2MDyadicModule8

/- Helper module AFT.ConditionRejection. -/
section P2MDyadicModule9

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {State : Type*} [Fintype State]

def eventCoin (event : State → Prop) : State → ℝ := fun point => if event point then 1 else 0

omit [Fintype State] in
theorem eventCoin_bounds (event : State → Prop) : ∀ point,0 ≤ eventCoin event point ∧ eventCoin event point ≤ 1 := by
  intro point
  simp only [eventCoin]
  split_ifs <;> norm_num

theorem eventCoin_acceptance (proposal : FiniteDist State) (event : State → Prop) :
    acceptance proposal (eventCoin event)=proposal.eventMass event := by
  simp only [acceptance,eventCoin,eventMass,mul_ite,mul_one,mul_zero]

theorem acceptedLaw_eventCoin (proposal : FiniteDist State) (event : State → Prop)
    (hpos : 0 < proposal.eventMass event) :
    acceptedLaw proposal (eventCoin event) (fun point => (eventCoin_bounds event point).1)
      (by rw [eventCoin_acceptance]; exact hpos)=proposal.condition event hpos := by
  ext point
  simp only [acceptedLaw,condition,eventCoin,eventCoin_acceptance,mul_ite,mul_one,mul_zero]

def cappedCondition (proposal : FiniteDist State) (event : State → Prop)
    (fallback : FiniteDist State) (count : ℕ) : FiniteDist State :=
  cappedRejection proposal (eventCoin event) (eventCoin_bounds event) fallback count

theorem cappedCondition_tv (proposal : FiniteDist State) (event : State → Prop)
    (hpos : 0 < proposal.eventMass event) (fallback : FiniteDist State) (count : ℕ) :
    TVBound (cappedCondition proposal event fallback count) (proposal.condition event hpos)
      (Real.exp (-(count : ℝ)*proposal.eventMass event)) := by
  have hh := cappedRejection_exp_bound proposal (eventCoin event) (eventCoin_bounds event)
    (by rw [eventCoin_acceptance]; exact hpos) fallback count
  rw [acceptedLaw_eventCoin proposal event hpos] at hh
  simpa only [eventCoin_acceptance,cappedCondition] using hh

end

end AFT.FiniteDist

end P2MDyadicModule9

/- Helper module AFT.FiniteConditionProgram. -/
section P2MDyadicModule10

namespace AFT.FiniteConditionProgram

open scoped BigOperators

variable {State : Type*}

def firstAccepted (event : State → Prop) [DecidablePred event] (fallback : State) :
    (attempts : ℕ) → (Fin attempts → State) → State
  | 0, _ => fallback
  | attempts + 1, proposals =>
      if event (proposals 0) then proposals 0
      else firstAccepted event fallback attempts (fun index => proposals index.succ)

noncomputable section

open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable [Fintype State]

theorem independent_cons (proposal : FiniteDist State) (attempts : ℕ) :
    FiniteDist.independent (fun _ : Fin (attempts + 1) => proposal) =
      (proposal.prod (FiniteDist.independent (fun _ : Fin attempts => proposal))).map
        (Fin.consEquiv (fun _ : Fin (attempts + 1) => State)) := by
  apply FiniteDist.ext
  intro word
  rw [FiniteDist.map_equiv_weight]
  change (∏ index, proposal.weight (word index)) =
    proposal.weight (word 0) * ∏ index : Fin attempts, proposal.weight (word index.succ)
  exact Fin.prod_univ_succ _

/-- A fresh proposal either succeeds or uses an independently computed
remaining output. This is the exact transition, including event failure. -/
theorem select_event_law {Random : Type*} [Fintype Random]
    (proposal : FiniteDist State) (remaining : FiniteDist Random)
    (output : Random → State) (event : State → Prop) [DecidablePred event] :
    (proposal.prod remaining).map (fun pair => if event pair.1 then pair.1 else output pair.2) =
      FiniteDist.rejectionStep proposal (FiniteDist.eventCoin event)
        (FiniteDist.eventCoin_bounds event) (remaining.map output) := by
  apply FiniteDist.ext
  intro target
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, Fintype.sum_prod_type]
  have hpoint (candidate : State) :
      (∑ random, if (if event candidate then candidate else output random) = target
        then proposal.weight candidate * remaining.weight random else 0) =
      (if event candidate then (if candidate = target then proposal.weight candidate else 0) else 0) +
        (if event candidate then 0 else proposal.weight candidate) *
          (remaining.map output).weight target := by
    by_cases he : event candidate
    · by_cases ht : candidate = target
      · subst candidate
        simp only [he, if_true, ← Finset.mul_sum, remaining.sum_one, mul_one, zero_mul, add_zero]
      · simp only [he, if_true, if_neg ht, Finset.sum_const_zero, zero_mul, add_zero]
    · simp only [he, if_false, zero_add, FiniteDist.map_weight, Finset.mul_sum, mul_ite, mul_zero]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have haccepted :
      (∑ candidate, if event candidate then (if candidate = target then proposal.weight candidate else 0) else 0) =
      if event target then proposal.weight target else 0 := by
    rw [Finset.sum_eq_single target]
    · simp
    · intro candidate _ hne
      simp [hne]
    · simp
  have hfailed : (∑ candidate, if event candidate then 0 else proposal.weight candidate) =
      1 - FiniteDist.acceptance proposal (FiniteDist.eventCoin event) := by
    calc
      _ = ∑ candidate, (proposal.weight candidate -
          proposal.weight candidate * FiniteDist.eventCoin event candidate) := by
        apply Finset.sum_congr rfl
        intro candidate _
        simp only [FiniteDist.eventCoin]
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, proposal.sum_one]; rfl
  rw [haccepted, hfailed]
  change (if event target then proposal.weight target else 0) + _ =
    proposal.weight target * FiniteDist.eventCoin event target + _
  simp only [FiniteDist.eventCoin, mul_ite, mul_one, mul_zero]

/-- Independent repeated proposals followed by the executable first-success
procedure have exactly the repository's capped conditioning law. -/
theorem firstAccepted_law (proposal : FiniteDist State)
    (event : State → Prop) [DecidablePred event] (fallback : State) (attempts : ℕ) :
    (FiniteDist.independent (fun _ : Fin attempts => proposal)).map
      (firstAccepted event fallback attempts) =
      FiniteDist.cappedCondition proposal event (CanonicalMoments.pointLaw fallback) attempts := by
  induction attempts with
  | zero =>
    apply FiniteDist.ext
    intro target
    change ((FiniteDist.independent (fun _ : Fin 0 => proposal)).map (fun _ => fallback)).weight target =
      (CanonicalMoments.pointLaw fallback).weight target
    rw [FiniteDist.map_const_weight]
    rfl
  | succ attempts ih =>
    rw [independent_cons, FiniteDist.map_map]
    have he : (fun pair : State × (Fin attempts → State) =>
        firstAccepted event fallback (attempts + 1)
          ((Fin.consEquiv (fun _ : Fin (attempts + 1) => State)) pair)) =
        (fun pair => if event pair.1 then pair.1 else firstAccepted event fallback attempts pair.2) := by
      funext pair
      simp only [firstAccepted, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [he, select_event_law, ih]
    rfl

end

end AFT.FiniteConditionProgram

end P2MDyadicModule10

/- Helper module AFT.BinaryBitTape. -/
section P2MDyadicModule11

namespace AFT.BinaryArithmetic

theorem readBitTape_length (bits : ℕ) (word : Fin bits → Fin 2) :
    (readBitTape bits word).digits.length=bits := by
  induction bits with
  | zero => rfl
  | succ bits ih => simp only [readBitTape,List.length_cons,ih]

end AFT.BinaryArithmetic

end P2MDyadicModule11

/- Helper module AFT.RationalPiProgram. -/
section P2MDyadicModule12

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem arctan_term_bound (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- On the two actual rational inputs, absolute geometric majorization
bounds the entire remaining series, including its alternating signs. -/
theorem arctanSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := arctan_term_bound (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum

/-- `bits+3` terms of each short series give the requested binary accuracy. -/
theorem piApprox_error (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := arctanSum_error (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := arctanSum_error (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring

end

end AFT.RationalNumerics

end P2MDyadicModule12

/- Helper module AFT.RationalExpProgram. -/
section P2MDyadicModule13

namespace AFT.RationalNumerics

open scoped BigOperators

noncomputable section

open scoped Classical

theorem expSum_error (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)

/-- Taking reciprocals of quantities at least one has Lipschitz constant
one; it avoids amplification by an exponentially large positive exponential. -/
theorem inv_error_of_ge_one (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem power_error_unit_interval (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- A polynomial range reduction parameter is sufficient for any requested
number of binary digits. The approximation remains positive and bounded. -/
theorem expNegScaled_error (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := power_error_unit_interval ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := inv_error_of_ge_one (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (expSum_error value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp

theorem expNegApprox_error (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := expNegScaled_error (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh

/-- On nonnegative arguments the negative exponential is globally
one-Lipschitz. This controls the separate rational argument approximation. -/
theorem exp_neg_lipschitz (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith

end

end AFT.RationalNumerics

end P2MDyadicModule13

/- Helper module AFT.RationalGaussianProgram. -/
section P2MDyadicModule14

namespace AFT.RationalNumerics

noncomputable section

/-- The finite pi and exponential programs together approximate the actual
Gaussian exponential; all precision guard digits are computed rationally. -/
theorem gaussianApprox_error (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := piApprox_error (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := expNegApprox_error argument (bits+1)
  have hl := exp_neg_lipschitz (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num

end

end AFT.RationalNumerics

end P2MDyadicModule14

/- Helper module AFT.RationalAcceptanceCoin. -/
section P2MDyadicModule15

namespace AFT.RationalAcceptanceCoin

open scoped BigOperators

noncomputable section

theorem draw_acceptance (bits : ℕ) (value : ℚ) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw bits value)).weight 0=probability bits value := by
  exact FiniteTicketSampler.drawBitTable_law bits (counts bits value) (counts_total bits value) 0

theorem probability_floor_error (bits : ℕ) (value : ℚ) :
    |probability bits value-(clipped value : ℝ)| ≤ 1/(2 : ℝ)^bits := by
  have hlo := Nat.floor_le (mul_nonneg (by positivity : (0 : ℚ) ≤ 2^bits) (clipped_bounds value).1)
  have hhi := Nat.lt_floor_add_one ((2^bits : ℚ)*clipped value)
  have hlod : (count bits value : ℚ) ≤ (2 : ℚ)^bits*clipped value := by simpa only [count] using hlo
  have hlo' : (count bits value : ℝ) ≤ (2 : ℝ)^bits*(clipped value : ℝ) := by exact_mod_cast hlod
  have hhid : (2 : ℚ)^bits*clipped value ≤ (count bits value : ℚ)+1 := by simpa only [count] using hhi.le
  have hhi' : (2 : ℝ)^bits*(clipped value : ℝ) ≤ (count bits value : ℝ)+1 := by exact_mod_cast hhid
  have hp : (0 : ℝ) < 2^bits := by positivity
  have he : probability bits value-(clipped value : ℝ)=
      ((count bits value : ℝ)-(2 : ℝ)^bits*(clipped value : ℝ))/(2 : ℝ)^bits := by
    unfold probability
    field_simp
  rw [he,abs_div,abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_le]
  constructor <;> linarith

/-- Clipping does not amplify error against any legal target probability. -/
theorem clipped_error (value : ℚ) (target : ℝ) (ht : 0 ≤ target ∧ target ≤ 1) :
    |(clipped value : ℝ)-target| ≤ |(value : ℝ)-target| := by
  have he : (clipped value : ℝ)=min 1 (max (value : ℝ) 0) := by
    simp [clipped]
  rw [he]
  by_cases hv : (value : ℝ) ≤ 0
  · rw [max_eq_right hv,min_eq_right (by norm_num : (0 : ℝ) ≤ 1),zero_sub,abs_neg,
      abs_of_nonneg ht.1,abs_of_nonpos (by linarith : (value : ℝ)-target ≤ 0)]
    linarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ value)]
    by_cases hv1 : (value : ℝ) ≤ 1
    · rw [min_eq_right hv1]
    · rw [min_eq_left (by linarith : (1 : ℝ) ≤ value),
        abs_of_nonneg (by linarith : 0 ≤ (1 : ℝ)-target),
        abs_of_nonneg (by linarith : 0 ≤ (value : ℝ)-target)]
      linarith

theorem probability_error (bits : ℕ) (value : ℚ) (target : ℝ)
    (ht : 0 ≤ target ∧ target ≤ 1) :
    |probability bits value-target| ≤ 1/(2 : ℝ)^bits+|(value : ℝ)-target| := by
  calc
    _ ≤ |probability bits value-(clipped value : ℝ)|+|(clipped value : ℝ)-target| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (probability_floor_error bits value) (clipped_error value target ht)

end

end AFT.RationalAcceptanceCoin

end P2MDyadicModule15

/- Helper module AFT.BinaryRationalFloor. -/
section P2MDyadicModule16

namespace AFT.BinaryArithmetic.RationalBits

open AFT.RationalNumerics

theorem clipUnit_value (input : RationalBits) :
    (clipUnit input).data.decode=RationalAcceptanceCoin.clipped input.decode := by
  have hd : (0 : ℚ)<value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le
      simp only [clipUnit,hs,ite_true,zero_value,RationalAcceptanceCoin.clipped,max_eq_right hn,
        min_eq_right (by norm_num : (0 : ℚ)≤ 1)]
  | false =>
      have he : input.decode=(value input.numerator : ℚ)/(value input.denominator : ℚ) := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      have hn : 0≤ input.decode := by rw [he];positivity
      simp only [clipUnit,hs,ite_false,Bool.false_eq_true,RationalAcceptanceCoin.clipped,max_eq_left hn]
      split <;> rename_i hb
      · have hc := (subtract_borrow input.numerator input.denominator).mp hb
        have hh : input.decode<1 := by rw [he,div_lt_one hd];exact_mod_cast hc
        exact (min_eq_right hh.le).symm
      · have hc : value input.denominator≤ value input.numerator := by
          exact Nat.le_of_not_gt (fun hh => hb ((subtract_borrow input.numerator input.denominator).mpr hh))
        have hh : 1≤ input.decode := by rw [he,le_div_iff₀ hd];simpa only [one_mul] using (show (value input.denominator : ℚ)≤value input.numerator by exact_mod_cast hc)
        rw [one_value,min_eq_left hh]

end AFT.BinaryArithmetic.RationalBits

end P2MDyadicModule16

/- Helper module AFT.BinaryAcceptanceCoin. -/
section P2MDyadicModule17

namespace AFT.BinaryArithmetic

open RationalNumerics PermutationProgram BetaReference

set_option backward.isDefEq.respectTransparency false in
private theorem rationalAcceptance_threshold (bits : ℕ) (input : ℚ) (word : Fin bits → Fin 2) :
    (RationalAcceptanceCoin.draw bits input word).val=
      if (FiniteTicketSampler.bitTicket bits word).val<RationalAcceptanceCoin.count bits input then 0 else 1 := by
  have ht := (FiniteTicketSampler.bitTicket bits word).isLt
  have hc := RationalAcceptanceCoin.count_le bits input
  simp only [RationalAcceptanceCoin.draw,RationalAcceptanceCoin.counts,FiniteTicketSampler.drawBitTable,
    FiniteTicketSampler.drawFin,Fin.val_cast,List.ofFn_succ,List.ofFn_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rw [FiniteTicketSampler.bucket]
  split_ifs with hfirst
  · rfl
  · have hh : (FiniteTicketSampler.bitTicket bits word).val-RationalAcceptanceCoin.count bits input <
        2^bits-RationalAcceptanceCoin.count bits input := by omega
    simp only [FiniteTicketSampler.bucket,if_pos hh,Nat.add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem binaryAcceptance_value (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryAcceptance input bits word).value=(RationalAcceptanceCoin.draw bits input.decode word).val := by
  rw [rationalAcceptance_threshold]
  have hb := subtract_borrow (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits
  rw [readBitTape_value,RationalBits.dyadicFloor_value,RationalBits.clipUnit_value] at hb
  change (if (subtract false (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits).borrow
      then 0 else 1)=_
  simp only [RationalAcceptanceCoin.count]
  split_ifs with haccept hthreshold hthreshold
  · simp only [if_pos hthreshold]
  · exact False.elim (hthreshold (hb.mp haccept))
  · exact False.elim (haccept (hb.mpr hthreshold))
  · simp only [if_neg hthreshold]

end AFT.BinaryArithmetic

end P2MDyadicModule17

/- Helper module AFT.BinaryRationalLiterals. -/
section P2MDyadicModule18

namespace AFT.BinaryArithmetic

theorem bits_value (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec with
  | zero => simp [value]
  | bit b n ih =>
    by_cases hn : n=0
    · subst n
      cases b <;> simp [Nat.bit_val,value]
    · rw [Nat.bits_append_bit n b (fun hh => False.elim (hn hh))]
      simp only [value,ih,Nat.bit_val]
      omega

namespace RationalBits

/-- Existence of a finite literal encoding, used when constructing a fixed
program. The result is stored data, not an invocation of a real oracle. -/
theorem exists_code (q : ℚ) : ∃ code : RationalBits,code.decode=q := by
  let negative := decide (q.num < 0)
  have hsign : signedValue negative q.num.natAbs.bits=q.num := by
    simp only [signedValue,bits_value,negative]
    by_cases hn : q.num < 0
    · simp [hn,abs_of_neg hn]
    · simp [hn,abs_of_nonneg (by omega : 0 ≤ q.num)]
  let code : RationalBits :=
    ⟨negative,q.num.natAbs.bits,q.den.bits,
      by rw [bits_value,Nat.size_eq_bits_len],
      by rw [bits_value,Nat.size_eq_bits_len],
      by simpa only [bits_value] using q.den_pos,
      by simpa only [bits_value] using q.reduced⟩
  refine ⟨code,?_⟩
  rw [decode_fraction]
  change (signedValue negative q.num.natAbs.bits : ℚ)/(value q.den.bits : ℚ)=q
  rw [hsign,bits_value,Rat.num_div_den]

end RationalBits

end AFT.BinaryArithmetic

end P2MDyadicModule18

/- Helper module AFT.CenteredGaussianProgram. -/
section P2MDyadicModule19

namespace AFT.RationalNumerics

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem centeredGaussianSquaredWidth_pos (squaredWidth center : ℚ) (hw : 0<squaredWidth) :
    0<centeredGaussianSquaredWidth squaredWidth center := by
  unfold centeredGaussianSquaredWidth
  have hd : (0 : ℚ)<center.den := by exact_mod_cast center.den_pos
  positivity

theorem centeredGaussianRatio (squaredWidth center : ℚ) (point : ℤ) :
    (gaussianRatio (centeredGaussianSquaredWidth squaredWidth center)
      (centeredGaussianNumerator center point) : ℝ)=
      ((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
  have hd : (center.den : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt center.den_pos)
  have hc : (center : ℝ)=(center.num : ℝ)/(center.den : ℝ) := Rat.cast_def center
  unfold gaussianRatio centeredGaussianSquaredWidth centeredGaussianNumerator
  push_cast
  rw [hc]
  field_simp

/-- The error is uniform in the center and integer point. All guard
precision in the pi and exponential programs is computed rationally. -/
theorem centeredGaussianApprox_error (squaredWidth center : ℚ) (point : ℤ) (bits : ℕ)
    (hw : 0<squaredWidth) :
    |(centeredGaussianApprox squaredWidth center point bits : ℝ)-
      Real.exp (-Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ))|≤1/(2 : ℝ)^bits := by
  have hh := gaussianApprox_error (centeredGaussianSquaredWidth squaredWidth center)
    (centeredGaussianNumerator center point) bits (centeredGaussianSquaredWidth_pos squaredWidth center hw)
  have he : -Real.pi*(centeredGaussianNumerator center point : ℝ)^2 /
      (centeredGaussianSquaredWidth squaredWidth center : ℝ)=
      -Real.pi*((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ) := by
    have hr := centeredGaussianRatio squaredWidth center point
    simp only [gaussianRatio,Rat.cast_div,Rat.cast_pow,Rat.cast_intCast] at hr
    calc
      _ = -Real.pi*((centeredGaussianNumerator center point : ℝ)^2 /
          (centeredGaussianSquaredWidth squaredWidth center : ℝ)) := by ring
      _ = -Real.pi*(((point : ℝ)-(center : ℝ))^2/(squaredWidth : ℝ)) := congrArg (-Real.pi*·) hr
      _ = _ := by ring
  rw [he] at hh
  exact hh

theorem centeredGaussianAnchor_bounds (center : ℚ) :
    (centeredGaussianAnchor center : ℝ)≤(center : ℝ) ∧
      (center : ℝ)<(centeredGaussianAnchor center : ℝ)+1 := by
  constructor
  · exact_mod_cast (Int.floor_le center)
  · exact_mod_cast (Int.lt_floor_add_one center)

end

end AFT.RationalNumerics

end P2MDyadicModule19

/- Helper module AFT.CenteredGaussianSampling. -/
section P2MDyadicModule20

namespace AFT.RationalNumerics

open GaussianSource FiniteConvolutionProgram

open scoped BigOperators

noncomputable section

open scoped Classical

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

def centeredWindowMass (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : Window cutoff) : ℝ :=
  shiftedWeight width center (centeredGaussianAnchor center+point)

end

end AFT.RationalNumerics

end P2MDyadicModule20

/- Helper module AFT.CountableNormalizedTilt. -/
section P2MDyadicModule21

namespace AFT

open scoped BigOperators

/-- Normalizing a positive approximate density costs at most
`error / (1-error)` in total variation. Both masses are genuine normalized
countable laws; no unknown normalizer is treated as one. -/
theorem normalized_tilt_total_variation {State : Type*}
    (reference actual : State → ℝ)
    (href : ∀ state, 0 ≤ reference state)
    (hreference : Summable reference) (hactual : Summable actual)
    (href_one : ∑' state, reference state = 1)
    (hactual_one : ∑' state, actual state = 1)
    (scale error : ℝ) (herror : 0 ≤ error) (herror_one : error < 1)
    (hpoint : ∀ state, |actual state - scale * reference state| ≤
      error * scale * reference state) :
    (∑' state, |actual state-reference state|) / 2 ≤ error / (1-error) := by
  have hdiff := hactual.sub (hreference.mul_left scale)
  have hnorm : |1-scale| ≤ error*scale := by
    have ht := norm_tsum_le_tsum_norm hdiff.norm
    rw [hactual.tsum_sub (hreference.mul_left scale),tsum_mul_left,hactual_one,href_one,mul_one,Real.norm_eq_abs] at ht
    have hb := hdiff.norm.tsum_le_tsum (fun state => by
      simpa only [Real.norm_eq_abs] using hpoint state) (hreference.mul_left (error*scale))
    rw [tsum_mul_left,href_one,mul_one] at hb
    exact ht.trans hb
  have hs : scale ≤ 1/(1-error) := by
    apply (le_div_iff₀ (by linarith : 0<1-error)).mpr
    have hh' := (neg_le_abs (1-scale)).trans hnorm
    nlinarith
  have hbound (state : State) : |actual state-reference state| ≤
      (2*error*scale)*reference state := by
    calc
      _ = |(actual state-scale*reference state)+(scale-1)*reference state| := by congr 1; ring
      _ ≤ |actual state-scale*reference state|+|(scale-1)*reference state| := abs_add_le _ _
      _ ≤ error*scale*reference state+(error*scale)*reference state := by
        apply add_le_add (hpoint state)
        rw [abs_mul,abs_of_nonneg (href state),abs_sub_comm]
        exact mul_le_mul_of_nonneg_right hnorm (href state)
      _ = _ := by ring
  have hsum := (hactual.sub hreference).norm.tsum_le_tsum
    (fun state => by simpa only [Real.norm_eq_abs] using hbound state)
    (hreference.mul_left (2*error*scale))
  simp only [Real.norm_eq_abs,tsum_mul_left,href_one,mul_one] at hsum
  have hmul := mul_le_mul_of_nonneg_left hs herror
  rw [mul_one_div] at hmul
  linarith

end AFT

end P2MDyadicModule21

/- Helper module AFT.CountableConditioning. -/
section P2MDyadicModule22

namespace AFT

open scoped BigOperators

/-- Deleting any nonnegative part of a countable mass and renormalizing
changes its probability law by at most the deleted fraction. -/
theorem normalized_deleted_total_variation {State : Type*}
    (full retained : State → ℝ) (_hfull : ∀ state,0≤ full state)
    (hretained : ∀ state,0≤ retained state) (hle : ∀ state,retained state≤ full state)
    (hfull_sum : Summable full) (hretained_pos : 0<∑' state,retained state) :
    (∑' state,|retained state/(∑' x,retained x)-full state/(∑' x,full x)|)/2≤
      ((∑' state,full state)-(∑' state,retained state))/(∑' state,full state) := by
  let total := ∑' state,full state
  let kept := ∑' state,retained state
  have hs := Summable.of_nonneg_of_le hretained hle hfull_sum
  have htotal : kept≤ total := hs.tsum_le_tsum hle hfull_sum
  have hkpos : 0< kept := hretained_pos
  have htpos : 0< total := hretained_pos.trans_le htotal
  have hp (state : State) :
      |retained state/kept-full state/total|≤
        (full state-retained state)/total+retained state*((total-kept)/(total*kept)) := by
    have ha : retained state/kept-retained state/total≥0 :=
      sub_nonneg.mpr (div_le_div_of_nonneg_left (hretained state) hretained_pos htotal)
    have hb : (retained state-full state)/total≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hle state)) htpos.le
    calc
      _ = |(retained state/kept-retained state/total)+(retained state-full state)/total| := by congr 1; ring
      _ ≤ |retained state/kept-retained state/total|+|(retained state-full state)/total| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ha,abs_of_nonpos hb]; field_simp [htpos.ne',hkpos.ne']; ring
  have hnorm := ((hs.div_const kept).sub (hfull_sum.div_const total)).norm
  have hmajor := ((hfull_sum.sub hs).div_const total).add (hs.mul_right ((total-kept)/(total*kept)))
  have hsum := hnorm.tsum_le_tsum (fun state => by simpa only [Real.norm_eq_abs] using hp state) hmajor
  simp only [Real.norm_eq_abs] at hsum
  rw [Summable.tsum_add ((hfull_sum.sub hs).div_const total) (hs.mul_right _),tsum_div_const,
    hfull_sum.tsum_sub hs,tsum_mul_right] at hsum
  change (∑' state,|retained state/kept-full state/total|)≤
    (total-kept)/total+kept*((total-kept)/(total*kept)) at hsum
  have he : (total-kept)/total+kept*((total-kept)/(total*kept))=2*((total-kept)/total) := by
    field_simp [htpos.ne',hkpos.ne']; ring
  rw [he] at hsum
  change (∑' state,|retained state/kept-full state/total|)/2≤(total-kept)/total
  linarith

end AFT

end P2MDyadicModule22

/- Helper module AFT.CountableFiniteChannel. -/
section P2MDyadicModule23

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Source Output : Type*} [Fintype Output]

/-- Markov postprocessing never increases the full countable L1 distance. -/
theorem countableMix_l1_le (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → FiniteDist Output) :
    (∑ output,|(countableMix first hf hsf hfone channel).weight output-
      (countableMix second hg hsg hgone channel).weight output|) ≤ ∑' source,|first source-second source| := by
  have hd : Summable (fun source => |first source-second source|) := by
    simpa only [Real.norm_eq_abs] using (hsf.sub hsg).norm
  have hparts (output : Output) := countable_channel_summable (fun source => |first source-second source|) hd channel output
  have hbound (output : Output) :
      |(countableMix first hf hsf hfone channel).weight output-
        (countableMix second hg hsg hgone channel).weight output| ≤ 
      ∑' source,|first source-second source| *(channel source).weight output := by
    change |(∑' source,first source*(channel source).weight output)-
      (∑' source,second source*(channel source).weight output)| ≤ _
    rw [← (countable_channel_summable first hsf channel output).tsum_sub
      (countable_channel_summable second hsg channel output)]
    have hh := norm_tsum_le_tsum_norm (countable_channel_summable (fun source => first source-second source) (hsf.sub hsg) channel output).norm
    simp_rw [← sub_mul]
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (FiniteDist.nonneg _ _)] using hh
  apply (Finset.sum_le_sum fun output _ => hbound output).trans_eq
  rw [← tsum_fintype (L := .unconditional Output) (f := fun output : Output => ∑' source,|first source-second source| *(channel source).weight output)]
  have hs : Summable (fun point : Output × Source => |first point.2-second point.2| *(channel point.2).weight point.1) :=
    (summable_prod_of_nonneg (fun point => mul_nonneg (abs_nonneg _) ((channel point.2).nonneg point.1))).mpr
      ⟨hparts,(hasSum_fintype _).summable⟩
  rw [← Summable.tsum_comm hs]
  simp only [tsum_fintype,← Finset.mul_sum,FiniteDist.sum_one,mul_one]

/-- The bound applies uniformly to every public-input dependent physical
channel, without resampling or examining the protected source. -/
theorem countableMix_tvBound (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → FiniteDist Output) (error : ℝ)
    (herror : (∑' source,|first source-second source|)/2 ≤ error) :
    TVBound (countableMix first hf hsf hfone channel) (countableMix second hg hsg hgone channel) error := by
  apply (tvBound_iff_totalVariation_le _ _ _).mpr
  rw [totalVariation_eq_half_l1]
  exact (div_le_div_of_nonneg_right (countableMix_l1_le first second hf hg hsf hsg hfone hgone channel)
    (by norm_num)).trans herror

end

end AFT.FiniteDist

end P2MDyadicModule23

/- Helper module AFT.FiniteMassOn. -/
section P2MDyadicModule24

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Input Source Output : Type*} [Fintype Input] [Fintype Output]

def massOn (law : FiniteDist Input) (map : Input → Source) (source : Source) : ℝ :=
  ∑ point,if map point=source then law.weight point else 0

omit [Fintype Output] in
theorem massOn_nonneg (law : FiniteDist Input) (map : Input → Source) (source : Source) :
    0 ≤ massOn law map source := Finset.sum_nonneg fun point _ => by
      split_ifs
      · exact law.nonneg point
      · exact le_rfl

omit [Fintype Output] in
theorem massOn_hasSum (law : FiniteDist Input) (map : Input → Source) : HasSum (massOn law map) 1 := by
  have hh := hasSum_sum (s := (Finset.univ : Finset Input))
    (fun point _ => hasSum_ite_eq (map point) (law.weight point))
  change HasSum (fun source => ∑ point,if map point=source then law.weight point else 0) 1
  simpa only [eq_comm,FiniteDist.sum_one] using hh

omit [Fintype Output] in
theorem massOn_summable (law : FiniteDist Input) (map : Input → Source) : Summable (massOn law map) :=
  (massOn_hasSum law map).summable

omit [Fintype Output] in
theorem massOn_sum (law : FiniteDist Input) (map : Input → Source) : (∑' source,massOn law map source)=1 :=
  (massOn_hasSum law map).tsum_eq

/-- Averaging a channel against the finite pushforward equals averaging it
against the original finite law, on all output coordinates. -/
theorem countableMix_massOn (law : FiniteDist Input) (map : Input → Source)
    (channel : Source → FiniteDist Output) :
    countableMix (massOn law map) (massOn_nonneg law map) (massOn_summable law map)
      (massOn_sum law map) channel=law.mix (fun point => channel (map point)) := by
  apply FiniteDist.ext
  intro output
  change (∑' source,(∑ point,if map point=source then law.weight point else 0)*(channel source).weight output)=_
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  have hsum (point : Input) : Summable (fun source =>
      if map point=source then law.weight point*(channel source).weight output else 0) := by
    have hh := (hasSum_ite_eq (map point) (law.weight point*(channel (map point)).weight output)).summable
    apply hh.congr
    intro source
    by_cases he : source=map point <;> simp [he,eq_comm]
  rw [Summable.tsum_finsetSum (fun point (_ : point∈Finset.univ) => hsum point)]
  simp only [eq_comm,tsum_ite_eq]
  rfl

theorem countableMix_massOn_tvBound (mass : Source → ℝ)
    (hnonneg : ∀ source,0 ≤ mass source) (hsum : Summable mass) (hone : ∑' source,mass source=1)
    (law : FiniteDist Input) (map : Input → Source) (channel : Source → FiniteDist Output)
    (error : ℝ) (herror : (∑' source,|mass source-massOn law map source|)/2≤error) :
    TVBound (countableMix mass hnonneg hsum hone channel) (law.mix (fun point => channel (map point))) error := by
  have hh := countableMix_tvBound mass (massOn law map) hnonneg (massOn_nonneg law map)
    hsum (massOn_summable law map) hone (massOn_sum law map) channel error herror
  rw [countableMix_massOn] at hh
  exact hh

end

end AFT.FiniteDist

end P2MDyadicModule24

/- Helper module AFT.CenteredGaussianChannel. -/
section P2MDyadicModule25

namespace AFT.RationalNumerics

open GaussianSource

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

def centeredScalarMass (width : ℝ) (center : ℚ) (point : ℤ) : ℝ :=
  shiftedWeight width center point/theta width center

theorem centeredScalarMass_nonneg (width : ℝ) (center : ℚ) (hw : 0<width) (point : ℤ) :
    0 ≤ centeredScalarMass width center point := div_nonneg (Real.exp_pos _).le (theta_pos width center hw).le

theorem centeredScalarMass_summable (width : ℝ) (center : ℚ) (hw : 0<width) :
    Summable (centeredScalarMass width center) := (summable_shiftedWeight width center hw).div_const _

theorem centeredScalarMass_sum (width : ℝ) (center : ℚ) (hw : 0<width) :
    (∑' point,centeredScalarMass width center point)=1 := by
  simp only [centeredScalarMass,tsum_div_const]
  exact div_self (theta_pos width center hw).ne'

def centeredRetainedWeight (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) : ℝ :=
  if point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then shiftedWeight width center point else 0

theorem centeredRetainedWeight_nonneg (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) :
    0 ≤ centeredRetainedWeight width center cutoff point := by
  unfold centeredRetainedWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · rfl

theorem centeredRetainedWeight_le (width : ℝ) (center : ℚ) (cutoff : ℕ) (point : ℤ) :
    centeredRetainedWeight width center cutoff point ≤ shiftedWeight width center point := by
  unfold centeredRetainedWeight
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem centeredRetainedWeight_sum (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    (∑' point,centeredRetainedWeight width center cutoff point)=∑ offset,centeredWindowMass width center cutoff offset := by
  let embedding : Window cutoff → ℤ := fun offset => centeredGaussianAnchor center+offset
  have hi : Function.Injective embedding := by
    intro first second he
    apply Subtype.ext
    exact add_left_cancel he
  have hsupport : Function.support (centeredRetainedWeight width center cutoff)⊆Set.range embedding := by
    intro point hp
    have hh : point-centeredGaussianAnchor center∈Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) := by
      by_contra hn
      exact hp (if_neg hn)
    exact ⟨⟨point-centeredGaussianAnchor center,hh⟩,by dsimp only [embedding];omega⟩
  rw [←hi.tsum_eq hsupport,tsum_fintype]
  apply Finset.sum_congr rfl
  intro offset _
  simp only [centeredRetainedWeight,embedding,add_sub_cancel_left,if_pos offset.property]
  rfl

end

end AFT.RationalNumerics

end P2MDyadicModule25

/- Helper module AFT.TriangularGaussian. -/
section P2MDyadicModule26

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def GaussianChain.weight : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      shiftedWeight width (center (Fin.tail word)) (word 0) * tail.weight (Fin.tail word)

def GaussianChain.volume : {count : ℕ} → GaussianChain count → ℝ
  | 0,.nil => 1
  | _+1,.cons width _ tail => width*tail.volume

def GaussianChain.Wide (base : ℝ) : {count : ℕ} → GaussianChain count → Prop
  | 0,.nil => True
  | _+1,.cons width _ tail => base ≤ width ∧ tail.Wide base

theorem GaussianChain.weight_pos {count : ℕ} (chain : GaussianChain count) (word : Fin count → ℤ) :
    0<chain.weight word := by
  induction chain with
  | nil => exact zero_lt_one
  | cons width center tail ih => exact mul_pos (Real.exp_pos _) (ih _)

theorem GaussianChain.volume_pos {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) : 0<chain.volume := by
  induction chain with
  | nil => exact zero_lt_one
  | cons width center tail ih => exact mul_pos (hb.trans_le hw.1) (ih hw.2)

/-- Summability and normalization bounds are proved together on the actual
integer vector sum. All centers are allowed to depend on the remaining
coordinates; no multivariate Poisson theorem is assumed. -/
theorem GaussianChain.summable_and_bounds {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0 ≤ error) (he1 : error ≤ 1)
    (htheta : thetaError base ≤ error) (hw : chain.Wide base) :
    Summable chain.weight ∧
      chain.volume*(1-error)^count  ≤  ∑' word,chain.weight word ∧
      (∑' word,chain.weight word)  ≤  chain.volume*(1+error)^count := by
  induction chain with
  | nil =>
    simp only [GaussianChain.weight,GaussianChain.volume,pow_zero,mul_one]
    exact ⟨(hasSum_fintype _).summable,by simp,by simp⟩
  | @cons count width center tail ih =>
    obtain ⟨hts,htlo,hthi⟩ := ih hw.2
    have hwidth : 0<width := hb.trans_le hw.1
    have hlocal (rest : Fin count → ℤ) :
        width*(1-error) ≤ theta width (center rest) ∧
          theta width (center rest) ≤ width*(1+error) := by
      have h := (theta_relative_error_exp width (center rest) hwidth).trans
        ((thetaError_antitone base width hb hw.1).trans htheta)
      obtain ⟨hl,hu⟩ := abs_le.mp h
      constructor
      · have hh := (le_div_iff₀ hwidth).mp (show 1-error ≤ theta width (center rest)/width by linarith)
        nlinarith
      · have hh := (div_le_iff₀ hwidth).mp (show theta width (center rest)/width ≤ 1+error by linarith)
        nlinarith
    have hs (rest : Fin count → ℤ) :
        Summable (fun first : ℤ => shiftedWeight width (center rest) first * tail.weight rest) :=
      (summable_shiftedWeight width (center rest) hwidth).mul_right _
    have hp : Summable (fun rest : Fin count → ℤ => theta width (center rest)*tail.weight rest) :=
      Summable.of_nonneg_of_le
        (fun rest => mul_nonneg (theta_pos width (center rest) hwidth).le (tail.weight_pos rest).le)
        (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).2 (tail.weight_pos rest).le)
        (hts.mul_left (width*(1+error)))
    have hpair : Summable (fun point : (Fin count → ℤ) × ℤ =>
        shiftedWeight width (center point.1) point.2*tail.weight point.1) := by
      apply (summable_prod_of_nonneg (fun point =>
        mul_nonneg (Real.exp_pos _).le (tail.weight_pos _).le)).mpr
      constructor
      · exact hs
      · simpa only [tsum_mul_right, theta, shiftedWeight] using hp
    let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
    have heq (point : (Fin count → ℤ) × ℤ) :
        (GaussianChain.cons width center tail).weight (equiv point) =
          shiftedWeight width (center point.1) point.2*tail.weight point.1 := by
      simp [equiv,GaussianChain.weight,Fin.consEquiv]
    have hsall : Summable (GaussianChain.cons width center tail).weight := by
      apply equiv.summable_iff.mp
      simpa only [Function.comp_def, heq] using hpair
    have hsum : (∑' word,(GaussianChain.cons width center tail).weight word) =
        ∑' rest : Fin count → ℤ,theta width (center rest)*tail.weight rest := by
      rw [← equiv.tsum_eq]
      simp only [heq]
      rw [hpair.tsum_prod]
      apply tsum_congr
      intro rest
      change (∑' first : ℤ,shiftedWeight width (center rest) first*tail.weight rest)=_
      exact tsum_mul_right
    refine ⟨hsall,?_,?_⟩
    · rw [hsum]
      calc
        (GaussianChain.cons width center tail).volume*(1-error)^(count+1) =
            width*(1-error)*(tail.volume*(1-error)^count) := by
          simp only [GaussianChain.volume,pow_succ]; ring
        _  ≤  width*(1-error)*(∑' rest,tail.weight rest) :=
          mul_le_mul_of_nonneg_left htlo (mul_nonneg hwidth.le (by linarith))
        _ = ∑' rest,width*(1-error)*tail.weight rest := tsum_mul_left.symm
        _  ≤  _ := (hts.mul_left _).tsum_le_tsum
          (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).1 (tail.weight_pos rest).le) hp
    · rw [hsum]
      calc
        _  ≤  ∑' rest,width*(1+error)*tail.weight rest := hp.tsum_le_tsum
          (fun rest => mul_le_mul_of_nonneg_right (hlocal rest).2 (tail.weight_pos rest).le) (hts.mul_left _)
        _ = width*(1+error)*(∑' rest,tail.weight rest) := tsum_mul_left
        _  ≤  width*(1+error)*(tail.volume*(1+error)^count) :=
          mul_le_mul_of_nonneg_left hthi (by positivity)
        _ = _ := by simp only [GaussianChain.volume,pow_succ]; ring

end

end AFT.GaussianSource

end P2MDyadicModule26

/- Helper module AFT.TriangularGaussianSampler. -/
section P2MDyadicModule27

namespace AFT.GaussianSource

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Each step draws its integer coordinate from the normalized scalar
Gaussian whose center is determined by all later realized coordinates. -/
def GaussianChain.sequentialMass : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      shiftedWeight width (center (Fin.tail word)) (word 0) / theta width (center (Fin.tail word)) *
        tail.sequentialMass (Fin.tail word)

/-- The target is the genuinely normalized correlated integer Gaussian. -/
def GaussianChain.normalizedMass {count : ℕ} (chain : GaussianChain count) (word : Fin count → ℤ) : ℝ :=
  chain.weight word/(∑' vector,chain.weight vector)

theorem GaussianChain.sequentialMass_nonneg {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) (word : Fin count → ℤ) :
    0≤chain.sequentialMass word := by
  induction chain with
  | nil => exact zero_le_one
  | cons width center tail ih =>
    exact mul_nonneg (div_nonneg (Real.exp_pos _).le (theta_pos width _ (hb.trans_le hw.1)).le) (ih hw.2 _)

/-- This finite recursive sequence is a probability law before any
comparison with its elliptic Gaussian target. -/
theorem GaussianChain.sequentialMass_probability {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) :
    Summable chain.sequentialMass ∧ (∑' word,chain.sequentialMass word)=1 := by
  induction chain with
  | nil => exact ⟨(hasSum_fintype _).summable,by simp [sequentialMass]⟩
  | @cons count width center tail ih =>
    obtain ⟨hts,htone⟩ := ih hw.2
    have hwidth : 0<width := hb.trans_le hw.1
    have hlocal (rest : Fin count → ℤ) :
        Summable (fun first : ℤ => shiftedWeight width (center rest) first/theta width (center rest)) ∧
        (∑' first : ℤ,shiftedWeight width (center rest) first/theta width (center rest))=1 := by
      refine ⟨(summable_shiftedWeight width (center rest) hwidth).div_const _,?_⟩
      rw [tsum_div_const]
      exact div_self (theta_pos width (center rest) hwidth).ne'
    have hinner (rest : Fin count → ℤ) :
        (∑' first : ℤ, shiftedWeight width (center rest) first/theta width (center rest)*tail.sequentialMass rest)=tail.sequentialMass rest := by
      rw [tsum_mul_right,(hlocal rest).2,one_mul]
    have hpair : Summable (fun point : (Fin count → ℤ) × ℤ =>
        shiftedWeight width (center point.1) point.2/theta width (center point.1)*tail.sequentialMass point.1) := by
      apply (summable_prod_of_nonneg (fun point => mul_nonneg
        (div_nonneg (Real.exp_pos _).le (theta_pos width _ hwidth).le)
        (tail.sequentialMass_nonneg base hb hw.2 _))).mpr
      constructor
      · intro rest
        exact (hlocal rest).1.mul_right (tail.sequentialMass rest)
      · change Summable (fun rest : Fin count → ℤ => ∑' first : ℤ,
          shiftedWeight width (center rest) first/theta width (center rest)*tail.sequentialMass rest)
        simpa only [hinner] using hts
    let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
      (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
    have heq (point : (Fin count → ℤ) × ℤ) :
        (GaussianChain.cons width center tail).sequentialMass (equiv point)=
          shiftedWeight width (center point.1) point.2/theta width (center point.1)*tail.sequentialMass point.1 := by
      simp [equiv,sequentialMass,Fin.consEquiv]
    constructor
    · apply equiv.summable_iff.mp
      simpa only [Function.comp_def, heq] using hpair
    · rw [← equiv.tsum_eq]
      simp only [heq]
      rw [hpair.tsum_prod]
      simpa only [hinner] using htone

/-- The sampler's actual normalizing factors along one realized vector. -/
def GaussianChain.localNormalizer : {count : ℕ} → GaussianChain count → (Fin count → ℤ) → ℝ
  | 0,.nil,_ => 1
  | _+1,.cons width center tail,word =>
      theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word)

theorem GaussianChain.weight_eq_sequential {count : ℕ} (chain : GaussianChain count)
    (base : ℝ) (hb : 0<base) (hw : chain.Wide base) (word : Fin count → ℤ) :
    chain.weight word=chain.localNormalizer word*chain.sequentialMass word := by
  induction chain with
  | nil => simp [weight,localNormalizer,sequentialMass]
  | cons width center tail ih =>
    change shiftedWeight width (center (Fin.tail word)) (word 0)*tail.weight (Fin.tail word)=
      (theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word))*
        (shiftedWeight width (center (Fin.tail word)) (word 0)/theta width (center (Fin.tail word))*tail.sequentialMass (Fin.tail word))
    rw [ih hw.2]
    have ht := (theta_pos width (center (Fin.tail word)) (hb.trans_le hw.1)).ne'
    field_simp

theorem GaussianChain.localNormalizer_bounds {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) (word : Fin count → ℤ) :
    chain.volume*(1-error)^count≤chain.localNormalizer word ∧
      chain.localNormalizer word≤chain.volume*(1+error)^count := by
  induction chain with
  | nil => simp [volume,localNormalizer]
  | @cons count width center tail ih =>
    have hwidth : 0<width := hb.trans_le hw.1
    have h := (theta_relative_error_exp width (center (Fin.tail word)) hwidth).trans
      ((thetaError_antitone base width hb hw.1).trans htheta)
    obtain ⟨hl,hu⟩ := abs_le.mp h
    have hlo : width*(1-error)≤theta width (center (Fin.tail word)) := by
      have hh := (le_div_iff₀ hwidth).mp (show 1-error≤theta width (center (Fin.tail word))/width by linarith)
      nlinarith
    have hhi : theta width (center (Fin.tail word))≤width*(1+error) := by
      have hh := (div_le_iff₀ hwidth).mp (show theta width (center (Fin.tail word))/width≤1+error by linarith)
      nlinarith
    obtain ⟨htlo,hthi⟩ := ih hw.2 (Fin.tail word)
    have hv := (tail.volume_pos base hb hw.2).le
    constructor
    · calc
        (GaussianChain.cons width center tail).volume*(1-error)^(count+1)=
            (width*(1-error))*(tail.volume*(1-error)^count) := by simp only [volume,pow_succ]; ring
        _ ≤ theta width (center (Fin.tail word))*tail.localNormalizer (Fin.tail word) :=
          mul_le_mul hlo htlo (mul_nonneg hv (pow_nonneg (by linarith) _)) (theta_pos width _ hwidth).le
        _ = _ := rfl
    · calc
        (GaussianChain.cons width center tail).localNormalizer word≤
            (width*(1+error))*(tail.volume*(1+error)^count) := by
          exact mul_le_mul hhi hthi
            ((mul_nonneg hv (pow_nonneg (by linarith) _)).trans htlo)
            (by positivity)
        _ = _ := by simp only [volume,pow_succ]; ring

/-- The error uses all dimensions, with the same multiplicative theta
factor as the frozen V7 sequential-sampling argument. -/
theorem GaussianChain.weight_sequential_error {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base) (word : Fin count → ℤ) :
    |chain.weight word-chain.volume*chain.sequentialMass word|≤
      ((1+error)^count-1)*chain.volume*chain.sequentialMass word := by
  obtain ⟨hlo,hhi⟩ := chain.localNormalizer_bounds base error hb he he1 htheta hw word
  have hv := chain.volume_pos base hb hw
  have hp := one_add_mul_le_pow (show (-2 : ℝ)≤error by linarith) count
  have hn := one_add_mul_le_pow (show (-2 : ℝ)≤ -error by linarith) count
  simp only [mul_neg,← sub_eq_add_neg] at hn
  have hs : |chain.localNormalizer word-chain.volume|≤((1+error)^count-1)*chain.volume := by
    apply abs_le.mpr
    constructor
    · have hh := mul_le_mul_of_nonneg_left (show 2-(1+error)^count≤(1-error)^count by linarith) hv.le
      nlinarith
    · nlinarith
  rw [chain.weight_eq_sequential base hb hw word,← sub_mul,abs_mul,
    abs_of_nonneg (chain.sequentialMass_nonneg base hb hw word)]
  exact mul_le_mul_of_nonneg_right hs (chain.sequentialMass_nonneg base hb hw word)

/-- Total variation between the true sequential normalized scalar draws
and the true normalized correlated target. Neither normalizer is omitted. -/
theorem GaussianChain.sequential_total_variation {count : ℕ} (chain : GaussianChain count)
    (base error : ℝ) (hb : 0<base) (he : 0≤error) (he1 : error≤1)
    (htheta : thetaError base≤error) (hw : chain.Wide base)
    (hsmall : (1+error)^count-1<1) :
    (∑' word,|chain.normalizedMass word-chain.sequentialMass word|)/2≤
      ((1+error)^count-1)/(1-((1+error)^count-1)) := by
  obtain ⟨hweight,_,_⟩ := chain.summable_and_bounds base error hb he he1 htheta hw
  obtain ⟨hseq,hseqone⟩ := chain.sequentialMass_probability base hb hw
  have hz : 0<∑' word,chain.weight word := by
    exact (chain.weight_pos (fun _ => 0)).trans_le (hweight.le_tsum (fun _ => 0) (fun word _ => (chain.weight_pos word).le))
  have hactual : Summable chain.normalizedMass := hweight.div_const _
  have hactualone : (∑' word,chain.normalizedMass word)=1 := by
    unfold normalizedMass
    rw [tsum_div_const,div_self hz.ne']
  have herr : 0≤(1+error)^count-1 := by
    have hh : 1≤(1+error)^count := one_le_pow₀ (by linarith)
    linarith
  apply normalized_tilt_total_variation chain.sequentialMass chain.normalizedMass
    (chain.sequentialMass_nonneg base hb hw) hseq hactual hseqone hactualone
    (chain.volume/(∑' word,chain.weight word)) _ herr hsmall
  intro word
  have hp := div_le_div_of_nonneg_right (chain.weight_sequential_error base error hb he he1 htheta hw word) hz.le
  change |chain.weight word / (∑' vector, chain.weight vector) -
    (chain.volume / (∑' vector, chain.weight vector)) * chain.sequentialMass word| ≤ _
  rw [div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos hz]
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hp

end

end AFT.GaussianSource

end P2MDyadicModule27

/- Helper module AFT.GaussianMatrixChain. -/
section P2MDyadicModule28

namespace AFT.GaussianSource

open Matrix

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

def upperGaussianChain : (count : ℕ) → (Fin count → ℝ) → (Fin count → ℝ) →
    Matrix (Fin count) (Fin count) ℝ → GaussianChain count
  | 0,_,_,_ => .nil
  | count+1,width,center,upper => .cons (width 0)
      (fun tail => center 0-∑ j,upper 0 j.succ*((tail j : ℝ)-center j.succ))
      (upperGaussianChain count (fun j => width j.succ) (fun j => center j.succ)
        (fun i j => upper i.succ j.succ))

theorem upperGaussianChain_wide (count : ℕ) (width center : Fin count → ℝ)
    (upper : Matrix (Fin count) (Fin count) ℝ) (base : ℝ) (hwidth : ∀ i,base≤width i) :
    (upperGaussianChain count width center upper).Wide base := by
  induction count with
  | zero => trivial
  | succ count ih => exact ⟨hwidth 0,ih _ _ _ (fun i => hwidth i.succ)⟩

theorem upperGaussianChain_weight (count : ℕ) (width center : Fin count → ℝ)
    (upper : Matrix (Fin count) (Fin count) ℝ)
    (htriangular : ∀ i j,j < i → upper i j=0) (hdiagonal : ∀ i,upper i i=1)
    (word : Fin count → ℤ) :
    (upperGaussianChain count width center upper).weight word=
      Real.exp (-Real.pi*∑ i,(upper.mulVec (fun j => (word j : ℝ)-center j) i)^2/(width i)^2) := by
  induction count with
  | zero => simp [upperGaussianChain,GaussianChain.weight]
  | succ count ih =>
    have hhead : upper.mulVec (fun j => (word j : ℝ)-center j) 0=
        (word 0 : ℝ)-center 0+∑ j : Fin count,upper 0 j.succ*((word j.succ : ℝ)-center j.succ) := by
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hdiagonal 0,one_mul]
    have htail (i : Fin count) : upper.mulVec (fun j => (word j : ℝ)-center j) i.succ=
        Matrix.mulVec (fun i j : Fin count => upper i.succ j.succ)
          (fun j => (Fin.tail word j : ℝ)-center j.succ) i := by
      simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,htriangular i.succ 0 (Fin.succ_pos _),
        zero_mul,zero_add,Fin.tail_def]
    simp only [upperGaussianChain,GaussianChain.weight]
    rw [ih _ _ _ (fun i j hj => htriangular i.succ j.succ (Fin.succ_lt_succ_iff.mpr hj))
      (fun i => hdiagonal i.succ),shiftedWeight,← Real.exp_add,Fin.sum_univ_succ,hhead]
    simp only [htail,Fin.tail_def]
    congr 1
    ring

end

end AFT.GaussianSource

end P2MDyadicModule28

/- Helper module AFT.FiniteChannelIdentities. -/
section P2MDyadicModule29

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

variable {Source Inner Output : Type*} [Fintype Source] [Fintype Inner] [Fintype Output]

theorem mix_comm (first : FiniteDist Source) (second : FiniteDist Inner)
    (channel : Source → Inner → FiniteDist Output) :
    first.mix (fun source => second.mix (channel source))=
      second.mix (fun inner => first.mix (fun source => channel source inner)) := by
  apply FiniteDist.ext
  intro output
  simp only [mix_weight,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inner _
  apply Finset.sum_congr rfl
  intro source _
  ring

omit [Fintype Inner] in
theorem TVBound.mix_right (law : FiniteDist Source) {first second : Source → FiniteDist Output}
    {error : ℝ} (hbound : ∀ source,TVBound (first source) (second source) error) :
    TVBound (law.mix first) (law.mix second) error := by
  intro event
  simp only [event_mix,← Finset.sum_sub_distrib,← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (law.nonneg _)]
  calc
    _ ≤ ∑ source,law.weight source*error :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hbound source event) (law.nonneg source)
    _ = error := by rw [← Finset.sum_mul,law.sum_one,one_mul]

end

end AFT.FiniteDist

end P2MDyadicModule29

/- Helper module AFT.RationalGaussianChain. -/
section P2MDyadicModule30

namespace AFT.RationalNumerics

open GaussianSource Matrix

open scoped BigOperators

/-- The actual rational triangular conditional centers. -/
def upperRationalGaussianChain : (count : ℕ) → (Fin count → ℚ) → (Fin count → ℚ) →
    Matrix (Fin count) (Fin count) ℚ → RationalGaussianChain count
  | 0,_,_,_ => .nil
  | count+1,squaredWidth,center,upper => .cons (squaredWidth 0)
      (fun tail => center 0-∑ j,upper 0 j.succ*((tail j : ℚ)-center j.succ))
      (upperRationalGaussianChain count (fun j => squaredWidth j.succ) (fun j => center j.succ)
        (fun i j => upper i.succ j.succ))

noncomputable section

open scoped Classical

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 300000

def RationalGaussianChain.realChain : {count : ℕ} → RationalGaussianChain count → GaussianChain count
  | 0,.nil => .nil
  | _+1,.cons squaredWidth center tail => .cons (Real.sqrt (squaredWidth : ℝ))
      (fun word => (center word : ℝ)) tail.realChain

theorem upperRationalGaussianChain_real (count : ℕ) (squaredWidth center : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) :
    (upperRationalGaussianChain count squaredWidth center upper).realChain=
      upperGaussianChain count (fun i => Real.sqrt (squaredWidth i : ℝ))
        (fun i => (center i : ℝ)) (fun i j => (upper i j : ℝ)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [upperRationalGaussianChain,RationalGaussianChain.realChain,upperGaussianChain,ih]
    congr 1
    funext word
    simp only [Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]

end

end AFT.RationalNumerics

end P2MDyadicModule30

/- Helper module AFT.CountableChannelComposition. -/
section P2MDyadicModule31

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {First Second Output : Type*} [Fintype Output]

theorem countableChannel_summable (mass : First → ℝ) (hs : Summable mass)
    (channel : First → FiniteDist Output) (output : Output) :
    Summable (fun point => mass point*(channel point).weight output) := by
  apply Summable.of_norm_bounded hs.norm
  intro point
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((channel point).nonneg output)]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [← (channel point).sum_one]
  exact Finset.single_le_sum (fun value _ => (channel point).nonneg value) (Finset.mem_univ output)

end

end AFT.FiniteDist

end P2MDyadicModule31

/- Helper module AFT.RationalGaussianChainAccuracy. -/
section P2MDyadicModule32

namespace AFT.RationalNumerics

open GaussianSource

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

variable {Output : Type*} [Fintype Output]

def RationalGaussianChain.exactChannel {count : ℕ} (chain : RationalGaussianChain count)
    (hw : chain.realChain.Wide 1) (channel : (Fin count → ℤ) → FiniteDist Output) : FiniteDist Output :=
  FiniteDist.countableMix chain.realChain.sequentialMass
    (chain.realChain.sequentialMass_nonneg 1 zero_lt_one hw)
    (chain.realChain.sequentialMass_probability 1 zero_lt_one hw).1
    (chain.realChain.sequentialMass_probability 1 zero_lt_one hw).2 channel

/-- Exact countable Fubini for the conditional scalar draws; the random
center depends on the entire realized tail throughout this identity. -/
theorem RationalGaussianChain.exactChannel_cons {count : ℕ} (squaredWidth : ℚ)
    (center : (Fin count → ℤ) → ℚ) (tail : RationalGaussianChain count)
    (hw : (RationalGaussianChain.cons squaredWidth center tail).realChain.Wide 1)
    (channel : (Fin (count+1) → ℤ) → FiniteDist Output) :
    (RationalGaussianChain.cons squaredWidth center tail).exactChannel hw channel=
      tail.exactChannel hw.2 (fun word => FiniteDist.countableMix
        (centeredScalarMass (Real.sqrt (squaredWidth : ℝ)) (center word))
        (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hw.1))
        (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hw.1))
        (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hw.1))
        (fun first => channel (Fin.cons first word))) := by
  let equiv : (Fin count → ℤ) × ℤ ≃ (Fin (count+1) → ℤ) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ => ℤ))
  have he (point : (Fin count → ℤ) × ℤ) : equiv point=Fin.cons point.2 point.1 := by cases point;rfl
  ext output
  change (∑' word,(RationalGaussianChain.cons squaredWidth center tail).realChain.sequentialMass word*
    (channel word).weight output)=_
  rw [←equiv.tsum_eq]
  have hs := FiniteDist.countableChannel_summable _
    ((RationalGaussianChain.cons squaredWidth center tail).realChain.sequentialMass_probability 1 zero_lt_one hw).1
    channel output
  have hp := equiv.summable_iff.mpr hs
  simp only [Function.comp_def,he,RationalGaussianChain.realChain,GaussianChain.sequentialMass,Fin.tail_cons,Fin.cons_zero] at hp ⊢
  rw [hp.tsum_prod]
  change _=∑' word,tail.realChain.sequentialMass word*
    (∑' first,centeredScalarMass (Real.sqrt (squaredWidth : ℝ)) (center word) first*
      (channel (Fin.cons first word)).weight output)
  apply tsum_congr
  intro word
  rw [←tsum_mul_left]
  apply tsum_congr
  intro first
  unfold centeredScalarMass
  ring

end

end AFT.RationalNumerics

end P2MDyadicModule32

/- Helper module AFT.CenteredGaussianResources. -/
section P2MDyadicModule33

namespace AFT.RationalNumerics

open GaussianSource FiniteConvolutionProgram

open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

set_option maxRecDepth 2048

theorem centeredGaussianRatio_rat (squaredWidth center : ℚ) (point : ℤ) :
    gaussianRatio (centeredGaussianSquaredWidth squaredWidth center) (centeredGaussianNumerator center point)=
      ((point : ℚ)-center)^2/squaredWidth := by
  exact_mod_cast centeredGaussianRatio squaredWidth center point

end

end AFT.RationalNumerics

end P2MDyadicModule33

/- Helper module AFT.FiniteConditionalSampling. -/
section P2MDyadicModule34

namespace AFT.FiniteDist

open scoped BigOperators Classical

noncomputable section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 400000

theorem map_prod_functions {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1,g pair.2))=(first.map f).prod (second.map g) := by
  ext point
  rcases point with ⟨left,right⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,Prod.mk.injEq,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : f a=left <;> by_cases hb : g b=right <;> simp [ha,hb]

end

end AFT.FiniteDist

end P2MDyadicModule34

/- Helper module Solutions.RegevBridgeGaussianRandomizedRounding. -/
section P2MDyadicModule35

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource

open scoped BigOperators Classical ENNReal

noncomputable section

def roundingNormalizer (width center : ℝ) : ℝ≥0∞ :=
  ∑' value : ℤ,ENNReal.ofReal (shiftedWeight width center value)

theorem roundingNormalizer_ne_zero (width center : ℝ) : roundingNormalizer width center≠0 := by
  intro hz
  have hv := ENNReal.tsum_eq_zero.mp hz (0 : ℤ)
  exact (not_le_of_gt (show 0<shiftedWeight width center 0 from Real.exp_pos _)) (ENNReal.ofReal_eq_zero.mp hv)

theorem roundingNormalizer_ne_top (width center : ℝ) (hwidth : 0<width) :
    roundingNormalizer width center≠⊤ :=
  (summable_shiftedWeight width center hwidth).tsum_ofReal_ne_top

/-- The kernel uses the existing shifted theta normalizer exactly. -/
theorem roundingNormalizer_toReal (width center : ℝ) :
    (roundingNormalizer width center).toReal=theta width center := by
  unfold roundingNormalizer theta
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro value
  exact ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- The displayed error is genuinely below one for widths at least one. -/
theorem roundingError_lt_one (width : ℝ) (hwidth : 1≤width) : thetaError width<1 := by
  have hs : 1≤width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he : 4<Real.exp (Real.pi*width^2) :=
    (by linarith : (4 : ℝ)<Real.pi*width^2+1).trans_le (Real.add_one_le_exp _)
  have hn : Real.exp (-Real.pi*width^2)<1/4 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/4)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

/-- The actual conditional PMF D_(Z-center),width shifted back to Z. -/
def roundingPMF (width : ℝ) (hwidth : 0<width) (center : ℝ) : PMF ℤ :=
  PMF.normalize (fun value => ENNReal.ofReal (shiftedWeight width center value))
    (roundingNormalizer_ne_zero width center) (roundingNormalizer_ne_top width center hwidth)

/-- Exact real conditional density of the normalized rounding PMF. -/
theorem roundingPMF_toReal (width : ℝ) (hwidth : 0<width) (center : ℝ) (value : ℤ) :
    (roundingPMF width hwidth center value).toReal=shiftedWeight width center value/theta width center := by
  change (ENNReal.ofReal (shiftedWeight width center value)*(roundingNormalizer width center)⁻¹).toReal=_
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,roundingNormalizer_toReal,
    ENNReal.toReal_ofReal (show 0 ≤ shiftedWeight width center value from Real.exp_nonneg _)]
  rfl

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule35

/- Helper module Solutions.RegevBridgeGaussianRoundingFiniteBits. -/
section P2MDyadicModule36

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

theorem windowMass_pos (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    0<∑ index : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff index) := by
  have hz : 0< shiftedWeight width center (windowPoint center cutoff 0) := Real.exp_pos _
  exact hz.trans_le (Finset.single_le_sum
    (f := fun index : Fin (2*cutoff+1) => shiftedWeight width center (windowPoint center cutoff index))
    (fun index _ => (show 0 ≤ shiftedWeight width center (windowPoint center cutoff index) from Real.exp_nonneg _))
    (Finset.mem_univ 0))

/-- The exact truncated law, using the same true Gaussian weights as the
infinite randomized-rounding PMF. -/
def windowLaw (width : ℝ) (center : ℚ) (cutoff : ℕ) : FiniteDist (Fin (2*cutoff+1)) :=
  FiniteDist.normalize (fun index => shiftedWeight width center (windowPoint center cutoff index))
    (fun _ => Real.exp_nonneg _) (windowMass_pos width center cutoff)

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule36

/- Helper module Solutions.RegevBridgeGaussianRoundingTail. -/
section P2MDyadicModule37

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

def tailEnvelope (width radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width)*
    Real.exp (-Real.pi*radius^2/(2*width^2))

theorem summable_roundingMass (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    Summable (fun value : ℤ => (roundingPMF width hwidth center value).toReal) := by
  simp_rw [roundingPMF_toReal]
  exact (summable_shiftedWeight width center hwidth).div_const _

private theorem theta_ratio_bound (width : ℝ) (hwidth : 1≤width) (center : ℝ) :
    theta (Real.sqrt 2*width) center/theta width center ≤
      Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  have hs := roundingError_lt_one width hwidth
  have hl := (abs_le.mp (theta_relative_error_exp width center hw)).1
  have hu := (abs_le.mp (theta_relative_error_exp (Real.sqrt 2*width) center hb)).2
  have hlow : width*(1-thetaError width)≤theta width center := by
    rw [mul_comm]
    exact (le_div_iff₀ hw).mp (by linarith)
  have hupp : theta (Real.sqrt 2*width) center≤
      (Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have hn : theta (Real.sqrt 2*width) center/(Real.sqrt 2*width)≤1+thetaError (Real.sqrt 2*width) := by linarith
    exact ((div_le_iff₀ hb).mp hn).trans_eq (mul_comm _ _)
  have hpos : 0<width*(1-thetaError width) := mul_pos hw (by linarith)
  have ha : 0≤(Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)) := by
    have he := thetaError_nonneg (Real.sqrt 2*width) hb
    positivity
  calc
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/theta width center :=
      div_le_div_of_nonneg_right hupp (theta_pos width center hw).le
    _ ≤ ((Real.sqrt 2*width)*(1+thetaError (Real.sqrt 2*width)))/(width*(1-thetaError width)) :=
      div_le_div_of_nonneg_left ha hpos hlow
    _ = _ := by field_simp [hw.ne']

/-- Pointwise tail domination uses the actual shifted Gaussian at both
widths, so it is uniform over all real centers. -/
theorem shiftedWeight_tail_le (width center radius : ℝ) (hwidth : 0<width) (hradius : 0≤radius)
    (value : ℤ) (hfar : radius≤|(value : ℝ)-center|) :
    shiftedWeight width center value≤
      Real.exp (-Real.pi*radius^2/(2*width^2))*shiftedWeight (Real.sqrt 2*width) center value := by
  have hroot : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsq : radius^2≤((value : ℝ)-center)^2 := by
    have h := (sq_le_sq₀ hradius (abs_nonneg ((value : ℝ)-center))).2 hfar
    simpa only [sq_abs] using h
  let a := Real.pi/(2*width^2)
  have ha : 0≤a := by dsimp [a];positivity
  have hh := mul_le_mul_of_nonneg_left hsq ha
  unfold shiftedWeight
  rw [←Real.exp_add,mul_pow,hroot]
  apply Real.exp_le_exp.mpr
  have he0 : -(Real.pi/width^2)*((value : ℝ)-center)^2=-2*a*((value : ℝ)-center)^2 := by dsimp [a];ring
  have he1 : -Real.pi*radius^2/(2*width^2)=-a*radius^2 := by dsimp [a];ring
  rw [he0,he1]
  change -2*a*((value : ℝ)-center)^2≤-a*radius^2+(-a)*((value : ℝ)-center)^2
  nlinarith

def roundingTail (width : ℝ) (hwidth : 0<width) (center radius : ℝ) : ℝ :=
  ∑' value : ℤ,if radius≤|(value : ℝ)-center| then (roundingPMF width hwidth center value).toReal else 0

/-- Full countable tail probability of the true normalized rounding PMF. -/
theorem roundingTail_le (width : ℝ) (hwidth : 1≤width) (center radius : ℝ) (hradius : 0≤radius) :
    roundingTail width (zero_lt_one.trans_le hwidth) center radius≤tailEnvelope width radius := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hb : 0<Real.sqrt 2*width := by positivity
  let factor := Real.exp (-Real.pi*radius^2/(2*width^2))/theta width center
  have hf : 0≤factor := div_nonneg (Real.exp_nonneg _) (theta_pos width center hw).le
  have hsum := (summable_shiftedWeight (Real.sqrt 2*width) center hb).mul_left factor
  have hp (value : ℤ) :
      (if radius≤|(value : ℝ)-center| then (roundingPMF width hw center value).toReal else 0)≤
        factor*shiftedWeight (Real.sqrt 2*width) center value := by
    split_ifs with hfar
    · rw [roundingPMF_toReal]
      have h := div_le_div_of_nonneg_right (shiftedWeight_tail_le width center radius hw hradius value hfar)
        (theta_pos width center hw).le
      exact h.trans_eq (by dsimp [factor];ring)
    · exact mul_nonneg hf (Real.exp_nonneg _)
  have hs : Summable (fun value : ℤ => if radius≤|(value : ℝ)-center| then
      (roundingPMF width hw center value).toReal else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hp hsum
  have ht := hs.tsum_le_tsum hp hsum
  rw [tsum_mul_left] at ht
  change roundingTail width hw center radius≤factor*theta (Real.sqrt 2*width) center at ht
  apply ht.trans
  unfold tailEnvelope factor
  have hr := mul_le_mul_of_nonneg_right (theta_ratio_bound width hwidth center)
    (Real.exp_nonneg (-Real.pi*radius^2/(2*width^2)))
  convert hr using 1
  ring

/-- Omitted points from the floor-centered palette are genuinely far from
the original rational center, using integer discreteness on both sides. -/
theorem outsideWindow_far (center : ℚ) (cutoff : ℕ) (value : ℤ)
    (hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) :
    (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| := by
  have hs := centeredGaussianAnchor_bounds center
  have ho : value≤centeredGaussianAnchor center-(cutoff : ℤ)-1 ∨
      centeredGaussianAnchor center+(cutoff : ℤ)+1≤value := by
    simp only [Finset.mem_Icc,not_and_or] at hout
    omega
  rcases ho with hl|hr
  · have hlR : (value : ℝ)≤(centeredGaussianAnchor center : ℝ)-(cutoff : ℝ)-1 := by exact_mod_cast hl
    apply le_trans _ (neg_le_abs ((value : ℝ)-(center : ℝ)))
    linarith [hs.1]
  · have hrR : (centeredGaussianAnchor center : ℝ)+(cutoff : ℝ)+1≤(value : ℝ) := by exact_mod_cast hr
    apply le_trans _ (le_abs_self ((value : ℝ)-(center : ℝ)))
    linarith [hs.2]

def outsideWindowMass (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) : ℝ :=
  ∑' value : ℤ,if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hwidth center value).toReal else 0

/-- A uniform analytic bound on the entire omitted probability of the same
infinite kernel approximated by the executed finite-bit sampler. -/
theorem outsideWindowMass_le (width : ℝ) (hwidth : 1≤width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width (zero_lt_one.trans_le hwidth) center cutoff≤tailEnvelope width cutoff := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hmass := summable_roundingMass width hw center
  have hs : Summable (fun value : ℤ => if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have ht : Summable (fun value : ℤ => if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then
      (roundingPMF width hw center value).toReal else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hmass
    intro value
    by_cases h : (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)|
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have hp (value : ℤ) :
      (if value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)) then (roundingPMF width hw center value).toReal else 0)≤
      (if (cutoff : ℝ)≤|(value : ℝ)-(center : ℝ)| then (roundingPMF width hw center value).toReal else 0) := by
    by_cases hout : value∉Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))
    · have hfar := outsideWindow_far center cutoff value hout
      rw [if_pos hout,if_pos hfar]
    · rw [if_neg hout]
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl
  exact (hs.tsum_le_tsum hp ht).trans (roundingTail_le width hwidth center cutoff (Nat.cast_nonneg _))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule37

/- Helper module Solutions.RegevBridgeGaussianRoundingTruncation. -/
section P2MDyadicModule38

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource AFT.RationalNumerics

open scoped BigOperators Classical

noncomputable section

/-- Exact indexing of the actual integer window around the computed floor. -/
def windowPointEquiv (center : ℚ) (cutoff : ℕ) : Fin (2*cutoff+1) ≃
    ↥(Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
      (centeredGaussianAnchor center+(cutoff : ℤ))) where
  toFun index := ⟨windowPoint center cutoff index,by
    have hi := index.isLt
    simp only [Finset.mem_Icc,windowPoint]
    constructor <;> omega⟩
  invFun point := ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,by
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    omega⟩
  left_inv index := by
    apply Fin.ext
    change ((windowPoint center cutoff index)-centeredGaussianAnchor center+(cutoff : ℤ)).toNat=index.val
    simp only [windowPoint]
    have hi := index.isLt
    omega
  right_inv point := by
    apply Subtype.ext
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp point.property
    change windowPoint center cutoff ⟨(point.val-centeredGaussianAnchor center+(cutoff : ℤ)).toNat,_⟩=point.val
    simp only [windowPoint]
    omega

theorem windowPoint_sum (center : ℚ) (cutoff : ℕ) (test : ℤ → ℝ) :
    (∑ index : Fin (2*cutoff+1),test (windowPoint center cutoff index))=
      ∑ value ∈ Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
        (centeredGaussianAnchor center+(cutoff : ℤ)),test value := by
  have h := (windowPointEquiv center cutoff).sum_comp (fun point => test point.val)
  rw [Finset.sum_coe_sort] at h
  exact h

/-- Real masses of the genuine countable rounding kernel sum to one. -/
theorem roundingMass_sum (width : ℝ) (hwidth : 0<width) (center : ℝ) :
    (∑' value : ℤ,(roundingPMF width hwidth center value).toReal)=1 := by
  simp_rw [roundingPMF_toReal]
  rw [tsum_div_const]
  exact div_self (theta_pos width center hwidth).ne'

def retainedResidue (q : ℕ) (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) (output : ZMod q) : ℝ :=
  ∑ index : Fin (2*cutoff+1),@ite ℝ ((windowPoint center cutoff index : ZMod q)=output)
    (Classical.propDecidable _) (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal 0

theorem retainedResidue_sum (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    (∑ output : ZMod q,retainedResidue q width hwidth center cutoff output)=
      ∑ index : Fin (2*cutoff+1),(roundingPMF width hwidth center (windowPoint center cutoff index)).toReal := by
  unfold retainedResidue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  exact @Fintype.sum_ite_eq (ZMod q) ℝ _ _
    (fun first second => Classical.propDecidable (first=second))
      (windowPoint center cutoff index : ZMod q)
      (fun _ => (roundingPMF width hwidth center (windowPoint center cutoff index)).toReal)

/-- The discarded countable mass is exactly one minus the retained finite
mass. This identity retains the true kernel normalization throughout. -/
theorem outsideWindowMass_eq (q : ℕ) [NeZero q] (width : ℝ) (hwidth : 0<width) (center : ℚ) (cutoff : ℕ) :
    outsideWindowMass width hwidth center cutoff=
      1-∑ output : ZMod q,retainedResidue q width hwidth center cutoff output := by
  rw [retainedResidue_sum,windowPoint_sum center cutoff
    (fun value : ℤ => (roundingPMF width hwidth center value).toReal)]
  let window := Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ))
    (centeredGaussianAnchor center+(cutoff : ℤ))
  let mass := fun value : ℤ => (roundingPMF width hwidth center value).toReal
  have hs := summable_roundingMass width hwidth center
  have hinside : Summable (fun value : ℤ => if value∈window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    split_ifs
    · exact le_rfl
    · exact ENNReal.toReal_nonneg
  have houtside : Summable (fun value : ℤ => if value∉window then mass value else 0) := by
    apply Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) _ hs
    intro value
    by_cases h : value∉window
    · rw [if_pos h]
    · rw [if_neg h]
      exact ENNReal.toReal_nonneg
  have he : (∑' value : ℤ,if value∈window then mass value else 0)+
      (∑' value : ℤ,if value∉window then mass value else 0)=1 := by
    rw [←hinside.tsum_add houtside]
    calc
      _ = ∑' value : ℤ,mass value := by
        apply tsum_congr
        intro value
        by_cases h : value∈window <;> simp [h]
      _ = _ := roundingMass_sum width hwidth center
  have hi : (∑' value : ℤ,if value∈window then mass value else 0)=∑ value∈window,mass value := by
    rw [tsum_eq_sum (s := window) (fun value hv => if_neg hv)]
    apply Finset.sum_congr rfl
    intro value hv
    rw [if_pos hv]
  rw [hi] at he
  change (∑' value : ℤ,if value∉window then mass value else 0)=1-∑ value∈window,mass value
  linarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule38

/- Helper module Solutions.RegevBridgeGaussianRoundingContinuous. -/
section P2MDyadicModule39

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency true

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource MeasureTheory

open scoped BigOperators Classical

noncomputable section

theorem roundingError_lt_half (width : ℝ) (hwidth : 1 ≤ width) : thetaError width<1/2 := by
  have hs : 1 ≤ width^2 := one_le_pow₀ hwidth
  have hp : 3<Real.pi*width^2 := by nlinarith [Real.pi_gt_three]
  have he3 : (8 : ℝ)<Real.exp 3 := by
    have h := Real.exp_one_gt_two
    have he : Real.exp 3=(Real.exp 1)^3 := by rw [←Real.exp_nat_mul];norm_num
    rw [he]
    have he2 : 4<(Real.exp 1)^2 := by nlinarith
    nlinarith [mul_pos (by linarith : 0<Real.exp 1-2) (by linarith : 0<(Real.exp 1)^2-4)]
  have he := he3.trans (Real.exp_lt_exp.mpr hp)
  have hn : Real.exp (-Real.pi*width^2)<1/8 := by
    rw [show -Real.pi*width^2=-(Real.pi*width^2) by ring,Real.exp_neg]
    apply (inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/8)).2
    simpa using he
  exact (thetaError_le_four_exp width hwidth).trans_lt (by linarith)

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule39

/- Helper module Integration9_9.TM2NativeFiniteDraw. -/
section P2MDyadicModule40

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.TM2NativeFiniteDraw

open AFT AFT.RationalNumerics AFT.BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open TM2NativeFiniteSeries TM2NativeRootGroupProfiles

open scoped BigOperators

theorem clipped_eq (q : ℚ) : clipped q=RationalAcceptanceCoin.clipped q := by
  unfold clipped RationalAcceptanceCoin.clipped
  split_ifs with h0 h1
  · rw [max_eq_right h0.le,min_eq_right (by norm_num)]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_right h1.le]
  · rw [max_eq_left (le_of_not_gt h0),min_eq_left (le_of_not_gt h1)]

theorem tape_ofFn (bits : ℕ) (word : Fin bits → Fin 2) :
    List.ofFn (fun i => digitBoolean (word i))=(readBitTape bits word).digits := by
  induction bits with
  | zero => rfl
  | succ bits ih =>
    simp only [List.ofFn_succ,readBitTape,ih]
    rfl

theorem acceptance_native (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) :
    acceptance (input.decode,List.ofFn (fun i => digitBoolean (word i)))=(binaryAcceptance input bits word).value := by
  have hb := subtract_borrow (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits
  simp only [RationalBits.dyadicFloor_value,RationalBits.clipUnit_value] at hb
  simp only [acceptance,tapeValue,dyadicFloor,ticks,List.length_map,clipped_eq,tape_ofFn,
    readBitTape_length,binaryAcceptance,hb]

end Integration9_9.TM2NativeFiniteDraw

end P2MDyadicModule40

/- Helper module Solutions.RegevBridgeGaussianRoundingNative. -/
section P2MDyadicModule41

set_option autoImplicit false

set_option maxHeartbeats 1000000

set_option maxRecDepth 10000

set_option synthInstance.maxSize 1024

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

theorem anchor_eq (center : ℚ) : anchor center=(centeredGaussianAnchor center : ℚ) := by
  unfold anchor
  split <;> rename_i hc
  · have hn := Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hc.le)
    rw [←Int.cast_natCast,hn,Int.ceil_neg,Int.cast_neg,neg_neg]
    rfl
  · rw [←Int.cast_natCast,Int.natCast_floor_eq_floor (le_of_not_gt hc)]
    rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

end P2MDyadicModule41

/- Helper module Solutions.RegevBridgeGaussianProjectionProbability. -/
section P2MDyadicModule42

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open AFT GaussianSource RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ProbabilitySpace := EuclideanSpace ℝ (Fin dimension)

/-- The genuine discrete Gaussian masses on the actual lattice coset. -/
def cosetMass (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) : ℝ :=
  discreteGaussian lattice shift width ((value : ProbabilitySpace (dimension:=dimension))+shift)

theorem cosetMass_formula (lattice : Submodule ℤ (ProbabilitySpace (dimension:=dimension)))
    (shift : ProbabilitySpace (dimension:=dimension)) (width : ℝ) (value : lattice) :
    cosetMass lattice shift width value=
      rho width ((value : ProbabilitySpace (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  unfold cosetMass discreteGaussian
  rw [Set.indicator_of_mem]
  simpa only [Set.mem_ofPred_eq,add_sub_cancel_right] using value.property

end

end InfoLossLAR.WorstCase.GaussianProjection

end P2MDyadicModule42

/- Helper module Solutions.RegevBridgeGaussianGridProjection. -/
section P2MDyadicModule43

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- Uniform truncation error profile over the publicly enumerated width
interval. The upper width controls the Gaussian tail; the lower width
controls both theta normalizers. -/
def intervalTail (lower upper radius : ℝ) : ℝ :=
  Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower)*Real.exp (-Real.pi*radius^2/(2*upper^2))

theorem tailEnvelope_interval {lower width upper : ℝ} (radius : ℝ)
    (hlower : 1 ≤ lower) (hlowerWidth : lower ≤ width) (hwidthUpper : width ≤ upper) :
    tailEnvelope width radius ≤ intervalTail lower upper radius := by
  have hlo : 0<lower := zero_lt_one.trans_le hlower
  have hw : 0<width := hlo.trans_le hlowerWidth
  have hu : 0<upper := hw.trans_le hwidthUpper
  have hwOne : 1 ≤ width := hlower.trans hlowerWidth
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by apply Real.le_sqrt_of_sq_le;norm_num
  have ht := thetaError_antitone lower width hlo hlowerWidth
  have htb := thetaError_antitone lower (Real.sqrt 2*width) hlo
    (hlowerWidth.trans (le_mul_of_one_le_left hw.le hroot))
  have hdlo : 0<1-thetaError lower := sub_pos.mpr (roundingError_lt_one lower hlower)
  have hdw : 0<1-thetaError width := sub_pos.mpr (roundingError_lt_one width hwOne)
  have hnum : 0 ≤ Real.sqrt 2*(1+thetaError lower) := by
    have he := thetaError_nonneg lower hlo
    positivity
  have hfactor : Real.sqrt 2*(1+thetaError (Real.sqrt 2*width))/(1-thetaError width) ≤
      Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) := by
    apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl htb) (Real.sqrt_nonneg 2)) hdw.le).trans
    exact div_le_div_of_nonneg_left hnum hdlo (by linarith)
  have hn : 0 ≤ Real.pi*radius^2 := mul_nonneg Real.pi_pos.le (sq_nonneg radius)
  have hsq : 2*width^2 ≤ 2*upper^2 := by nlinarith [(sq_le_sq₀ hw.le hu.le).mpr hwidthUpper]
  have hfrac := div_le_div_of_nonneg_left hn (mul_pos (by norm_num : (0 : ℝ)<2) (sq_pos_of_pos hw)) hsq
  have hexp : Real.exp (-Real.pi*radius^2/(2*width^2)) ≤ Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
    apply Real.exp_le_exp.mpr
    calc
      _ = -(Real.pi*radius^2/(2*width^2)) := by ring
      _ ≤ -(Real.pi*radius^2/(2*upper^2)) := neg_le_neg hfrac
      _ = _ := by ring
  unfold tailEnvelope intervalTail
  exact (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hexp (div_nonneg hnum hdlo.le))

end

end InfoLossLAR.WorstCase.GaussianProjection.VarianceGrid

end P2MDyadicModule43

/- Helper module Solutions.RegevBridgeGaussianRoundingTable. -/
section P2MDyadicModule44

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1000000

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding

open AFT GaussianSource

open scoped BigOperators Classical

noncomputable section

/-- Fresh independent tapes mapped coordinatewise give the literal
product of the individual output laws. -/
theorem independent_map_coordinatewise {Index Input Output : Type*}
    [Fintype Index] [Fintype Input] [Fintype Output] [DecidableEq Index]
    (law : Index → FiniteDist Input) (compute : Index → Input → Output) :
    (FiniteDist.independent law).map (fun input index => compute index (input index))=
      FiniteDist.independent (fun index => (law index).map (compute index)) := by
  ext output
  simp only [FiniteDist.map_weight,FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro input _
  by_cases h : ∀ index,compute index (input index)=output index
  · have he : (fun index => compute index (input index))=output := funext h
    simp only [he,ite_true]
    apply Finset.prod_congr rfl
    intro index _
    rw [if_pos (h index)]
  · have he : (fun index => compute index (input index))≠output := fun hh => h (congrFun hh)
    rw [if_neg he]
    obtain ⟨index,hindex⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg hindex)

end

namespace Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

end Native

end InfoLossLAR.WorstCase.GaussianRandomizedRounding

end P2MDyadicModule44

/- Helper module Solutions.RegevBridgeIntegerBasis. -/
section P2MDyadicModule45

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

/-- The coefficient vector sent to the native program represents exactly
its target-defined lattice point `latVec basis value`. -/
theorem coefficient_point (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) :
    ((integerBasis basis hdet).equivFun.symm value : Space (dimension:=dimension))=latVec basis value := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum,Submodule.coe_smul,integerBasis_apply]
  ext row
  simp only [WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,latVec,Matrix.mulVec,dotProduct,
    Int.cast_sum,Int.cast_mul,zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  exact mul_comm _ _

end

end InfoLossLAR.WorstCase.IntegerBasis

end P2MDyadicModule45

/- Helper module Solutions.RegevBridgeIntegerBasisNative. -/
section P2MDyadicModule46

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis.Native

open AFT GaussianSource GaussianProjection GaussianRandomizedRounding BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

private theorem zip_ofFn {α β : Type*} {count : ℕ} (left : Fin count → α) (right : Fin count → β) :
    (List.ofFn left).zip (List.ofFn right)=List.ofFn (fun index => (left index,right index)) := by
  apply List.ext_getElem
  · simp
  · intros;simp

theorem dot_ofFn {count : ℕ} (left : Fin count → ℚ) (right : Fin count → ℤ) :
    dot (List.ofFn left,List.ofFn right)=∑ index,left index*(right index : ℚ) := by
  simp only [dot,zip_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]

end InfoLossLAR.WorstCase.IntegerBasis.Native

end P2MDyadicModule46

/- Helper module Solutions.RegevBridgeGaussianNumericalBudget. -/
section P2MDyadicModule47

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding RegevLWE.GaussConv

open scoped BigOperators

noncomputable section

/-- The complete shifted-normalizer prefactor is uniformly bounded in
the actual wide-kernel regime, including its dependence on both widths. -/
theorem intervalTail_le_six {lower upper radius : ℝ} (hlower : 1 ≤ lower) :
    VarianceGrid.intervalTail lower upper radius ≤ 6*Real.exp (-Real.pi*radius^2/(2*upper^2)) := by
  have ht := roundingError_lt_half lower hlower
  have htzero := thetaError_nonneg lower (zero_lt_one.trans_le hlower)
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := by apply Real.sqrt_le_iff.mpr;norm_num
  have hden : 0<1-thetaError lower := by linarith
  have hnum : Real.sqrt 2*(1+thetaError lower) ≤ 3 := by nlinarith
  have hfactor : Real.sqrt 2*(1+thetaError lower)/(1-thetaError lower) ≤ 6 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)

/-- Elementary explicit exponential bound, before taking any asymptotic
limit. It also discharges the theta smallness premise at every sigma≥2. -/
theorem sigma_gaussian_exp_le (sigma : ℕ) (hsigma : 2 ≤ sigma) :
    Real.exp (-Real.pi*(sigma : ℝ)^2/2) ≤ 1/(2 : ℝ)^(2*sigma) := by
  have hs : (2 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  have hp : (0 : ℝ)<sigma := by linarith
  have hquad : 2*(sigma : ℝ) ≤ Real.pi*(sigma : ℝ)^2/2 := by
    nlinarith [Real.pi_gt_three,sq_nonneg ((sigma : ℝ)-2)]
  have he : (2 : ℝ)^(2*sigma) ≤ Real.exp ((2*sigma : ℕ) : ℝ) := by
    have heq : Real.exp ((2*sigma : ℕ) : ℝ)=(Real.exp 1)^(2*sigma) := by
      rw [←Real.exp_nat_mul]
      simp only [mul_one]
    rw [heq]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le _
  calc
    _ ≤ Real.exp (-((2*sigma : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = 1/Real.exp ((2*sigma : ℕ) : ℝ) := by rw [Real.exp_neg,one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) he

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

end P2MDyadicModule47

/- Helper module Solutions.AdvantageBridgeBoundedUniform. -/
section P2MDyadicModule48

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

namespace InfoLossLAR.WorstCase

open AFT

open scoped BigOperators Classical

private theorem boundedFinDraw_some_iff (count : ℕ) (tape : Fin (Nat.size count) → Bool)
    (index : Fin count) :
    boundedFinDraw count tape=some index ↔
      boundedBoolTicket (Nat.size count) tape=Fin.castLE (Nat.lt_size_self count).le index := by
  unfold boundedFinDraw
  dsimp only
  split_ifs with h
  · simp only [Option.some.injEq,Fin.ext_iff,Fin.val_mk,Fin.coe_castLE]
  · constructor
    · intro heq
      cases heq
    · intro heq
      have hv := congrArg Fin.val heq
      exact (h (by simpa only [Fin.coe_castLE] using hv.symm ▸ index.isLt)).elim

/-- Every successful index has exactly one bit ticket. -/
theorem boundedFinLaw_some (count : ℕ) (index : Fin count) :
    (boundedFinLaw count).weight (some index)=((2 : ℝ)^Nat.size count)⁻¹ := by
  simp only [boundedFinLaw,FiniteDist.map_weight,FiniteDist.uniform_weight]
  simp_rw [boundedFinDraw_some_iff,←(boundedBoolTicket (Nat.size count)).eq_symm_apply]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]

/-- A single joint rejection attempt succeeds with probability at least one half. -/
theorem boundedFinSuccess_half (count : ℕ) (hcount : 0<count) :
    (1/2 : ℝ) ≤ boundedFinSuccess count := by
  have hs : 0<Nat.size count := Nat.size_pos.mpr hcount
  have hm : Nat.size count-1<Nat.size count := by omega
  have hpow : 2^(Nat.size count-1) ≤ count := Nat.lt_size.mp hm
  have hsucc : Nat.size count-1+1=Nat.size count := by omega
  have hcap : 2^Nat.size count ≤ 2*count := by
    calc
      _ = 2^(Nat.size count-1)*2 := by
        simpa only [Nat.succ_eq_add_one,hsucc] using Nat.pow_succ 2 (Nat.size count-1)
      _ ≤ count*2 := Nat.mul_le_mul_right 2 hpow
      _ = _ := Nat.mul_comm _ _
  have hcap' : (2 : ℝ)^Nat.size count ≤ 2*(count : ℝ) := by exact_mod_cast hcap
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(2 : ℝ)^Nat.size count)).mpr
  nlinarith

end InfoLossLAR.WorstCase

end P2MDyadicModule48

/- Helper module Solutions.AdvantageBridgeCoinMachine. -/
section P2MDyadicModule49

set_option autoImplicit false

set_option maxHeartbeats 2000000

set_option maxRecDepth 10000

set_option backward.isDefEq.respectTransparency false

namespace Integration9_9.LARCoinMachine

open InfoLossLAR.WorstCase QAlgorithms.Complexity

open OAI.MetricKMedian.Binary

open OAI.MetricKMedian.Binary.Automatic

open OAI.MetricKMedian.Binary.Automatic.Poly

open QMCNumericRuntime

open LARPlatformEncoding Polynomial

open scoped BigOperators

private theorem word_value_ofFn (count : ℕ) (tape : Fin count → Bool) :
    Word.value (List.ofFn tape)=∑ index,(tape index).toNat*2^index.val := by
  induction count with
  | zero => simp
  | succ count ih =>
    simp only [List.ofFn_succ,Word.value_cons,Fin.sum_univ_succ,Fin.val_zero,pow_zero,
      mul_one,Fin.val_succ]
    rw [ih]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [pow_succ]
    ring

/-- The actual binary-value machine reads precisely the fair-bit ticket
used by the proved rejection-sampling law. -/
theorem bitValue_boundedBoolTicket (count : ℕ) (tape : Fin count → Bool) :
    bitValue (List.ofFn tape)=(boundedBoolTicket count tape).val := by
  rw [bitValue_eq_word,word_value_ofFn]
  change (∑ index,(tape index).toNat*2^index.val)=
    ∑ index,((finTwoEquiv.symm (tape index)).val)*2^index.val
  apply Finset.sum_congr rfl
  intro index _
  cases tape index <;> rfl

end Integration9_9.LARCoinMachine

end P2MDyadicModule49

/- Helper module Solutions.RegevBridgeWideGaussianScale. -/
section P2MDyadicModule50

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteDraw

open scoped BigOperators

/-- A binary power-of-two width envelope is derived from numerator and
denominator bit lengths, without evaluating an irrational square root. -/
def scaleEnvelope (numerator denominator : ℕ) : ℕ :=
  2^((Nat.size numerator-Nat.size denominator+2)/2)

theorem binary_size_bounds (value : ℕ) (hvalue : 0<value) :
    2^(Nat.size value-1) ≤ value ∧ value<2^Nat.size value := by
  have hs : 0<Nat.size value := Nat.size_pos.mpr hvalue
  exact ⟨Nat.lt_size.mp (by omega),Nat.lt_size_self value⟩

/-- The envelope is within a fixed factor in squared width, even when
the width itself is exponentially large in the input bit length. -/
theorem scaleEnvelope_bounds (numerator denominator : ℕ) (hdenominator : 0<denominator)
    (hratio : denominator ≤ numerator) :
    numerator ≤ (scaleEnvelope numerator denominator)^2*denominator ∧
      (scaleEnvelope numerator denominator)^2*denominator ≤ 8*numerator := by
  have hnum : 0<numerator := hdenominator.trans_le hratio
  have hsize := Nat.size_le_size hratio
  have hnsize : 0<Nat.size numerator := Nat.size_pos.mpr hnum
  have hdsize : 0<Nat.size denominator := Nat.size_pos.mpr hdenominator
  obtain ⟨hnlower,hnupper⟩ := binary_size_bounds numerator hnum
  obtain ⟨hdlower,hdupper⟩ := binary_size_bounds denominator hdenominator
  let gap := Nat.size numerator-Nat.size denominator
  have hsum : Nat.size numerator=gap+Nat.size denominator := (Nat.sub_add_cancel hsize).symm
  have hsquare : (scaleEnvelope numerator denominator)^2=2^(2*((gap+2)/2)) := by
    unfold scaleEnvelope
    rw [←pow_mul]
    congr 1
    change ((gap+2)/2)*2=2*((gap+2)/2)
    omega
  have hlowExponent : gap+1 ≤ 2*((gap+2)/2) := by omega
  have huppExponent : 2*((gap+2)/2) ≤ gap+2 := by omega
  have hlowPow : 2^(gap+1) ≤ (scaleEnvelope numerator denominator)^2 := by
    rw [hsquare]
    exact Nat.pow_le_pow_right (by norm_num) hlowExponent
  have huppPow : (scaleEnvelope numerator denominator)^2 ≤ 2^(gap+2) := by
    rw [hsquare]
    exact Nat.pow_le_pow_right (by norm_num) huppExponent
  constructor
  · calc
      numerator ≤ 2^Nat.size numerator := hnupper.le
      _ = 2^(gap+1)*2^(Nat.size denominator-1) := by
        rw [←pow_add]
        congr 1
        omega
      _ ≤ 2^(gap+1)*denominator := Nat.mul_le_mul_left _ hdlower
      _ ≤ _ := Nat.mul_le_mul_right _ hlowPow
  · calc
      _ ≤ 2^(gap+2)*2^Nat.size denominator := Nat.mul_le_mul huppPow hdupper.le
      _ = 8*2^(Nat.size numerator-1) := by
        rw [←pow_add,show (8 : ℕ)=2^3 by norm_num,←pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.mul_le_mul_left _ hnlower

@[fun_prop] theorem naturalBits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩

@[fun_prop] theorem signedAbsolute_poly : Poly Int.natAbs := ⟨PolyProgram.intAbs⟩

@[fun_prop] theorem dropTicks_poly : Poly (fun input : List Unit × ℕ => input.1.drop input.2) :=
  ⟨PolyProgram.listDrop Automatic.enc ()⟩

def numeratorTicks (squaredWidth : ℚ) : List Unit := (Nat.bits squaredWidth.num.natAbs).map (fun _ => ())

@[fun_prop] theorem numeratorTicks_poly : Poly numeratorTicks := by unfold numeratorTicks;fun_prop

def rawScaleTicks (squaredWidth : ℚ) : List Unit :=
  (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)++[(),()]

@[fun_prop] theorem rawScaleTicks_poly : Poly rawScaleTicks := by
  have hd : Poly (fun squaredWidth : ℚ => (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)) :=
    Poly.comp (f:=fun input : List Unit × ℕ => input.1.drop input.2)
      (g:=fun squaredWidth : ℚ => (numeratorTicks squaredWidth,Nat.size squaredWidth.den)) dropTicks_poly (by fun_prop)
  unfold rawScaleTicks
  exact Poly.comp (f:=fun ticks : List Unit => ticks++[(),()])
    (g:=fun squaredWidth : ℚ => (numeratorTicks squaredWidth).drop (Nat.size squaredWidth.den)) (by fun_prop) hd

@[fun_prop] theorem takeTicks_poly : Poly (fun input : List Unit × ℕ => input.1.take input.2) :=
  ⟨PolyProgram.listTake Automatic.enc ()⟩

def scaleTicks (squaredWidth : ℚ) : List Unit :=
  (rawScaleTicks squaredWidth).take ((rawScaleTicks squaredWidth).length/2)

@[fun_prop] theorem scaleTicks_poly : Poly scaleTicks := by
  unfold scaleTicks
  exact Poly.comp (f:=fun input : List Unit × ℕ => input.1.take input.2)
    (g:=fun squaredWidth : ℚ => (rawScaleTicks squaredWidth,(rawScaleTicks squaredWidth).length/2))
    takeTicks_poly (by fun_prop)

def scale (squaredWidth : ℚ) : ℕ := dyadicPower (scaleTicks squaredWidth)

@[fun_prop] theorem scale_poly : Poly scale := by unfold scale;fun_prop

theorem scale_eq (squaredWidth : ℚ) : scale squaredWidth=scaleEnvelope squaredWidth.num.natAbs squaredWidth.den := by
  simp only [scale,dyadicPower,scaleTicks,rawScaleTicks,numeratorTicks,List.length_take,List.length_append,List.length_drop,
    List.length_map,List.length_cons,List.length_nil,Nat.size_eq_bits_len]
  rw [Nat.min_eq_left (Nat.div_le_self _ _)]
  rfl

/-- The real sampler receives the rational variance. Its native scale is
proved to sandwich that exact variance without an irrational-width input. -/
theorem scale_variance_bounds (squaredWidth : ℚ) (hwidth : 1 ≤ squaredWidth) :
    squaredWidth ≤ (scale squaredWidth : ℚ)^2 ∧
      (scale squaredWidth : ℚ)^2 ≤ 8*squaredWidth := by
  have hpositive : 0<squaredWidth := zero_lt_one.trans_le hwidth
  have hnpositive : 0<squaredWidth.num := Rat.num_pos.mpr hpositive
  have hncast : (squaredWidth.num.natAbs : ℚ)=(squaredWidth.num : ℚ) := by
    have he : (squaredWidth.num.natAbs : ℤ)=squaredWidth.num := by
      rw [Int.natCast_natAbs,abs_of_pos hnpositive]
    simpa only [Int.cast_natCast] using congrArg (fun value : ℤ => (value : ℚ)) he
  have hd : (0 : ℚ)<squaredWidth.den := by exact_mod_cast squaredWidth.pos
  have heq : squaredWidth=(squaredWidth.num.natAbs : ℚ)/(squaredWidth.den : ℚ) := by
    rw [hncast,Rat.num_div_den]
  have hratio : squaredWidth.den ≤ squaredWidth.num.natAbs := by
    have h := (le_div_iff₀ hd).mp (heq ▸ hwidth)
    simp only [one_mul] at h
    exact_mod_cast h
  have hbounds := scaleEnvelope_bounds squaredWidth.num.natAbs squaredWidth.den squaredWidth.pos hratio
  rw [←scale_eq squaredWidth] at hbounds
  constructor
  · conv_lhs => rw [heq]
    apply (div_le_iff₀ hd).mpr
    exact_mod_cast hbounds.1
  · conv_rhs => rw [heq,←mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    exact_mod_cast hbounds.2

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule50

/- Helper module Solutions.RegevBridgeWideGaussianProposal. -/
section P2MDyadicModule51

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 QMCNumericRuntime LARPlatformEncoding

open scoped BigOperators

/-- A literal native bounded interval proposal. The count is binary; the
machine reads only its bit length and never materializes the interval. -/
def intervalProposal (input : ℕ × List Bool) : Bool × ℕ :=
  let ticket := bitValue (input.2.take (Nat.size input.1))
  (decide (ticket < input.1),ticket)

@[fun_prop] theorem intervalProposal_poly : Poly intervalProposal := by
  have ht : Poly (fun input : ℕ × List Bool => bitValue (input.2.take (Nat.size input.1))) :=
    Poly.comp QMCNumericRuntime.bitValue_poly (Poly.comp QMCNumericRuntime.parser_take_poly
      (Poly.pair (by fun_prop) (Poly.comp LARCoinMachine.naturalSize_poly (by fun_prop))))
  unfold intervalProposal
  exact Poly.pair (Poly.nat_lt_comp ht (by fun_prop)) ht

/-- The observed finite type includes explicit rejection. -/
def decodeProposal (count : ℕ) (output : Bool × ℕ) : Option (Fin count) :=
  if h : output.1=true ∧ output.2 < count then some ⟨output.2,h.2⟩ else none

/-- Every valid finite coin tape has exactly the established bounded
uniform ticket semantics, including its failure event. -/
theorem intervalProposal_exact (count : ℕ) (tape : Fin (Nat.size count) → Bool) :
    decodeProposal count (intervalProposal (count,List.ofFn tape))=boundedFinDraw count tape := by
  have htake : (List.ofFn tape).take (Nat.size count)=List.ofFn tape := List.take_of_length_le (by simp)
  simp only [intervalProposal,htake,LARCoinMachine.bitValue_boundedBoolTicket,decodeProposal,boundedFinDraw]
  split_ifs <;> simp_all

/-- The actual native proposal law under fresh fair bits. -/
noncomputable def intervalProposalLaw (count : ℕ) : FiniteDist (Option (Fin count)) :=
  (FiniteDist.uniform (Fin (Nat.size count) → Bool)).map (fun tape => decodeProposal count (intervalProposal (count,List.ofFn tape)))

theorem intervalProposalLaw_eq (count : ℕ) : intervalProposalLaw count=boundedFinLaw count := by
  unfold intervalProposalLaw boundedFinLaw
  apply congrArg (FiniteDist.uniform (Fin (Nat.size count) → Bool)).map
  funext tape
  exact intervalProposal_exact count tape

theorem intervalProposalLaw_some (count : ℕ) (index : Fin count) :
    (intervalProposalLaw count).weight (some index)=((2 : ℝ)^Nat.size count)⁻¹ := by
  rw [intervalProposalLaw_eq,boundedFinLaw_some]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule51

/- Helper module Solutions.RegevBridgeWideGaussianPoint. -/
section P2MDyadicModule52

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeGaussian

open scoped BigOperators

abbrev PointRequest := (ℚ × ℚ) × (List Unit × List Unit)

def variance (input : PointRequest) : ℚ := if 1 ≤ input.1.1 then input.1.1 else 1

@[fun_prop] theorem variance_poly : Poly variance := by unfold variance;fun_prop

def radius (input : PointRequest) : ℕ := input.2.1.length*scale (variance input)

@[fun_prop] theorem radius_poly : Poly radius := by unfold radius;fun_prop

def intervalCount (input : PointRequest) : ℕ := 2*radius input+1

@[fun_prop] theorem intervalCount_poly : Poly intervalCount := by unfold intervalCount;fun_prop

def anchorInteger (center : ℚ) : ℤ := (GaussianRandomizedRounding.Native.anchor center).num

@[fun_prop] theorem anchorInteger_poly : Poly anchorInteger := by unfold anchorInteger;fun_prop

theorem anchorInteger_eq (center : ℚ) : anchorInteger center=⌊center⌋ := by
  simp only [anchorInteger,GaussianRandomizedRounding.Native.anchor_eq,centeredGaussianAnchor,Rat.num_intCast]

/-- One random binary interval ticket becomes its translated integer point. -/
def point (input : PointRequest × ℕ) : ℤ := anchorInteger input.1.1.2+(input.2 : ℤ)-(radius input.1 : ℤ)

@[fun_prop] theorem point_poly : Poly point := by unfold point;fun_prop

def pointRatio (input : PointRequest × ℕ) : ℚ := ((point input : ℚ)-input.1.1.2)^2/variance input.1

@[fun_prop] theorem pointRatio_poly : Poly pointRatio := by
  have h : Poly (fun input : PointRequest × ℕ => (((point input : ℚ)-input.1.1.2)*((point input : ℚ)-input.1.1.2))/variance input.1) := by fun_prop
  unfold pointRatio
  simpa only [pow_two] using h

/-- The exponent loop guard is polynomial in the unary radius multiplier,
and independent of the numerical magnitude of the binary Gaussian width. -/
def pointGuardTicks (input : PointRequest) : List Unit :=
  ((input.2.1++[()]).flatMap (fun _ => input.2.1++[()])).flatMap (fun _ => List.replicate 8 ())

@[fun_prop] theorem pointGuardTicks_poly : Poly pointGuardTicks := by unfold pointGuardTicks;fun_prop

theorem pointGuardTicks_length (input : PointRequest) : (pointGuardTicks input).length=8*(input.2.1.length+1)^2 := by
  simp only [pointGuardTicks,List.length_flatMap,List.length_append,List.length_singleton,List.map_const',List.sum_replicate,List.length_replicate]
  ring

def pointValue (input : PointRequest × ℕ) : ℚ :=
  gaussianCapped ((pointRatio input,input.1.2.2),pointGuardTicks input.1)

noncomputable def pointProgram : PolyProgram Automatic.enc Ratio.encode pointValue := by
  let prepare : PolyProgram Automatic.enc TM2NativeGaussian.requestCode
      (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) :=
    (show Poly (fun input : PointRequest × ℕ => ((pointRatio input,input.1.2.2),pointGuardTicks input.1)) by fun_prop).program
  exact prepare.comp gaussianProgram

@[fun_prop] theorem pointValue_poly : Poly pointValue := ⟨pointProgram⟩

/-- The actual fresh-bit acceptance coin is evaluated directly after the
single native Gaussian score, with no stored weight table. -/
def pointCoin (input : (PointRequest × ℕ) × List Bool) : ℕ :=
  TM2NativeFiniteDraw.acceptance (pointValue input.1,input.2)

@[fun_prop] theorem pointCoin_poly : Poly pointCoin := by unfold pointCoin;fun_prop

noncomputable section

theorem variance_ge_one (input : PointRequest) : 1 ≤ variance input := by unfold variance;split <;> first | assumption | exact le_rfl

theorem variance_eq (input : PointRequest) (hwidth : 1 ≤ input.1.1) : variance input=input.1.1 := by simp only [variance,hwidth,ite_true]

/-- Every accepted interval proposal obeys the same width-independent
polynomial Gaussian exponent guard. -/
theorem pointRatio_bounds (input : PointRequest) (index : Fin (intervalCount input)) :
    0 ≤ pointRatio (input,index.val) ∧ pointRatio (input,index.val) ≤ (pointGuardTicks input).length := by
  have hv : (0 : ℚ)<variance input := zero_lt_one.trans_le (variance_ge_one input)
  have hscale := (scale_variance_bounds (variance input) (variance_ge_one input)).2
  have hsNat : 1 ≤ scale (variance input) := by rw [scale_eq];exact Nat.one_le_pow _ _ (by norm_num)
  have hs : (1 : ℚ) ≤ scale (variance input) := by exact_mod_cast hsNat
  have hindex : (index.val : ℚ) ≤ 2*(radius input : ℚ) := by
    have hi := index.isLt
    unfold intervalCount at hi
    exact_mod_cast (show index.val ≤ 2*radius input by omega)
  have hfloor := Int.floor_le input.1.2
  have hfloorUpper := Int.lt_floor_add_one input.1.2
  have hdisplacement : |(point (input,index.val) : ℚ)-input.1.2| ≤ (radius input : ℚ)+1 := by
    rw [abs_le]
    simp only [point,anchorInteger_eq,Int.cast_sub,Int.cast_add,Int.cast_natCast]
    constructor <;> linarith [show (0 : ℚ) ≤ index.val by positivity]
  have hrad : (radius input : ℚ)+1 ≤ (input.2.1.length+1 : ℚ)*(scale (variance input) : ℚ) := by
    unfold radius
    push_cast
    nlinarith
  have hsq : ((point (input,index.val) : ℚ)-input.1.2)^2 ≤
      (input.2.1.length+1 : ℚ)^2*(scale (variance input) : ℚ)^2 := by
    have hb := hdisplacement.trans hrad
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : (0 : ℚ) ≤ (input.2.1.length+1 : ℚ)*(scale (variance input) : ℚ))).mpr hb
    simpa only [sq_abs,mul_pow] using hh
  constructor
  · unfold pointRatio;positivity
  · unfold pointRatio
    rw [pointGuardTicks_length]
    apply (div_le_iff₀ hv).mpr
    have hmul := mul_le_mul_of_nonneg_left hscale (sq_nonneg (input.2.1.length+1 : ℚ))
    push_cast
    nlinarith

/-- The literal capped native exponent evaluator equals the previously
verified exact rational Gaussian approximation at this one point. -/
theorem pointValue_eq (input : PointRequest) (index : Fin (intervalCount input)) :
    pointValue (input,index.val)=centeredGaussianApprox (variance input) input.1.2
      (point (input,index.val)) input.2.2.length := by
  have h := pointRatio_bounds input index
  rw [pointValue,gaussianCapped_eq _ h.1 h.2]
  simp only [centeredGaussianApprox,gaussianApprox,gaussianGuard,centeredGaussianRatio_rat]
  rfl

/-- Actual finite rational exponent evaluation has the requested absolute
error, uniformly in a binary-wide variance and arbitrary rational center. -/
theorem pointValue_error (input : PointRequest) (index : Fin (intervalCount input)) :
    |(pointValue (input,index.val) : ℝ)-Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ))| ≤
      1/(2 : ℝ)^input.2.2.length := by
  rw [pointValue_eq input index]
  exact centeredGaussianApprox_error (variance input) input.1.2 (point (input,index.val)) input.2.2.length
    (zero_lt_one.trans_le (variance_ge_one input))

/-- The acceptance coin's dyadic quantization contributes only one more
absolute dyadic unit. Neither error scales with the window cardinality. -/
theorem pointAcceptance_error (input : PointRequest) (index : Fin (intervalCount input)) :
    |RationalAcceptanceCoin.probability input.2.2.length (pointValue (input,index.val))-
      Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ))| ≤
        2/(2 : ℝ)^input.2.2.length := by
  have hv : (0 : ℝ)<variance input := by exact_mod_cast (zero_lt_one.trans_le (variance_ge_one input))
  have he : -Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
    · exact hv.le
  have htarget : 0 ≤ Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ)) ∧
      Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/(variance input : ℝ)) ≤ 1 :=
    ⟨Real.exp_nonneg _,(Real.exp_le_one_iff).mpr he⟩
  have h := RationalAcceptanceCoin.probability_error input.2.2.length (pointValue (input,index.val)) _ htarget
  have hweight := pointValue_error input index
  simp only [div_eq_mul_inv,one_mul] at h hweight ⊢
  linarith

/-- The native finite-coin path is exactly the analyzed dyadic acceptance
experiment, for every point ticket and every fresh finite random tape. -/
theorem pointCoin_exact (input : PointRequest) (index : ℕ)
    (word : Fin input.2.2.length → Fin 2) :
    pointCoin ((input,index),List.ofFn (fun position => digitBoolean (word position)))=
      (RationalAcceptanceCoin.draw input.2.2.length (pointValue (input,index)) word).val := by
  obtain ⟨code,hcode⟩ := RationalBits.exists_code (pointValue (input,index))
  have h := TM2NativeFiniteDraw.acceptance_native code input.2.2.length word
  rw [binaryAcceptance_value,hcode] at h
  exact h

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule52

/- Helper module Solutions.RegevBridgeWideGaussianTrial. -/
section P2MDyadicModule53

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- One actual bounded binary interval proposal and one independent
fresh-bit Gaussian acceptance test, with explicit rejection. -/
def trial (input : PointRequest × (List Bool × List Bool)) : Bool × ℕ :=
  let proposal := intervalProposal (intervalCount input.1,input.2.1)
  (proposal.1 && decide (pointCoin ((input.1,proposal.2),input.2.2)=0),proposal.2)

@[fun_prop] theorem trial_poly : Poly trial := by unfold trial;fun_prop

/-- Mathematical observation of one native trial, retaining explicit
interval rejection and coin rejection separately in its implementation. -/
def trialOption (input : PointRequest) (proposal : Option (Fin (intervalCount input)))
    (coinWord : Fin input.2.2.length → Fin 2) : Option (Fin (intervalCount input)) :=
  match proposal with
  | none => none
  | some index => if (RationalAcceptanceCoin.draw input.2.2.length (pointValue (input,index.val)) coinWord).val=0 then some index else none

theorem trial_exact (input : PointRequest)
    (proposalWord : Fin (Nat.size (intervalCount input)) → Bool) (coinWord : Fin input.2.2.length → Fin 2) :
    decodeProposal (intervalCount input)
      (trial (input,(List.ofFn proposalWord,List.ofFn (fun position => digitBoolean (coinWord position)))))=
      trialOption input (boundedFinDraw (intervalCount input) proposalWord) coinWord := by
  have htake : (List.ofFn proposalWord).take (Nat.size (intervalCount input))=List.ofFn proposalWord := List.take_of_length_le (by simp)
  simp only [trial,intervalProposal,htake,Integration9_9.LARCoinMachine.bitValue_boundedBoolTicket,pointCoin_exact,
    decodeProposal,boundedFinDraw]
  by_cases hproposal : (boundedBoolTicket (Nat.size (intervalCount input)) proposalWord).val < intervalCount input <;>
    by_cases hcoin : (RationalAcceptanceCoin.draw input.2.2.length
      (pointValue (input,(boundedBoolTicket (Nat.size (intervalCount input)) proposalWord).val)) coinWord).val=0 <;>
    simp [hproposal,hcoin,trialOption]

noncomputable section

open scoped Classical

def coinFair (input : PointRequest) : FiniteDist (Fin input.2.2.length → Fin 2) :=
  FiniteDist.independent (fun _ : Fin input.2.2.length => FiniteDist.uniform (Fin 2))

def trialKernel (input : PointRequest) (proposal : Option (Fin (intervalCount input))) :
    FiniteDist (Option (Fin (intervalCount input))) :=
  (coinFair input).map (trialOption input proposal)

/-- Literal fresh finite tapes drive the native binary program. -/
def trialLaw (input : PointRequest) : FiniteDist (Option (Fin (intervalCount input))) :=
  (FiniteDist.uniform (Fin (Nat.size (intervalCount input)) → Bool)).mix (fun proposalWord =>
    (coinFair input).map (fun coinWord => decodeProposal (intervalCount input)
      (trial (input,(List.ofFn proposalWord,List.ofFn (fun position => digitBoolean (coinWord position)))))))

/-- Exact law factorization is justified from the actual two independent
coin tapes. No uniform successful proposal law is postulated. -/
theorem trialLaw_decomposition (input : PointRequest) :
    trialLaw input=(intervalProposalLaw (intervalCount input)).mix (trialKernel input) := by
  simp only [trialLaw,trial_exact]
  rw [intervalProposalLaw_eq,boundedFinLaw,FiniteDist.mix_map]
  rfl

theorem trialKernel_none (input : PointRequest) (index : Fin (intervalCount input)) :
    (trialKernel input none).weight (some index)=0 := by
  unfold trialKernel trialOption
  rw [FiniteDist.map_const_weight]
  simp

theorem trialKernel_some (input : PointRequest) (selected index : Fin (intervalCount input)) :
    (trialKernel input (some selected)).weight (some index)=
      if selected=index then RationalAcceptanceCoin.probability input.2.2.length (pointValue (input,selected.val)) else 0 := by
  unfold trialKernel
  change ((coinFair input).map ((fun output : Fin 2 => if output.val=0 then some selected else none) ∘
    RationalAcceptanceCoin.draw input.2.2.length (pointValue (input,selected.val)))).weight (some index)=_
  simp only [Function.comp_def]
  rw [←FiniteDist.map_map (coinFair input)
    (RationalAcceptanceCoin.draw input.2.2.length (pointValue (input,selected.val)))
    (fun output : Fin 2 => if output.val=0 then some selected else none),FiniteDist.map_weight,Fin.sum_univ_two]
  simp only [Fin.val_zero,Fin.val_one,if_true,if_false,one_ne_zero]
  by_cases h : selected=index
  · simpa [h,coinFair] using RationalAcceptanceCoin.draw_acceptance input.2.2.length (pointValue (input,index.val))
  · simp [h]

/-- Successful output masses of the actual binary trial are exactly a
common ticket scale times its actual dyadic Gaussian acceptance score. -/
theorem trialLaw_some (input : PointRequest) (index : Fin (intervalCount input)) :
    (trialLaw input).weight (some index)=((2 : ℝ)^Nat.size (intervalCount input))⁻¹*
      RationalAcceptanceCoin.probability input.2.2.length (pointValue (input,index.val)) := by
  rw [trialLaw_decomposition,FiniteDist.mix_weight,Fintype.sum_option,trialKernel_none,mul_zero,zero_add]
  simp_rw [trialKernel_some,intervalProposalLaw_some,mul_ite,mul_zero]
  simp

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule53

/- Helper module Solutions.RegevBridgeWideGaussianRetry. -/
section P2MDyadicModule54

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- Scan a supplied finite list of native trial results and retain the
first success. Exhaustion is represented explicitly by the false flag. -/
def firstSuccess (results : List (Bool × ℕ)) : Bool × ℕ :=
  (results[results.findIdx (fun result => result.1)]?).getD (false,0)

@[fun_prop] theorem firstSuccess_poly : Poly firstSuccess := by
  have hf : Poly (fun results : List (Bool × ℕ) => results.findIdx (fun result => result.1)) := by
    apply Poly.list_findIdx
    · fun_prop
    · exact Poly.identity
  unfold firstSuccess
  fun_prop

abbrev RetryRequest := PointRequest × List (List Bool × List Bool)

def trialResults (input : RetryRequest) : List (Bool × ℕ) := input.2.map (fun word => trial (input.1,word))

@[fun_prop] theorem trialResults_poly : Poly trialResults := by unfold trialResults;fun_prop

def retry (input : RetryRequest) : Bool × ℕ := firstSuccess (trialResults input)

@[fun_prop] theorem retry_poly : Poly retry := by unfold retry;fun_prop

/-- The actual wide Gaussian sampler emits the accepted integer point,
or its fixed floor anchor if its supplied retry list is exhausted. -/
def output (input : RetryRequest) : ℤ :=
  let selected := retry input
  if selected.1 then point (input.1,selected.2) else anchorInteger input.1.1.2

@[fun_prop] theorem output_poly : Poly output := by unfold output;fun_prop

theorem firstSuccess_nil : firstSuccess []=(false,0) := rfl

theorem firstSuccess_cons (head : Bool × ℕ) (tail : List (Bool × ℕ)) :
    firstSuccess (head::tail)=if head.1 then head else firstSuccess tail := by
  cases hflag : head.1 <;> simp [firstSuccess,List.findIdx_cons,hflag]

/-- A native trial can set its success flag only for an actual interval
point, on arbitrary encoded tapes as well as on valid fair tapes. -/
theorem trial_success_valid (input : PointRequest) (word : List Bool × List Bool)
    (hsuccess : (trial (input,word)).1=true) : (trial (input,word)).2 < intervalCount input := by
  have h := (Bool.and_eq_true_iff.mp hsuccess).1
  change decide (QMCNumericRuntime.bitValue (word.1.take (Nat.size (intervalCount input))) < intervalCount input)=true at h
  exact of_decide_eq_true h

/-- The observational finite interval result follows exactly the same
first-success execution on every valid native trial stream. -/
theorem decode_firstSuccess (count : ℕ) (results : List (Bool × ℕ))
    (hvalid : ∀ result ∈ results,result.1=true → result.2<count) :
    decodeProposal count (firstSuccess results)=
      results.foldr (fun result remaining => match decodeProposal count result with | none => remaining | some index => some index) none := by
  induction results with
  | nil => simp [firstSuccess_nil,decodeProposal]
  | cons head tail ih =>
    rw [firstSuccess_cons,List.foldr_cons]
    cases hflag : head.1
    · have hhead : decodeProposal count head=none := by simp [decodeProposal,hflag]
      simp only [Bool.false_eq_true,if_false,hhead]
      exact ih (fun result membership => hvalid result (by simp only [List.mem_cons];exact Or.inr membership))
    · have hlt := hvalid head (by simp) hflag
      have hhead : decodeProposal count head=some ⟨head.2,hlt⟩ := by simp [decodeProposal,hflag,hlt]
      simp only [if_true,hhead]

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule54

/- Helper module Solutions.RegevBridgeWideGaussianMass. -/
section P2MDyadicModule55

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

theorem scale_width_bounds (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    width ≤ (scale (variance input) : ℝ) ∧ (scale (variance input) : ℝ) ≤ 3*width := by
  have h := scale_variance_bounds (variance input) (variance_ge_one input)
  have hl : width^2 ≤ (scale (variance input) : ℝ)^2 := by
    have hh : (variance input : ℝ) ≤ (scale (variance input) : ℝ)^2 := by exact_mod_cast h.1
    rwa [←hsquare] at hh
  have hu : (scale (variance input) : ℝ)^2 ≤ 8*width^2 := by
    have hh : (scale (variance input) : ℝ)^2 ≤ 8*(variance input : ℝ) := by exact_mod_cast h.2
    rwa [←hsquare] at hh
  constructor
  · exact (sq_le_sq₀ (zero_lt_one.trans_le hwidth).le (Nat.cast_nonneg _)).mp hl
  · nlinarith [show (0 : ℝ) ≤ scale (variance input) by positivity,sq_nonneg width]

theorem point_eq_windowPoint (input : PointRequest) (index : Fin (intervalCount input)) :
    point (input,index.val)=windowPoint input.1.2 (radius input) index := by
  rw [point,anchorInteger_eq]
  rfl

def trueWindowMass (input : PointRequest) (width : ℝ) : ℝ :=
  ∑ index : Fin (intervalCount input),shiftedWeight width input.1.2 (point (input,index.val))

/-- Every valid wide window contains nearly all true shifted Gaussian
mass; the discarded infinite tail is bounded without enumerating points. -/
theorem wide_tail_half (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    tailEnvelope width (radius input) ≤ 1/2 := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hscale := (scale_width_bounds input width hwidth hsquare).1
  have hf : (2 : ℝ) ≤ input.2.1.length := by exact_mod_cast hfactor
  have hrad : 2*width ≤ (radius input : ℝ) := by
    unfold radius
    push_cast
    nlinarith
  have htail := (VarianceGrid.tailEnvelope_interval (radius input : ℝ) hwidth le_rfl le_rfl).trans
    (intervalTail_le_six hwidth)
  have hratio : (2 : ℝ) ≤ (radius input : ℝ)^2/(2*width^2) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*width^2)).mpr
    nlinarith
  have hexponent : -Real.pi*(radius input : ℝ)^2/(2*width^2) ≤ -Real.pi*(2 : ℝ)^2/2 := by
    calc
      _ = -Real.pi*((radius input : ℝ)^2/(2*width^2)) := by ring
      _ ≤ -Real.pi*2 := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr Real.pi_pos.le)
      _ = _ := by ring
  have hexp := Real.exp_le_exp.mpr hexponent
  have htwo : Real.exp (-Real.pi*(2 : ℝ)^2/2) ≤ 1/16 := by
    convert sigma_gaussian_exp_le 2 (by omega) using 1 <;> norm_num
  have hbound := hexp.trans htwo
  linarith

/-- The true accepted weight has a width-linear lower bound, even at an
arbitrary rational shifted center and exponentially wide binary scale. -/
theorem trueWindowMass_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    width/4 ≤ trueWindowMass input width := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have ht := roundingError_lt_half width hwidth
  have hrelative := (abs_le.mp (theta_relative_error_exp width (input.1.2 : ℝ) hw)).1
  have htheta : width/2 ≤ theta width input.1.2 := by
    have hlo : 1-thetaError width ≤ theta width input.1.2/width := by linarith
    have hb := (le_div_iff₀ hw).mp hlo
    nlinarith
  have hout := (outsideWindowMass_le width hwidth input.1.2 (radius input)).trans (wide_tail_half input width hwidth hsquare hfactor)
  have heq := outsideWindowMass_eq 1 width hw input.1.2 (radius input)
  rw [retainedResidue_sum] at heq
  simp_rw [roundingPMF_toReal] at heq
  rw [←Finset.sum_div] at heq
  have hmass : (∑ index : Fin (2*radius input+1),shiftedWeight width input.1.2 (windowPoint input.1.2 (radius input) index))=
      trueWindowMass input width := by
    unfold trueWindowMass
    simp_rw [point_eq_windowPoint]
    rfl
  rw [hmass] at heq
  have hr : 1/2 ≤ trueWindowMass input width/theta width input.1.2 := by linarith
  have hb := (le_div_iff₀ (theta_pos width input.1.2 hw)).mp hr
  linarith

/-- Binary ticket length is controlled by the width-linear window size;
this is the key cancellation in the rejection success probability. -/
theorem wide_ticket_bound (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    (2 : ℝ)^Nat.size (intervalCount input) ≤ 14*(input.2.1.length : ℝ)*width := by
  have hscale := (scale_width_bounds input width hwidth hsquare).2
  have hf : (2 : ℝ) ≤ input.2.1.length := by exact_mod_cast hfactor
  have hcount : (intervalCount input : ℝ) ≤ 7*(input.2.1.length : ℝ)*width := by
    unfold intervalCount radius
    push_cast
    nlinarith
  have hhalf := boundedFinSuccess_half (intervalCount input) (by unfold intervalCount;omega)
  unfold boundedFinSuccess at hhalf
  have hb := (le_div_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (intervalCount input))).mp hhalf
  nlinarith

/-- One ideal Gaussian-weight interval trial succeeds with inverse-linear
probability in the public unary multiplier, independent of width value. -/
theorem ideal_trial_success_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    1/(56*(input.2.1.length : ℝ)) ≤ trueWindowMass input width/(2 : ℝ)^Nat.size (intervalCount input) := by
  have hmass := trueWindowMass_lower input width hwidth hsquare hfactor
  have hticket := wide_ticket_bound input width hwidth hsquare hfactor
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hh := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 56*(input.2.1.length : ℝ) by positivity)
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (intervalCount input))).mpr
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<56*(input.2.1.length : ℝ))).mpr
  nlinarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule55

/- Helper module Solutions.RegevBridgeWideGaussianAcceptance. -/
section P2MDyadicModule56

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators Classical

noncomputable section

def successMass (input : PointRequest) : ℝ := ∑ index : Fin (intervalCount input),(trialLaw input).weight (some index)

def idealTicketMass (input : PointRequest) (width : ℝ) (index : Fin (intervalCount input)) : ℝ :=
  ((2 : ℝ)^Nat.size (intervalCount input))⁻¹*shiftedWeight width input.1.2 (point (input,index.val))

/-- Although the window may have exponentially many points, its
unnormalized numerical error has no cardinality loss: the common ticket
mass cancels the entire window size. -/
theorem trial_mass_l1 (input : PointRequest) (width : ℝ) (_hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    (∑ index : Fin (intervalCount input),|(trialLaw input).weight (some index)-idealTicketMass input width index|) ≤
      2/(2 : ℝ)^input.2.2.length := by
  let ticketScale : ℝ := ((2 : ℝ)^Nat.size (intervalCount input))⁻¹
  have hticket : 0 ≤ ticketScale := by positivity
  have hpoint (index : Fin (intervalCount input)) :
      |(trialLaw input).weight (some index)-idealTicketMass input width index| ≤
        ticketScale*(2/(2 : ℝ)^input.2.2.length) := by
    rw [trialLaw_some,idealTicketMass,←mul_sub,abs_mul,abs_of_nonneg hticket]
    apply mul_le_mul_of_nonneg_left _ hticket
    have heq : shiftedWeight width input.1.2 (point (input,index.val))=
        Real.exp (-Real.pi*((point (input,index.val) : ℝ)-(input.1.2 : ℝ))^2/width^2) := by
      unfold shiftedWeight
      congr 1
      ring
    rw [heq,hsquare]
    exact pointAcceptance_error input index
  have hs := Finset.sum_le_sum (fun index (_ : index ∈ (Finset.univ : Finset (Fin (intervalCount input)))) => hpoint index)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hcount : (intervalCount input : ℝ)*ticketScale ≤ 1 := by
    apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (intervalCount input))).mpr
    rw [one_mul]
    exact_mod_cast (Nat.lt_size_self (intervalCount input)).le
  have hlast := mul_le_mul_of_nonneg_right hcount (show (0 : ℝ) ≤ 2/(2 : ℝ)^input.2.2.length by positivity)
  calc
    _ ≤ (intervalCount input : ℝ)*(ticketScale*(2/(2 : ℝ)^input.2.2.length)) := hs
    _ ≤ _ := by nlinarith

/-- The actual trial success mass differs from its ideal Gaussian trial
by at most the same two dyadic units. -/
theorem successMass_error (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    |successMass input-trueWindowMass input width/(2 : ℝ)^Nat.size (intervalCount input)| ≤
      2/(2 : ℝ)^input.2.2.length := by
  have h := SignedConditioning.mass_difference_le_l1
    (fun index : Fin (intervalCount input) => (trialLaw input).weight (some index)) (idealTicketMass input width)
  have he : (∑ index : Fin (intervalCount input),idealTicketMass input width index)=
      trueWindowMass input width/(2 : ℝ)^Nat.size (intervalCount input) := by
    simp only [idealTicketMass,←Finset.mul_sum,trueWindowMass,div_eq_mul_inv]
    ring
  rw [he] at h
  exact h.trans (trial_mass_l1 input width hwidth hsquare)

/-- The exact native finite-tape trial has a width-independent positive
success floor once the public numerical precision is sufficiently large. -/
theorem successMass_lower (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length)
    (hbits : 2/(2 : ℝ)^input.2.2.length ≤ 1/(112*(input.2.1.length : ℝ))) :
    1/(112*(input.2.1.length : ℝ)) ≤ successMass input := by
  have hi := ideal_trial_success_lower input width hwidth hsquare hfactor
  have he := (abs_le.mp (successMass_error input width hwidth hsquare)).1
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hsplit : 1/(56*(input.2.1.length : ℝ))=2/(112*(input.2.1.length : ℝ)) := by ring
  rw [hsplit] at hi
  simp only [div_eq_mul_inv,one_mul] at hi he hbits ⊢
  linarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule56

/- Helper module Solutions.RegevBridgeWideGaussianPrecision. -/
section P2MDyadicModule57

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- A logarithmic guard in the public unary radius multiplier, followed
by the requested unary accuracy budget. No variance-size loop is added. -/
def precisionTicks (input : List Unit × List Unit) : List Unit :=
  (Nat.bits (224*input.1.length)).map (fun _ => ())++input.2

@[fun_prop] theorem precisionTicks_poly : Poly precisionTicks := by unfold precisionTicks;fun_prop

theorem precisionTicks_length (input : List Unit × List Unit) :
    (precisionTicks input).length=Nat.size (224*input.1.length)+input.2.length := by
  simp only [precisionTicks,List.length_append,List.length_map,Nat.size_eq_bits_len]

abbrev ConfigureRequest := (ℚ × ℚ) × (List Unit × List Unit)

/-- The actual running point sampler receives the executable buffer. -/
def configure (input : ConfigureRequest) : PointRequest := (input.1,(input.2.1,precisionTicks input.2))

@[fun_prop] theorem configure_poly : Poly configure := by unfold configure;fun_prop

noncomputable section

theorem configured_dyadic_bound (input : ConfigureRequest) (hfactor : 0 < input.2.1.length) :
    2/(2 : ℝ)^(configure input).2.2.length ≤ 1/(112*(input.2.1.length : ℝ)) := by
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast hfactor
  have hbase : 224*(input.2.1.length : ℝ) ≤ (2 : ℝ)^Nat.size (224*input.2.1.length) := by
    exact_mod_cast (Nat.lt_size_self (224*input.2.1.length)).le
  have hpow : (2 : ℝ)^Nat.size (224*input.2.1.length) ≤ (2 : ℝ)^(configure input).2.2.length := by
    apply pow_le_pow_right₀ (by norm_num)
    change Nat.size (224*input.2.1.length) ≤ (precisionTicks input.2).length
    rw [precisionTicks_length]
    omega
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2^(configure input).2.2.length)
    (by positivity : (0 : ℝ)<112*(input.2.1.length : ℝ))).mpr
  linarith

/-- The public precision buffer completely discharges the numeric
smallness premise in the actual trial-success theorem. -/
theorem configured_success_lower (input : ConfigureRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance (configure input) : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    1/(112*(input.2.1.length : ℝ)) ≤ successMass (configure input) := by
  exact successMass_lower (configure input) width hwidth hsquare hfactor
    (configured_dyadic_bound input (by omega))

/-- Once the actual trial is normalized, all logarithmic guard bits
cancel the inverse-success factor, leaving exactly the requested dyadic
accuracy independently of the width value. -/
theorem configured_normalization_budget (input : ConfigureRequest) (_hfactor : 0 < input.2.1.length) :
    (224*(input.2.1.length : ℝ))/(2 : ℝ)^(configure input).2.2.length ≤ 1/(2 : ℝ)^input.2.2.length := by
  have hbase : 224*(input.2.1.length : ℝ) ≤ (2 : ℝ)^Nat.size (224*input.2.1.length) := by
    exact_mod_cast (Nat.lt_size_self (224*input.2.1.length)).le
  change (224*(input.2.1.length : ℝ))/(2 : ℝ)^(precisionTicks input.2).length ≤ _
  rw [precisionTicks_length,pow_add]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2^Nat.size (224*input.2.1.length)*2^input.2.2.length)
    (by positivity : (0 : ℝ)<2^input.2.2.length)).mpr
  nlinarith [pow_pos (by norm_num : (0 : ℝ)<2) input.2.2.length]

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule57

/- Helper module Solutions.RegevBridgeWideGaussianSuccessfulLaw. -/
section P2MDyadicModule58

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators Classical

noncomputable section

def successfulLaw (input : PointRequest) (hpositive : 0 < successMass input) : FiniteDist (Fin (intervalCount input)) where
  weight index := (trialLaw input).weight (some index)/successMass input
  nonneg index := div_nonneg ((trialLaw input).nonneg _) hpositive.le
  sum_one := by rw [←Finset.sum_div];exact div_self hpositive.ne'

/-- Numerical normalization uses the actual total native acceptance mass,
which has already been proved positive, and the actual true window law. -/
theorem successfulLaw_totalVariation (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) (hfactor : 2 ≤ input.2.1.length)
    (hbits : 2/(2 : ℝ)^input.2.2.length ≤ 1/(112*(input.2.1.length : ℝ))) :
    let hpositive := (show 0 < 1/(112*(input.2.1.length : ℝ)) by positivity).trans_le
      (successMass_lower input width hwidth hsquare hfactor hbits)
    (∑ index : Fin (intervalCount input),|(successfulLaw input hpositive).weight index-
      (windowLaw width input.1.2 (radius input)).weight index|)/2 ≤
        (224*(input.2.1.length : ℝ))/(2 : ℝ)^input.2.2.length := by
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hfloor := successMass_lower input width hwidth hsquare hfactor hbits
  have hpositive : 0 < successMass input := (by positivity : 0 < 1/(112*(input.2.1.length : ℝ))).trans_le hfloor
  let ticketScale : ℝ := ((2 : ℝ)^Nat.size (intervalCount input))⁻¹
  have hscale : 0 < ticketScale := by positivity
  have hmass : 0 < trueWindowMass input width := by
    have h := trueWindowMass_lower input width hwidth hsquare hfactor
    linarith
  have hreference : 0 < ∑ index : Fin (intervalCount input),idealTicketMass input width index := by
    simp only [idealTicketMass,←Finset.mul_sum]
    exact mul_pos hscale hmass
  have hequal (index : Fin (intervalCount input)) :
      idealTicketMass input width index/(∑ selected : Fin (intervalCount input),idealTicketMass input width selected)=
        (windowLaw width input.1.2 (radius input)).weight index := by
    simp only [idealTicketMass,←Finset.mul_sum,windowLaw,FiniteDist.normalize,point_eq_windowPoint]
    have hticket : ((2 : ℝ)^Nat.size (intervalCount input))⁻¹≠0 := hscale.ne'
    field_simp
    rfl
  have hnormal := SignedConditioning.normalized_signed_l1
    (fun index : Fin (intervalCount input) => (trialLaw input).weight (some index)) (idealTicketMass input width)
    (fun index => mul_nonneg hscale.le (Real.exp_nonneg _)) hpositive hreference
  simp_rw [hequal] at hnormal
  have hl1 := trial_mass_l1 input width hwidth hsquare
  have hbound : (∑ index : Fin (intervalCount input),|(successfulLaw input hpositive).weight index-
      (windowLaw width input.1.2 (radius input)).weight index|)/2 ≤
      (2/(2 : ℝ)^input.2.2.length)/successMass input := by
    change (∑ index : Fin (intervalCount input),|(trialLaw input).weight (some index)/successMass input-
      (windowLaw width input.1.2 (radius input)).weight index|)/2 ≤ _
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ 2)) hpositive.le
    change (∑ index : Fin (intervalCount input),|(trialLaw input).weight (some index)/successMass input-
      (windowLaw width input.1.2 (radius input)).weight index|) ≤
        (2*(∑ index : Fin (intervalCount input),|(trialLaw input).weight (some index)-idealTicketMass input width index|))/successMass input at hnormal
    have hfinal := hnormal.trans hh
    simp only [div_eq_mul_inv] at hfinal ⊢
    linarith
  apply hbound.trans
  calc
    _ ≤ (2/(2 : ℝ)^input.2.2.length)/(1/(112*(input.2.1.length : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfloor
    _ = _ := by field_simp;ring

/-- With the executable logarithmic guard, the actual successful output
law has the requested dyadic accuracy, independent of Gaussian width. -/
theorem configured_successfulLaw_totalVariation (input : ConfigureRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance (configure input) : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    let hpositive := (show 0 < 1/(112*(input.2.1.length : ℝ)) by positivity).trans_le
      (configured_success_lower input width hwidth hsquare hfactor)
    (∑ index : Fin (intervalCount (configure input)),|(successfulLaw (configure input) hpositive).weight index-
      (windowLaw width input.1.2 (radius (configure input))).weight index|)/2 ≤ 1/(2 : ℝ)^input.2.2.length := by
  exact (successfulLaw_totalVariation (configure input) width hwidth hsquare hfactor
    (configured_dyadic_bound input (by omega))).trans (configured_normalization_budget input (by omega))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule58

/- Helper module Solutions.RegevBridgeWideGaussianRetryLaw. -/
section P2MDyadicModule59

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic

open scoped BigOperators

noncomputable section

abbrev TrialRandom (input : PointRequest) := (Fin (Nat.size (intervalCount input)) → Bool) × (Fin input.2.2.length → Fin 2)

def trialData (input : PointRequest) (word : TrialRandom input) : List Bool × List Bool :=
  (List.ofFn word.1,List.ofFn (fun position => digitBoolean (word.2 position)))

def decodeTrial (input : PointRequest) (word : TrialRandom input) : Option (Fin (intervalCount input)) :=
  decodeProposal (intervalCount input) (trial (input,trialData input word))

def rawFair (input : PointRequest) : FiniteDist (TrialRandom input) :=
  (FiniteDist.uniform (Fin (Nat.size (intervalCount input)) → Bool)).prod (coinFair input)

/-- The observed actual two-tape trial law is exactly the analyzed law. -/
theorem rawFair_map (input : PointRequest) : (rawFair input).map (decodeTrial input)=trialLaw input := by
  classical
  ext output
  simp only [rawFair,FiniteDist.map_weight,FiniteDist.prod_weight,Fintype.sum_prod_type,trialLaw,
    FiniteDist.mix_weight,FiniteDist.map_weight,Finset.mul_sum,mul_ite,mul_zero]
  rfl

def retryData (input : PointRequest) (attempts : ℕ) (word : Fin attempts → TrialRandom input) : RetryRequest :=
  (input,List.ofFn (fun index => trialData input (word index)))

def acceptedEvent {count : ℕ} (output : Option (Fin count)) : Prop := output.isSome=true

instance acceptedEvent_decidable {count : ℕ} : DecidablePred (acceptedEvent (count:=count)) :=
  fun output => inferInstanceAs (Decidable (output.isSome=true))

theorem foldr_firstAccepted {count attempts : ℕ} (proposals : Fin attempts → Option (Fin count)) :
    (List.ofFn proposals).foldr (fun result remaining => match result with | none => remaining | some index => some index) none=
      FiniteConditionProgram.firstAccepted acceptedEvent none attempts proposals := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    rw [List.ofFn_succ,List.foldr_cons]
    simp only [FiniteConditionProgram.firstAccepted]
    cases hhead : proposals 0 <;> simp only [acceptedEvent,Option.isSome_none,Option.isSome_some,
      Bool.false_eq_true,if_false,if_true]
    exact ih (fun index => proposals index.succ)

/-- Every finite raw-tape stream follows the same executable first-success
procedure on its true observed interval results. -/
theorem retry_exact (input : PointRequest) (attempts : ℕ) (word : Fin attempts → TrialRandom input) :
    decodeProposal (intervalCount input) (retry (retryData input attempts word))=
      FiniteConditionProgram.firstAccepted acceptedEvent none attempts (fun index => decodeTrial input (word index)) := by
  have hresults : trialResults (retryData input attempts word)=
      List.ofFn (fun index => trial (input,trialData input (word index))) := by
    simp only [trialResults,retryData,List.map_ofFn]
    rfl
  unfold retry
  rw [hresults,decode_firstSuccess]
  · have hmap : (List.ofFn (fun index => trial (input,trialData input (word index)))).map (decodeProposal (intervalCount input))=
        List.ofFn (fun index => decodeTrial input (word index)) := by
      simp only [List.map_ofFn,decodeTrial,Function.comp_def]
    have hfold := foldr_firstAccepted (fun index => decodeTrial input (word index))
    rw [←hmap,List.foldr_map] at hfold
    exact hfold
  · intro result membership hflag
    obtain ⟨index,hindex⟩ := List.mem_ofFn.mp membership
    rw [←hindex] at hflag ⊢
    exact trial_success_valid input (trialData input (word index)) hflag

/-- Literal independent fresh raw trials followed by the native retry
program, with exhaustion kept as an explicit none output. -/
def retryLaw (input : PointRequest) (attempts : ℕ) : FiniteDist (Option (Fin (intervalCount input))) :=
  (FiniteDist.independent (fun _ : Fin attempts => rawFair input)).map
    (fun word => decodeProposal (intervalCount input) (retry (retryData input attempts word)))

/-- Native bounded repetition has exactly the proved capped conditioning
law, including its independently generated failed-trial history. -/
theorem retryLaw_eq (input : PointRequest) (attempts : ℕ) :
    retryLaw input attempts=FiniteDist.cappedCondition (trialLaw input) acceptedEvent (CanonicalMoments.pointLaw none) attempts := by
  classical
  have hmap := independent_map_coordinatewise (fun _ : Fin attempts => rawFair input)
    (fun _ => decodeTrial input)
  simp_rw [rawFair_map] at hmap
  have hfinal := congrArg (fun law : FiniteDist (Fin attempts → Option (Fin (intervalCount input))) =>
    law.map (FiniteConditionProgram.firstAccepted acceptedEvent none attempts)) hmap
  rw [FiniteDist.map_map] at hfinal
  unfold retryLaw
  simp_rw [retry_exact]
  exact hfinal.trans (FiniteConditionProgram.firstAccepted_law (trialLaw input) acceptedEvent none attempts)

/-- The native first-success selector retains interval validity on every
raw input stream. This invariant is discharged by the actual trial code. -/
theorem firstSuccess_valid (count : ℕ) (results : List (Bool × ℕ))
    (hvalid : ∀ result ∈ results,result.1=true → result.2<count)
    (hsuccess : (firstSuccess results).1=true) : (firstSuccess results).2<count := by
  induction results with
  | nil => simp [firstSuccess_nil] at hsuccess
  | cons head tail ih =>
    rw [firstSuccess_cons] at hsuccess ⊢
    cases hflag : head.1
    · simp only [hflag,Bool.false_eq_true,if_false] at hsuccess ⊢
      exact ih (fun result membership => hvalid result (by simp only [List.mem_cons];exact Or.inr membership)) hsuccess
    · simp only [if_true]
      exact hvalid head (by simp) hflag

theorem retry_success_valid (input : RetryRequest) (hsuccess : (retry input).1=true) :
    (retry input).2 < intervalCount input.1 := by
  apply firstSuccess_valid (intervalCount input.1) (trialResults input) _ hsuccess
  intro result membership hflag
  obtain ⟨word,_,hword⟩ := List.mem_map.mp membership
  rw [←hword] at hflag ⊢
  exact trial_success_valid input.1 word hflag

/-- A valid floor-anchor fallback is used when every trial rejects. -/
def resolveIndex (input : PointRequest) : Option (Fin (intervalCount input)) → Fin (intervalCount input)
  | none => ⟨radius input,by unfold intervalCount;omega⟩
  | some index => index

/-- Exact native integer output on arbitrary supplied finite tapes. -/
theorem output_resolve (input : RetryRequest) :
    output input=point (input.1,(resolveIndex input.1 (decodeProposal (intervalCount input.1) (retry input))).val) := by
  cases hflag : (retry input).1
  · simp [output,hflag,decodeProposal,resolveIndex,point]
  · have hi := retry_success_valid input hflag
    simp [output,hflag,decodeProposal,hi,resolveIndex]

/-- Conditioning is on the actual native success event. -/
theorem acceptedEvent_mass (input : PointRequest) : (trialLaw input).eventMass acceptedEvent=successMass input := by
  simp only [FiniteDist.eventMass,Fintype.sum_option,acceptedEvent,Option.isSome_none,Option.isSome_some,
    Bool.false_eq_true,if_false,if_true,zero_add,successMass]

theorem condition_resolve (input : PointRequest) (hpositive : 0 < successMass input) :
    ((trialLaw input).condition acceptedEvent (by rw [acceptedEvent_mass];exact hpositive)).map (resolveIndex input)=
      successfulLaw input hpositive := by
  ext index
  simp only [FiniteDist.map_weight,Fintype.sum_option,FiniteDist.condition,acceptedEvent,
    Option.isSome_none,Option.isSome_some,Bool.false_eq_true,if_false,if_true,zero_div,ite_self,zero_add,
    resolveIndex,acceptedEvent_mass,successfulLaw]
  simp

/-- The actual bounded native sampler differs from its true successful
law only by its exponentially small finite retry budget. -/
theorem retry_resolve_tv (input : PointRequest) (attempts : ℕ) (hpositive : 0 < successMass input) :
    FiniteDist.TVBound ((retryLaw input attempts).map (resolveIndex input)) (successfulLaw input hpositive)
      (Real.exp (-(attempts : ℝ)*successMass input)) := by
  have h := FiniteDist.cappedCondition_tv (trialLaw input) acceptedEvent
    (by rw [acceptedEvent_mass];exact hpositive) (CanonicalMoments.pointLaw none) attempts
  rw [←retryLaw_eq] at h
  have hm := h.map (resolveIndex input)
  rw [condition_resolve] at hm
  simpa only [acceptedEvent_mass] using hm

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule59

/- Helper module Solutions.RegevBridgeWideGaussianConfiguredRetry. -/
section P2MDyadicModule60

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

/-- The retry count is materialized from actual unary public controls. -/
def attemptTicks (input : List Unit × List Unit) : List Unit :=
  input.1.flatMap (fun _ => (input.2++[()]).flatMap (fun _ => List.replicate 112 ()))

@[fun_prop] theorem attemptTicks_poly : Poly attemptTicks := by unfold attemptTicks;fun_prop

theorem attemptTicks_length (input : List Unit × List Unit) :
    (attemptTicks input).length=112*input.1.length*(input.2.length+1) := by
  simp only [attemptTicks,List.length_flatMap,List.length_append,List.length_singleton,List.length_replicate,
    List.map_const',List.sum_replicate]
  ring

/-- An unconditional native binary program configures both the numerical
precision and the bounded retry cap, then returns an actual integer. -/
def configuredOutput (input : ConfigureRequest × List (List Bool × List Bool)) : ℤ :=
  output (configure input.1,input.2.take (attemptTicks input.1.2).length)

@[fun_prop] theorem configuredOutput_poly : Poly configuredOutput := by
  have ht : Poly (fun input : ConfigureRequest × List (List Bool × List Bool) => input.2.take (attemptTicks input.1.2).length) :=
    Poly.comp (f:=fun pair : List (List Bool × List Bool) × ℕ => pair.1.take pair.2)
      (g:=fun input : ConfigureRequest × List (List Bool × List Bool) => (input.2,(attemptTicks input.1.2).length))
      QMCNumericRuntime.parser_take_poly (by fun_prop)
  unfold configuredOutput
  exact Poly.comp (f:=output)
    (g:=fun input : ConfigureRequest × List (List Bool × List Bool) => (configure input.1,input.2.take (attemptTicks input.1.2).length))
    output_poly (Poly.pair (by fun_prop) ht)

noncomputable section

open scoped Classical

/-- First add the exact native retry error to the already proved
successful-law numerical error. -/
theorem configured_retry_window_tv (input : ConfigureRequest) (attempts : ℕ)
    (width : ℝ) (hwidth : 1 ≤ width) (hsquare : width^2=(variance (configure input) : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    (∑ index : Fin (intervalCount (configure input)),|((retryLaw (configure input) attempts).map (resolveIndex (configure input))).weight index-
      (windowLaw width input.1.2 (radius (configure input))).weight index|)/2 ≤
        Real.exp (-(attempts : ℝ)*successMass (configure input))+1/(2 : ℝ)^input.2.2.length := by
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hpositive := (by positivity : 0 < 1/(112*(input.2.1.length : ℝ))).trans_le
    (configured_success_lower input width hwidth hsquare hfactor)
  have hretry := retry_resolve_tv (configure input) attempts hpositive
  have hr := (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp hretry
  rw [FiniteDist.totalVariation_eq_half_l1] at hr
  change (∑ index : Fin (intervalCount (configure input)),|((retryLaw (configure input) attempts).map (resolveIndex (configure input))).weight index-
    (successfulLaw (configure input) hpositive).weight index|)/2 ≤ _ at hr
  have hg := configured_successfulLaw_totalVariation input width hwidth hsquare hfactor
  have htriangle := Finset.sum_le_sum (fun index (_ : index ∈ (Finset.univ : Finset (Fin (intervalCount (configure input))))) =>
    abs_sub_le (((retryLaw (configure input) attempts).map (resolveIndex (configure input))).weight index)
      ((successfulLaw (configure input) hpositive).weight index) ((windowLaw width input.1.2 (radius (configure input))).weight index))
  rw [Finset.sum_add_distrib] at htriangle
  linarith

/-- The executable retry count makes its exact exhaustion error dyadic,
with no dependence on the Gaussian width's numerical magnitude. -/
theorem configured_retry_error (input : ConfigureRequest)
    (width : ℝ) (hwidth : 1 ≤ width) (hsquare : width^2=(variance (configure input) : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    Real.exp (-((attemptTicks input.2).length : ℝ)*successMass (configure input)) ≤
      1/(2 : ℝ)^(input.2.2.length+1) := by
  have hf : (0 : ℝ) < input.2.1.length := by exact_mod_cast (show 0 < input.2.1.length by omega)
  have hfloor := configured_success_lower input width hwidth hsquare hfactor
  have hcount := mul_le_mul_of_nonneg_left hfloor (show (0 : ℝ) ≤ (attemptTicks input.2).length by positivity)
  have heq : ((attemptTicks input.2).length : ℝ)*(1/(112*(input.2.1.length : ℝ)))=(input.2.2.length+1 : ℝ) := by
    rw [attemptTicks_length]
    push_cast
    field_simp
  rw [heq] at hcount
  have hexp : Real.exp (-((attemptTicks input.2).length : ℝ)*successMass (configure input)) ≤
      Real.exp (-(input.2.2.length+1 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hpow : (2 : ℝ)^(input.2.2.length+1) ≤ Real.exp (input.2.2.length+1 : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le (input.2.2.length+1)
    rw [←Real.exp_nat_mul] at h
    simpa only [mul_one,Nat.cast_add,Nat.cast_one] using h
  calc
    _ ≤ Real.exp (-(input.2.2.length+1 : ℝ)) := hexp
    _ = 1/Real.exp (input.2.2.length+1 : ℝ) := by rw [Real.exp_neg,one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpow

/-- Complete actual bounded-native-retry window law accuracy. -/
theorem configured_retry_totalVariation (input : ConfigureRequest)
    (width : ℝ) (hwidth : 1 ≤ width) (hsquare : width^2=(variance (configure input) : ℝ)) (hfactor : 2 ≤ input.2.1.length) :
    (∑ index : Fin (intervalCount (configure input)),|((retryLaw (configure input) (attemptTicks input.2).length).map (resolveIndex (configure input))).weight index-
      (windowLaw width input.1.2 (radius (configure input))).weight index|)/2 ≤ 2/(2 : ℝ)^input.2.2.length := by
  have h := configured_retry_window_tv input (attemptTicks input.2).length width hwidth hsquare hfactor
  have he := configured_retry_error input width hwidth hsquare hfactor
  have hp : 1/(2 : ℝ)^(input.2.2.length+1) ≤ 1/(2 : ℝ)^input.2.2.length := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  simp only [div_eq_mul_inv,one_mul] at h he hp ⊢
  linarith

/-- On the exact prescribed finite raw tapes, configuredOutput is the
same native integer program whose complete retry law was proved above. -/
theorem configuredOutput_exact (input : ConfigureRequest)
    (word : Fin (attemptTicks input.2).length → TrialRandom (configure input)) :
    configuredOutput (input,(retryData (configure input) (attemptTicks input.2).length word).2)=
      point (configure input,(resolveIndex (configure input)
        (decodeProposal (intervalCount (configure input)) (retry (retryData (configure input) (attemptTicks input.2).length word)))).val) := by
  unfold configuredOutput
  rw [show ((retryData (configure input) (attemptTicks input.2).length word).2).take (attemptTicks input.2).length=
      (retryData (configure input) (attemptTicks input.2).length word).2 by simp [retryData]]
  exact output_resolve _

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule60

/- Helper module Solutions.RegevBridgeGaussianWindowCountable. -/
section P2MDyadicModule61

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics FiniteConvolutionProgram

open scoped BigOperators Classical

noncomputable section

theorem indexed_retained_sum (width : ℝ) (center : ℚ) (cutoff : ℕ) :
    (∑' value : ℤ,centeredRetainedWeight width center cutoff value)=
      ∑ index : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff index) := by
  rw [centeredRetainedWeight_sum]
  have h := (windowIndexEquiv cutoff).sum_comp (fun offset => centeredWindowMass width center cutoff offset)
  rw [←h]
  apply Finset.sum_congr rfl
  intro index _
  unfold centeredWindowMass
  have hp : centeredGaussianAnchor center+(windowIndexEquiv cutoff index : ℤ)=windowPoint center cutoff index := by
    simp only [windowIndexEquiv,Equiv.coe_fn_mk,windowPoint]
    ring
  rw [hp]

/-- The finite indexed window law is exactly the normalized countable
Gaussian weight retained in that actual translated integer interval. -/
theorem windowLaw_massOn (width : ℝ) (center : ℚ) (cutoff : ℕ) (value : ℤ) :
    FiniteDist.massOn (windowLaw width center cutoff) (windowPoint center cutoff) value=
      centeredRetainedWeight width center cutoff value/(∑' point : ℤ,centeredRetainedWeight width center cutoff point) := by
  rw [indexed_retained_sum]
  simp only [FiniteDist.massOn,windowLaw,FiniteDist.normalize]
  have hterm (index : Fin (2*cutoff+1)) :
      (if windowPoint center cutoff index=value then
        shiftedWeight width center (windowPoint center cutoff index)/(∑ selected : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff selected)) else 0)=
      (if windowPoint center cutoff index=value then shiftedWeight width center (windowPoint center cutoff index) else 0)/
        (∑ selected : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff selected)) := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [←Finset.sum_div]
  rw [windowPoint_sum center cutoff (fun point => if point=value then shiftedWeight width center point else 0)]
  congr 1
  rw [Finset.sum_ite_eq']
  unfold centeredRetainedWeight
  by_cases hinside : value-centeredGaussianAnchor center ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · have hw : value ∈ Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ)) (centeredGaussianAnchor center+(cutoff : ℤ)) := by
      simp only [Finset.mem_Icc] at hinside ⊢
      omega
    simp only [hinside,hw,ite_true]
  · have hw : value ∉ Finset.Icc (centeredGaussianAnchor center-(cutoff : ℤ)) (centeredGaussianAnchor center+(cutoff : ℤ)) := by
      intro membership
      apply hinside
      simp only [Finset.mem_Icc] at membership ⊢
      omega
    simp only [hinside,hw,ite_false]

/-- Full integer-line truncation error with no extra width prefactor.
This is needed for a width that may be exponential in input bit length. -/
theorem window_countable_totalVariation (width : ℝ) (center : ℚ) (cutoff : ℕ) (hwidth : 1 ≤ width) :
    (∑' value : ℤ,|FiniteDist.massOn (windowLaw width center cutoff) (windowPoint center cutoff) value-
      (roundingPMF width (zero_lt_one.trans_le hwidth) center value).toReal|)/2 ≤ tailEnvelope width cutoff := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hs := summable_shiftedWeight width center hw
  have hp : 0 < ∑' value : ℤ,centeredRetainedWeight width center cutoff value := by
    rw [indexed_retained_sum]
    exact windowMass_pos width center cutoff
  have h := normalized_deleted_total_variation (shiftedWeight width center) (centeredRetainedWeight width center cutoff)
    (fun _ => Real.exp_nonneg _) (centeredRetainedWeight_nonneg width center cutoff)
    (centeredRetainedWeight_le width center cutoff) hs hp
  have he := outsideWindowMass_eq 1 width hw center cutoff
  rw [retainedResidue_sum] at he
  simp_rw [roundingPMF_toReal] at he
  rw [←Finset.sum_div] at he
  have hequal : ((∑' value : ℤ,shiftedWeight width center value)-
      (∑' value : ℤ,centeredRetainedWeight width center cutoff value))/(∑' value : ℤ,shiftedWeight width center value)=
      outsideWindowMass width hw center cutoff := by
    rw [he,indexed_retained_sum]
    change (theta width center-(∑ index : Fin (2*cutoff+1),shiftedWeight width center (windowPoint center cutoff index)))/theta width center=_
    field_simp [(theta_pos width center hw).ne']
  rw [hequal] at h
  have hfinal := h.trans (outsideWindowMass_le width hwidth center cutoff)
  simp_rw [windowLaw_massOn,roundingPMF_toReal]
  exact hfinal

/-- Finite deterministic postprocessing contracts L1 even when its target
is the whole countable integer line, rather than a finite alphabet. -/
theorem massOn_l1_le {Input Source : Type*} [Fintype Input]
    (first second : FiniteDist Input) (image : Input → Source) :
    (∑' output : Source,|FiniteDist.massOn first image output-FiniteDist.massOn second image output|) ≤
      ∑ input,|first.weight input-second.weight input| := by
  let majorant := fun output : Source => ∑ input : Input,if image input=output then |first.weight input-second.weight input| else 0
  have hs : HasSum majorant (∑ input : Input,|first.weight input-second.weight input|) := by
    have h := hasSum_sum (s:=(Finset.univ : Finset Input))
      (fun input _ => hasSum_ite_eq (image input) |first.weight input-second.weight input|)
    simpa only [majorant,eq_comm] using h
  have hpoint (output : Source) : |FiniteDist.massOn first image output-FiniteDist.massOn second image output| ≤ majorant output := by
    simp only [FiniteDist.massOn,←Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro input _
    split_ifs <;> simp
  have hactual := ((FiniteDist.massOn_summable first image).sub (FiniteDist.massOn_summable second image)).norm
  have h := hactual.tsum_le_tsum (fun output => by simpa only [Real.norm_eq_abs] using hpoint output) hs.summable
  simpa only [Real.norm_eq_abs,hs.tsum_eq] using h

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule61

/- Helper module Solutions.RegevBridgeWideGaussianSampler. -/
section P2MDyadicModule62

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics BinaryArithmetic GaussianProjection GaussianProjection.CosetGeometry

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

abbrev PublicRequest := (ℚ × ℚ) × List Unit

def publicConfigure (input : PublicRequest) : ConfigureRequest := (input.1,([(),()]++input.2,input.2))

@[fun_prop] theorem publicConfigure_poly : Poly publicConfigure := by unfold publicConfigure;fun_prop

def pointInput (input : PublicRequest) : PointRequest := configure (publicConfigure input)

@[fun_prop] theorem pointInput_poly : Poly pointInput := by unfold pointInput;fun_prop

/-- All loop bounds are derived by the actual program from public unary
accuracy controls and the binary variance representation. -/
def sample (input : PublicRequest × List (List Bool × List Bool)) : ℤ :=
  configuredOutput (publicConfigure input.1,input.2)

@[fun_prop] theorem sample_poly : Poly sample := by unfold sample;fun_prop

def trialBitTicks (input : PointRequest) : List Unit :=
  (Nat.bits (intervalCount input)).map (fun _ => ())++input.2.2

@[fun_prop] theorem trialBitTicks_poly : Poly trialBitTicks := by unfold trialBitTicks;fun_prop

/-- A genuine polynomial-time generator materializes exactly the number
of fair bits used by every independent bounded trial, without listing the
exponentially wide integer output interval. -/
def randomTicks (input : PublicRequest) : List Unit :=
  (attemptTicks (publicConfigure input).2).flatMap (fun _ => trialBitTicks (pointInput input))

@[fun_prop] theorem randomTicks_poly : Poly randomTicks := by unfold randomTicks;fun_prop

theorem randomTicks_length (input : PublicRequest) :
    (randomTicks input).length=(attemptTicks (publicConfigure input).2).length*
      (Nat.size (intervalCount (pointInput input))+(pointInput input).2.2.length) := by
  simp only [randomTicks,trialBitTicks,List.length_flatMap,List.map_const',List.sum_replicate,List.length_append,
    List.length_replicate,Nat.size_eq_bits_len,nsmul_eq_mul,Nat.cast_id]

noncomputable section

open scoped Classical

def sampleLaw (input : PublicRequest) : FiniteDist (Fin (intervalCount (pointInput input))) :=
  (retryLaw (pointInput input) (attemptTicks (publicConfigure input).2).length).map (resolveIndex (pointInput input))

def integerMass (input : PublicRequest) : ℤ → ℝ :=
  FiniteDist.massOn (sampleLaw input) (fun index => point (pointInput input,index.val))

/-- Exact finite tapes drive the same literal integer program. -/
theorem sample_exact (input : PublicRequest)
    (word : Fin (attemptTicks (publicConfigure input).2).length → TrialRandom (pointInput input)) :
    sample (input,(retryData (pointInput input) (attemptTicks (publicConfigure input).2).length word).2)=
      point (pointInput input,(resolveIndex (pointInput input)
        (decodeProposal (intervalCount (pointInput input))
          (retry (retryData (pointInput input) (attemptTicks (publicConfigure input).2).length word)))).val) := by
  exact configuredOutput_exact (publicConfigure input) word

/-- The final infinite Gaussian tail estimate has no prefactor depending
on the numerical width. -/
theorem scaled_tail_bound (input : PointRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(variance input : ℝ)) :
    tailEnvelope width (radius input) ≤ 6*Real.exp (-Real.pi*(input.2.1.length : ℝ)^2/2) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hscale := (scale_width_bounds input width hwidth hsquare).1
  have hrad : (input.2.1.length : ℝ)*width ≤ (radius input : ℝ) := by
    simpa only [radius,Nat.cast_mul] using mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg input.2.1.length)
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (input.2.1.length : ℝ)*width) (Nat.cast_nonneg (radius input))).mpr hrad
  have hratio := div_le_div_of_nonneg_right hsq (show (0 : ℝ) ≤ 2*width^2 by positivity)
  have heq : ((input.2.1.length : ℝ)*width)^2/(2*width^2)=(input.2.1.length : ℝ)^2/2 := by field_simp
  rw [heq] at hratio
  have hexponent : -Real.pi*(radius input : ℝ)^2/(2*width^2) ≤ -Real.pi*(input.2.1.length : ℝ)^2/2 := by
    calc
      _ = -Real.pi*((radius input : ℝ)^2/(2*width^2)) := by ring
      _ ≤ -Real.pi*((input.2.1.length : ℝ)^2/2) := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr Real.pi_pos.le)
      _ = _ := by ring
  have htail := (VarianceGrid.tailEnvelope_interval (radius input : ℝ) hwidth le_rfl le_rfl).trans (intervalTail_le_six hwidth)
  exact htail.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num))

/-- Complete error against the genuine Gaussian kernel on the entire
integer line, rather than against a finite palette or only residues. -/
theorem sample_totalVariation (input : PublicRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(input.1.1 : ℝ)) :
    (∑' value : ℤ,|integerMass input value-
      (roundingPMF width (zero_lt_one.trans_le hwidth) input.1.2 value).toReal|)/2 ≤
        2/(2 : ℝ)^input.2.length+6*Real.exp (-Real.pi*(input.2.length+2 : ℝ)^2/2) := by
  have hw : 0<width := zero_lt_one.trans_le hwidth
  have hraw : (1 : ℝ) ≤ (input.1.1 : ℝ) := by rw [←hsquare];exact one_le_pow₀ hwidth
  have hq : (1 : ℚ) ≤ input.1.1 := by exact_mod_cast hraw
  have hvar : variance (pointInput input)=input.1.1 := variance_eq (pointInput input) hq
  have hs : width^2=(variance (pointInput input) : ℝ) := by rw [hvar];exact hsquare
  have hk : 2 ≤ (publicConfigure input).2.1.length := by simp [publicConfigure]
  have hf := configured_retry_totalVariation (publicConfigure input) width hwidth hs hk
  change (∑ index : Fin (intervalCount (pointInput input)),|(sampleLaw input).weight index-
      (windowLaw width input.1.2 (radius (pointInput input))).weight index|)/2 ≤ 2/(2 : ℝ)^input.2.length at hf
  have hpoint : (fun index : Fin (intervalCount (pointInput input)) => point (pointInput input,index.val))=
      windowPoint input.1.2 (radius (pointInput input)) := by
    funext index
    exact point_eq_windowPoint (pointInput input) index
  have hm : integerMass input=FiniteDist.massOn (sampleLaw input) (windowPoint input.1.2 (radius (pointInput input))) := by
    unfold integerMass
    rw [hpoint]
  rw [hm]
  let reference := windowLaw width input.1.2 (radius (pointInput input))
  let image := windowPoint input.1.2 (radius (pointInput input))
  have hfinite := massOn_l1_le (sampleLaw input) reference image
  have hgaussian := window_countable_totalVariation width input.1.2 (radius (pointInput input)) hwidth
  have hfirst : Summable (fun value : ℤ => |FiniteDist.massOn (sampleLaw input) image value-FiniteDist.massOn reference image value|) := by
    simpa only [Real.norm_eq_abs] using ((FiniteDist.massOn_summable (sampleLaw input) image).sub (FiniteDist.massOn_summable reference image)).norm
  have hsecond : Summable (fun value : ℤ => |FiniteDist.massOn reference image value-(roundingPMF width hw input.1.2 value).toReal|) := by
    simpa only [Real.norm_eq_abs] using ((FiniteDist.massOn_summable reference image).sub (summable_roundingMass width hw input.1.2)).norm
  have hactual : Summable (fun value : ℤ => |FiniteDist.massOn (sampleLaw input) image value-(roundingPMF width hw input.1.2 value).toReal|) := by
    simpa only [Real.norm_eq_abs] using ((FiniteDist.massOn_summable (sampleLaw input) image).sub (summable_roundingMass width hw input.1.2)).norm
  have htriangle := hactual.tsum_le_tsum (fun value =>
    abs_sub_le (FiniteDist.massOn (sampleLaw input) image value) (FiniteDist.massOn reference image value)
      (roundingPMF width hw input.1.2 value).toReal) (hfirst.add hsecond)
  rw [hfirst.tsum_add hsecond] at htriangle
  have htail := scaled_tail_bound (pointInput input) width hwidth hs
  have hlen : ((pointInput input).2.1.length : ℝ)=(input.2.length+2 : ℝ) := by
    simp only [pointInput,configure,publicConfigure,List.length_append,List.length_cons,List.length_nil]
    push_cast
    ring
  rw [hlen] at htail
  change (∑' value : ℤ,|FiniteDist.massOn (sampleLaw input) image value-(roundingPMF width hw input.1.2 value).toReal|)/2 ≤ _
  linarith

def sampleError (precision : ℕ) : ℝ :=
  2/(2 : ℝ)^precision+6*Real.exp (-Real.pi*((precision : ℝ)+2)^2/2)

/-- Explicit final accuracy interface for the actual binary sampler,
including finite rejection exhaustion and the omitted infinite tail. -/
theorem sample_full_error (input : PublicRequest) (width : ℝ) (hwidth : 1 ≤ width)
    (hsquare : width^2=(input.1.1 : ℝ)) :
    (∑' value : ℤ,|integerMass input value-
      (roundingPMF width (zero_lt_one.trans_le hwidth) input.1.2 value).toReal|)/2 ≤ sampleError input.2.length :=
  sample_totalVariation input width hwidth hsquare

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule62

/- Helper module Solutions.RegevBridgeWideGaussianChannel. -/
section P2MDyadicModule63

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

noncomputable section

/-- The literal binary sampler retains its whole countable error through
any finite physical channel, including a channel reading other coordinates. -/
theorem sample_channel_tv {Output : Type*} [Fintype Output] (input : PublicRequest)
    (width : ℝ) (hwidth : 1 ≤ width) (hsquare : width^2=(input.1.1 : ℝ))
    (channel : ℤ → FiniteDist Output) :
    FiniteDist.TVBound ((sampleLaw input).mix (fun index => channel (point (pointInput input,index.val))))
      (FiniteDist.countableMix (centeredScalarMass width input.1.2)
        (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hwidth))
        (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hwidth))
        (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hwidth)) channel)
      (sampleError input.2.length) := by
  have herror := sample_full_error input width hwidth hsquare
  apply FiniteDist.TVBound.symm
  apply FiniteDist.countableMix_massOn_tvBound (centeredScalarMass width input.1.2)
    (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hwidth))
    (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hwidth))
    (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hwidth))
    (sampleLaw input) (fun index => point (pointInput input,index.val)) channel
    (sampleError input.2.length)
  simpa only [roundingPMF_toReal,centeredScalarMass,integerMass,abs_sub_comm] using herror

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule63

/- Helper module Solutions.RegevBridgeRationalGramSchmidt. -/
section P2MDyadicModule64

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

theorem realVec_zero {dimension : ℕ} : realVec (0 : QVector dimension)=0 := by ext index;simp [realVec]

theorem realVec_add {dimension : ℕ} (left right : QVector dimension) : realVec (left+right)=realVec left+realVec right := by
  ext index
  exact Rat.cast_add _ _

theorem realVec_sub {dimension : ℕ} (left right : QVector dimension) : realVec (left-right)=realVec left-realVec right := by
  ext index
  exact Rat.cast_sub _ _

theorem realVec_smul {dimension : ℕ} (scalar : ℚ) (vector : QVector dimension) :
    realVec (scalar • vector)=(scalar : ℝ) • realVec vector := by
  ext index
  exact Rat.cast_mul _ _

theorem realVec_list_sum {dimension : ℕ} (vectors : List (QVector dimension)) :
    realVec vectors.sum=(vectors.map realVec).sum := by
  induction vectors with
  | nil => exact realVec_zero
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,realVec_add,ih]

theorem innerQ_real {dimension : ℕ} (left right : QVector dimension) :
    (innerQ left right : ℝ)=inner ℝ (realVec left) (realVec right) := by
  unfold innerQ realVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

theorem cache_length {dimension count : ℕ} (vectors : Fin count → QVector dimension) (steps : ℕ) :
    (cache vectors steps).length=steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cache,List.length_append,List.length_singleton,ih]

def squaredNorm {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : ℚ := innerQ (orthogonal vectors index) (orthogonal vectors index)

noncomputable section

theorem projection_real {dimension : ℕ} (orthogonal current : QVector dimension) :
    realVec (projection orthogonal current)=
      (inner ℝ (realVec orthogonal) (realVec current)/‖realVec orthogonal‖^2) • realVec orthogonal := by
  rw [projection,realVec_smul,Rat.cast_div,innerQ_real,innerQ_real,real_inner_self_eq_norm_sq]

theorem orthogonalStep_real {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) :
    realVec (orthogonalStep previous current)=realVec current-
      ((previous.map realVec).map (fun orthogonal => (inner ℝ orthogonal (realVec current)/‖orthogonal‖^2) • orthogonal)).sum := by
  rw [orthogonalStep,realVec_sub,realVec_list_sum]
  simp only [List.map_map,Function.comp_def,projection_real]

private theorem sum_Iio_fin {count : ℕ} {Value : Type*} [AddCommMonoid Value]
    (index : Fin count) (function : Fin count → Value) :
    (∑ previous ∈ Finset.Iio index,function previous)=
      ∑ previous : Fin index.val,function ⟨previous.val,previous.isLt.trans index.isLt⟩ := by
  classical
  refine Finset.sum_bij (fun previous membership =>
    (⟨previous.val,show previous < index from Finset.mem_Iio.mp membership⟩ : Fin index.val)) ?_ ?_ ?_ ?_
  · intro previous membership
    exact Finset.mem_univ _
  · intro first hfirst second hsecond hequal
    exact Fin.ext (congrArg (fun value : Fin index.val => value.val) hequal)
  · intro previous membership
    refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,Finset.mem_Iio.mpr (show (⟨previous.val,previous.isLt.trans index.isLt⟩ : Fin count) < index from previous.isLt),?_⟩
    rfl
  · intro previous membership
    congr 1

/-- Every materialized rational cache prefix is exactly the ordinary real
Gram--Schmidt prefix after the actual rational-to-real embedding. -/
theorem cache_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (cache vectors steps).map realVec=List.ofFn (fun index : Fin steps =>
      gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hsteps index)) := by
  classical
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps<count := by omega
    let index : Fin count := ⟨steps,hstep⟩
    rw [cache,List.map_append,List.map_singleton,ih hprevious,List.ofFn_succ_last]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext previous
      congr 1
    · apply congrArg (fun value : Space dimension => [value])
      change realVec (orthogonalStep (cache vectors steps) (if h : steps<count then vectors ⟨steps,h⟩ else 0))=
        gramSchmidt ℝ (fun position => realVec (vectors position)) index
      rw [dif_pos hstep,orthogonalStep_real,ih hprevious]
      simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
      have h := gramSchmidt_def'' ℝ (fun position => realVec (vectors position)) index
      rw [sum_Iio_fin] at h
      have hequal : (∑ previous : Fin steps,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous)‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) (Fin.castLE hprevious previous))=
          ∑ previous : Fin index.val,
          (inner ℝ (gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩)
            (realVec (vectors index))/‖gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩‖^2) •
              gramSchmidt ℝ (fun position => realVec (vectors position)) ⟨previous.val,previous.isLt.trans index.isLt⟩ := rfl
      rw [hequal]
      exact sub_eq_iff_eq_add.mpr h

theorem orthogonal_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    realVec (orthogonal vectors index)=gramSchmidt ℝ (fun position => realVec (vectors position)) index := by
  have h := congrArg (fun values : List (Space dimension) => values.getD index.val (realVec (0 : QVector dimension)))
    (cache_real vectors count (le_refl count))
  rw [List.getD_map] at h
  simpa [orthogonal,index.isLt] using h

theorem squaredNorm_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    (squaredNorm vectors index : ℝ)=‖gramSchmidt ℝ (fun position => realVec (vectors position)) index‖^2 := by
  rw [squaredNorm,innerQ_real,orthogonal_real,real_inner_self_eq_norm_sq]

theorem squaredNorm_pos {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun position => realVec (vectors position)))
    (index : Fin count) : 0 < squaredNorm vectors index := by
  have h := sq_pos_of_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero index independent))
  rw [←squaredNorm_real] at h
  exact_mod_cast h

theorem orthogonal_pairwise {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (first second : Fin count) (different : first ≠ second) :
    innerQ (orthogonal vectors first) (orthogonal vectors second)=0 := by
  have h := gramSchmidt_orthogonal ℝ (fun position => realVec (vectors position)) different
  rw [←orthogonal_real,←orthogonal_real,←innerQ_real] at h
  exact_mod_cast h

/-- Orthogonal projection only decreases the original column's square norm. -/
theorem gramSchmidt_norm_sq_le {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    ‖gramSchmidt ℝ vectors index‖^2 ≤ ‖vectors index‖^2 := by
  let orthogonal := gramSchmidt ℝ vectors
  have heq : inner ℝ (orthogonal index) (vectors index)=inner ℝ (orthogonal index) (orthogonal index) := by
    conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
    simp only [RCLike.ofReal_real_eq_id,id_eq]
    rw [inner_add_right]
    suffices inner ℝ (orthogonal index)
        (∑ previous ∈ Finset.Iio index,
          (inner ℝ (orthogonal previous) (vectors index)/‖orthogonal previous‖^2) • orthogonal previous)=0 by
      change inner ℝ (orthogonal index) (orthogonal index)+_=inner ℝ (orthogonal index) (orthogonal index)
      rw [this,add_zero]
    simp only [inner_sum,inner_smul_right]
    apply Finset.sum_eq_zero
    intro previous membership
    rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]
  have hnonneg := (real_inner_self_nonneg (x := vectors index-orthogonal index))
  rw [inner_sub_sub_self,real_inner_comm (orthogonal index) (vectors index),heq,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hnonneg
  change ‖orthogonal index‖^2 ≤ _
  linarith

theorem squaredNorm_le {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) :
    squaredNorm vectors index ≤ innerQ (vectors index) (vectors index) := by
  have h := gramSchmidt_norm_sq_le (fun position => realVec (vectors position)) index
  rw [←squaredNorm_real,←real_inner_self_eq_norm_sq,←innerQ_real] at h
  exact_mod_cast h

end

noncomputable section

theorem inputVectors_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (column : Fin dimension) :
    realVec (inputVectors basis column)=IntegerBasis.realBasis basis hdet column := by
  rw [IntegerBasis.realBasis_apply]
  ext row
  simp [realVec,inputVectors]

theorem inputVectors_independent {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    LinearIndependent ℝ (fun position => realVec (inputVectors basis position)) := by
  simpa only [inputVectors_real basis hdet] using (IntegerBasis.realBasis basis hdet).linearIndependent

theorem input_squaredNorm_pos {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (index : Fin dimension) :
    0 < squaredNorm (inputVectors basis) index :=
  squaredNorm_pos _ (inputVectors_independent basis hdet) index

end

def entryMass {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) : ℚ :=
  ∑ row,∑ column,|(basis row column : ℚ)|

def initialWidth {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) : ℚ := base*(1+entryMass basis)

def initialVariance {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) (index : Fin dimension) : ℚ :=
  (initialWidth basis base)^2/squaredNorm (inputVectors basis) index

theorem entryMass_nonneg {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    0 ≤ entryMass basis := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem input_column_norm_le {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) :
    innerQ (inputVectors basis index) (inputVectors basis index) ≤ (1+entryMass basis)^2 := by
  have hsum : (∑ row,|(basis row index : ℚ)|) ≤ entryMass basis := by
    apply Finset.sum_le_sum
    intro row _
    exact Finset.single_le_sum (fun column _ => abs_nonneg (basis row column : ℚ)) (Finset.mem_univ index)
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
    (f:=fun row => |(basis row index : ℚ)|) (fun row _ => abs_nonneg _)
  simp only [sq_abs] at hsq
  change (∑ row,(basis row index : ℚ)*(basis row index : ℚ)) ≤ _
  have hnonneg := entryMass_nonneg basis
  have hcolnonneg : 0 ≤ ∑ row,|(basis row index : ℚ)| := Finset.sum_nonneg (fun row _ => abs_nonneg _)
  simp only [←sq] at *
  nlinarith

theorem initialVariance_lower {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (index : Fin dimension) :
    base^2 ≤ initialVariance basis base index := by
  rw [initialVariance,le_div_iff₀ (input_squaredNorm_pos basis hdet index)]
  have h := (squaredNorm_le (inputVectors basis) index).trans (input_column_norm_le basis index)
  calc
    base^2*squaredNorm (inputVectors basis) index ≤ base^2*(1+entryMass basis)^2 :=
      mul_le_mul_of_nonneg_left h (sq_nonneg base)
    _ = (initialWidth basis base)^2 := by unfold initialWidth;ring

noncomputable section

theorem initialWidth_pos {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) (hbase : 0 < base) : 0 < initialWidth basis base := by
  exact mul_pos hbase (by have h := entryMass_nonneg basis;linarith)

/-- The original, possibly poorly conditioned input basis admits rational
scalar variances above every requested public base squared. -/
theorem initial_scalar_width_lower {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 ≤ base) (index : Fin dimension) :
    (base : ℝ) ≤ Real.sqrt (initialVariance basis base index : ℝ) := by
  have h := initialVariance_lower basis hdet base index
  have hreal : (base : ℝ)^2 ≤ (initialVariance basis base index : ℝ) := by exact_mod_cast h
  exact (Real.le_sqrt (by exact_mod_cast hbase) ((sq_nonneg _).trans hreal)).mpr hreal

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule64

/- Helper module Solutions.RegevBridgeRationalGramSchmidtGeometry. -/
section P2MDyadicModule65

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

/-- Exact rational upper-triangular change from original input columns to
its materialized orthogonal cache. -/
def upper {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) : ℚ :=
  innerQ (orthogonal vectors row) (vectors column)/squaredNorm vectors row

noncomputable section

theorem inner_gramSchmidt_original {dimension count : ℕ} (vectors : Fin count → Space dimension)
    (index : Fin count) :
    inner ℝ (gramSchmidt ℝ vectors index) (vectors index)=‖gramSchmidt ℝ vectors index‖^2 := by
  conv_lhs => arg 3; rw [gramSchmidt_def'' ℝ vectors index]
  simp only [RCLike.ofReal_real_eq_id,id_eq]
  rw [inner_add_right]
  suffices inner ℝ (gramSchmidt ℝ vectors index)
      (∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ vectors previous) (vectors index)/‖gramSchmidt ℝ vectors previous‖^2) •
          gramSchmidt ℝ vectors previous)=0 by
    rw [this,add_zero,real_inner_self_eq_norm_sq]
  simp only [inner_sum,inner_smul_right]
  apply Finset.sum_eq_zero
  intro previous membership
  rw [gramSchmidt_orthogonal ℝ vectors (Finset.mem_Iio.mp membership).ne',mul_zero]

theorem upper_real {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) :
    (upper vectors row column : ℝ)=
      inner ℝ (gramSchmidt ℝ (fun index => realVec (vectors index)) row) (realVec (vectors column))/
        ‖gramSchmidt ℝ (fun index => realVec (vectors index)) row‖^2 := by
  rw [upper,Rat.cast_div,innerQ_real,orthogonal_real,squaredNorm_real]

theorem upper_diagonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (index : Fin count) :
    upper vectors index index=1 := by
  have hreal : (upper vectors index index : ℝ)=1 := by
    rw [upper_real,inner_gramSchmidt_original]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero index independent)))
  exact_mod_cast hreal

theorem upper_triangular {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (row column : Fin count) (before : column < row) :
    upper vectors row column=0 := by
  have hreal : (upper vectors row column : ℝ)=0 := by
    rw [upper_real,gramSchmidt_inv_triangular ℝ (fun index => realVec (vectors index)) before,zero_div]
  exact_mod_cast hreal

/-- The finite cached coefficient matrix reconstructs each original column
using the actual orthogonal vectors, including its diagonal coefficient. -/
theorem column_decomposition {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index))) (column : Fin count) :
    realVec (vectors column)=∑ row,(upper vectors row column : ℝ) • realVec (orthogonal vectors row) := by
  classical
  let orthogonalReal := gramSchmidt ℝ (fun index => realVec (vectors index))
  have hterm (row : Fin count) : (upper vectors row column : ℝ) • orthogonalReal row=
      (if row=column then orthogonalReal column else 0)+
        (if row < column then (upper vectors row column : ℝ) • orthogonalReal row else 0) := by
    by_cases hequal : row=column
    · subst row
      simp [upper_diagonal vectors independent]
    · by_cases hbefore : row < column
      · simp [hequal,hbefore]
      · have hafter : column < row := lt_of_le_of_ne (le_of_not_gt hbefore) (Ne.symm hequal)
        simp [hequal,hbefore,upper_triangular vectors row column hafter]
  have hfilter : (∑ row,if row < column then (upper vectors row column : ℝ) • orthogonalReal row else 0)=
      ∑ row ∈ Finset.Iio column,(upper vectors row column : ℝ) • orthogonalReal row := by
    rw [←Finset.sum_filter]
    congr 1
    ext row
    simp
  simp only [orthogonal_real]
  change realVec (vectors column)=∑ row,(upper vectors row column : ℝ) • orthogonalReal row
  have hsum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun row _ => hterm row)
  rw [hsum,Finset.sum_add_distrib,Finset.sum_ite_eq',hfilter]
  simp only [Finset.mem_univ,if_true]
  simpa only [upper_real,orthogonalReal,RCLike.ofReal_real_eq_id,id_eq] using
    (gramSchmidt_def'' ℝ (fun index => realVec (vectors index)) column)

theorem combination_decomposition {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index)))
    (coefficients : Fin count → ℝ) :
    (∑ column,coefficients column • realVec (vectors column))=
      ∑ row,(Matrix.mulVec (fun row column => (upper vectors row column : ℝ)) coefficients row) •
        realVec (orthogonal vectors row) := by
  simp_rw [column_decomposition vectors independent,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  rw [Matrix.mulVec,dotProduct,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro column _
  rw [mul_comm]

/-- The original input lattice norm is exactly the diagonal orthogonal
quadratic form of the rational upper-triangular coordinates. -/
theorem combination_norm_sq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (independent : LinearIndependent ℝ (fun index => realVec (vectors index)))
    (coefficients : Fin count → ℝ) :
    ‖∑ column,coefficients column • realVec (vectors column)‖^2=
      ∑ row,(squaredNorm vectors row : ℝ)*
        (Matrix.mulVec (fun row column => (upper vectors row column : ℝ)) coefficients row)^2 := by
  classical
  rw [combination_decomposition vectors independent,←real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,RCLike.conj_to_real]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.sum_eq_single row]
  · rw [←innerQ_real]
    change _*( _*(squaredNorm vectors row : ℝ))=_
    ring
  · intro other _ different
    rw [←innerQ_real,orthogonal_pairwise vectors other row different]
    simp
  · simp

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule65

/- Helper module Solutions.RegevBridgeInitialGaussianChain. -/
section P2MDyadicModule66

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

open AFT.GaussianSource AFT.RationalNumerics RegevLWE.GaussConv

/-- The original basis's rational Klein chain uses the actual cached
squared norms and conditional centers from its exact rational upper factor. -/
def initialChain {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (base : ℚ) : RationalGaussianChain dimension :=
  upperRationalGaussianChain dimension (initialVariance basis base) 0 (upper (inputVectors basis))

noncomputable section

theorem latticePoint_sum {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (word : Fin dimension → ℤ) :
    latVec basis word=∑ column,(word column : ℝ) • realVec (inputVectors basis column) := by
  ext row
  simp only [latVec,Matrix.mulVec,dotProduct,realVec,inputVectors,WithLp.ofLp_sum,
    WithLp.ofLp_smul,WithLp.ofLp_toLp,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Int.cast_sum,Int.cast_mul,
    Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro column _
  exact mul_comm _ _

theorem initialChain_wide {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 ≤ base) :
    (initialChain basis base).realChain.Wide (base : ℝ) := by
  rw [initialChain,upperRationalGaussianChain_real]
  exact upperGaussianChain_wide _ _ _ _ _ (initial_scalar_width_lower basis hdet base hbase)

/-- The chain's unnormalized correlated weight is exactly the original
lattice Gaussian at the chosen public initial width. -/
theorem initialChain_weight {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 < base) (word : Fin dimension → ℤ) :
    (initialChain basis base).realChain.weight word=
      rho (initialWidth basis base : ℝ) (latVec basis word) := by
  have independent := inputVectors_independent basis hdet
  have hvariance (index : Fin dimension) : 0 < (initialVariance basis base index : ℝ) := by
    have h := initialVariance_lower basis hdet base index
    have hp : 0 < base^2 := sq_pos_of_pos hbase
    exact_mod_cast hp.trans_le h
  have hwidth : (initialWidth basis base : ℝ) ≠ 0 := by
    exact_mod_cast (initialWidth_pos basis base hbase).ne'
  rw [initialChain,upperRationalGaussianChain_real,upperGaussianChain_weight]
  · simp only [Pi.zero_apply,Rat.cast_zero,sub_zero,Real.sq_sqrt (hvariance _).le]
    unfold rho
    congr 1
    have hnorm := combination_norm_sq (inputVectors basis) independent (fun index => (word index : ℝ))
    rw [←latticePoint_sum] at hnorm
    rw [hnorm]
    simp only [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro index _
    rw [initialVariance,Rat.cast_div,Rat.cast_pow]
    field_simp
  · intro row column before
    exact_mod_cast upper_triangular (inputVectors basis) row column before
  · intro index
    exact_mod_cast upper_diagonal (inputVectors basis) independent index

/-- Reindexing by the original integral basis identifies the complete
chain normalizer with the genuine lattice Gaussian normalizer. -/
theorem initialChain_sum {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 < base) :
    (∑' word,(initialChain basis base).realChain.weight word)=
      rhoCoset (initialWidth basis base : ℝ) (IntegerBasis.inputLattice basis hdet) 0 := by
  unfold rhoCoset
  rw [←(IntegerBasis.integerBasis basis hdet).equivFun.toEquiv.symm.tsum_eq]
  apply tsum_congr
  intro word
  rw [initialChain_weight basis hdet base hbase]
  change _=rho (initialWidth basis base : ℝ)
    (((IntegerBasis.integerBasis basis hdet).equivFun.symm word : Space dimension)+0)
  rw [IntegerBasis.coefficient_point,add_zero]

theorem initialChain_normalizedMass {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 < base) (word : Fin dimension → ℤ) :
    (initialChain basis base).realChain.normalizedMass word=
      GaussianProjection.cosetMass (IntegerBasis.inputLattice basis hdet) 0 (initialWidth basis base)
        ((IntegerBasis.integerBasis basis hdet).equivFun.symm word) := by
  rw [GaussianChain.normalizedMass,initialChain_weight basis hdet base hbase,
    initialChain_sum basis hdet base hbase,GaussianProjection.cosetMass_formula,
    IntegerBasis.coefficient_point,add_zero]

/-- This error compares the complete correlated sequential law with the
true lattice Gaussian. Conditional centers depend on all realized tail
coordinates, and both normalizers remain present. -/
theorem initial_sequential_lattice_tv {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 0 < base) (error : ℝ)
    (herror : 0 ≤ error) (herrorOne : error ≤ 1)
    (htheta : thetaError (base : ℝ) ≤ error) (hsmall : (1+error)^dimension-1 < 1) :
    (∑' word,|GaussianProjection.cosetMass (IntegerBasis.inputLattice basis hdet) 0 (initialWidth basis base)
        ((IntegerBasis.integerBasis basis hdet).equivFun.symm word)-
      (initialChain basis base).realChain.sequentialMass word|)/2 ≤
      ((1+error)^dimension-1)/(1-((1+error)^dimension-1)) := by
  have hbaseReal : (0 : ℝ) < base := by exact_mod_cast hbase
  have h := (initialChain basis base).realChain.sequential_total_variation (base : ℝ) error hbaseReal
    herror herrorOne htheta (initialChain_wide basis hdet base hbase.le) hsmall
  simpa only [initialChain_normalizedMass basis hdet base hbase] using h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule66

/- Helper module Solutions.RegevBridgeWideGaussianChain. -/
section P2MDyadicModule67

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

noncomputable section

/-- Literal finite-output law of fresh bounded native scalar calls. Each
head center is computed from the entire already materialized tail. -/
def chainChannel {Output : Type*} [Fintype Output] (accuracy : List Unit) :
    {count : ℕ} → RationalGaussianChain count →
      ((Fin count → ℤ) → FiniteDist Output) → FiniteDist Output
  | 0,.nil,channel => channel Fin.elim0
  | _+1,.cons variance center tail,channel => chainChannel accuracy tail
      (fun word => (sampleLaw ((variance,center word),accuracy)).mix
        (fun index => channel (Fin.cons (point (pointInput ((variance,center word),accuracy),index.val)) word)))

/-- A shared, correlated downstream finite channel does not amplify the
uniform error across the actual recursive sampling law. -/
theorem chainChannel_right_tv {Output : Type*} [Fintype Output] {count : ℕ}
    (chain : RationalGaussianChain count) (accuracy : List Unit)
    (first second : (Fin count → ℤ) → FiniteDist Output) (error : ℝ)
    (herror : ∀ word,FiniteDist.TVBound (first word) (second word) error) :
    FiniteDist.TVBound (chainChannel accuracy chain first) (chainChannel accuracy chain second) error := by
  induction chain with
  | nil => exact herror Fin.elim0
  | @cons count variance center tail ih =>
    apply ih
    intro word
    exact FiniteDist.TVBound.mix_right _ (fun index => herror _)

/-- Whole-word accuracy of the real finite scalar-call law. No independence
of final coordinates, or equality of single-coordinate marginals, is used. -/
theorem chainChannel_accuracy {Output : Type*} [Fintype Output] {count : ℕ}
    (chain : RationalGaussianChain count) (hwide : chain.realChain.Wide 1)
    (accuracy : List Unit) (channel : (Fin count → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound (chainChannel accuracy chain channel) (chain.exactChannel hwide channel)
      (count*sampleError accuracy.length) := by
  induction chain with
  | nil =>
    have he : RationalGaussianChain.nil.exactChannel hwide channel=channel Fin.elim0 := by
      ext output
      change (∑' word : Fin 0 → ℤ,1*(channel word).weight output)=(channel Fin.elim0).weight output
      simp only [one_mul,tsum_fintype,Fintype.sum_unique]
      have he (word : Fin 0 → ℤ) : word=Fin.elim0 := by funext index;exact Fin.elim0 index
      exact congrArg (fun word => (channel word).weight output) (he _)
    rw [he]
    intro event
    simp [chainChannel]
  | @cons count variance center tail ih =>
    let actual (word : Fin count → ℤ) := FiniteDist.countableMix
      (centeredScalarMass (Real.sqrt (variance : ℝ)) (center word))
      (centeredScalarMass_nonneg _ _ (zero_lt_one.trans_le hwide.1))
      (centeredScalarMass_summable _ _ (zero_lt_one.trans_le hwide.1))
      (centeredScalarMass_sum _ _ (zero_lt_one.trans_le hwide.1))
      (fun first => channel (Fin.cons first word))
    let computed (word : Fin count → ℤ) :=
      (sampleLaw ((variance,center word),accuracy)).mix
        (fun index => channel (Fin.cons (point (pointInput ((variance,center word),accuracy),index.val)) word))
    have hstep (word : Fin count → ℤ) : FiniteDist.TVBound (computed word) (actual word)
        (sampleError accuracy.length) := by
      exact sample_channel_tv ((variance,center word),accuracy) (Real.sqrt (variance : ℝ)) hwide.1
        (Real.sq_sqrt (Real.sqrt_pos.mp (zero_lt_one.trans_le hwide.1)).le)
        (fun first => channel (Fin.cons first word))
    have hfirst := chainChannel_right_tv tail accuracy computed actual (sampleError accuracy.length) hstep
    have hsecond := ih hwide.2 actual
    have h := hfirst.triangle hsecond
    rw [RationalGaussianChain.exactChannel_cons]
    simpa only [chainChannel,actual,computed,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using h

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule67

/- Helper module Solutions.RegevBridgeInitialGaussianBudget. -/
section P2MDyadicModule68

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT GaussianSource

open scoped BigOperators

noncomputable section

/-- A direct finite product estimate, with its small-error premise stated
in terms of the actual dimension times the scalar normalizer error. -/
theorem one_add_pow_le_reciprocal (count : ℕ) (error : ℝ) (herror : 0 ≤ error)
    (hsmall : count*error < 1) :
    (1+error)^count ≤ 1/(1-count*error) := by
  induction count with
  | zero => simp
  | succ count ih =>
    have hprevious : count*error < 1 := by
      have : (count : ℝ) ≤ (count+1 : ℕ) := by exact_mod_cast Nat.le_succ count
      nlinarith
    have hden : 0 < 1-(count : ℝ)*error := by linarith
    have hdenNext : 0 < 1-((count+1 : ℕ) : ℝ)*error := by linarith
    rw [pow_succ]
    apply (mul_le_mul_of_nonneg_right (ih hprevious) (by linarith : 0 ≤ 1+error)).trans
    apply (le_div_iff₀ hdenNext).mpr
    have hequal : 1/(1-(count : ℝ)*error)*(1+error)*(1-((count+1 : ℕ) : ℝ)*error)=
        ((1+error)*(1-((count+1 : ℕ) : ℝ)*error))/(1-(count : ℝ)*error) := by ring
    rw [hequal]
    apply (div_le_iff₀ hden).mpr
    have hsquare := sq_nonneg error
    have hcount : (0 : ℝ) ≤ count := Nat.cast_nonneg count
    have hmul := mul_nonneg hcount hsquare
    push_cast at *
    nlinarith

/-- Complete normalizer distortion is at most twice its first-order
budget, before normalizing the correlated lattice law. -/
theorem normalizer_product_error_le (count : ℕ) (error : ℝ) (herror : 0 ≤ error)
    (hbudget : count*error ≤ 1/4) :
    (1+error)^count-1 ≤ 2*(count*error) := by
  have hsmall : count*error < 1 := by linarith
  have h := one_add_pow_le_reciprocal count error herror hsmall
  have hden : 0 < 1-(count : ℝ)*error := by linarith
  have hupper : 1/(1-(count : ℝ)*error) ≤ 1+2*((count : ℝ)*error) := by
    apply (div_le_iff₀ hden).mpr
    have hnonneg : 0 ≤ (count : ℝ)*error := mul_nonneg (Nat.cast_nonneg count) herror
    nlinarith
  linarith

/-- The genuine correlated lattice sequential-law error is linear in
its public dimension-times-theta budget; no smallness assumption remains
hidden in a multiplicative power expression. -/
theorem initial_sequential_lattice_tv_linear {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (base : ℚ) (hbase : 0 < base) (error : ℝ) (herror : 0 ≤ error) (herrorOne : error ≤ 1)
    (htheta : thetaError (base : ℝ) ≤ error) (hbudget : dimension*error ≤ 1/4) :
    (∑' word,|GaussianProjection.cosetMass (IntegerBasis.inputLattice basis hdet) 0 (initialWidth basis base)
        ((IntegerBasis.integerBasis basis hdet).equivFun.symm word)-
      (initialChain basis base).realChain.sequentialMass word|)/2 ≤ 4*(dimension*error) := by
  have hproduct := normalizer_product_error_le dimension error herror hbudget
  have hnonneg : 0 ≤ (1+error)^dimension-1 := by
    have h := one_le_pow₀ (n:=dimension) (by linarith : 1 ≤ 1+error)
    linarith
  have hsmall : (1+error)^dimension-1 < 1 := by linarith
  apply (initial_sequential_lattice_tv basis hdet base hbase error herror herrorOne htheta hsmall).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-((1+error)^dimension-1))).mpr
  have hbudgetNonneg : 0 ≤ (dimension : ℝ)*error := mul_nonneg (Nat.cast_nonneg dimension) herror
  nlinarith

def initialThetaBudget (width : ℕ) : ℝ := 4/(2 : ℝ)^(4*width)

theorem thetaError_integer_le (width : ℕ) (hwidth : 2 ≤ width) :
    thetaError (width : ℝ) ≤ initialThetaBudget width := by
  have hw : (1 : ℝ) ≤ width := by exact_mod_cast (show 1 ≤ width by omega)
  have htheta := thetaError_le_four_exp (width : ℝ) hw
  have hexp := GaussianProjection.CosetGeometry.sigma_gaussian_exp_le width hwidth
  have hpos : 0 ≤ Real.exp (-Real.pi*(width : ℝ)^2/2) := (Real.exp_pos _).le
  have hpow : 0 ≤ 1/(2 : ℝ)^(2*width) := by positivity
  have hsquare := (sq_le_sq₀ hpos hpow).mpr hexp
  have hequal : Real.exp (-Real.pi*(width : ℝ)^2/2)^2=Real.exp (-Real.pi*(width : ℝ)^2) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [hequal,div_pow,one_pow,←pow_mul] at hsquare
  have hexponent : (2*width)*2=4*width := by omega
  rw [hexponent] at hsquare
  unfold initialThetaBudget
  calc
    _ ≤ 4*Real.exp (-Real.pi*(width : ℝ)^2) := htheta
    _ ≤ 4*(1/(2 : ℝ)^(4*width)) := mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = _ := by ring

theorem initialThetaBudget_nonneg (width : ℕ) : 0 ≤ initialThetaBudget width := by
  unfold initialThetaBudget
  positivity

theorem initialThetaBudget_small (width : ℕ) (hwidth : 2 ≤ width) :
    initialThetaBudget width ≤ 1 := by
  have hpow : (4 : ℝ) ≤ 2^(4*width) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ 4*width by omega)
    norm_num at h ⊢
    exact h
  unfold initialThetaBudget
  exact (div_le_one (by positivity)).mpr hpow

/-- Any dimension bounded by the public integer base automatically meets
the complete multiplicative-normalizer smallness requirement. -/
theorem initialThetaBudget_dimension (dimension width : ℕ) (hwidth : 2 ≤ width)
    (hdimension : dimension ≤ width) :
    dimension*initialThetaBudget width ≤ 1/4 := by
  have hself : (width : ℝ) ≤ 2^width := by exact_mod_cast (Nat.lt_two_pow_self (n:=width)).le
  have hsixteen : (16 : ℝ) ≤ 2^(3*width) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 4 ≤ 3*width by omega)
    norm_num at h ⊢
    exact h
  have hdim : (dimension : ℝ) ≤ width := by exact_mod_cast hdimension
  have hbound : 16*(dimension : ℝ) ≤ 2^(4*width) := by
    calc
      _ ≤ 16*(width : ℝ) := by gcongr
      _ ≤ 16*(2 : ℝ)^width := by gcongr
      _ ≤ 2^(3*width)*(2 : ℝ)^width := by gcongr
      _ = _ := by rw [←pow_add];congr 1;omega
  unfold initialThetaBudget
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have hp : (0 : ℝ) < 2^(4*width) := by positivity
  have hequal : (dimension : ℝ)*(4/2^(4*width))*4=16*(dimension : ℝ)/2^(4*width) := by ring
  rw [hequal]
  exact (div_le_one hp).mpr hbound

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule68

/- Helper module Solutions.RegevBridgeInitialGaussianChannel. -/
section P2MDyadicModule69

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT GaussianSource RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

/-- Genuine normalizability of the complete correlated integer weight. -/
theorem initial_weight_summable {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    Summable (initialChain basis base).realChain.weight := by
  have htheta : thetaError 1 ≤ 1 := (roundingError_lt_half 1 le_rfl).le.trans (by norm_num)
  have hwide : (initialChain basis base).realChain.Wide 1 := by
    rw [initialChain,upperRationalGaussianChain_real]
    apply upperGaussianChain_wide
    intro index
    have hbaseReal : (1 : ℝ) ≤ base := by exact_mod_cast hbase
    exact hbaseReal.trans (initial_scalar_width_lower basis hdet base (by linarith) index)
  exact ((initialChain basis base).realChain.summable_and_bounds 1 1 zero_lt_one zero_le_one le_rfl htheta hwide).1

theorem initialChain_wide_one {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    (initialChain basis base).realChain.Wide 1 := by
  rw [initialChain,upperRationalGaussianChain_real]
  apply upperGaussianChain_wide
  intro index
  have hbaseReal : (1 : ℝ) ≤ base := by exact_mod_cast hbase
  exact hbaseReal.trans (initial_scalar_width_lower basis hdet base (by linarith) index)

/-- The actual lattice Gaussian written in the original integral basis. -/
def initialMass {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (word : Fin dimension → ℤ) : ℝ :=
  GaussianProjection.cosetMass (IntegerBasis.inputLattice basis hdet) 0 (initialWidth basis base)
    ((IntegerBasis.integerBasis basis hdet).equivFun.symm word)

theorem initialMass_eq {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    initialMass basis hdet base=(initialChain basis base).realChain.normalizedMass := by
  funext word
  exact (initialChain_normalizedMass basis hdet base (by linarith) word).symm

theorem initial_normalizer_pos {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    0 < ∑' word,(initialChain basis base).realChain.weight word := by
  exact ((initialChain basis base).realChain.weight_pos (fun _ => 0)).trans_le
    ((initial_weight_summable basis hdet base hbase).le_tsum (fun _ => 0)
      (fun word _ => ((initialChain basis base).realChain.weight_pos word).le))

theorem initialMass_nonneg {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) (word : Fin dimension → ℤ) :
    0 ≤ initialMass basis hdet base word := by
  rw [initialMass_eq basis hdet base hbase]
  exact div_nonneg ((initialChain basis base).realChain.weight_pos word).le
    (initial_normalizer_pos basis hdet base hbase).le

theorem initialMass_summable {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    Summable (initialMass basis hdet base) := by
  rw [initialMass_eq basis hdet base hbase]
  exact (initial_weight_summable basis hdet base hbase).div_const _

theorem initialMass_sum {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (base : ℚ) (hbase : 1 ≤ base) :
    (∑' word,initialMass basis hdet base word)=1 := by
  rw [initialMass_eq basis hdet base hbase]
  unfold GaussianChain.normalizedMass
  rw [tsum_div_const,div_self (initial_normalizer_pos basis hdet base hbase).ne']

/-- True D_L at the initial width followed by any finite physical channel
of its complete original-basis coefficient vector. -/
def initialGaussianChannel {dimension : ℕ} {Output : Type*} [Fintype Output]
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (base : ℚ) (hbase : 1 ≤ base) (channel : (Fin dimension → ℤ) → FiniteDist Output) :
    FiniteDist Output := FiniteDist.countableMix (initialMass basis hdet base)
      (initialMass_nonneg basis hdet base hbase) (initialMass_summable basis hdet base hbase)
      (initialMass_sum basis hdet base hbase) channel

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule69

/- Helper module Solutions.RegevBridgeWideGaussianChainTapes. -/
section P2MDyadicModule70

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

abbrev ScalarRandom (variance : ℚ) (accuracy : List Unit) :=
  Fin (attemptTicks (publicConfigure ((variance,0),accuracy)).2).length →
    TrialRandom (pointInput ((variance,0),accuracy))

/-- All fresh finite scalar tapes are fixed by public variances. The
conditional rational center changes no tape-space cardinality. -/
def ChainRandom (accuracy : List Unit) : {count : ℕ} → RationalGaussianChain count → Type
  | 0,.nil => Unit
  | _+1,.cons variance _ tail => ScalarRandom variance accuracy × ChainRandom accuracy tail

instance chainRandom_fintype (accuracy : List Unit) : {count : ℕ} →
    (chain : RationalGaussianChain count) → Fintype (ChainRandom accuracy chain)
  | 0,.nil => inferInstanceAs (Fintype Unit)
  | _+1,.cons variance _ tail =>
      @instFintypeProd (ScalarRandom variance accuracy) (ChainRandom accuracy tail)
        inferInstance (chainRandom_fintype accuracy tail)

/-- Actual materialized integer output from fresh independent raw bit
streams, with every already drawn tail retained before its head call. -/
def chainDraw (accuracy : List Unit) : {count : ℕ} → (chain : RationalGaussianChain count) →
    ChainRandom accuracy chain → Vector ℤ count
  | 0,.nil,_ => Vector.ofFn Fin.elim0
  | _+1,.cons variance center tail,word =>
      let previous := chainDraw accuracy tail word.2
      let input : PublicRequest := ((variance,center previous.get),accuracy)
      let first := sample (input,(retryData (pointInput input)
        (attemptTicks (publicConfigure input).2).length word.1).2)
      Vector.ofFn (Fin.cons first previous.get)

noncomputable section

def scalarRandomLaw (variance : ℚ) (accuracy : List Unit) : FiniteDist (ScalarRandom variance accuracy) :=
  FiniteDist.independent (fun _ => rawFair (pointInput ((variance,0),accuracy)))

def chainRandomLaw (accuracy : List Unit) : {count : ℕ} → (chain : RationalGaussianChain count) →
    FiniteDist (ChainRandom accuracy chain)
  | 0,.nil => FiniteDist.uniform Unit
  | _+1,.cons variance _ tail => (scalarRandomLaw variance accuracy).prod (chainRandomLaw accuracy tail)

/-- One scalar native call on the public fresh fair tapes has exactly the
same finite observed law as the scalar kernel used in the chain analysis. -/
theorem scalarRandomLaw_channel {Output : Type*} [Fintype Output]
    (variance center : ℚ) (accuracy : List Unit) (channel : ℤ → FiniteDist Output) :
    (scalarRandomLaw variance accuracy).mix (fun word => channel
      (sample (((variance,center),accuracy),(retryData (pointInput ((variance,center),accuracy))
        (attemptTicks (publicConfigure ((variance,center),accuracy)).2).length word).2)))=
      (sampleLaw ((variance,center),accuracy)).mix
        (fun index => channel (point (pointInput ((variance,center),accuracy),index.val))) := by
  simp_rw [sample_exact]
  unfold scalarRandomLaw sampleLaw retryLaw
  rw [FiniteDist.mix_map,FiniteDist.mix_map]
  rfl

/-- Full joint law of the literal finite-tape recursive computation, after
any finite channel of the complete integer word. This identity keeps the
shared conditional centers and all tail correlations. -/
theorem chainDraw_channel {Output : Type*} [Fintype Output]
    {count : ℕ} (chain : RationalGaussianChain count) (accuracy : List Unit)
    (channel : (Fin count → ℤ) → FiniteDist Output) :
    (chainRandomLaw accuracy chain).mix (fun word => channel (chainDraw accuracy chain word).get)=
      chainChannel accuracy chain channel := by
  induction chain with
  | nil =>
    ext output
    simp only [chainRandomLaw,chainDraw,chainChannel,FiniteDist.mix_weight,FiniteDist.uniform_weight,
      Fintype.card_unique,Nat.cast_one,inv_one,one_mul]
    have he : (Vector.ofFn (Fin.elim0 : Fin 0 → ℤ)).get=Fin.elim0 := by funext index;exact Fin.elim0 index
    rw [he]
    change (∑ _word : Unit,(channel Fin.elim0).weight output)=(channel Fin.elim0).weight output
    simp
  | @cons count variance center tail ih =>
    have hprod (value : ScalarRandom variance accuracy → ChainRandom accuracy tail → FiniteDist Output) :
        ((scalarRandomLaw variance accuracy).prod (chainRandomLaw accuracy tail)).mix
          (fun pair => value pair.1 pair.2)=
        (scalarRandomLaw variance accuracy).mix (fun first => (chainRandomLaw accuracy tail).mix (value first)) := by
      ext output
      simp only [FiniteDist.mix_weight,FiniteDist.prod_weight,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    change ((scalarRandomLaw variance accuracy).prod (chainRandomLaw accuracy tail)).mix
      (fun word : ScalarRandom variance accuracy × ChainRandom accuracy tail =>
        channel (chainDraw accuracy (.cons variance center tail) word).get)=_
    rw [hprod (fun first rest => channel (chainDraw accuracy (.cons variance center tail) (first,rest)).get),
      FiniteDist.mix_comm]
    simp only [chainDraw]
    have hget (function : Fin (count+1) → ℤ) : (Vector.ofFn function).get=function := by
      funext index
      exact Vector.get_ofFn _ _
    simp only [hget]
    have hhead (rest : ChainRandom accuracy tail) :
        (scalarRandomLaw variance accuracy).mix (fun first => channel
          (Fin.cons (sample (((variance,center (chainDraw accuracy tail rest).get),accuracy),
            (retryData (pointInput ((variance,center (chainDraw accuracy tail rest).get),accuracy))
              (attemptTicks (publicConfigure ((variance,center (chainDraw accuracy tail rest).get),accuracy)).2).length first).2))
            (chainDraw accuracy tail rest).get))=
          (sampleLaw ((variance,center (chainDraw accuracy tail rest).get),accuracy)).mix
            (fun index => channel (Fin.cons
              (point (pointInput ((variance,center (chainDraw accuracy tail rest).get),accuracy),index.val))
              (chainDraw accuracy tail rest).get)) :=
      scalarRandomLaw_channel variance (center (chainDraw accuracy tail rest).get) accuracy
        (fun first => channel (Fin.cons first (chainDraw accuracy tail rest).get))
    simp only [hhead]
    exact ih (fun word => (sampleLaw ((variance,center word),accuracy)).mix
      (fun index => channel (Fin.cons (point (pointInput ((variance,center word),accuracy),index.val)) word)))

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule70

/- Helper module Integration9_9.FairBitPadding. -/
section P2MDyadicModule71

set_option autoImplicit false

namespace Integration9_9.FairBitPadding

open InfoLossLAR.WorstCase

/-- Relabeling a finite uniform source by a bijection preserves every average. -/
theorem avg_equiv {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [e.sum_comp, Fintype.card_congr e]

/-- Unused independent randomness has no effect on a finite average. -/
theorem avg_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) : avg (fun p : α × β => f p.1) = avg f := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  field_simp

/-- Padding a fair-bit tape by a fixed number of unused bits preserves its law. -/
theorem avg_prefix_add (n extra : ℕ) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin (n+extra) → Bool => f (fun i => tape (Fin.castAdd extra i))) = avg f := by
  calc
    _ = avg (fun tape => (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1)
          (splitEquiv n extra tape)) := rfl
    _ = avg (fun p : (Fin n → Bool) × (Fin extra → Bool) => f p.1) :=
      avg_equiv (splitEquiv n extra) (fun p => f p.1)
    _ = avg f := avg_fst f

/-- Any upper bound on the required random tape can be used as an exact tape length. -/
theorem avg_prefix {n m : ℕ} (h : n ≤ m) (f : (Fin n → Bool) → ℝ) :
    avg (fun tape : Fin m → Bool => f (fun i => tape (Fin.castLE h i))) = avg f := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Fin.castLE, Fin.castAdd] using avg_prefix_add n extra f

end Integration9_9.FairBitPadding

end P2MDyadicModule71

/- Helper module Solutions.RegevBridgeWideGaussianFlatTapes. -/
section P2MDyadicModule72

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

abbrev trialProposalBits (variance : ℚ) (accuracy : List Unit) :=
  Nat.size (intervalCount (pointInput ((variance,0),accuracy)))

abbrev trialCoinBits (variance : ℚ) (accuracy : List Unit) :=
  (pointInput ((variance,0),accuracy)).2.2.length

abbrev scalarAttempts (variance : ℚ) (accuracy : List Unit) :=
  (attemptTicks (publicConfigure ((variance,0),accuracy)).2).length

def scalarBits (variance : ℚ) (accuracy : List Unit) : ℕ :=
  scalarAttempts variance accuracy*(trialProposalBits variance accuracy+trialCoinBits variance accuracy)

/-- This is the actual prefix/suffix split of one contiguous trial block,
with only the explicit Bool/Fin2 bit-alphabet conversion. -/
def trialFlatEquiv (variance : ℚ) (accuracy : List Unit) :
    (Fin (trialProposalBits variance accuracy+trialCoinBits variance accuracy) → Bool) ≃
      TrialRandom (pointInput ((variance,0),accuracy)) :=
  (Integration9_9.FairBitPadding.splitEquiv _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm))

/-- Explicit contiguous block addressing, rather than an arbitrary
cardinality equivalence, provides all native scalar trial tapes. -/
def scalarFlatEquiv (variance : ℚ) (accuracy : List Unit) :
    (Fin (scalarBits variance accuracy) → Bool) ≃ ScalarRandom variance accuracy :=
  (Integration9_9.BlockCoins.blockEquiv _ _).trans
    (Equiv.piCongrRight (fun _ => trialFlatEquiv variance accuracy))

def decodeScalarTape (variance : ℚ) (accuracy : List Unit) (total : ℕ)
    (hbits : scalarBits variance accuracy ≤ total) (tape : Fin total → Bool) : ScalarRandom variance accuracy :=
  scalarFlatEquiv variance accuracy (fun index => tape (Fin.castLE hbits index))

noncomputable section

theorem independent_uniform {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Value] [Nonempty Value] :
    FiniteDist.independent (fun _ : Index => FiniteDist.uniform Value)=FiniteDist.uniform (Index → Value) := by
  ext word
  simp only [FiniteDist.independent,FiniteDist.uniform_weight,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow,inv_pow]

theorem product_uniform {First Second : Type*} [Fintype First] [Fintype Second] [Nonempty First] [Nonempty Second] :
    (FiniteDist.uniform First).prod (FiniteDist.uniform Second)=FiniteDist.uniform (First × Second) := by
  ext word
  simp only [FiniteDist.prod_weight,FiniteDist.uniform_weight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev]
  ring

theorem rawFair_uniform (input : PointRequest) : rawFair input=FiniteDist.uniform (TrialRandom input) := by
  rw [rawFair,coinFair,independent_uniform,product_uniform]

theorem scalarRandomLaw_uniform (variance : ℚ) (accuracy : List Unit) :
    scalarRandomLaw variance accuracy=FiniteDist.uniform (ScalarRandom variance accuracy) := by
  unfold scalarRandomLaw
  simp only [rawFair_uniform,independent_uniform]

/-- A genuinely padded flat fair-bit prefix has exactly the corresponding
short uniform law; unused suffix bits create no dependence or bias. -/
theorem uniform_prefix_map (required total : ℕ) (hbits : required ≤ total) :
    (FiniteDist.uniform (Fin total → Bool)).map (fun tape index => tape (Fin.castLE hbits index))=
      FiniteDist.uniform (Fin required → Bool) := by
  classical
  ext output
  have h := Integration9_9.FairBitPadding.avg_prefix hbits
    (fun tape : Fin required → Bool => if tape=output then (1 : ℝ) else 0)
  simp only [avg,div_eq_mul_inv,Finset.sum_mul,ite_mul,one_mul,zero_mul] at h
  simpa only [FiniteDist.map_weight,FiniteDist.uniform_weight,Finset.sum_ite_eq',Finset.mem_univ,if_true] using h

/-- Exact observed law of the explicit contiguous scalar loader from a
flat, polynomially padded fair-bit tape. -/
theorem decodeScalarTape_law (variance : ℚ) (accuracy : List Unit) (total : ℕ)
    (hbits : scalarBits variance accuracy ≤ total) :
    (FiniteDist.uniform (Fin total → Bool)).map (decodeScalarTape variance accuracy total hbits)=
      scalarRandomLaw variance accuracy := by
  have h := congrArg (fun law : FiniteDist (Fin (scalarBits variance accuracy) → Bool) =>
    law.map (scalarFlatEquiv variance accuracy)) (uniform_prefix_map _ _ hbits)
  rw [FiniteDist.map_map,FiniteDist.uniform_map_equiv] at h
  exact h.trans (scalarRandomLaw_uniform variance accuracy).symm

theorem scalarBits_eq_randomTicks (variance : ℚ) (accuracy : List Unit) :
    scalarBits variance accuracy=(randomTicks ((variance,0),accuracy)).length := by
  rw [randomTicks_length]
  rfl

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule72

/- Helper module Solutions.RegevBridgeFlatTrialParser. -/
section P2MDyadicModule73

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Pure integer-address parser correctness, separated from Gaussian
metadata so elaboration never expands a numerical width configuration. -/
theorem splitTrial_ofFn (proposal coin attempts total : ℕ) (hbits : attempts*(proposal+coin) ≤ total)
    (tape : Fin total → Bool) (attempt : Fin attempts) :
    splitTrial ((proposal,coin),(List.ofFn tape,attempt.val))=
      (List.ofFn (fun bit : Fin proposal => tape (Fin.castLE hbits
        (finProdFinEquiv (attempt,Fin.castAdd coin bit)))),
       List.ofFn (fun bit : Fin coin => tape (Fin.castLE hbits
        (finProdFinEquiv (attempt,Fin.natAdd proposal bit))))) := by
  let start := attempt.val*(proposal+coin)
  have hend : start+proposal+coin ≤ total := by
    have htrial := Nat.mul_le_mul_right (proposal+coin) (show attempt.val+1 ≤ attempts by omega)
    dsimp [start]
    nlinarith
  apply Prod.ext
  · apply List.ext_getElem
    · simp only [splitTrial,List.length_take,List.length_drop,List.length_ofFn]
      change min proposal (total-start)=proposal
      omega
    · intro bit hfirst hsecond
      simp only [splitTrial,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
      apply congrArg tape
      apply Fin.ext
      simp only [Fin.val_castLE,finProdFinEquiv,Equiv.coe_fn_mk]
      dsimp [start]
      ac_rfl
  · apply List.ext_getElem
    · simp only [splitTrial,List.length_take,List.length_drop,List.length_ofFn]
      change min coin (total-start-proposal)=coin
      omega
    · intro bit hfirst hsecond
      simp only [splitTrial,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
      apply congrArg tape
      apply Fin.ext
      simp only [Fin.val_castLE,finProdFinEquiv,Equiv.coe_fn_mk]
      dsimp [start]
      ac_rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule73

/- Helper module Solutions.RegevBridgeWideGaussianFlatNative. -/
section P2MDyadicModule74

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT GaussianSource RationalNumerics

open scoped BigOperators

abbrev FlatScalarInput := (ℚ × List Unit) × List Bool

/-- The actual parser addresses a contiguous proposal/acceptance pair in
one public trial block of the supplied flat Boolean tape. -/
def flatTrial (input : FlatScalarInput × ℕ) : List Bool × List Bool :=
  splitTrial ((trialProposalBits input.1.1.1 input.1.1.2,trialCoinBits input.1.1.1 input.1.1.2),
    (input.1.2,input.2))

@[fun_prop] theorem flatTrial_poly : Poly flatTrial := by
  have hheader : Poly (fun input : FlatScalarInput × ℕ =>
      ((trialProposalBits input.1.1.1 input.1.1.2,trialCoinBits input.1.1.1 input.1.1.2),(input.1.2,input.2))) := by
    unfold trialProposalBits trialCoinBits
    fun_prop
  unfold flatTrial
  exact Poly.comp splitTrial_poly hheader

/-- Every trial record is generated by this native take/drop parser;
there is no operation on an abstract finite-type equivalence at runtime. -/
def flatRawBlock (input : FlatScalarInput) : List (List Bool × List Bool) :=
  (List.range (scalarAttempts input.1.1 input.1.2)).map (fun trial => flatTrial (input,trial))

@[fun_prop] theorem flatRawBlock_poly : Poly flatRawBlock := by
  have hindices : Poly (fun input : FlatScalarInput => List.range (scalarAttempts input.1.1 input.1.2)) :=
    Poly.comp (f:=fun slots : List Unit => List.range slots.length)
      (g:=fun input : FlatScalarInput => attemptTicks (publicConfigure ((input.1.1,0),input.1.2)).2)
      Poly.list_indices (by fun_prop)
  unfold flatRawBlock
  exact Poly.list_map flatTrial_poly hindices

noncomputable section

private theorem digitBoolean_decode (bit : Bool) :
    AFT.BinaryArithmetic.digitBoolean (finTwoEquiv.symm bit)=bit := by cases bit <;> rfl

theorem flatTrial_correct (variance : ℚ) (accuracy : List Unit) (total : ℕ)
    (hbits : scalarBits variance accuracy ≤ total) (tape : Fin total → Bool)
    (attempt : Fin (scalarAttempts variance accuracy)) :
    flatTrial (((variance,accuracy),List.ofFn tape),attempt.val)=
      trialData (pointInput ((variance,0),accuracy))
        (decodeScalarTape variance accuracy total hbits tape attempt) := by
  rw [flatTrial,splitTrial_ofFn (trialProposalBits variance accuracy) (trialCoinBits variance accuracy)
    (scalarAttempts variance accuracy) total hbits tape attempt]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext bit
    rfl
  · apply congrArg List.ofFn
    funext bit
    exact (digitBoolean_decode _).symm

/-- Pathwise equality of the literal native scalar parser and the proved
contiguous fair-bit decomposition, on every padded input tape. -/
theorem flatRawBlock_correct (variance : ℚ) (accuracy : List Unit) (total : ℕ)
    (hbits : scalarBits variance accuracy ≤ total) (tape : Fin total → Bool) :
    flatRawBlock ((variance,accuracy),List.ofFn tape)=
      (retryData (pointInput ((variance,0),accuracy)) (scalarAttempts variance accuracy)
        (decodeScalarTape variance accuracy total hbits tape)).2 := by
  apply List.ext_getElem
  · simp only [flatRawBlock,List.length_map,List.length_range,retryData,List.length_ofFn]
  · intro attempt hfirst hsecond
    have hattempt : attempt < scalarAttempts variance accuracy := by
      simpa only [flatRawBlock,List.length_map,List.length_range] using hfirst
    simp only [flatRawBlock,List.getElem_map,List.getElem_range,retryData,List.getElem_ofFn]
    exact flatTrial_correct variance accuracy total hbits tape ⟨attempt,hattempt⟩

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule74

/- Helper module Solutions.RegevBridgeWideGaussianMagnitude. -/
section P2MDyadicModule75

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

open AFT GaussianSource RationalNumerics

open scoped BigOperators

noncomputable section

/-- Every native interval point lies within its center plus the actual
binary-wide radius, including the explicit floor-anchor fallback. -/
theorem point_abs_bound (input : PointRequest) (index : Fin (intervalCount input)) :
    |(point (input,index.val) : ℚ)| ≤ |input.1.2|+(radius input : ℚ)+1 := by
  have hindex : (index.val : ℚ) ≤ 2*(radius input : ℚ) := by
    have h := index.isLt
    unfold intervalCount at h
    exact_mod_cast (show index.val ≤ 2*radius input by omega)
  have hindexNonneg : (0 : ℚ) ≤ index.val := by positivity
  have hfloor := Int.floor_le input.1.2
  have hfloorUpper := Int.lt_floor_add_one input.1.2
  rw [abs_le]
  simp only [point,anchorInteger_eq,Int.cast_sub,Int.cast_add,Int.cast_natCast]
  constructor <;> linarith [le_abs_self input.1.2,neg_abs_le input.1.2]

/-- The magnitude guarantee holds on arbitrary supplied bit lists; it is
not conditioned on rejection success or on a probabilistic event. -/
theorem sample_abs_bound (input : PublicRequest) (randomness : List (List Bool × List Bool)) :
    |(sample (input,randomness) : ℚ)| ≤ |input.1.2|+(radius (pointInput input) : ℚ)+1 := by
  rw [sample,configuredOutput,output_resolve]
  exact point_abs_bound _ _

/-- A binary upper bound on the public squared width gives a binary upper
bound on the proposal radius, independently of its numerical magnitude. -/
theorem scale_le_binary (input : PointRequest) (height : ℕ)
    (hvariance : variance input ≤ (2 : ℚ)^height) :
    (scale (variance input) : ℚ) ≤ (2 : ℚ)^(height+2) := by
  have hscale := (scale_variance_bounds (variance input) (variance_ge_one input)).2
  have hpower : (1 : ℚ) ≤ 2^height := one_le_pow₀ (by norm_num)
  have hsquare : ((scale (variance input) : ℚ))^2 ≤ ((2 : ℚ)^(height+2))^2 := by
    calc
      _ ≤ 8*variance input := hscale
      _ ≤ 8*(2 : ℚ)^height := by gcongr
      _ ≤ _ := by rw [pow_add];norm_num;nlinarith
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare

theorem sample_radius_binary (input : PublicRequest) (height : ℕ)
    (hvariance : input.1.1 ≤ (2 : ℚ)^height) :
    (radius (pointInput input) : ℚ) ≤ (2 : ℚ)^(input.2.length+height+4) := by
  have hpower : (1 : ℚ) ≤ 2^height := one_le_pow₀ (by norm_num)
  have hclamp : variance (pointInput input) ≤ (2 : ℚ)^height := by
    unfold variance
    split_ifs
    · exact hvariance
    · exact hpower
  have hscale := scale_le_binary (pointInput input) height hclamp
  have hfactor : ((input.2.length+2 : ℕ) : ℚ) ≤ (2 : ℚ)^(input.2.length+2) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=input.2.length+2)).le
  have hlength : (pointInput input).2.1.length=input.2.length+2 := by
    simp only [pointInput,configure,publicConfigure,List.length_append,List.length_cons,List.length_nil]
    omega
  unfold radius
  rw [Nat.cast_mul,hlength]
  calc
    _ ≤ (2 : ℚ)^(input.2.length+2)*2^(height+2) :=
      mul_le_mul hfactor hscale (by positivity) (by positivity)
    _ = _ := by rw [←pow_add];congr 1;omega

/-- Uniform additive output-magnitude budget for native sampling on any
finite supplied bit stream and any encoded rational center. -/
theorem sample_abs_binary (input : PublicRequest) (height : ℕ)
    (hvariance : input.1.1 ≤ (2 : ℚ)^height) (randomness : List (List Bool × List Bool)) :
    |(sample (input,randomness) : ℚ)| ≤ |input.1.2|+(2 : ℚ)^(input.2.length+height+5) := by
  have h := sample_abs_bound input randomness
  have hradius := sample_radius_binary input height hvariance
  have hpower : (1 : ℚ) ≤ 2^(input.2.length+height+4) := one_le_pow₀ (by norm_num)
  have hnext : (2 : ℚ)^(input.2.length+height+5)=2^(input.2.length+height+4)*2 := by
    rw [show input.2.length+height+5=(input.2.length+height+4)+1 by omega,pow_succ]
  rw [hnext]
  linarith

end

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Wide

end P2MDyadicModule75

/- Helper module Solutions.RegevBridgeGramDeterminant. -/
section P2MDyadicModule76

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open InnerProductSpace

open scoped BigOperators

noncomputable section

theorem prefixGram_real {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).map (fun value => (value : ℝ))=
      Matrix.gram ℝ (fun index => realVec (inputVectors basis (Fin.castLE hsteps index))) := by
  ext first second
  simp only [prefixGram,Matrix.map_apply,Matrix.gram_apply,realVec,inputVectors,PiLp.inner_apply,
    Real.inner_apply,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]

theorem prefixGram_det_ne_zero {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) (steps : ℕ) (hsteps : steps ≤ dimension) :
    (prefixGram basis steps hsteps).det ≠ 0 := by
  have independent : LinearIndependent ℝ
      (fun index : Fin steps => realVec (inputVectors basis (Fin.castLE hsteps index))) :=
    (inputVectors_independent basis hdet).comp (Fin.castLE hsteps) (Fin.castLE_injective hsteps)
  have h := Matrix.det_gram_ne_zero_iff_linearIndependent.mpr independent
  rw [←prefixGram_real,←Int.cast_det] at h
  exact_mod_cast h

/-- The subtraction made by Gram--Schmidt lies in the span of precisely
the original earlier columns, not an assumed short basis. -/
theorem gramSchmidt_correction_mem_prefix {dimension count : ℕ}
    (vectors : Fin count → QVector dimension) (index : Fin count) :
    realVec (vectors index)-realVec (orthogonal vectors index) ∈
      Submodule.span ℝ (Set.range (fun previous : Fin index.val =>
        realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))) := by
  classical
  let family := fun position => realVec (vectors position)
  have hset : Set.range (fun previous : Fin index.val =>
      realVec (vectors ⟨previous.val,previous.isLt.trans index.isLt⟩))=family '' Set.Iio index := by
    ext point
    constructor
    · rintro ⟨previous,rfl⟩
      refine ⟨⟨previous.val,previous.isLt.trans index.isLt⟩,?_,rfl⟩
      exact previous.isLt
    · rintro ⟨previous,hprevious,rfl⟩
      exact ⟨⟨previous.val,hprevious⟩,rfl⟩
  rw [hset,←span_gramSchmidt_Iio ℝ family index,orthogonal_real]
  have h := gramSchmidt_def'' ℝ family index
  have hcorrection : family index-gramSchmidt ℝ family index=
      ∑ previous ∈ Finset.Iio index,
        (inner ℝ (gramSchmidt ℝ family previous) (family index)/‖gramSchmidt ℝ family previous‖^2) •
          gramSchmidt ℝ family previous := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm,RCLike.ofReal_real_eq_id,id_eq] using h)
  change family index-gramSchmidt ℝ family index ∈ _
  rw [hcorrection]
  apply Submodule.sum_mem
  intro previous hprevious
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨previous,Finset.mem_Iio.mp hprevious,rfl⟩

end

def prefixPairing {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (previous : Fin index.val) : ℤ :=
  ∑ row,basis row ⟨previous.val,previous.isLt.trans index.isLt⟩*basis row index

def gramNumerator {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (index : Fin dimension) (row : Fin dimension) : ℤ :=
  (prefixGram basis index.val index.isLt.le).det*basis row index-
    ∑ previous : Fin index.val,
      Matrix.cramer (prefixGram basis index.val index.isLt.le) (prefixPairing basis index) previous*
        basis row ⟨previous.val,previous.isLt.trans index.isLt⟩

noncomputable section

/-- Multiplying the cached rational GS vector by the original integer
prefix-Gram determinant gives an explicitly integral Cramer numerator.
This is the denominator control needed for binary, rather than unit-cost,
complexity of the cached rational orthogonalization. -/
theorem gram_determinant_scales_orthogonal {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (index : Fin dimension) :
    ((prefixGram basis index.val index.isLt.le).det : ℚ) • orthogonal (inputVectors basis) index=
      fun row => (gramNumerator basis index row : ℚ) := by
  classical
  let previousColumn (previous : Fin index.val) : Fin dimension :=
    ⟨previous.val,previous.isLt.trans index.isLt⟩
  let family (previous : Fin index.val) := realVec (inputVectors basis (previousColumn previous))
  let gram := prefixGram basis index.val index.isLt.le
  let rhs := prefixPairing basis index
  let castGram := gram.map (fun value => (value : ℝ))
  obtain ⟨coefficients,hcoefficients⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (gramSchmidt_correction_mem_prefix (inputVectors basis) index)
  change (∑ previous,coefficients previous • family previous)=
    realVec (inputVectors basis index)-realVec (orthogonal (inputVectors basis) index) at hcoefficients
  have hinner (first second : Fin index.val) : inner ℝ (family first) (family second)=
      (gram first second : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,
      gram,prefixGram,Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
    rfl
  have htarget (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (inputVectors basis index))=(rhs previous : ℝ) := by
    simp only [family,previousColumn,realVec,inputVectors,PiLp.inner_apply,Real.inner_apply,prefixPairing,rhs,
      Int.cast_sum,Int.cast_mul,Rat.cast_intCast]
  have horthogonal (previous : Fin index.val) :
      inner ℝ (family previous) (realVec (orthogonal (inputVectors basis) index))=0 := by
    rw [orthogonal_real,real_inner_comm]
    exact gramSchmidt_inv_triangular ℝ (fun position => realVec (inputVectors basis position)) previous.isLt
  have hlinear : castGram.mulVec coefficients=fun previous => (rhs previous : ℝ) := by
    funext previous
    have h := congrArg (fun vector : Space dimension => inner ℝ (family previous) vector) hcoefficients
    simp only [inner_sum,inner_smul_right,inner_sub_right,horthogonal,sub_zero,htarget,hinner] at h
    simpa only [Matrix.mulVec,dotProduct,castGram,Matrix.map_apply,mul_comm] using h
  have hcramer : Matrix.cramer castGram (fun previous => (rhs previous : ℝ))=
      (gram.det : ℝ) • coefficients := by
    rw [←hlinear,Matrix.cramer_eq_adjugate_mulVec,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
      Matrix.smul_mulVec,Matrix.one_mulVec,←Int.cast_det]
  have hcramerCast (previous : Fin index.val) :
      Matrix.cramer castGram (fun position => (rhs position : ℝ)) previous=
        (Matrix.cramer gram rhs previous : ℝ) := by
    rw [Matrix.cramer_apply,Matrix.cramer_apply]
    have hmatrix : castGram.updateCol previous (fun position => (rhs position : ℝ))=
        (gram.updateCol previous rhs).map (fun value => (value : ℝ)) := by
      ext first second
      simp only [Matrix.updateCol_apply,Matrix.map_apply,castGram]
      split_ifs <;> rfl
    rw [hmatrix,←Int.cast_det]
  have hscaled : (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=
      ∑ previous,(Matrix.cramer gram rhs previous : ℝ) • family previous := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro previous _
    rw [smul_smul]
    have h := congrArg (fun values : Fin index.val → ℝ => values previous) hcramer
    simp only [Pi.smul_apply,smul_eq_mul,hcramerCast] at h
    rw [←h]
  have h := congrArg (fun vector : Space dimension => (gram.det : ℝ) • vector) hcoefficients
  change (gram.det : ℝ) • (∑ previous,coefficients previous • family previous)=_ at h
  rw [hscaled] at h
  ext row
  have hrow := congrArg (fun vector : Space dimension => vector row) h
  simp only [family,previousColumn,realVec,inputVectors,WithLp.ofLp_sum,WithLp.ofLp_smul,WithLp.ofLp_sub,Finset.sum_apply,
    Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Rat.cast_intCast] at hrow
  change (gram.det : ℚ)*orthogonal (inputVectors basis) index row=(gramNumerator basis index row : ℚ)
  apply Rat.cast_injective (α:=ℝ)
  simp only [gramNumerator,Rat.cast_sub,Rat.cast_mul,Rat.cast_sum,Rat.cast_intCast,Int.cast_sub,Int.cast_mul,Int.cast_sum]
  change (gram.det : ℝ)*(orthogonal (inputVectors basis) index row : ℝ)=_
  dsimp [gram,rhs] at hrow ⊢
  linarith

theorem prefixGram_entry_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) (first second : Fin steps) :
    |prefixGram basis steps hsteps first second| ≤ (dimension : ℤ)*bound^2 := by
  unfold prefixGram
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ row,|basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)|) ≤
        ∑ _row : Fin dimension,bound^2 := by
      apply Finset.sum_le_sum
      intro row _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hentries row _) (hentries row _) (abs_nonneg _) hbound
    _ = _ := by simp

/-- Every prefix determinant has a bound whose logarithm is polynomial
in the input dimension and the logarithmic entry bound. -/
theorem prefixGram_det_bound {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (bound : ℤ) (hbound : 0 ≤ bound)
    (hentries : ∀ row column,|basis row column| ≤ bound) :
    |(prefixGram basis steps hsteps).det| ≤ (steps.factorial : ℤ)*((dimension : ℤ)*bound^2)^steps := by
  have h := Matrix.det_le (abv:=AbsoluteValue.abs)
    (prefixGram_entry_bound basis steps hsteps bound hbound hentries)
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul] using h

/-- A uniform polynomial exponent bounds every integer prefix Gram
normalizer, directly from an entry bit bound of the original input. -/
theorem prefixGram_det_binary_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height) :
    |(prefixGram basis steps hsteps).det| ≤ (2 : ℤ)^((2*dimension+2*height)*dimension) := by
  have hdimension : (dimension : ℤ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hstep : (steps : ℤ) ≤ 2^dimension := (by exact_mod_cast hsteps : (steps : ℤ) ≤ dimension).trans hdimension
  have hfactorial : (steps.factorial : ℤ) ≤ 2^(dimension*steps) := by
    calc
      _ ≤ (steps : ℤ)^steps := by exact_mod_cast Nat.factorial_le_pow steps
      _ ≤ ((2 : ℤ)^dimension)^steps := pow_le_pow_left₀ (Nat.cast_nonneg steps) hstep _
      _ = _ := by rw [←pow_mul]
  have hentryGram : (dimension : ℤ)*((2 : ℤ)^height)^2 ≤ 2^(dimension+2*height) := by
    calc
      _ ≤ (2 : ℤ)^dimension*((2 : ℤ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimension (sq_nonneg _)
      _ = _ := by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _ ≤ (steps.factorial : ℤ)*((dimension : ℤ)*((2 : ℤ)^height)^2)^steps :=
      prefixGram_det_bound basis steps hsteps ((2 : ℤ)^height) (by positivity) hentries
    _ ≤ (2 : ℤ)^(dimension*steps)*(2^(dimension+2*height))^steps :=
      mul_le_mul hfactorial (pow_le_pow_left₀ (by positivity) hentryGram _)
        (by positivity) (by positivity)
    _ = 2^((2*dimension+2*height)*steps) := by
      rw [←pow_mul,←pow_add]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left (2*dimension+2*height) hsteps)

/-- Every cached rational coordinate has a small absolute magnitude even
when canonical numerators and denominators require separate control. -/
theorem orthogonal_coordinate_abs_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (height : ℕ)
    (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    |orthogonal (inputVectors basis) index row| ≤ (2 : ℚ)^(dimension+height) := by
  have hcoordinate : orthogonal (inputVectors basis) index row^2 ≤
      squaredNorm (inputVectors basis) index := by
    unfold squaredNorm innerQ
    simp only [←sq]
    exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ row)
  have hcolumn : innerQ (inputVectors basis index) (inputVectors basis index) ≤
      (dimension : ℚ)*((2 : ℚ)^height)^2 := by
    unfold innerQ inputVectors
    simp only [←sq]
    calc
      _ ≤ ∑ _ : Fin dimension,((2 : ℚ)^height)^2 := by
        apply Finset.sum_le_sum
        intro position _
        have hentry : |(basis position index : ℚ)| ≤ (2 : ℚ)^height := by
          exact_mod_cast hentries position index
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hentry
      _ = _ := by simp
  have hdimension : (dimension : ℚ) ≤ 2^dimension := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=dimension)).le
  have hpower : (1 : ℚ) ≤ 2^dimension := one_le_pow₀ (by norm_num)
  have hdimensionSquare : (dimension : ℚ) ≤ ((2 : ℚ)^dimension)^2 := by nlinarith
  have hsquare : orthogonal (inputVectors basis) index row^2 ≤ ((2 : ℚ)^(dimension+height))^2 := by
    calc
      _ ≤ squaredNorm (inputVectors basis) index := hcoordinate
      _ ≤ innerQ (inputVectors basis index) (inputVectors basis index) := squaredNorm_le _ index
      _ ≤ (dimension : ℚ)*((2 : ℚ)^height)^2 := hcolumn
      _ ≤ ((2 : ℚ)^dimension)^2*((2 : ℚ)^height)^2 :=
        mul_le_mul_of_nonneg_right hdimensionSquare (sq_nonneg _)
      _ = _ := by rw [pow_add,mul_pow]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsquare)

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule76

/- Helper module Solutions.RegevBridgeRationalDenominator. -/
section P2MDyadicModule77

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.RationalDenominator

/-- Any nonzero integral clearing denominator is divisible by the canonical
positive denominator of the rational number. -/
theorem den_dvd {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    (r.den : ℤ) ∣ D := by
  have hDQ : (D : ℚ)≠0 := by exact_mod_cast hD
  have hr : r=(N : ℚ)/(D : ℚ) := (eq_div_iff hDQ).mpr (by simpa only [mul_comm] using h)
  rw [hr]
  simpa only [Rat.divInt_eq_div] using Rat.den_dvd N D

/-- Canonical denominators never exceed any nonzero integral clearing denominator. -/
theorem den_le_natAbs {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    r.den≤D.natAbs := by
  have hd := den_dvd hD h
  have hn : r.den ∣ D.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hn

/-- Clearing-denominator bounds control the canonical numerator as well. -/
theorem num_bound_rat {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N) :
    |(r.num : ℚ)| ≤ |(D : ℚ)| * |r| := by
  have hd : (r.den : ℚ) ≤ |(D : ℚ)| := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using
      (Nat.cast_le (α := ℚ)).mpr (den_le_natAbs hD h)
  calc
    |(r.num : ℚ)|=|(r.den : ℚ)*r| := congrArg abs (Rat.den_mul_eq_num r).symm
    _ = (r.den : ℚ)*|r| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (abs_nonneg _)

/-- A magnitude bound and clearing-denominator bound yield a natural bound
on both stored rational integer fields. -/
theorem fields_bound {r : ℚ} {D N : ℤ} (hD : D≠0) (h : (D : ℚ)*r=N)
    (M : ℕ) (hM : |r|≤M) : r.den≤D.natAbs ∧ r.num.natAbs≤D.natAbs*M := by
  refine ⟨den_le_natAbs hD h,?_⟩
  have hn := (num_bound_rat hD h).trans (mul_le_mul_of_nonneg_left hM (abs_nonneg _))
  have hn' : (r.num.natAbs : ℚ) ≤ ((D.natAbs*M : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul,Nat.cast_natAbs,Int.cast_abs] using hn
  exact_mod_cast hn'

end InfoLossLAR.WorstCase.RationalDenominator

end P2MDyadicModule77

/- Helper module Solutions.RegevBridgeRationalGramSchmidtHeight. -/
section P2MDyadicModule78

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT.RationalNumerics

open scoped BigOperators

/-- A fixed polynomial in the dimension and input entry height controls
every reduced cached rational coordinate. -/
def coordinateHeight (dimension height : ℕ) : ℕ :=
  (2*dimension+2*height)*dimension+dimension+height

noncomputable section

/-- Canonical numerator and denominator sizes are polynomial, using the
actual integer Gram determinant rather than an arithmetic-operation count. -/
theorem orthogonal_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (index row : Fin dimension) :
    HeightBound (orthogonal (inputVectors basis) index row) (coordinateHeight dimension height) := by
  have hnonzero := prefixGram_det_ne_zero basis hdet index.val index.isLt.le
  have hvector := gram_determinant_scales_orthogonal basis index
  have hcoordinate := congrArg (fun vector : QVector dimension => vector row) hvector
  simp only [Pi.smul_apply,smul_eq_mul] at hcoordinate
  have habs := orthogonal_coordinate_abs_bound basis height hentries index row
  have hM : |orthogonal (inputVectors basis) index row| ≤ ((2^(dimension+height) : ℕ) : ℚ) := by
    exact_mod_cast habs
  obtain ⟨hden,hnum⟩ := RationalDenominator.fields_bound hnonzero hcoordinate (2^(dimension+height)) hM
  have hD : (prefixGram basis index.val index.isLt.le).det.natAbs ≤
      2^((2*dimension+2*height)*dimension) := by
    have h := prefixGram_det_binary_bound basis index.val index.isLt.le height hentries
    have hcast : (((prefixGram basis index.val index.isLt.le).det.natAbs : ℕ) : ℤ) ≤
        (2 : ℤ)^((2*dimension+2*height)*dimension) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast hcast
  constructor
  · apply hnum.trans
    apply (Nat.mul_le_mul_right (2^(dimension+height)) hD).trans_eq
    rw [←pow_add]
    congr 1
    unfold coordinateHeight
    omega
  · apply (hden.trans hD).trans
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by unfold coordinateHeight;omega)

theorem realVec_injective {dimension : ℕ} : Function.Injective (realVec (dimension:=dimension)) := by
  intro first second hequal
  funext index
  apply Rat.cast_injective (α:=ℝ)
  exact congrArg (fun vector : Space dimension => vector index) hequal

/-- Every materialized prefix consists of the very same final cached
orthogonal vectors, so all prefix state encodings share one height bound. -/
theorem cache_prefix_eq {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (steps : ℕ) (hsteps : steps ≤ count) :
    cache vectors steps=List.ofFn (fun index : Fin steps => orthogonal vectors (Fin.castLE hsteps index)) := by
  apply (List.map_injective_iff.mpr realVec_injective)
  rw [cache_real vectors steps hsteps,List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  exact (orthogonal_real vectors _).symm

theorem cache_coordinate_height {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) (vector : QVector dimension)
    (membership : vector ∈ cache (inputVectors basis) steps) (row : Fin dimension) :
    HeightBound (vector row) (coordinateHeight dimension height) := by
  rw [cache_prefix_eq _ steps hsteps] at membership
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp membership
  exact orthogonal_coordinate_height basis hdet height hentries _ row

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule78

/- Helper module Solutions.RegevBridgeRationalGramSchmidtNative. -/
section P2MDyadicModule79

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Total native rational list dot product; malformed lengths truncate. -/
def dot (input : List ℚ × List ℚ) : ℚ :=
  ((input.1.zip input.2).map (fun pair => pair.1*pair.2)).sum

@[fun_prop] theorem dot_poly : Poly dot := by unfold dot;fun_prop

def projectionEntry (input : (List ℚ × List ℚ) × ℕ) : ℚ :=
  dot (input.1.1,input.1.2)/dot (input.1.1,input.1.1)*input.1.1[input.2]?.getD 0

@[fun_prop] theorem projectionEntry_poly : Poly projectionEntry := by unfold projectionEntry;fun_prop

def rowValue (input : (List (List ℚ) × List ℚ) × ℕ) : ℚ :=
  input.1.2[input.2]?.getD 0-
    (input.1.1.map (fun previous => projectionEntry ((previous,input.1.2),input.2))).sum

@[fun_prop] theorem rowValue_poly : Poly rowValue := by unfold rowValue;fun_prop

/-- One native materialized Gram--Schmidt step uses its original current
column throughout and stores the complete new rational vector. -/
def orthogonalStep (input : List (List ℚ) × List ℚ) : List ℚ :=
  (List.range input.2.length).map (fun row => rowValue (input,row))

@[fun_prop] theorem orthogonalStep_poly : Poly orthogonalStep := by
  have hindices : Poly (fun input : List (List ℚ) × List ℚ => List.range input.2.length) :=
    Poly.comp (f:=fun values : List ℚ => List.range values.length) (g:=Prod.snd) Poly.list_indices Poly.snd
  unfold orthogonalStep
  exact Poly.list_map rowValue_poly hindices

/-- Unary size reflection materializes the exact actual binary encoding
length; it never enumerates a Gaussian window or a numerical magnitude. -/
def rationalTicks (value : ℚ) : List Unit :=
  List.replicate 7 ()++(value.num.natAbs.bits.flatMap (fun _ => [(),()]))++
    value.den.bits.map (fun _ => ())

@[fun_prop] theorem rationalTicks_poly : Poly rationalTicks := by unfold rationalTicks;fun_prop

def vectorTicks (vector : List ℚ) : List Unit :=
  vector.flatMap (fun value => rationalTicks value++rationalTicks value++[()])

@[fun_prop] theorem vectorTicks_poly : Poly vectorTicks := by unfold vectorTicks;fun_prop

def matrixTicks (matrix : List (List ℚ)) : List Unit :=
  matrix.flatMap (fun vector => vectorTicks vector++vectorTicks vector++[()])

@[fun_prop] theorem matrixTicks_poly : Poly matrixTicks := by unfold matrixTicks;fun_prop

theorem rationalTicks_length (value : ℚ) : (rationalTicks value).length=(Ratio.encode value).length := by
  rw [Ratio.encode_length]
  simp only [rationalTicks,List.length_append,List.length_replicate,List.length_flatMap,
    List.map_const',List.sum_replicate,List.length_cons,List.length_nil,nsmul_eq_mul,Nat.cast_id]
  omega

theorem vectorTicks_length (vector : List ℚ) :
    (vectorTicks vector).length=(encodeList Ratio.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [vectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      rationalTicks_length,EncodedList.cons_length] at *
    omega

theorem matrixTicks_length (matrix : List (List ℚ)) :
    (matrixTicks matrix).length=(encodeList (encodeList Ratio.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [matrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      vectorTicks_length,EncodedList.cons_length] at *
    omega

/-- Every intermediate cache is size-guarded, giving an unconditional
polynomial-time loop on arbitrary encodings. Valid matrix correctness will
be discharged using the independently proved integer-Gram height bound. -/
def cacheStep (state : List Unit × List (List ℚ)) (current : List ℚ) : List Unit × List (List ℚ) :=
  let next := state.2++[orthogonalStep (state.2,current)]
  (state.1,if (matrixTicks next).length ≤ state.1.length then next else [])

@[fun_prop] theorem cacheStep_poly : Poly (fun input : (List Unit × List (List ℚ)) × List ℚ =>
    cacheStep input.1 input.2) := by unfold cacheStep;fun_prop

theorem ticks_encoding_length (ticks : List Unit) : (enc ticks).length=ticks.length := by
  change (encodeList (fun _ : Unit => []) ticks).length=ticks.length
  induction ticks with
  | nil => rfl
  | cons head tail ih => simp only [EncodedList.cons_length,List.length_nil,List.length_cons,ih];omega

theorem state_encoding_length (state : List Unit × List (List ℚ)) :
    (enc state).length=2*state.1.length+1+(encodeList (encodeList Ratio.encode) state.2).length := by
  change (encodePair (encodeList enc) (encodeList (encodeList Ratio.encode)) state).length=_
  rw [encodePair_length]
  change 2*(enc state.1).length+1+_= _
  rw [ticks_encoding_length]

theorem cacheStep_length (state : List Unit × List (List ℚ)) (current : List ℚ) :
    (enc (cacheStep state current)).length ≤ 3*state.1.length+1 := by
  rw [state_encoding_length]
  unfold cacheStep
  simp only
  split_ifs with h
  · rw [matrixTicks_length] at h
    omega
  · change 2*state.1.length+1+0 ≤ _
    omega

theorem fold_encoding_length (columns : List (List ℚ)) (state : List Unit × List (List ℚ)) :
    (enc (columns.foldl cacheStep state)).length ≤ max (enc state).length (3*state.1.length+1) := by
  induction columns generalizing state with
  | nil => simp only [List.foldl_nil];exact le_max_left _ _
  | cons current rest ih =>
    rw [List.foldl_cons]
    apply (ih (cacheStep state current)).trans
    apply max_le
    · exact (cacheStep_length state current).trans (le_max_right _ _)
    · exact le_max_right _ _

theorem cacheFold_bound (columns : List (List ℚ)) (state : List Unit × List (List ℚ))
    (pre suffix : List (List ℚ)) (_hsplit : columns=pre++suffix) :
    (enc (pre.foldl cacheStep state)).length ≤
      (3*Polynomial.X+1 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length := by
  let inputLength := (encodePair (encodeList (enc : List ℚ → List Bool)) enc (columns,state)).length
  have hstate : (enc state).length ≤ inputLength := by
    dsimp [inputLength]
    rw [encodePair_length]
    change (enc state).length ≤ 2*(encodeList (enc : List ℚ → List Bool) columns).length+1+(enc state).length
    omega
  have hticks : state.1.length ≤ inputLength := by
    rw [state_encoding_length] at hstate
    omega
  apply (fold_encoding_length pre state).trans
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change max _ _ ≤ 3*inputLength+1
  omega

@[fun_prop] theorem cacheFold_poly : Poly (fun input : List (List ℚ) × (List Unit × List (List ℚ)) =>
    input.1.foldl cacheStep input.2) :=
  ⟨cacheStep_poly.program.listFold [] (3*Polynomial.X+1) cacheFold_bound⟩

/-- Actual guarded list cache program. The guard's complete runtime bound
holds for every encoded input, including malformed or singular matrices. -/
def cached (input : List (List ℚ) × List Unit) : List (List ℚ) :=
  (input.1.foldl cacheStep (input.2,[])).2

@[fun_prop] theorem cached_poly : Poly cached := by
  have hf := Poly.comp cacheFold_poly
    (show Poly (fun input : List (List ℚ) × List Unit => (input.1,(input.2,([] : List (List ℚ))))) by fun_prop)
  unfold cached
  exact Poly.comp Poly.snd hf

theorem dot_ofFn {dimension : ℕ} (first second : QVector dimension) :
    dot (List.ofFn first,List.ofFn second)=innerQ first second := by
  induction dimension with
  | zero => simp [dot,innerQ]
  | succ dimension ih =>
    simp only [dot,List.ofFn_succ,List.zip_cons_cons,List.map_cons,List.sum_cons]
    change first 0*second 0+dot (List.ofFn (Fin.tail first),List.ofFn (Fin.tail second))= _
    rw [ih]
    simp only [innerQ,Fin.sum_univ_succ,Fin.tail_def]

theorem vector_list_sum_apply {dimension : ℕ} (vectors : List (QVector dimension)) (index : Fin dimension) :
    vectors.sum index=(vectors.map (fun vector => vector index)).sum := by
  induction vectors with
  | nil => rfl
  | cons head tail ih => simp only [List.sum_cons,List.map_cons,Pi.add_apply,ih]

theorem orthogonalStep_ofFn {dimension : ℕ} (previous : List (QVector dimension))
    (current : QVector dimension) :
    orthogonalStep (previous.map List.ofFn,List.ofFn current)=
      List.ofFn (RationalGramSchmidt.orthogonalStep previous current) := by
  apply List.ext_getElem
  · simp only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < dimension := by
      simpa only [orthogonalStep,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [orthogonalStep,List.length_ofFn,List.getElem_map,List.getElem_range,rowValue,
      List.getElem?_ofFn,hrow,↓reduceDIte,Option.getD_some,List.map_map,Function.comp_def,
      projectionEntry,dot_ofFn,List.getElem_ofFn]
    simp only [RationalGramSchmidt.orthogonalStep,Pi.sub_apply,vector_list_sum_apply,List.map_map,
      Function.comp_def,projection,Pi.smul_apply,smul_eq_mul]

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule79

/- Helper module Solutions.RegevBridgeRationalGramSchmidtCacheBudget. -/
section P2MDyadicModule80

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

noncomputable section

theorem encoded_list_length_bound {Value : Type} (encoding : Value → List Bool)
    (values : List Value) (bound : ℕ) (hbound : ∀ value ∈ values,(encoding value).length ≤ bound) :
    (encodeList encoding values).length ≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp only [EncodedList.nil,List.length_nil,zero_mul,le_refl]
  | cons head tail ih =>
    rw [EncodedList.cons_length,List.length_cons]
    have hhead := hbound head (by simp)
    have htail := ih (fun value membership => hbound value (by simp [membership]))
    nlinarith

theorem rational_encoding_height {value : ℚ} {height : ℕ} (hvalue : HeightBound value height) :
    (Ratio.encode value).length ≤ 3*height+10 := by
  apply Ratio.length_height
  constructor
  · have h := (Nat.cast_le (α:=ℤ)).mpr hvalue.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h
  · exact_mod_cast hvalue.2

theorem vector_encoding_height {dimension : ℕ} (vector : QVector dimension) (height : ℕ)
    (hvector : ∀ row,HeightBound (vector row) height) :
    (encodeList Ratio.encode (List.ofFn vector)).length ≤ dimension*(6*height+21) := by
  have h := encoded_list_length_bound Ratio.encode (List.ofFn vector) (3*height+10) (by
    intro value membership
    obtain ⟨row,rfl⟩ := List.mem_ofFn.mp membership
    exact rational_encoding_height (hvector row))
  simpa only [List.length_ofFn,show 2*(3*height+10)+1=6*height+21 by omega] using h

def cacheEncodingBound (dimension height : ℕ) : ℕ :=
  dimension*(2*dimension*(6*coordinateHeight dimension height+21)+1)

/-- The original determinant-derived height bound controls every complete
native cache-prefix encoding by one public polynomial. -/
theorem cache_encoding_bound {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (steps : ℕ) (hsteps : steps ≤ dimension) :
    (encodeList (encodeList Ratio.encode) ((cache (inputVectors basis) steps).map List.ofFn)).length ≤
      cacheEncodingBound dimension height := by
  have h := encoded_list_length_bound (encodeList Ratio.encode)
    ((cache (inputVectors basis) steps).map List.ofFn) (dimension*(6*coordinateHeight dimension height+21)) (by
      intro vector membership
      obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp membership
      exact vector_encoding_height source _ (cache_coordinate_height basis hdet height hentries steps hsteps source hsource))
  rw [List.length_map,cache_length] at h
  apply h.trans
  unfold cacheEncodingBound
  calc
    steps*(2*(dimension*(6*coordinateHeight dimension height+21))+1) ≤
        dimension*(2*(dimension*(6*coordinateHeight dimension height+21))+1) := Nat.mul_le_mul_right _ hsteps
    _ = _ := by ring

/-- Prefix refinement is proved for the actual guarded list loop. Its
encoding bound is a local arithmetic invariant, discharged below from the
original integer matrix's determinant-derived size bounds. -/
theorem cacheFold_ofFn {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (ticks : List Unit)
    (hbudget : ∀ steps,steps ≤ count →
      (encodeList (encodeList Ratio.encode) ((cache vectors steps).map List.ofFn)).length ≤ ticks.length)
    (steps : ℕ) (hsteps : steps ≤ count) :
    (List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hsteps index)))).foldl cacheStep (ticks,[])=
      (ticks,(cache vectors steps).map List.ofFn) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    have hprevious : steps ≤ count := by omega
    have hstep : steps < count := by omega
    rw [List.ofFn_succ_last,List.foldl_append]
    change List.foldl cacheStep
      ((List.ofFn (fun index : Fin steps => List.ofFn (vectors (Fin.castLE hprevious index)))).foldl cacheStep (ticks,[]))
      [List.ofFn (vectors ⟨steps,hstep⟩)] = _
    rw [ih hprevious,List.foldl_cons,List.foldl_nil]
    have hnext : (cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))]=
        (cache vectors (steps+1)).map List.ofFn := by
      rw [orthogonalStep_ofFn,cache,List.map_append,List.map_singleton,dif_pos hstep]
    have hguard : (matrixTicks ((cache vectors steps).map List.ofFn++
        [orthogonalStep ((cache vectors steps).map List.ofFn,List.ofFn (vectors ⟨steps,hstep⟩))])).length ≤ ticks.length := by
      rw [hnext,matrixTicks_length]
      exact hbudget (steps+1) hsteps
    simp only [cacheStep,hguard,if_true]
    exact congrArg (fun matrix => (ticks,matrix)) hnext

/-- For every nonsingular input basis, the actual native cache agrees
exactly with rational Gram--Schmidt once supplied the public polynomial
encoding budget. No oracle or assumed GS algorithm appears. -/
theorem cached_integer_basis {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (height : ℕ) (hentries : ∀ row column,|basis row column| ≤ (2 : ℤ)^height)
    (ticks : List Unit) (hticks : cacheEncodingBound dimension height ≤ ticks.length) :
    cached (List.ofFn (fun index => List.ofFn (inputVectors basis index)),ticks)=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  have h := cacheFold_ofFn (inputVectors basis) ticks (fun steps hsteps =>
    (cache_encoding_bound basis hdet height hentries steps hsteps).trans hticks) dimension (le_refl dimension)
  change (List.ofFn (fun index : Fin dimension => List.ofFn (inputVectors basis index))).foldl cacheStep (ticks,[])=_ at h
  exact congrArg Prod.snd h

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule80

/- Helper module Solutions.RegevBridgeRationalGramSchmidtInput. -/
section P2MDyadicModule81

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

@[fun_prop] theorem integerTicks_poly : Poly integerTicks := by unfold integerTicks;fun_prop

@[fun_prop] theorem integerVectorTicks_poly : Poly integerVectorTicks := by unfold integerVectorTicks;fun_prop

@[fun_prop] theorem integerMatrixTicks_poly : Poly integerMatrixTicks := by unfold integerMatrixTicks;fun_prop

/-- The guard budget is generated in unary polynomial size from the
actual binary input length, not from an exponentially large entry value. -/
def inputBudget (input : List (List ℤ)) : List Unit :=
  let slots := integerMatrixTicks input++[()]
  slots.flatMap (fun _ => slots.flatMap (fun _ => slots.flatMap
    (fun _ => slots.flatMap (fun _ => List.replicate 128 ()))))

@[fun_prop] theorem inputBudget_poly : Poly inputBudget := by unfold inputBudget;fun_prop

def rationalColumn (column : List ℤ) : List ℚ := column.map (fun value : ℤ => (value : ℚ))

@[fun_prop] theorem rationalColumn_poly : Poly rationalColumn := by
  unfold rationalColumn
  exact Poly.list_map (show Poly (fun input : List ℤ × ℤ => (input.2 : ℚ)) by fun_prop) Poly.identity

def rationalColumns (input : List (List ℤ)) : List (List ℚ) := input.map rationalColumn

@[fun_prop] theorem rationalColumns_poly : Poly rationalColumns := by
  unfold rationalColumns
  exact Poly.list_map (Poly.comp rationalColumn_poly Poly.snd) Poly.identity

/-- Complete unconditional native cached orthogonalization of original
integer input columns, with all guards and loop sizes computed publicly. -/
def inputCache (input : List (List ℤ)) : List (List ℚ) := cached (rationalColumns input,inputBudget input)

@[fun_prop] theorem inputCache_poly : Poly inputCache := by unfold inputCache;fun_prop

theorem integerTicks_length (value : ℤ) : (integerTicks value).length=(Signed.encode value).length := by
  simp only [integerTicks,List.length_append,List.length_replicate,List.length_map,Signed.encode_length]

theorem integerVectorTicks_length (vector : List ℤ) :
    (integerVectorTicks vector).length=(encodeList Signed.encode vector).length := by
  induction vector with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerVectorTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerTicks_length,EncodedList.cons_length] at *
    omega

theorem integerMatrixTicks_length (matrix : List (List ℤ)) :
    (integerMatrixTicks matrix).length=(encodeList (encodeList Signed.encode) matrix).length := by
  induction matrix with
  | nil => rfl
  | cons head tail ih =>
    simp only [integerMatrixTicks,List.flatMap_cons,List.length_append,List.length_singleton,
      integerVectorTicks_length,EncodedList.cons_length] at *
    omega

theorem inputBudget_length (matrix : List (List ℤ)) :
    (inputBudget matrix).length=128*((integerMatrixTicks matrix).length+1)^4 := by
  simp only [inputBudget,List.length_flatMap,List.map_const',List.sum_replicate,List.length_replicate,
    List.length_append,List.length_singleton,nsmul_eq_mul,Nat.cast_id]
  ring

def transposeColumn (input : List (List ℤ) × ℕ) : List ℤ :=
  input.1.map (fun row => row[input.2]?.getD 0)

@[fun_prop] theorem transposeColumn_poly : Poly transposeColumn := by unfold transposeColumn;fun_prop

def transpose (input : List (List ℤ)) : List (List ℤ) :=
  (List.range input.length).map (fun column => transposeColumn (input,column))

@[fun_prop] theorem transpose_poly : Poly transpose := by
  unfold transpose
  exact Poly.list_map transposeColumn_poly Poly.list_indices

/-- Actual row-encoded matrix input is transposed by a native program
before the cached column orthogonalization. -/
def basisCache (input : List (List ℤ)) : List (List ℚ) := inputCache (transpose input)

@[fun_prop] theorem basisCache_poly : Poly basisCache := by unfold basisCache;fun_prop

noncomputable section

/-- Coarse fixed polynomial suitable for unconditional guarded runtime. -/
theorem cacheEncodingBound_coarse (dimension height length : ℕ)
    (hdimension : dimension ≤ length) (hheight : height ≤ length) :
    cacheEncodingBound dimension height ≤ 128*(length+1)^4 := by
  have hlinear : length ≤ (length+1)^2 := by nlinarith
  have hcross : height*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hheight hdimension
      _ ≤ _ := by nlinarith
  have hsquare : dimension*dimension ≤ (length+1)^2 := by
    calc
      _ ≤ length*length := Nat.mul_le_mul hdimension hdimension
      _ ≤ _ := by nlinarith
  have hcache : coordinateHeight dimension height ≤ 6*(length+1)^2 := by
    unfold coordinateHeight
    nlinarith
  unfold cacheEncodingBound
  calc
    _ ≤ (length+1)*(2*(length+1)*(6*(6*(length+1)^2)+21)+1) := by gcongr <;> omega
    _ ≤ _ := by
      have hpowerOne := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 1 ≤ 4 by omega)
      have hpowerTwo := Nat.pow_le_pow_right (by omega : 1 ≤ length+1) (show 2 ≤ 4 by omega)
      simp only [pow_one] at hpowerOne
      nlinarith

theorem inputColumns_dimension {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    dimension ≤ (integerMatrixTicks (inputColumns basis)).length := by
  rw [integerMatrixTicks_length]
  have h := EncodedList.length_le (encodeList Signed.encode) (inputColumns basis)
  simpa only [inputColumns,List.length_ofFn] using h

theorem inputColumns_entry_height {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (row column : Fin dimension) :
    |basis row column| ≤ (2 : ℤ)^(integerMatrixTicks (inputColumns basis)).length := by
  have hcolumn : List.ofFn (fun position => basis position column) ∈ inputColumns basis :=
    List.mem_ofFn.mpr ⟨column,rfl⟩
  have hentry : basis row column ∈ List.ofFn (fun position => basis position column) :=
    List.mem_ofFn.mpr ⟨row,rfl⟩
  have hcolumnSize := EncodedList.member_length (encodeList Signed.encode) (inputColumns basis) _ hcolumn
  have hentrySize := EncodedList.member_length Signed.encode _ _ hentry
  have hbits : (basis row column).natAbs.bits.length ≤ (integerMatrixTicks (inputColumns basis)).length := by
    rw [integerMatrixTicks_length]
    rw [Signed.encode_length] at hentrySize
    omega
  have hvalue := (NatBinary.le_two_pow_length (basis row column).natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits)
  have hcast := (Nat.cast_le (α:=ℤ)).mpr hvalue
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using hcast

theorem rationalColumns_input {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    rationalColumns (inputColumns basis)=List.ofFn (fun index => List.ofFn (inputVectors basis index)) := by
  simp only [rationalColumns,rationalColumn,inputColumns,List.map_ofFn,Function.comp_def]
  rfl

/-- The fully generated binary-input native cache exactly returns the
original nonsingular integer basis's rational orthogonalization. Every
size guard is discharged from the actual input encoding itself. -/
theorem inputCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    inputCache (inputColumns basis)=(cache (inputVectors basis) dimension).map List.ofFn := by
  unfold inputCache
  rw [rationalColumns_input]
  apply cached_integer_basis basis hdet (integerMatrixTicks (inputColumns basis)).length
    (inputColumns_entry_height basis)
  rw [inputBudget_length]
  exact cacheEncodingBound_coarse dimension _ _ (inputColumns_dimension basis) le_rfl

theorem transpose_input_rows {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) :
    transpose (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=inputColumns basis := by
  apply List.ext_getElem
  · simp only [transpose,List.length_map,List.length_range,List.length_ofFn,inputColumns]
  · intro column hfirst hsecond
    have hcolumn : column < dimension := by
      simpa only [transpose,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [transpose,List.length_ofFn,List.getElem_map,List.getElem_range,transposeColumn,
      List.map_ofFn,Function.comp_def,List.getElem?_ofFn,hcolumn,↓reduceDIte,Option.getD_some,
      inputColumns,List.getElem_ofFn]

/-- End-to-end exact native GS caching for the target's original row-major
integer matrix convention, with an unconditional polynomial-time program. -/
theorem basisCache_correct {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (hdet : basis.det ≠ 0) :
    basisCache (List.ofFn (fun row => List.ofFn (fun column => basis row column)))=
      (cache (inputVectors basis) dimension).map List.ofFn := by
  rw [basisCache,transpose_input_rows,inputCache_correct basis hdet]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule81

/- Helper module Solutions.RegevBridgeInitialGaussianParameters. -/
section P2MDyadicModule82

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- One materialized scalar row contains its exact rational squared width
and the complete rational upper-triangular conditional-center coefficients. -/
def parameterRow (input : (ℚ × List (List ℚ)) × List ℚ) : ℚ × List ℚ :=
  (input.1.1*input.1.1/dot (input.2,input.2),
    input.1.2.map (fun column => dot (input.2,column)/dot (input.2,input.2)))

@[fun_prop] theorem parameterRow_poly : Poly parameterRow := by unfold parameterRow;fun_prop

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule82

/- Helper module Solutions.RegevBridgeInitialGaussianNativeStep. -/
section P2MDyadicModule83

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

abbrev ScalarRow := ℚ × List ℚ

abbrev RawBlock := List (List Bool × List Bool)

abbrev DrawState := (List Unit × List ℤ) × List RawBlock

/-- One actual native right-to-left scalar call stores its new integer
coordinate and consumes one fresh public-sized block of supplied bits. -/
def drawStep (state : DrawState) (row : ScalarRow) : DrawState :=
  let center := -IntegerBasis.Native.dot (row.2,state.1.2)
  let value := Wide.sample (((row.1,center),state.1.1),state.2.head?.getD [])
  ((state.1.1,value::state.1.2),state.2.tail)

@[fun_prop] theorem drawStep_poly : Poly (fun input : DrawState × ScalarRow => drawStep input.1 input.2) := by
  unfold drawStep
  fun_prop

noncomputable section

/-- Magnitude, rather than numerator height of an intermediate center,
controls the integers retained by the native sequential loop. -/
theorem native_dot_abs_bound (coefficients : List ℚ) (word : List ℤ)
    (coefficientBound wordBound : ℚ) (hc : 0 ≤ coefficientBound) (hw : 0 ≤ wordBound)
    (hcoefficients : ∀ value ∈ coefficients,|value| ≤ coefficientBound)
    (hword : ∀ value ∈ word,|(value : ℚ)| ≤ wordBound) :
    |IntegerBasis.Native.dot (coefficients,word)| ≤ coefficients.length*coefficientBound*wordBound := by
  induction coefficients generalizing word with
  | nil => simp [IntegerBasis.Native.dot]
  | cons coefficient rest ih =>
    cases word with
    | nil => simp only [IntegerBasis.Native.dot,List.zip_nil_right,List.map_nil,List.sum_nil,abs_zero]
             positivity
    | cons value remaining =>
      have hhead := hcoefficients coefficient (by simp)
      have hvalue := hword value (by simp)
      have htail := ih remaining (fun item membership => hcoefficients item (by simp [membership]))
        (fun item membership => hword item (by simp [membership]))
      change |coefficient*(value : ℚ)+IntegerBasis.Native.dot (rest,remaining)| ≤ _
      apply (abs_add_le _ _).trans
      have hproduct : |coefficient*(value : ℚ)| ≤ coefficientBound*wordBound := by
        rw [abs_mul]
        exact mul_le_mul hhead hvalue (abs_nonneg _) hc
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      linarith

/-- Each stored integer gains only an additive number of bits at one
native scalar call, even for an exponentially wide proposal interval. -/
theorem drawStep_integer_bound (state : DrawState) (row : ScalarRow) (wordHeight rowHeight : ℕ)
    (hword : ∀ value ∈ state.1.2,|(value : ℚ)| ≤ (2 : ℚ)^wordHeight)
    (hcoefficients : ∀ value ∈ row.2,|value| ≤ (2 : ℚ)^rowHeight)
    (hvariance : row.1 ≤ (2 : ℚ)^rowHeight) :
    ∀ value ∈ (drawStep state row).1.2,
      |(value : ℚ)| ≤ (2 : ℚ)^(wordHeight+row.2.length+rowHeight+state.1.1.length+6) := by
  have hdot := native_dot_abs_bound row.2 state.1.2 (2^rowHeight) (2^wordHeight)
    (by positivity) (by positivity) hcoefficients hword
  have hsample := Wide.sample_abs_binary ((row.1,-IntegerBasis.Native.dot (row.2,state.1.2)),state.1.1)
    rowHeight hvariance (state.2.head?.getD [])
  simp only [abs_neg] at hsample
  let exponent := wordHeight+row.2.length+rowHeight+state.1.1.length+5
  have hcount : (row.2.length : ℚ) ≤ 2^row.2.length := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=row.2.length)).le
  have hdotBound : |IntegerBasis.Native.dot (row.2,state.1.2)| ≤ (2 : ℚ)^exponent := by
    apply hdot.trans
    calc
      _ ≤ (2 : ℚ)^row.2.length*2^rowHeight*2^wordHeight := by gcongr
      _ = 2^(row.2.length+rowHeight+wordHeight) := by rw [pow_add,pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by dsimp [exponent];omega)
  have hwideBound : (2 : ℚ)^(state.1.1.length+rowHeight+5) ≤ 2^exponent :=
    pow_le_pow_right₀ (by norm_num) (by dsimp [exponent];omega)
  have hnext : (2 : ℚ)^(wordHeight+row.2.length+rowHeight+state.1.1.length+6)=2^exponent*2 := by
    rw [show wordHeight+row.2.length+rowHeight+state.1.1.length+6=exponent+1 by rfl,pow_succ]
  intro value membership
  change value ∈ _::_ at membership
  rcases List.mem_cons.mp membership with hhead|htail
  · subst value
    rw [hnext]
    linarith
  · exact (hword value htail).trans (pow_le_pow_right₀ (by norm_num) (by omega))

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule83

/- Helper module Solutions.RegevBridgeInitialGaussianNativeFold. -/
section P2MDyadicModule84

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

theorem drawFold_accuracy (rows : List ScalarRow) (state : DrawState) :
    (rows.foldl drawStep state).1.1=state.1.1 := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => exact ih (drawStep state row)

theorem drawFold_word_length (rows : List ScalarRow) (state : DrawState) :
    (rows.foldl drawStep state).1.2.length=state.1.2.length+rows.length := by
  induction rows generalizing state with
  | nil => simp
  | cons row rows ih =>
    rw [List.foldl_cons,ih]
    simp only [drawStep,List.length_cons]
    omega

theorem drawFold_random (rows : List ScalarRow) (state : DrawState) :
    (rows.foldl drawStep state).2=state.2.drop rows.length := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih =>
    rw [List.foldl_cons,ih]
    simp only [drawStep,List.length_cons,List.drop_tail]

theorem drawFold_integer_bound (rows : List ScalarRow) (state : DrawState)
    (wordHeight rowHeight coefficientCount : ℕ)
    (hword : ∀ value ∈ state.1.2,|(value : ℚ)| ≤ (2 : ℚ)^wordHeight)
    (hrows : ∀ row ∈ rows,row.1 ≤ (2 : ℚ)^rowHeight ∧
      (∀ value ∈ row.2,|value| ≤ (2 : ℚ)^rowHeight) ∧ row.2.length ≤ coefficientCount) :
    ∀ value ∈ (rows.foldl drawStep state).1.2,
      |(value : ℚ)| ≤ (2 : ℚ)^(wordHeight+rows.length*(coefficientCount+rowHeight+state.1.1.length+6)) := by
  induction rows generalizing state wordHeight with
  | nil => simpa only [List.foldl_nil,List.length_nil,zero_mul,add_zero] using hword
  | cons row rows ih =>
    obtain ⟨hvariance,hcoefficients,hcount⟩ := hrows row (by simp)
    have hstep := drawStep_integer_bound state row wordHeight rowHeight hword hcoefficients hvariance
    have hstepWide : ∀ value ∈ (drawStep state row).1.2,
        |(value : ℚ)| ≤ (2 : ℚ)^(wordHeight+coefficientCount+rowHeight+state.1.1.length+6) := by
      intro value membership
      apply (hstep value membership).trans
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h := ih (drawStep state row) (wordHeight+coefficientCount+rowHeight+state.1.1.length+6)
      hstepWide (fun value membership => hrows value (by simp [membership]))
    have hexponent : wordHeight+coefficientCount+rowHeight+state.1.1.length+6+
        rows.length*(coefficientCount+rowHeight+(drawStep state row).1.1.length+6)=
        wordHeight+(row::rows).length*(coefficientCount+rowHeight+state.1.1.length+6) := by
      simp only [drawStep,List.length_cons]
      ring
    simpa only [List.foldl_cons,hexponent] using h

theorem encoded_drop_le {Value : Type} (encoding : Value → List Bool) (values : List Value) (count : ℕ) :
    (encodeList encoding (values.drop count)).length ≤ (encodeList encoding values).length := by
  have h := congrArg (fun list => (encodeList encoding list).length) (List.take_append_drop count values)
  rw [EncodedList.append,List.length_append] at h
  omega

theorem rational_abs_encoding (value : ℚ) : |value| ≤ (2 : ℚ)^(Ratio.encode value).length := by
  have hnum : |(value.num : ℚ)| ≤ (2 : ℚ)^(Ratio.encode value).length := by
    exact_mod_cast (Ratio.height_length value).1
  have hden : (1 : ℚ) ≤ value.den := by exact_mod_cast value.den_pos
  have hdenAbs : |(value.den : ℚ)|=(value.den : ℚ) := abs_of_nonneg (Nat.cast_nonneg _)
  calc
    |value|=|(value.num : ℚ)/(value.den : ℚ)| := congrArg abs value.num_div_den.symm
    _ = |(value.num : ℚ)|/(value.den : ℚ) := by rw [abs_div,hdenAbs]
    _ ≤ |(value.num : ℚ)| := div_le_self (abs_nonneg _) hden
    _ ≤ _ := hnum

theorem integer_encoding_magnitude (value : ℤ) :
    |(value : ℚ)| ≤ (2 : ℚ)^(Signed.encode value).length := by
  have h := (NatBinary.le_two_pow_length value.natAbs).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show value.natAbs.bits.length ≤ (Signed.encode value).length by rw [Signed.encode_length];omega))
  have hcast := (Nat.cast_le (α:=ℚ)).mpr h
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs] using hcast

theorem integer_encoding_bound (value : ℤ) (height : ℕ) (hvalue : |(value : ℚ)| ≤ (2 : ℚ)^height) :
    (Signed.encode value).length ≤ height+4 := by
  have habs : (value.natAbs : ℚ) ≤ (2 : ℚ)^height := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hvalue
  have hn : value.natAbs ≤ 2^height := by exact_mod_cast habs
  have hbits := NatBinary.length_le_height hn
  rw [Signed.encode_length]
  omega

theorem integer_word_encoding_bound (word : List ℤ) (height : ℕ)
    (hword : ∀ value ∈ word,|(value : ℚ)| ≤ (2 : ℚ)^height) :
    (encodeList Signed.encode word).length ≤ word.length*(2*height+9) := by
  have h := encoded_list_length_bound Signed.encode word (height+4)
    (fun value membership => integer_encoding_bound value height (hword value membership))
  simpa only [show 2*(height+4)+1=2*height+9 by omega] using h

theorem scalarRow_encoding_bounds (row : ScalarRow) :
    row.1 ≤ (2 : ℚ)^(enc row).length ∧
      (∀ value ∈ row.2,|value| ≤ (2 : ℚ)^(enc row).length) ∧ row.2.length ≤ (enc row).length := by
  have hlength : (enc row).length=2*(Ratio.encode row.1).length+1+(encodeList Ratio.encode row.2).length :=
    encodePair_length _ _ _
  refine ⟨?_,?_,?_⟩
  · exact (le_abs_self _).trans ((rational_abs_encoding _).trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  · intro value membership
    have hentry := EncodedList.member_length Ratio.encode row.2 value membership
    exact (rational_abs_encoding value).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  · have h := EncodedList.length_le Ratio.encode row.2
    omega

theorem drawState_encoding_length (state : DrawState) :
    (enc state).length=4*state.1.1.length+2*(encodeList Signed.encode state.1.2).length+
      (enc state.2).length+3 := by
  change (encodePair (encodePair enc enc) enc state).length=_
  simp only [encodePair_length]
  change 2*(2*(enc state.1.1).length+1+(encodeList Signed.encode state.1.2).length)+1+(enc state.2).length=_
  rw [ticks_encoding_length]
  ring

/-- Every intermediate native sampling state has polynomial binary length
on arbitrary public rows and arbitrary supplied finite bit lists. -/
theorem drawFold_bound (rows : List ScalarRow) (state : DrawState)
    (pre suffix : List ScalarRow) (hsplit : rows=pre++suffix) :
    (enc (pre.foldl drawStep state)).length ≤
      (200*(Polynomial.X+1)^3 : Polynomial ℕ).eval
        (encodePair (encodeList (enc : ScalarRow → List Bool)) enc (rows,state)).length := by
  let length := (encodePair (encodeList (enc : ScalarRow → List Bool)) enc (rows,state)).length
  have hinput : length=2*(encodeList (enc : ScalarRow → List Bool) rows).length+1+(enc state).length :=
    encodePair_length _ _ _
  have hstate : (enc state).length ≤ length := by omega
  have hrowCode : (encodeList (enc : ScalarRow → List Bool) rows).length ≤ length := by omega
  have hstateFields := drawState_encoding_length state
  have hticks : state.1.1.length ≤ length := by omega
  have hwordCode : (encodeList Signed.encode state.1.2).length ≤ length := by omega
  have hrandomCode : (enc state.2).length ≤ length := by omega
  have hwordLength : state.1.2.length ≤ length :=
    (EncodedList.length_le Signed.encode state.1.2).trans hwordCode
  have hpreLength : pre.length ≤ length := by
    have hpre : pre.length ≤ rows.length := by rw [hsplit,List.length_append];omega
    exact hpre.trans ((EncodedList.length_le (enc : ScalarRow → List Bool) rows).trans hrowCode)
  have hword : ∀ value ∈ state.1.2,|(value : ℚ)| ≤ (2 : ℚ)^length := by
    intro value membership
    have hentry := EncodedList.member_length Signed.encode state.1.2 value membership
    exact (integer_encoding_magnitude value).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hrows : ∀ row ∈ pre,row.1 ≤ (2 : ℚ)^length ∧
      (∀ value ∈ row.2,|value| ≤ (2 : ℚ)^length) ∧ row.2.length ≤ length := by
    intro row membership
    have hall : row ∈ rows := by rw [hsplit];exact List.mem_append.mpr (Or.inl membership)
    have hentry := (EncodedList.member_length (enc : ScalarRow → List Bool) rows row hall).trans hrowCode
    obtain ⟨hvariance,hcoefficients,hcount⟩ := scalarRow_encoding_bounds row
    have hpower : (2 : ℚ)^(enc row).length ≤ 2^length := pow_le_pow_right₀ (by norm_num) hentry
    exact ⟨hvariance.trans hpower,fun value membership => (hcoefficients value membership).trans hpower,
      hcount.trans hentry⟩
  let outputHeight := length+length*(3*length+6)
  have houtput : ∀ value ∈ (pre.foldl drawStep state).1.2,|(value : ℚ)| ≤ (2 : ℚ)^outputHeight := by
    have h := drawFold_integer_bound pre state length length length hword hrows
    intro value membership
    apply (h value membership).trans
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [outputHeight]
    gcongr <;> omega
  have houtputLength : (pre.foldl drawStep state).1.2.length ≤ 2*length := by
    rw [drawFold_word_length]
    omega
  have houtputCode : (encodeList Signed.encode (pre.foldl drawStep state).1.2).length ≤
      2*length*(2*outputHeight+9) :=
    (integer_word_encoding_bound _ outputHeight houtput).trans (Nat.mul_le_mul_right _ houtputLength)
  have hremainingCode : (enc (pre.foldl drawStep state).2).length ≤ length := by
    rw [drawFold_random]
    exact (encoded_drop_le (enc : RawBlock → List Bool) state.2 pre.length).trans hrandomCode
  have hactual : (enc (pre.foldl drawStep state)).length ≤
      4*length+2*(2*length*(2*outputHeight+9))+length+3 := by
    rw [drawState_encoding_length,drawFold_accuracy]
    omega
  apply hactual.trans
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change 4*length+2*(2*length*(2*outputHeight+9))+length+3 ≤ 200*(length+1)^3
  dsimp [outputHeight]
  nlinarith [Nat.zero_le (length^3),Nat.zero_le (length^2)]

@[fun_prop] theorem drawFold_poly : Poly (fun input : List ScalarRow × DrawState =>
    input.1.foldl drawStep input.2) :=
  ⟨drawStep_poly.program.listFold (0,[]) (200*(Polynomial.X+1)^3) drawFold_bound⟩

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule84

/- Helper module Solutions.RegevBridgeInitialGaussianNativeDraw. -/
section P2MDyadicModule85

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding

abbrev DrawInput := (List ScalarRow × List Unit) × List RawBlock

/-- Actual polynomial-time native sequential sampler on materialized
rational scalar rows and independent supplied finite bit blocks. -/
def draw (input : DrawInput) : List ℤ :=
  ((input.1.1.reverse).foldl drawStep ((input.1.2,[]),input.2.reverse)).1.2

@[fun_prop] theorem draw_poly : Poly draw := by
  have h := Poly.comp drawFold_poly (show Poly (fun input : DrawInput =>
    (input.1.1.reverse,((input.1.2,([] : List ℤ)),input.2.reverse))) by fun_prop)
  unfold draw
  exact Poly.comp (f:=fun state : DrawState => state.1.2)
    (g:=fun input : DrawInput => (input.1.1.reverse).foldl drawStep ((input.1.2,[]),input.2.reverse))
    (show Poly (fun state : DrawState => state.1.2) by fun_prop) h

/-- Recursive specification of the same right-to-left actual native
calls, used only for proving the full finite-tape output law. -/
def drawRec (accuracy : List Unit) : List ScalarRow → List RawBlock → List ℤ
  | [],_ => []
  | row::tail,randomness =>
      let previous := drawRec accuracy tail randomness.tail
      let first := Wide.sample (((row.1,-IntegerBasis.Native.dot (row.2,previous)),accuracy),randomness.head?.getD [])
      first::previous

noncomputable section

theorem drawFold_random_suffix (rows : List ScalarRow) (accuracy : List Unit)
    (word : List ℤ) (blocks extra : List RawBlock) (hlength : rows.length=blocks.length) :
    rows.foldl drawStep ((accuracy,word),blocks++extra)=
      ((rows.foldl drawStep ((accuracy,word),blocks)).1,extra) := by
  induction rows generalizing word blocks with
  | nil =>
    have hblocks : blocks=[] := List.length_eq_zero_iff.mp hlength.symm
    simp only [hblocks,List.nil_append,List.foldl_nil]
  | cons row rows ih =>
    cases blocks with
    | nil => simp at hlength
    | cons first blocks =>
      have htail : rows.length=blocks.length := by simpa using hlength
      simp only [List.foldl_cons,drawStep,List.cons_append,List.head?_cons,Option.getD_some,List.tail_cons]
      exact ih _ _ htail

/-- The actual native fold is exactly the recursive finite-tape sampler
when the supplied public row and tape-block counts agree. -/
theorem draw_eq_rec (rows : List ScalarRow) (accuracy : List Unit) (blocks : List RawBlock)
    (hlength : rows.length=blocks.length) :
    draw ((rows,accuracy),blocks)=drawRec accuracy rows blocks := by
  induction rows generalizing blocks with
  | nil => rfl
  | cons row rows ih =>
    cases blocks with
    | nil => simp at hlength
    | cons first blocks =>
      have htail : rows.length=blocks.length := by simpa using hlength
      have hreverse : rows.reverse.length=blocks.reverse.length := by simpa using htail
      have hsuffix := drawFold_random_suffix rows.reverse accuracy [] blocks.reverse [first] hreverse
      have haccuracy := drawFold_accuracy rows.reverse ((accuracy,[]),blocks.reverse)
      have hprevious := ih blocks htail
      simp only [draw,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [hsuffix]
      simp only [drawStep,List.head?_cons,Option.getD_some,List.tail_cons,drawRec]
      rw [haccuracy]
      change (rows.reverse.foldl drawStep ((accuracy,[]),blocks.reverse)).1.2=drawRec accuracy rows blocks at hprevious
      rw [hprevious]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule85

/- Helper module Solutions.RegevBridgeInitialGaussianNativeRows. -/
section P2MDyadicModule86

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

/-- Native upper-triangular row conversion removes all coordinates not
yet drawn by the right-to-left loop. -/
def trimRow (input : List ScalarRow × ℕ) : ScalarRow :=
  let row := input.1[input.2]?.getD (0,[])
  (row.1,row.2.drop (input.2+1))

@[fun_prop] theorem trimRow_poly : Poly trimRow := by
  have hrow : Poly (fun input : List ScalarRow × ℕ => input.1[input.2]?.getD (0,[])) := by fun_prop
  have hfirst := Poly.comp (f:=Prod.fst) Poly.fst hrow
  have hsecond := Poly.comp (f:=Prod.snd) Poly.snd hrow
  have hdrop := Poly.comp (f:=fun pair : List ℚ × ℕ => pair.1.drop pair.2)
    (g:=fun input : List ScalarRow × ℕ => ((input.1[input.2]?.getD (0,[])).2,input.2+1))
    QMCNumericRuntime.parser_drop_poly (Poly.pair hsecond (by fun_prop))
  unfold trimRow
  exact Poly.pair hfirst hdrop

def trimRows (input : List ScalarRow) : List ScalarRow :=
  (List.range input.length).map (fun row => trimRow (input,row))

@[fun_prop] theorem trimRows_poly : Poly trimRows := by
  unfold trimRows
  exact Poly.list_map trimRow_poly Poly.list_indices

/-- Rational upper-chain rows in the same original order as the matrix. -/
def upperRows : (count : ℕ) → (Fin count → ℚ) → Matrix (Fin count) (Fin count) ℚ → List ScalarRow
  | 0,_,_ => []
  | count+1,variance,upper => (variance 0,List.ofFn (fun column => upper 0 column.succ))::
      upperRows count (fun row => variance row.succ) (fun row column => upper row.succ column.succ)

noncomputable section

theorem upperRows_length (count : ℕ) (variance : Fin count → ℚ) (upper : Matrix (Fin count) (Fin count) ℚ) :
    (upperRows count variance upper).length=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [upperRows,List.length_cons,ih]

theorem upperRows_eq_ofFn (count : ℕ) (variance : Fin count → ℚ) (upper : Matrix (Fin count) (Fin count) ℚ) :
    upperRows count variance upper=List.ofFn (fun row =>
      (variance row,(List.ofFn (fun column => upper row column)).drop (row.val+1))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [upperRows,ih,List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Fin.val_zero,zero_add,List.ofFn_succ,List.drop_succ_cons,List.drop_zero]
    · apply congrArg List.ofFn
      funext row
      simp only [Fin.val_succ]
      rw [List.ofFn_succ,List.drop_succ_cons]

theorem trimRows_ofFn (count : ℕ) (variance : Fin count → ℚ) (upper : Matrix (Fin count) (Fin count) ℚ) :
    trimRows (List.ofFn (fun row => (variance row,List.ofFn (fun column => upper row column))))=
      upperRows count variance upper := by
  rw [upperRows_eq_ofFn]
  apply List.ext_getElem
  · simp only [trimRows,List.length_map,List.length_range,List.length_ofFn]
  · intro row hfirst hsecond
    have hrow : row < count := by
      simpa only [trimRows,List.length_map,List.length_range,List.length_ofFn] using hfirst
    simp only [trimRows,List.length_ofFn,List.getElem_map,List.getElem_range,trimRow,List.getElem?_ofFn,
      hrow,↓reduceDIte,Option.getD_some,List.getElem_ofFn]

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule86

/- Helper module Solutions.RegevBridgeInitialGaussianNativeRefinement. -/
section P2MDyadicModule87

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

/-- All scalar bit blocks are materialized from the predetermined public
variance-only tape spaces; no conditional center is sampled or observed. -/
def chainRawData (accuracy : List Unit) : {count : ℕ} → (chain : RationalGaussianChain count) →
    Wide.ChainRandom accuracy chain → List RawBlock
  | 0,.nil,_ => []
  | _+1,.cons variance _ tail,word =>
      (Wide.retryData (Wide.pointInput ((variance,0),accuracy))
        (Wide.attemptTicks (Wide.publicConfigure ((variance,0),accuracy)).2).length word.1).2::
      chainRawData accuracy tail word.2

noncomputable section

theorem chainRawData_length {count : ℕ} (chain : RationalGaussianChain count) (accuracy : List Unit)
    (word : Wide.ChainRandom accuracy chain) : (chainRawData accuracy chain word).length=count := by
  induction chain with
  | nil => rfl
  | @cons count variance center tail ih => simp only [chainRawData,List.length_cons,ih]

private theorem vectorGet_ofFn {count : ℕ} (function : Fin count → ℤ) :
    (Vector.ofFn function).get=function := by
  funext index
  exact Vector.get_ofFn _ _

/-- The literal native scalar-call recursion computes exactly the analyzed
upper rational chain on every one of its fixed fair-bit input streams. -/
theorem drawRec_upper_refinement (count : ℕ) (variance : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) (accuracy : List Unit)
    (word : Wide.ChainRandom accuracy (upperRationalGaussianChain count variance 0 upper)) :
    drawRec accuracy (upperRows count variance upper)
        (chainRawData accuracy (upperRationalGaussianChain count variance 0 upper) word)=
      List.ofFn (Wide.chainDraw accuracy (upperRationalGaussianChain count variance 0 upper) word).get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have htail := ih (fun row => variance row.succ) (fun row column => upper row.succ column.succ) word.2
    simp only [upperRows,upperRationalGaussianChain,chainRawData,drawRec,Wide.chainDraw,
      List.head?_cons,Option.getD_some,List.tail_cons,vectorGet_ofFn,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,
      Pi.zero_apply,sub_zero,zero_sub]
    apply congrArg₂ List.cons
    · have hdot := congrArg (fun previous : List ℤ => IntegerBasis.Native.dot
        (List.ofFn (fun column : Fin count => upper 0 column.succ),previous)) htail
      rw [IntegerBasis.Native.dot_ofFn] at hdot
      have hsample := congrArg (fun value : ℚ => Wide.sample (((variance 0,-value),accuracy),
        (Wide.retryData (Wide.pointInput ((variance 0,0),accuracy))
          (Wide.attemptTicks (Wide.publicConfigure ((variance 0,0),accuracy)).2).length word.1).2)) hdot
      exact hsample
    · exact htail

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule87

/- Helper module Solutions.RegevBridgeInitialGaussianFlatRowsLaw. -/
section P2MDyadicModule88

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1600000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open AFT AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

/-- Sum of all public scalar tape lengths; each row receives a whole block
of this length, so no row's conditional center affects its tape space. -/
def chainBits (accuracy : List Unit) : {count : ℕ} → RationalGaussianChain count → ℕ
  | 0,.nil => 0
  | _+1,.cons variance _ tail => Wide.scalarBits variance accuracy+chainBits accuracy tail

/-- Genuine row-prefix parsing of a common padded block, coordinate by
coordinate. Only public variances and fresh independent rows are read. -/
def decodeRows (accuracy : List Unit) (total : ℕ) : {count : ℕ} →
    (chain : RationalGaussianChain count) → chainBits accuracy chain ≤ total →
      (Fin count → Fin total → Bool) → Wide.ChainRandom accuracy chain
  | 0,.nil,_,_ => ()
  | _+1,.cons variance _ tail,hbits,word =>
      (Wide.decodeScalarTape variance accuracy total (by simpa only [chainBits] using
        (Nat.le_add_right (Wide.scalarBits variance accuracy) (chainBits accuracy tail)).trans hbits) (word 0),
       decodeRows accuracy total tail
        ((Nat.le_add_left (chainBits accuracy tail) (Wide.scalarBits variance accuracy)).trans hbits)
        (fun index => word index.succ))

/-- Exact head/tail decomposition of actual row addresses. -/
def rowsConsEquiv (count total : ℕ) : (Fin (count+1) → Fin total → Bool) ≃
    (Fin total → Bool) × (Fin count → Fin total → Bool) where
  toFun word := (word 0,fun index => word index.succ)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv word := by funext index;exact Fin.cases (by rfl) (fun _ => rfl) index
  right_inv pair := by cases pair;rfl

/-- All row tapes jointly induce exactly the analyzed fresh-product law.
No independence of the final Gaussian coordinates is asserted. -/
theorem decodeRows_law (accuracy : List Unit) (total : ℕ) {count : ℕ}
    (chain : RationalGaussianChain count) (hbits : chainBits accuracy chain ≤ total) :
    (FiniteDist.uniform (Fin count → Fin total → Bool)).map (decodeRows accuracy total chain hbits)=
      Wide.chainRandomLaw accuracy chain := by
  classical
  induction chain with
  | nil =>
    ext output
    cases output
    simp [decodeRows,Wide.chainRandomLaw,FiniteDist.map_weight,FiniteDist.uniform_weight]
  | @cons count variance center tail ih =>
    have hhead : Wide.scalarBits variance accuracy ≤ total := (Nat.le_add_right _ _).trans hbits
    have htail : chainBits accuracy tail ≤ total := (Nat.le_add_left _ _).trans hbits
    let head := Wide.decodeScalarTape variance accuracy total hhead
    let rest := decodeRows accuracy total tail htail
    calc
      _ = ((FiniteDist.uniform (Fin (count+1) → Fin total → Bool)).map
          (rowsConsEquiv count total)).map (fun pair => (head pair.1,rest pair.2)) := by
        rw [FiniteDist.map_map]
        rfl
      _ = (FiniteDist.uniform ((Fin total → Bool) × (Fin count → Fin total → Bool))).map
          (fun pair => (head pair.1,rest pair.2)) := by rw [FiniteDist.uniform_map_equiv]
      _ = ((FiniteDist.uniform (Fin total → Bool)).prod
          (FiniteDist.uniform (Fin count → Fin total → Bool))).map
          (fun pair => (head pair.1,rest pair.2)) := by rw [Wide.product_uniform]
      _ = ((FiniteDist.uniform (Fin total → Bool)).map head).prod
          ((FiniteDist.uniform (Fin count → Fin total → Bool)).map rest) :=
        FiniteDist.map_prod_functions _ _ head rest
      _ = Wide.chainRandomLaw accuracy (.cons variance center tail) := by
        rw [show (FiniteDist.uniform (Fin total → Bool)).map head=Wide.scalarRandomLaw variance accuracy from
          Wide.decodeScalarTape_law variance accuracy total hhead]
        rw [show (FiniteDist.uniform (Fin count → Fin total → Bool)).map rest=Wide.chainRandomLaw accuracy tail from ih htail]
        rfl

/-- Actual contiguous flat tape decomposition, with the same row-major
addresses used later by the executable take/drop parser. -/
def decodeFlatChain (accuracy : List Unit) (total : ℕ) {count : ℕ}
    (chain : RationalGaussianChain count) (hbits : chainBits accuracy chain ≤ total)
    (word : Fin (count*total) → Bool) : Wide.ChainRandom accuracy chain :=
  decodeRows accuracy total chain hbits (Integration9_9.BlockCoins.blockEquiv count total word)

theorem decodeFlatChain_law (accuracy : List Unit) (total : ℕ) {count : ℕ}
    (chain : RationalGaussianChain count) (hbits : chainBits accuracy chain ≤ total) :
    (FiniteDist.uniform (Fin (count*total) → Bool)).map (decodeFlatChain accuracy total chain hbits)=
      Wide.chainRandomLaw accuracy chain := by
  have h := congrArg (fun law : FiniteDist (Fin count → Fin total → Bool) =>
      law.map (decodeRows accuracy total chain hbits))
    (FiniteDist.uniform_map_equiv (Integration9_9.BlockCoins.blockEquiv count total))
  rw [FiniteDist.map_map] at h
  exact h.trans (decodeRows_law accuracy total chain hbits)

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule88

/- Helper module Solutions.RegevBridgeInitialGaussianFlatRowsNative. -/
section P2MDyadicModule89

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT AFT.RationalNumerics GaussianRandomizedRounding

abbrev FlatRowsInput := (List ScalarRow × List Unit) × List Bool

/-- A public common row budget is the sum of all scalar request budgets. -/
def rowTicks (input : List ScalarRow × List Unit) : List Unit :=
  input.1.flatMap (fun row => Wide.randomTicks ((row.1,0),input.2))

@[fun_prop] theorem rowTicks_poly : Poly rowTicks := by unfold rowTicks;fun_prop

/-- An actual scalar raw block is reconstructed only from this row's own
padded fair-bit slice and the public variance/accuracy metadata. -/
def parseRow (input : FlatRowsInput × ℕ) : RawBlock :=
  let row := input.1.1.1[input.2]?.getD (0,[])
  Wide.flatRawBlock ((row.1,input.1.1.2),
    rowSlice (((rowTicks input.1.1).length,input.1.2),input.2))

@[fun_prop] theorem parseRow_poly : Poly parseRow := by
  have hrow : Poly (fun input : FlatRowsInput × ℕ => input.1.1.1[input.2]?.getD (0,[])) := by fun_prop
  have hvariance := Poly.comp (f:=Prod.fst) Poly.fst hrow
  have hslice : Poly (fun input : FlatRowsInput × ℕ =>
      rowSlice (((rowTicks input.1.1).length,input.1.2),input.2)) := by fun_prop
  unfold parseRow
  exact Poly.comp Wide.flatRawBlock_poly (Poly.pair (Poly.pair hvariance (by fun_prop)) hslice)

def flatRawRows (input : FlatRowsInput) : List RawBlock :=
  (List.range input.1.1.length).map (fun row => parseRow (input,row))

@[fun_prop] theorem flatRawRows_poly : Poly flatRawRows := by
  unfold flatRawRows
  exact Poly.list_map parseRow_poly (Poly.comp (f:=fun rows : List ScalarRow => List.range rows.length)
    (g:=fun input : FlatRowsInput => input.1.1) Poly.list_indices (by fun_prop))

/-- Padding every public row to the common budget keeps the entire source
length polynomial without any hidden variance or center oracle. -/
def paddedRowsTicks (input : List ScalarRow × List Unit) : List Unit :=
  input.1.flatMap (fun _ => rowTicks input)

@[fun_prop] theorem paddedRowsTicks_poly : Poly paddedRowsTicks := by unfold paddedRowsTicks;fun_prop

noncomputable section

theorem rowSlice_ofFn (count total : ℕ) (tape : Fin (count*total) → Bool) (row : Fin count) :
    rowSlice ((total,List.ofFn tape),row.val)=
      List.ofFn (Integration9_9.BlockCoins.blockEquiv count total tape row) := by
  have h := congrArg Prod.fst (Wide.splitTrial_ofFn total 0 count (count*total) (by simp) tape row)
  change (Wide.splitTrial ((total,0),(List.ofFn tape,row.val))).1=_
  refine h.trans ?_
  apply congrArg List.ofFn
  funext bit
  apply congrArg tape
  apply Fin.ext
  rfl

theorem paddedRowsTicks_length (input : List ScalarRow × List Unit) :
    (paddedRowsTicks input).length=input.1.length*(rowTicks input).length := by
  have h (rows : List ScalarRow) (ticks : List Unit) :
      (rows.flatMap (fun _ => ticks)).length=rows.length*ticks.length := by
    induction rows with
    | nil => simp
    | cons row rest ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,ih,Nat.add_mul,Nat.one_mul];omega
  exact h input.1 (rowTicks input)

/-- Public padding equality is kept separate from the tape type, avoiding
any runtime casts or data-dependent changes in the number of fair bits. -/
theorem parseRow_ofFn_budget {count : ℕ} (rows : Fin count → ScalarRow) (accuracy : List Unit)
    (total : ℕ) (htotal : (rowTicks (List.ofFn rows,accuracy)).length=total)
    (tape : Fin (count*total) → Bool) (row : Fin count) :
    parseRow (((List.ofFn rows,accuracy),List.ofFn tape),row.val)=
      Wide.flatRawBlock (((rows row).1,accuracy),List.ofFn
        (Integration9_9.BlockCoins.blockEquiv count total tape row)) := by
  simp only [parseRow,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,Fin.eta,htotal]
  rw [rowSlice_ofFn]

theorem flatRawRows_ofFn_budget {count : ℕ} (rows : Fin count → ScalarRow) (accuracy : List Unit)
    (total : ℕ) (htotal : (rowTicks (List.ofFn rows,accuracy)).length=total)
    (tape : Fin (count*total) → Bool) :
    flatRawRows ((List.ofFn rows,accuracy),List.ofFn tape)=
      List.ofFn (fun row => Wide.flatRawBlock (((rows row).1,accuracy),List.ofFn
        (Integration9_9.BlockCoins.blockEquiv count total tape row))) := by
  apply List.ext_getElem
  · simp only [flatRawRows,List.length_map,List.length_range,List.length_ofFn]
  · intro row hleft hright
    have hrow : row < count := by simpa only [flatRawRows,List.length_map,List.length_range,List.length_ofFn] using hleft
    simpa only [flatRawRows,List.length_ofFn,List.getElem_map,List.getElem_range,List.getElem_ofFn] using
      parseRow_ofFn_budget rows accuracy total htotal tape ⟨row,hrow⟩

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule89

/- Helper module Solutions.RegevBridgeInitialGaussianFlatRowsRefinement. -/
section P2MDyadicModule90

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open AFT AFT.RationalNumerics GaussianRandomizedRounding

/-- The native sum of actual public scalar coin requests equals the
abstract chain's exact required budget, irrespective of its centers. -/
theorem rowTicks_upper (count : ℕ) (variance center : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) (accuracy : List Unit) :
    (rowTicks (upperRows count variance upper,accuracy)).length=
      chainBits accuracy (upperRationalGaussianChain count variance center upper) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [upperRows,rowTicks,List.flatMap_cons,List.length_append,
      upperRationalGaussianChain,chainBits,Wide.scalarBits_eq_randomTicks]
    exact congrArg (Nat.add _) (ih (fun index => variance index.succ)
      (fun index => center index.succ) (fun row column => upper row.succ column.succ))

/-- Materializing all independently decoded row tapes reproduces exactly
the already verified raw blocks for the whole correlated Gaussian chain. -/
theorem chainRawData_decodeRows_upper (count : ℕ) (variance center : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) (accuracy : List Unit) (total : ℕ)
    (hbits : chainBits accuracy (upperRationalGaussianChain count variance center upper) ≤ total)
    (tape : Fin count → Fin total → Bool) :
    chainRawData accuracy (upperRationalGaussianChain count variance center upper)
      (decodeRows accuracy total (upperRationalGaussianChain count variance center upper) hbits tape)=
      List.ofFn (fun row => Wide.flatRawBlock ((variance row,accuracy),List.ofFn (tape row))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hhead : Wide.scalarBits (variance 0) accuracy ≤ total :=
      (Nat.le_add_right _ _).trans hbits
    have htail : chainBits accuracy (upperRationalGaussianChain count (fun index => variance index.succ)
        (fun index => center index.succ) (fun row column => upper row.succ column.succ)) ≤ total :=
      (Nat.le_add_left _ _).trans hbits
    simp only [upperRationalGaussianChain,chainRawData,decodeRows,List.ofFn_succ]
    apply congrArg₂ List.cons
    · exact (Wide.flatRawBlock_correct (variance 0) accuracy total hhead (tape 0)).symm
    · exact ih (fun index => variance index.succ) (fun index => center index.succ)
        (fun row column => upper row.succ column.succ) htail (fun index => tape index.succ)

/-- Executable take/drop row addressing is the same exact BlockCoins
addressing used by the independent product-law proof. -/
theorem flatRawRows_upper (count : ℕ) (variance : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) (accuracy : List Unit) (total : ℕ)
    (htotal : (rowTicks (upperRows count variance upper,accuracy)).length=total)
    (tape : Fin (count*total) → Bool) :
    flatRawRows ((upperRows count variance upper,accuracy),List.ofFn tape)=
      List.ofFn (fun row => Wide.flatRawBlock ((variance row,accuracy),List.ofFn
        (Integration9_9.BlockCoins.blockEquiv count total tape row))) := by
  let rows : Fin count → ScalarRow := fun row =>
    (variance row,(List.ofFn (fun column => upper row column)).drop (row.val+1))
  have hrows : upperRows count variance upper=List.ofFn rows := upperRows_eq_ofFn count variance upper
  have htotal' : (rowTicks (List.ofFn rows,accuracy)).length=total := by rw [←hrows];exact htotal
  calc
    _ = flatRawRows ((List.ofFn rows,accuracy),List.ofFn tape) :=
      congrArg (fun values => flatRawRows ((values,accuracy),List.ofFn tape)) hrows
    _ = _ := flatRawRows_ofFn_budget rows accuracy total htotal' tape

theorem flatRawRows_upper_decode (count : ℕ) (variance center : Fin count → ℚ)
    (upper : Matrix (Fin count) (Fin count) ℚ) (accuracy : List Unit) (total : ℕ)
    (htotal : (rowTicks (upperRows count variance upper,accuracy)).length=total)
    (hbits : chainBits accuracy (upperRationalGaussianChain count variance center upper) ≤ total)
    (tape : Fin (count*total) → Bool) :
    flatRawRows ((upperRows count variance upper,accuracy),List.ofFn tape)=
      chainRawData accuracy (upperRationalGaussianChain count variance center upper)
        (decodeFlatChain accuracy total (upperRationalGaussianChain count variance center upper) hbits tape) := by
  rw [flatRawRows_upper count variance upper accuracy total htotal tape]
  exact (chainRawData_decodeRows_upper count variance center upper accuracy total hbits
    (Integration9_9.BlockCoins.blockEquiv count total tape)).symm

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule90

/- Helper module Solutions.RegevBridgeInitialGaussianFlatRowsSource. -/
section P2MDyadicModule91

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 10000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open AFT AFT.RationalNumerics GaussianRandomizedRounding

noncomputable section

/-- Equal public tape lengths give the same exact fair-bit experiment;
all list inputs to the native program are kept unchanged. -/
theorem uniformTape_mix_congr {Output : Type*} [Fintype Output] {first second : ℕ}
    (h : first=second) (channel : List Bool → FiniteDist Output) :
    (FiniteDist.uniform (Fin first → Bool)).mix (fun word => channel (List.ofFn word))=
      (FiniteDist.uniform (Fin second → Bool)).mix (fun word => channel (List.ofFn word)) := by
  cases h
  rfl

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end P2MDyadicModule91

/- Helper module ExactWide. -/
section P2MDyadicModule92

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1500000

set_option maxRecDepth 12000

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RationalGramSchmidt

open AFT GaussianSource RationalNumerics GaussianRandomizedRounding

noncomputable section

/-- Rational multiplier corresponding to the exact specified Gaussian width. -/
def wideBase {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (W : ℚ) :=
  W / (1 + entryMass D)

theorem width_at_base {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (W : ℚ) :
    initialWidth D (wideBase D W) = W := by
  have h : 0 < 1+entryMass D := by linarith [entryMass_nonneg D]
  exact div_mul_cancel₀ _ h.ne'

theorem wideBase_floor {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (W : ℚ)
    (m : ℕ) (h : initialWidth D m ≤ W) : (m:ℚ) ≤ wideBase D W := by
  exact (le_div_iff₀ (by linarith [entryMass_nonneg D])).mpr h

theorem initial_channel_wide {n : ℕ} {Output : Type*} [Fintype Output]
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0)
    (m : ℕ) (hm : 2 ≤ m) (hn : n ≤ m) (b : ℚ) (hb : (m:ℚ) ≤ b)
    (accuracy : List Unit) (channel : (Fin n → ℤ) → FiniteDist Output) :
    FiniteDist.TVBound (Wide.chainChannel accuracy (initialChain D b) channel)
      (initialGaussianChannel D hD b (by
        have hi : (1:ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
        exact hi.trans hb) channel)
      (n*Wide.sampleError accuracy.length + 4*((n:ℝ)*initialThetaBudget m)) := by
  have hb1 : (1:ℚ) ≤ b := (by exact_mod_cast (show 1 ≤ m by omega) : (1:ℚ) ≤ m).trans hb
  have hw := initialChain_wide_one D hD b hb1
  have htv := Wide.chainChannel_accuracy (initialChain D b) hw accuracy channel
  apply htv.triangle
  apply FiniteDist.TVBound.symm
  apply FiniteDist.countableMix_tvBound
  apply initial_sequential_lattice_tv_linear D hD b (by linarith) _ (initialThetaBudget_nonneg m)
    (initialThetaBudget_small m hm) _ (initialThetaBudget_dimension n m hm hn)
  exact (thetaError_antitone (m:ℝ) b (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast hb)).trans
    (thetaError_integer_le m hm)

theorem initialMass_at_width {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0)
    (W : ℚ) (z : Fin n → ℤ) :
    initialMass D hD (wideBase D W) z = RegevSketch.coefficientMass D W z := by
  let e := (IntegerBasis.integerBasis D hD).equivFun.symm.toEquiv
  have hcoe (y : Fin n → ℤ) : RegevLWE.GaussConv.rho W (e y : EuclideanSpace ℝ (Fin n)) = rhoInt W (D.mulVec y) := by
    change RegevLWE.GaussConv.rho W ((IntegerBasis.integerBasis D hD).equivFun.symm y : EuclideanSpace ℝ (Fin n)) = _
    rw [IntegerBasis.coefficient_point]
    rfl
  unfold initialMass RegevSketch.coefficientMass
  rw [width_at_base, GaussianProjection.cosetMass_formula,add_zero]
  congr 1
  · exact hcoe z
  · unfold RegevLWE.GaussConv.rhoCoset
    simp only [add_zero]
    rw [←e.tsum_eq]
    exact tsum_congr hcoe

end

end InfoLossLAR.WorstCase.RationalGramSchmidt

end P2MDyadicModule92

/- Helper module ExactProgram. -/
section P2MDyadicModule93

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 1800000

set_option maxRecDepth 12000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

def rows (data : List (List ℤ) × ℚ) : List ScalarRow :=
  trimRows ((basisCache data.1).map (fun vector =>
    parameterRow ((data.2, rationalColumns (transpose data.1)),vector)))

@[fun_prop] theorem rows_poly : Poly rows := by unfold rows; fun_prop

abbrev Setup := (List (List ℤ) × ℚ) × List Unit

def ticks (s : Setup) : List Unit := paddedRowsTicks (rows s.1, s.2)

@[fun_prop] theorem ticks_poly : Poly ticks := by unfold ticks; fun_prop

def sample (u : Setup × List Bool) : List ℤ :=
  draw ((rows u.1.1,u.1.2),flatRawRows ((rows u.1.1,u.1.2),u.2))

@[fun_prop] theorem sample_poly : Poly sample := by unfold sample; fun_prop

def setup {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (W : ℚ) (a : List Unit) : Setup :=
  ((List.ofFn fun i => List.ofFn fun j => D i j,W),a)

theorem rows_correct {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (W : ℚ) :
    rows (List.ofFn (fun i => List.ofFn (fun j => D i j)),W) =
    upperRows n (initialVariance D (wideBase D W)) (upper (inputVectors D)) := by
  unfold rows
  rw [basisCache_correct D hD,cache_prefix_eq _ n (le_refl n)]
  simp only [List.map_ofFn, Function.comp_def]
  rw [←trimRows_ofFn]
  apply congrArg trimRows
  apply congrArg List.ofFn
  funext i
  rw [parameterRow,transpose_input_rows,rationalColumns_input]
  simp only [dot_ofFn,List.map_ofFn,Function.comp_def,initialVariance,width_at_base,
    squaredNorm,upper,pow_two,Fin.castLE_refl]

noncomputable section

/-- Flat-bit law for arbitrary explicitly generated upper-triangular rational
rows, including all conditional centers of the original dependent draw. -/
theorem flat_upper_law {n : ℕ} {Output : Type*} [Fintype Output] (variance : Fin n → ℚ)
    (upper : Matrix (Fin n) (Fin n) ℚ) (a : List Unit) (chan : (Fin n → ℤ) → FiniteDist Output) :
    let rows := upperRows n variance upper
    let control := (rows,a)
    (FiniteDist.uniform (Fin (paddedRowsTicks control).length → Bool)).mix
      (fun tape => chan (fun i => (draw (control,flatRawRows (control,List.ofFn tape)))[i.val]?.getD 0)) =
    Wide.chainChannel a (upperRationalGaussianChain n variance 0 upper) chan := by
  dsimp only
  let data := upperRows n variance upper
  let chain := upperRationalGaussianChain n variance 0 upper
  let total := (rowTicks (data,a)).length
  have hbits : chainBits a chain ≤ total := (rowTicks_upper n variance 0 upper a).symm.le
  have ht : (paddedRowsTicks (data,a)).length = n * total := by
    rw [paddedRowsTicks_length]
    change data.length*total=n*total
    rw [upperRows_length]
  change (FiniteDist.uniform (Fin (paddedRowsTicks (data,a)).length → Bool)).mix _ = _
  rw [uniformTape_mix_congr ht (fun bits => chan (fun i =>
    (draw ((data,a),flatRawRows ((data,a),bits)))[i.val]?.getD 0))]
  have hpath (tape : Fin (n*total) → Bool) :
      draw ((data,a),flatRawRows ((data,a),List.ofFn tape)) =
        List.ofFn (Wide.chainDraw a chain (decodeFlatChain a total chain hbits tape)).get := by
    rw [flatRawRows_upper_decode n variance 0 upper a total rfl hbits tape, draw_eq_rec]
    · apply drawRec_upper_refinement
    · rw [upperRows_length,chainRawData_length]
  have h := congrArg (fun law : FiniteDist (Wide.ChainRandom a chain) =>
    law.mix (fun raw => chan (Wide.chainDraw a chain raw).get))
    (decodeFlatChain_law a total chain hbits)
  rw [FiniteDist.mix_map] at h
  rw [← Wide.chainDraw_channel]
  convert h using 1
  apply congrArg (FiniteDist.mix _)
  funext tape
  rw [hpath]
  simp

theorem sample_law {n : ℕ} {Output : Type*} [Fintype Output]
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (W : ℚ) (a : List Unit)
    (chan : (Fin n → ℤ) → FiniteDist Output) :
    (FiniteDist.uniform (Fin (ticks (setup D W a)).length → Bool)).mix
      (fun tape => chan (fun i => (sample (setup D W a,List.ofFn tape))[i.val]?.getD 0)) =
    Wide.chainChannel a (initialChain D (wideBase D W)) chan := by
  change (FiniteDist.uniform (Fin (paddedRowsTicks
      (rows (List.ofFn (fun i => List.ofFn (fun j => D i j)),W),a)).length → Bool)).mix
    (fun tape => chan (fun i => (draw ((rows (List.ofFn (fun i => List.ofFn (fun j => D i j)),W),a),
      flatRawRows ((rows (List.ofFn (fun i => List.ofFn (fun j => D i j)),W),a),List.ofFn tape)))[i.val]?.getD 0)) = _
  rw [rows_correct D hD W]
  exact flat_upper_law (initialVariance D (wideBase D W)) (upper (inputVectors D)) a chan

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

end P2MDyadicModule93

/- Helper module InitLaw. -/
section P2MDyadicModule94

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 700000

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

open AFT AFT.RationalNumerics GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

/-- The actual flat fair-bit sampler at a rational public width W above the
coarse Gaussian floor. Both its sample and its tape-length generator are
the executable Poly programs in this namespace. The ideal output mass is
specified for an arbitrary finite stochastic channel of the coefficients. -/
theorem sample_at_width {n : ℕ} {O : Type*} [Fintype O]
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (W : ℚ)
    (m : ℕ) (hm : 2 ≤ m) (hn : n ≤ m) (hfloor : RationalGramSchmidt.initialWidth D m ≤ W)
    (a : List Unit) (ch : (Fin n → ℤ) → FiniteDist O) :
    let actual := (FiniteDist.uniform (Fin (ticks (setup D W a)).length → Bool)).mix
      (fun tape => ch (fun i => (sample (setup D W a,List.ofFn tape))[i.val]?.getD 0))
    ∃ ideal : FiniteDist O,
      (∀ o, ideal.weight o = ∑' z, RegevSketch.coefficientMass D W z * (ch z).weight o) ∧
      FiniteDist.TVBound actual ideal
        (n * Wide.sampleError a.length + 4 * ((n:ℝ) * initialThetaBudget m)) := by
  dsimp only
  have hb := wideBase_floor D W m hfloor
  have hb1 : (1:ℚ) ≤ wideBase D W := (show (1:ℚ) ≤ m by exact_mod_cast (show 1 ≤ m by omega)).trans hb
  refine ⟨initialGaussianChannel D hD (wideBase D W) hb1 ch, ?_, ?_⟩
  · intro o
    change (∑' z, initialMass D hD (wideBase D W) z * (ch z).weight o) = _
    simp only [initialMass_at_width D hD W]
  · rw [sample_law D hD W a ch]
    exact initial_channel_wide D hD m hm hn (wideBase D W) hb a ch

/-- Instantiation at the precise rational maximum used by the width schedule. -/
theorem scheduled_initial_sample {n : ℕ} {O : Type*} [Fintype O]
    (D : Matrix (Fin n) (Fin n) ℤ) (hD : D.det ≠ 0) (hn : 1 ≤ n)
    (r : ℚ) (a : List Unit) (ch : (Fin n → ℤ) → FiniteDist O) :
    let W := max (RationalGramSchmidt.initialWidth D (n+1:ℕ)) (r * (famσ n : ℚ))
    let actual := (FiniteDist.uniform (Fin (ticks (setup D W a)).length → Bool)).mix
      (fun tape => ch (fun i => (sample (setup D W a,List.ofFn tape))[i.val]?.getD 0))
    ∃ ideal : FiniteDist O,
      (∀ o, ideal.weight o = ∑' z, RegevSketch.coefficientMass D W z * (ch z).weight o) ∧
      FiniteDist.TVBound actual ideal
        (n * Wide.sampleError a.length + 4 * ((n:ℝ) * initialThetaBudget (n+1))) := by
  apply sample_at_width D hD _ (n+1) (by omega) (by omega) (le_max_left _ _) a ch

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native.ExactWide

end P2MDyadicModule94

/- Helper module WideWitness. -/
section P2MDyadicModule95

set_option autoImplicit false

set_option maxHeartbeats 900000

namespace InfoLossLAR.WorstCase.RegevSearch

open QAlgorithms.Complexity RegevSketch AFT AFT.RationalNumerics

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators Classical

theorem _root_.solution :
    ∃ (bits : (List (List ℤ) × ℚ) × List Unit → List Unit)
      (draw : ((List (List ℤ) × ℚ) × List Unit) × List Bool → List ℤ), Poly bits ∧ Poly draw ∧
    ∀ {n : ℕ} {O : Type} [Fintype O] (D : Matrix (Fin n) (Fin n) ℤ), D.det≠0 → 1≤n →
    ∀ (r : ℚ) (a : List Unit) (post : (Fin n→ℤ) → FiniteDist O),
    let W : ℚ := max ((n+1:ℕ)*(1+∑ i,∑ j,|(D i j:ℚ)|)) (r*(famσ n:ℚ))
    let cfg := ((List.ofFn (fun i=>List.ofFn (fun j=>D i j)), W),a)
    let actual := (FiniteDist.uniform (Fin (bits cfg).length → Bool)).mix
      (fun tape => post (fun i => (draw (cfg,List.ofFn tape))[i.val]?.getD 0))
    ∃ ideal : FiniteDist O, (∀ o, ideal.weight o=∑' z,coefficientMass D W z*(post z).weight o) ∧
      FiniteDist.TVBound actual ideal
        (n*(2/(2:ℝ)^a.length+6*Real.exp (-Real.pi*((a.length:ℝ)+2)^2/2))+
          4*((n:ℝ)*(4/(2:ℝ)^(4*(n+1))))) := by
  let ticks:=RationalGramSchmidt.Native.ExactWide.ticks
  let sample:=RationalGramSchmidt.Native.ExactWide.sample
  refine ⟨ticks,sample,RationalGramSchmidt.Native.ExactWide.ticks_poly,RationalGramSchmidt.Native.ExactWide.sample_poly,?_⟩
  intro n O _ D hD hn r a post
  exact RationalGramSchmidt.Native.ExactWide.scheduled_initial_sample D hD hn r a post

end InfoLossLAR.WorstCase.RegevSearch

end P2MDyadicModule95
