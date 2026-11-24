-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.tile_sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:41.620017+00:00
-- url     : https://prove2.me/submissions/f23cf467-265c-485b-a96f-c65be6df5830

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution {G ι : Type} [MeasurableSpace G] [Countable ι] (μ : Measure G)
    (tile : ι → Set G) (hm : ∀ i, MeasurableSet (tile i))
    (hd : Pairwise (Function.onFun Disjoint tile)) (hc : ⋃ i, tile i = Set.univ) (n : ℕ)
    (hn : ∀ i, μ (tile i) = n) (a : ι → ℝ) (ha : Summable a) (f g : G → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (h : ∀ i, ∀ y ∈ tile i, |a i - f y| ≤ g y) :
    |(n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ| ≤ ∫ y, g y ∂μ := by
  have hsum : ∀ {u : G → ℝ}, Integrable u μ →
      HasSum (fun i => ∫ y in tile i, u y ∂μ) (∫ y, u y ∂μ) := by
    intro u hu
    have := hasSum_integral_iUnion (f := u) (μ := μ) hm hd (by rw [hc]; exact hu.integrableOn)
    rwa [hc, setIntegral_univ] at this
  have hfin : ∀ i, μ (tile i) ≠ ⊤ := fun i => by rw [hn]; exact ENNReal.natCast_ne_top n
  have hconst : ∀ i, ∫ y in tile i, (a i - f y) ∂μ = (n : ℝ) * a i - ∫ y in tile i, f y ∂μ := by
    intro i
    have hi : Integrable (fun _ : G => a i) (μ.restrict (tile i)) := integrableOn_const (hfin i)
    rw [integral_sub hi hf.integrableOn, setIntegral_const]
    simp [Measure.real, hn, smul_eq_mul]
  have hA : HasSum (fun i => ∫ y in tile i, (a i - f y) ∂μ)
      ((n : ℝ) * ∑' i, a i - ∫ y, f y ∂μ) := by
    simp_rw [hconst]
    exact (ha.hasSum.mul_left _).sub (hsum hf)
  have key := hA.norm_le_of_bounded (hsum hg) (fun i => by
    refine norm_integral_le_of_norm_le hg.integrableOn ?_
    exact ae_restrict_of_forall_mem (hm i) (fun y hy => by
      simpa [Real.norm_eq_abs] using h i y hy))
  simpa [Real.norm_eq_abs] using key
end GlobalTheory.CompanionTheory.RiemannCore
