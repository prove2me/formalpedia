-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.compact_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:26.376081+00:00
-- url     : https://prove2.me/submissions/932cebfe-70d2-4114-a035-0d5528c03e51

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_norm_integral_schwartz_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution (m : Measure V) [IsFiniteMeasure m] (hi : Integrable (chf m)) {K U : Set V}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    m K ≤ ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) * volume U := by
  obtain ⟨K', hK', hKi, hKU'⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞)) (𝓘(ℝ, V))
    (isOpen_interior (s := K')).isClosed_compl hK.isClosed (s := (interior K')ᶜ) (t := K)
    (Set.disjoint_left.2 fun x hx hxK => hx (hKi hxK))
  have hχ : ContDiff ℝ ∞ (f : V → ℝ) := f.contMDiff.contDiff
  have hsupp : Function.support (f : V → ℝ) ⊆ K' := by
    intro x hx
    by_contra hxK
    exact hx (hf0 (fun h => hxK (interior_subset h)))
  have hcs : HasCompactSupport (f : V → ℝ) := HasCompactSupport.of_support_subset_isCompact hK' hsupp
  have hcs' : HasCompactSupport fun z => ((f z : ℝ) : ℂ) := hcs.comp_left Complex.ofReal_zero
  let g : 𝓢(V, ℂ) := hcs'.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hχ)
  have hg : ∀ z, g z = ((f z : ℝ) : ℂ) := fun z => rfl
  have hbound := norm_integral_schwartz_le m hi g
  have hmono : Integrable (f : V → ℝ) m :=
    (integrable_const (1 : ℝ)).mono' hχ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 z).1]; exact (hf01 z).2)
  have hvol : Integrable (f : V → ℝ) volume := hχ.continuous.integrable_of_hasCompactSupport hcs
  have h0 : ∀ z, 0 ≤ f z := fun z => (hf01 z).1
  have hint : ∫ y, g y ∂m = ((∫ y, f y ∂m : ℝ) : ℂ) := by
    simp only [hg]; exact integral_ofReal
  have hnorm : ∫ x, ‖g x‖ = ∫ x, f x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [hg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  rw [hint, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg h0)] at hbound
  have e1 : m K ≤ ENNReal.ofReal (∫ y, f y ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal hmono (Filter.Eventually.of_forall h0),
      ← lintegral_indicator_one hK.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ K
    · simp [hz, hf1 hz]
    · simp [hz]
  have e2 : ENNReal.ofReal (∫ y, f y) ≤ volume U := by
    rw [ofReal_integral_eq_lintegral_ofReal hvol (Filter.Eventually.of_forall h0),
      ← lintegral_indicator_one hU.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ U
    · simpa [hz] using (hf01 z).2
    · have : f z = 0 := by
        by_contra h
        exact hz (hKU' (hsupp h))
      simp [hz, this]
  calc m K ≤ ENNReal.ofReal (∫ y, f y ∂m) := e1
    _ ≤ ENNReal.ofReal ((∫ x, f x) * ∫ ξ, ‖chf m ξ‖) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (∫ ξ, ‖chf m ξ‖) * ENNReal.ofReal (∫ x, f x) := by
        rw [ENNReal.ofReal_mul (integral_nonneg h0), mul_comm]
    _ ≤ _ := by gcongr
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
