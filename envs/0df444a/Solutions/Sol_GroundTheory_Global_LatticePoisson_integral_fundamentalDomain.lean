-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.integral_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:01.040135+00:00
-- url     : https://prove2.me/submissions/d69f9cd9-f28c-4ee0-8458-880b3131b7ea

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_fourierChar_add_intCast
import Theorems.Thm_GroundTheory_Global_mem_dualLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
open GroundTheory.Global.LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
variable [MeasurableSpace E] [BorelSpace E]
omit [DecidableEq ι]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (f : 𝓢(E, ℂ)) {μ : E} (hμ : μ ∈ dualLattice L) :
    ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L),
      (𝐞 (-⟪y, μ⟫) : ℂ) * ∑' ℓ : L, f (y + ℓ) = 𝓕 (f : E → ℂ) μ := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure E)
  set D := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hphase : ∀ (ℓ : L) (y : E), (𝐞 (-⟪(ℓ : E) + y, μ⟫) : ℂ) = 𝐞 (-⟪y, μ⟫) := by
    intro ℓ y
    obtain ⟨k, hk⟩ := (mem_dualLattice.mp hμ) ℓ ℓ.2
    rw [inner_add_left, real_inner_comm, hk, neg_add, add_comm, ← Int.cast_neg,
      fourierChar_add_intCast]
  have hint : Integrable (fun y => (𝐞 (-⟪y, μ⟫) : ℂ) * f y) := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) μ).mpr f.integrable
    simpa [Circle.smul_def] using this
  have hce : Continuous fun y : E => (𝐞 (-⟪y, μ⟫) : ℂ) := by fun_prop
  have hmeas : ∀ ℓ : L, AEStronglyMeasurable (fun y => (𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y))
      (volume.restrict D) := fun ℓ =>
    (hce.mul (f.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hfin : ∑' ℓ : L, ∫⁻ y in D, ‖(𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y)‖ₑ ≠ ⊤ := by
    have h1 : ∀ (ℓ : L) (y : E), ‖(𝐞 (-⟪y, μ⟫) : ℂ) * f (ℓ + y)‖ₑ = ‖f (ℓ + y)‖ₑ := by
      intro ℓ y
      rw [enorm_mul, ← ofReal_norm (𝐞 _ : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
    simp_rw [h1]
    have h2 := hD.lintegral_eq_tsum' (fun y => ‖f y‖ₑ)
    rw [← (Equiv.neg L).tsum_eq] at h2
    simp only [Equiv.neg_apply, neg_neg, Submodule.vadd_def, vadd_eq_add] at h2
    rw [← h2]
    exact f.integrable.2.ne
  rw [Real.fourier_eq]
  simp_rw [Circle.smul_def, smul_eq_mul]
  rw [hD.integral_eq_tsum'' _ hint]
  simp only [Submodule.vadd_def, vadd_eq_add, hphase]
  rw [← integral_tsum hmeas hfin]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [← tsum_mul_left]
  exact tsum_congr fun ℓ => by rw [add_comm y]
end GroundTheory.Global.LatticePoisson
