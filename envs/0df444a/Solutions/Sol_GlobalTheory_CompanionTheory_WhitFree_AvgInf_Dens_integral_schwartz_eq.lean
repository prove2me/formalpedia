-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.integral_schwartz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:46.01597+00:00
-- url     : https://prove2.me/submissions/89aff262-2341-472b-8e8f-da9f4bb2aa8b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_schwartz_inv

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
theorem _root_.solution (m : Measure V) [IsFiniteMeasure m] (g : 𝓢(V, ℂ)) :
    ∫ y, g y ∂m = ∫ ξ, (𝓕 g) ξ * chf m ξ := by
  have hc : Continuous fun p : V × V => Complex.exp (2 * π * I * ((⟪p.1, p.2⟫ : ℝ) : ℂ)) * (𝓕 g) p.2 := by
    have := (𝓕 g).continuous
    fun_prop
  have hint : Integrable (fun p : V × V => Complex.exp (2 * π * I * ((⟪p.1, p.2⟫ : ℝ) : ℂ)) * (𝓕 g) p.2)
      (m.prod volume) := by
    refine ((𝓕 g).integrable (μ := volume)).norm.comp_snd m |>.mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have : ‖Complex.exp (2 * π * I * ((⟪p.1, p.2⟫ : ℝ) : ℂ))‖ = 1 := by
      have : 2 * π * I * ((⟪p.1, p.2⟫ : ℝ) : ℂ) = ((2 * π * ⟪p.1, p.2⟫ : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    simp [this]
  calc ∫ y, g y ∂m = ∫ y, ∫ ξ, Complex.exp (2 * π * I * ((⟪y, ξ⟫ : ℝ) : ℂ)) * (𝓕 g) ξ ∂volume ∂m :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => schwartz_inv g y)
    _ = ∫ ξ, ∫ y, Complex.exp (2 * π * I * ((⟪y, ξ⟫ : ℝ) : ℂ)) * (𝓕 g) ξ ∂m ∂volume :=
        integral_integral_swap hint
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        beta_reduce
        rw [chf, integral_mul_const, mul_comm]
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
