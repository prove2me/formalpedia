-- Prove2me | solution 1 for GlobalTheory.latticeFourierCoeff_tsum_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:43.873814+00:00
-- url     : https://prove2.me/submissions/d5e19f29-082e-4bca-8488-d655b27b8652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_integrable_of_lattice_translate_dominated
import Theorems.Thm_GlobalTheory_cexp_neg_inner_add_lattice
import Theorems.Thm_GlobalTheory_continuous_cexp_neg_inner_smul
import Theorems.Thm_GlobalTheory_integrableOn_latticeCell_of_continuous
import Theorems.Thm_GlobalTheory_isAddFundamentalDomain_latticeCell
import Theorems.Thm_GlobalTheory_isBounded_latticeCell
import Theorems.Thm_GlobalTheory_norm_cexp_two_pi_I
import Theorems.Thm_GlobalTheory_volume_latticeCell_lt_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
namespace GlobalTheory
theorem _root_.solution [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    {y : E} (hy : y ∈ dualLattice L) :
    latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y =
      (ZLattice.covolume L)⁻¹ • 𝓕 f y := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hint : Integrable fun v : E ↦ e[-⟪y, v⟫] • f v :=
    (integrable_of_lattice_translate_dominated L hc hdom).norm.mono'
      (continuous_cexp_neg_inner_smul hc y).aestronglyMeasurable
      (.of_forall fun v ↦ by rw [norm_smul, norm_cexp_two_pi_I, one_mul])
  have hF : 𝓕 f y = ∫ v, e[-⟪y, v⟫] • f v := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (.of_forall fun v ↦ ?_)
    simp only [real_inner_comm y]
    congr 2
    push_cast
    ring
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  rw [hF, (isAddFundamentalDomain_latticeCell L volume).integral_eq_tsum'' _ hint,
    latticeFourierCoeff]
  congr 1
  have h1 : ∀ (x : L) (u : E), e[-⟪y, x +ᵥ u⟫] • f (x +ᵥ u) = e[-⟪y, u⟫] • f (x + u) :=
    fun x u ↦ by
      rw [← cexp_neg_inner_add_lattice hy x.2 u, add_comm u]; rfl
  simp only [h1, ← tsum_const_smul'' e[-⟪y, _⟫]]
  refine (hasSum_integral_of_summable_integral_norm (fun x ↦
    integrableOn_latticeCell_of_continuous L (by fun_prop)) ?_).tsum_eq.symm
  refine .of_norm_bounded (hg.mul_right (volume.real (latticeCell L))) fun x ↦ ?_
  refine norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun u hu ↦ ?_
  rw [norm_norm, norm_smul, norm_cexp_two_pi_I, one_mul]
  exact h x u (hR u hu)
end GlobalTheory
