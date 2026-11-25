-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.pairC_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:25.030469+00:00
-- url     : https://prove2.me/submissions/083559c9-42d3-481b-ad4f-e15f6e4eeead

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_re_trace_mul_self
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_pairC_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_mem_hermC


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
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
variable {W : Type} [Fintype W]
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution {n : ℕ} {c : W → ℝ} (hc : ∀ w, c w ≠ 0) (u : W → hermC n)
    (h : ∀ v, pairC n c u v = 0) : u = 0 := by
  have h1 := h fun w => (c w)⁻¹ • u w
  have h2 : ∑ w, ∑ i, ∑ j, ‖(u w : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 0 := by
    rw [← h1, pairC_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [coe_smul_hermC, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul,
      ← mul_assoc, mul_inv_cancel₀ (hc w), one_mul, re_trace_mul_self (mem_hermC.1 (u w).2)]
  have hnn : ∀ w ∈ Finset.univ, 0 ≤ ∑ i, ∑ j, ‖(u w : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 :=
    fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  funext w
  apply Subtype.ext
  ext i j
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h2 w (Finset.mem_univ w)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity).1 h3 i
    (Finset.mem_univ i)
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).1 h4 j (Finset.mem_univ j)
  simpa using h5
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
