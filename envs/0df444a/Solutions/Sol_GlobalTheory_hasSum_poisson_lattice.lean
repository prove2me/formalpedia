-- Prove2me | solution 1 for GlobalTheory.hasSum_poisson_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:17.931155+00:00
-- url     : https://prove2.me/submissions/a3b7b144-a43b-43de-bea6-1e1d37e4560e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Theorems.Thm_GlobalTheory_continuous_tsum_lattice_translate
import Theorems.Thm_GlobalTheory_periodic_tsum_lattice_translate
import Theorems.Thm_GlobalTheory_latticeFourierCoeff_tsum_translate
import Theorems.Thm_GlobalTheory_hasSum_latticeFourier_of_summable_norm


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
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    HasSum (fun y : dualLattice L ↦ (ZLattice.covolume L)⁻¹ • e[⟪(y : E), u⟫] • 𝓕 f y)
      (∑' x : L, f (x + u)) := by
  have h := hasSum_latticeFourier_of_summable_norm (L := L)
    (A := fun u : E ↦ ∑' x : L, f (x + u)) (fun z hz ↦ periodic_tsum_lattice_translate L f hz)
    (continuous_tsum_lattice_translate L hc hdom) (by
      refine ((hs.mul_left ‖(ZLattice.covolume L)⁻¹‖).congr fun y ↦ ?_ :
        Summable fun y : dualLattice L ↦ _)
      rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, norm_smul]) u
  have h' : HasSum (fun y : dualLattice L ↦ e[⟪(y : E), u⟫] •
      latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y) (∑' x : L, f (x + u)) := h
  convert h' using 2 with y
  rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, smul_comm]
end GlobalTheory
