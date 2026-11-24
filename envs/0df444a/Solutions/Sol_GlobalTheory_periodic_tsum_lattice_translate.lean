-- Prove2me | solution 1 for GlobalTheory.periodic_tsum_lattice_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:26.351961+00:00
-- url     : https://prove2.me/submissions/93a65878-010c-4360-a91f-b9b4f212b09d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv

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
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution (f : E → V) {z : E} (hz : z ∈ L) :
    Function.Periodic (fun u : E ↦ ∑' x : L, f (x + u)) z := fun u ↦ by
  beta_reduce
  rw [← (Equiv.addRight (⟨z, hz⟩ : L)).tsum_eq fun x : L ↦ f (x + u)]
  refine tsum_congr fun x ↦ ?_
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  congr 1
  abel
end GlobalTheory
