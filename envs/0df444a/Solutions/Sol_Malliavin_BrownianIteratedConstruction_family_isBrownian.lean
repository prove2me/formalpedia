-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.family_isBrownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:01.964219+00:00
-- url     : https://prove2.me/submissions/a7aab2a6-a03b-4f31-8b30-51e605189f71

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_box
import Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_of_pos


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    (hdense : PositiveOrderedBoxDense) :
    (family hB hsm hdense).IsBrownian B := by
  apply IteratedIntegralFamily.IsBrownian.of_pos
  intro n hn u v huv hord
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let a : OrderedBoxIndex (k + 1) := ⟨u, v, huv, hord⟩
  have hbox := positiveIntegralCLM_box hB hsm (hdense k) a
  change positiveIntegralCLM hB k (boxKernel u v) = chainIntegralLp hB u v at hbox
  rw [show (family hB hsm hdense).integral (k + 1) = positiveIntegralCLM hB k from rfl,
    hbox]
  exact coeFn_chainIntegralLp hB u v
end Malliavin.BrownianIteratedConstruction
