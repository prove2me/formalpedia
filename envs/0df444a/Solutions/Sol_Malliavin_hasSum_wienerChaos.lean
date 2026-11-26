-- Prove2me | solution 1 for Malliavin.hasSum_wienerChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:08:35.066394+00:00
-- url     : https://prove2.me/submissions/a783bad9-1ff5-46a1-a679-be04ec69af36

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) :
    HasSum
      (fun n : ℕ =>
        ((wienerChaosEquiv hB htotal F) n).1)
      F := by
  simpa [wienerChaosEquiv] using
    (wienerChaos_isHilbertSum_of_total hB htotal).hasSum_linearIsometryEquiv_symm
      (wienerChaosEquiv hB htotal F)
end Malliavin
