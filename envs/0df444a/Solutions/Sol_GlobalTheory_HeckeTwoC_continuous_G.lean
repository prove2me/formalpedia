-- Prove2me | solution 1 for GlobalTheory.HeckeTwoC.continuous_G
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:15.095574+00:00
-- url     : https://prove2.me/submissions/417261a0-7782-4a86-81cb-c494fd587d80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_tI_ne
import Theorems.Thm_GlobalTheory_HeckeTwoC_continuous_lg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory
namespace GlobalTheory.HeckeTwoC
theorem _root_.solution (σ : ℂ) : Continuous (G σ) := by
  unfold G
  have : Continuous fun t : ℝ => ((t : ℂ) + I)⁻¹ :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + I).inv₀ tI_ne
  exact (this.pow 2).mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp continuous_lg).mul continuous_const))
end GlobalTheory.HeckeTwoC
