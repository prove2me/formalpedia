-- Prove2me | solution 1 for GlobalTheory.VFComp.sum_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:45.885386+00:00
-- url     : https://prove2.me/submissions/66c9d894-9880-49f1-9e28-e859183bc6f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}
namespace GlobalTheory.VFComp
theorem _root_.solution {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (Fin (k + 1) → Fin d) → M) :
    ∑ w : Fin (k + 1) → Fin d, g w = ∑ j : Fin d, ∑ w : Fin k → Fin d, g (Fin.cons j w) := by
  rw [← (Fin.consEquiv fun _ => Fin d).sum_comp, Fintype.sum_prod_type]
  rfl
end GlobalTheory.VFComp
