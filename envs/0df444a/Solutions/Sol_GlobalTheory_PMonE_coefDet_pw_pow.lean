-- Prove2me | solution 1 for GlobalTheory.PMonE.coefDet_pw_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:40.155411+00:00
-- url     : https://prove2.me/submissions/b0ced8ba-c210-4d12-a7f5-b7f12b48e76b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MoorePowSubSelfEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalizedRowCoefficientMatricesDetNorm
import Theorems.Thm_GlobalTheory_PMonE_coefDet_pw_pow_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
namespace GlobalTheory.PMonE
theorem _root_.solution (k : ℤ) (x : F) (a : ℕ) : pw p k x ^ p ^ a = pw p (k + a) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, pow_mul, ih, coefDet_pw_pow_p]
    congr 1; push_cast; ring
end GlobalTheory.PMonE
