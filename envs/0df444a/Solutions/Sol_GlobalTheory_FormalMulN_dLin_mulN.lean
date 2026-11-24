-- Prove2me | solution 1 for GlobalTheory.FormalMulN.dLin_mulN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:14.928263+00:00
-- url     : https://prove2.me/submissions/299a9a8c-bc0f-410e-93ab-586d31c75fdc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_const_mulN
import Theorems.Thm_GlobalTheory_FormalMulN_dLin_add
import Theorems.Thm_GlobalTheory_FormalMulN_dLin_pt
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one



set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)
namespace GlobalTheory.FormalMulN
theorem _root_.solution (k : ℕ) : dLin (mulN G k) = (k : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  induction k with
  | zero =>
    ext i j
    simp [dLin, mulN]
  | succ k ih =>
    show dLin (G.add (mulN G k) (pt R d 0)) = _
    rw [dLin_add G (const_mulN G k) (const_pt 0), ih, dLin_pt, Nat.cast_succ, add_smul, one_smul]
end GlobalTheory.FormalMulN
