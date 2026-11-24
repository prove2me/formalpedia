-- Prove2me | solution 1 for GlobalTheory.FormalMulN.lin_F_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:00:03.539262+00:00
-- url     : https://prove2.me/submissions/397caffe-48a7-435b-899c-56e48dd6a35c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_lin_ev_two
import Theorems.Thm_GlobalTheory_FormalMulN_coeff_single_pt
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_pt
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_zero
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
theorem _root_.solution (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (G.F i) = if i = l then 1 else 0 := by
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), l) 1)) (G.unit i)
  have hX : coeff (Finsupp.single ((0 : Fin 1), l) 1) (X ((0 : Fin 1), i) : PS R 1 d) =
      if i = l then 1 else 0 := coeff_single_pt 0 i l
  rw [lin_ev_two const_zero (const_pt 0), hX] at h
  simpa [coeff_single_pt] using h
end GlobalTheory.FormalMulN
