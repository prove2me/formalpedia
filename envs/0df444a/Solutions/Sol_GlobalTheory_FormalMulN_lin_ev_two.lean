-- Prove2me | solution 1 for GlobalTheory.FormalMulN.lin_ev_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:38.99028+00:00
-- url     : https://prove2.me/submissions/5389e61b-ea7f-4876-8a20-1a4370538ea7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_coeff_single_one
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_GaugeAdjoint_const_two
import Theorems.Thm_GlobalTheory_GaugeAdjoint_constantCoeff_ev
import Theorems.Thm_GlobalTheory_GaugeAdjoint_pderiv_ev
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
theorem _root_.solution {x y : Pt R n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS R 2 d) (s : Fin n × Fin d) :
    coeff (Finsupp.single s 1) (ev ![x, y] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (x l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single s 1) (y l) := by
  have ha := const_two hx hy
  rw [coeff_single_one s (ev ![x, y] f), pderiv_ev ha, map_sum, Fin.sum_univ_two]
  simp only [map_sum, map_mul, constantCoeff_ev ha, ← coeff_single_one, Matrix.cons_val_zero,
    Matrix.cons_val_one]
end GlobalTheory.FormalMulN
