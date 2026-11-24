-- Prove2me | solution 1 for GlobalTheory.FormalMulN.dLin_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:10.067172+00:00
-- url     : https://prove2.me/submissions/f2d8e1c0-49f4-49cd-952b-82c3d152cd1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Theorems.Thm_GlobalTheory_FormalMulN_lin_ev_two
import Theorems.Thm_GlobalTheory_FormalMulN_lin_F_right
import Theorems.Thm_GlobalTheory_FormalMulN_lin_F_left
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
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
theorem _root_.solution {x y : Pt R 1 d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) : dLin (G.add x y) = dLin x + dLin y := by
  ext i j
  rw [Matrix.add_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![x, y] (G.F i)) =
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (x i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (y i)
  rw [lin_ev_two hx hy]
  simp [lin_F_left G, lin_F_right G]
end GlobalTheory.FormalMulN
