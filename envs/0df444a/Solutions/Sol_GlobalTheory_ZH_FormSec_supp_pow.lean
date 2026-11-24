-- Prove2me | solution 1 for GlobalTheory.ZH.FormSec.supp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:54.030346+00:00
-- url     : https://prove2.me/submissions/6c35b148-e54b-449e-8b15-f1f3b36316e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFormSec
import Theorems.Thm_GlobalTheory_ZH_FormSec_supp_mul
import Theorems.Thm_GlobalTheory_ZH_FormSec_supp_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.FormSec
open scoped Pointwise
variable {A X : Type} [CommRing A] [AddCommGroup X]
namespace GlobalTheory.ZH.FormSec
theorem _root_.solution {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact supp_one
  | succ n ih => rw [pow_succ, succ_nsmul]; exact supp_mul ih hx
end GlobalTheory.ZH.FormSec
