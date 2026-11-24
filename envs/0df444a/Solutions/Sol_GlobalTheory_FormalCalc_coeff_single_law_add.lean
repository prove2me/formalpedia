-- Prove2me | solution 1 for GlobalTheory.FormalCalc.coeff_single_law_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:28:22.332149+00:00
-- url     : https://prove2.me/submissions/f7cc52bb-582e-4d71-a7ea-57bce3ad5877

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_ev_two
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_law_snd
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_law_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalCalc
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.FormalCalc
theorem _root_.solution {n : ℕ} (G : FGLaw R d) (p q : Pt R n d)
    (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0) (i : Fin d)
    (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (G.add p q i) =
      coeff (Finsupp.single j 1) (p i) + coeff (Finsupp.single j 1) (q i) := by
  show coeff (Finsupp.single j 1) (ev ![p, q] (G.F i)) = _
  rw [coeff_single_ev_two p q hp hq]
  simp [coeff_law_fst, coeff_law_snd, boole_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
end GlobalTheory.FormalCalc
