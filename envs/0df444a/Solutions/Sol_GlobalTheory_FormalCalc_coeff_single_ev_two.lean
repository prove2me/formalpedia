-- Prove2me | solution 1 for GlobalTheory.FormalCalc.coeff_single_ev_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.277801+00:00
-- url     : https://prove2.me/submissions/62fa5317-8d63-488e-92e1-fd1c0b8c4eea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Theorems.Thm_GlobalTheory_FormalCalc_coeff_single_subst

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
theorem _root_.solution {n : ℕ} (p q : Pt R n d) (hp : ∀ i, constantCoeff (p i) = 0)
    (hq : ∀ i, constantCoeff (q i) = 0) (f : PS R 2 d) (j : Fin n × Fin d) :
    coeff (Finsupp.single j 1) (ev ![p, q] f) =
      ∑ l, coeff (Finsupp.single ((0 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (p l) +
      ∑ l, coeff (Finsupp.single ((1 : Fin 2), l) 1) f * coeff (Finsupp.single j 1) (q l) := by
  have h0 : ∀ s : Fin 2 × Fin d, constantCoeff ((![p, q] : Fin 2 → Pt R n d) s.1 s.2) = 0 := by
    rintro ⟨b, i⟩
    fin_cases b
    · exact hp i
    · exact hq i
  unfold ev
  rw [coeff_single_subst h0, Fintype.sum_prod_type, Fin.sum_univ_two]
  all_goals rfl
end GlobalTheory.FormalCalc
