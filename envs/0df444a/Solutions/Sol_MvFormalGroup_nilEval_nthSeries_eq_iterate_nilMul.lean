-- Prove2me | solution 1 for MvFormalGroup.nilEval_nthSeries_eq_iterate_nilMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/13d45ae8-58c6-5f9c-b91f-0e6ee44a7374

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_nilEval_nthSeries_eq_iterate_nilMul

set_option autoImplicit false

open MvPowerSeries

theorem solution
    {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (ν : ℕ) (hJ : J ^ (ν + 1) = ⊥)
    (s : Fin g → B') (hs : ∀ i, s i ∈ J) (m : ℕ) (i : Fin g) :
    MvFormalGroup.nilEval ν (F.nthSeries m i) s = ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) i := by
  classical
  induction m generalizing i with
  | zero =>
    simp only [MvFormalGroup.nthSeries_zero, Function.iterate_zero, id_eq, Pi.zero_apply]
    simp [MvFormalGroup.nilEval]
  | succ m ih =>
    rw [Function.iterate_succ_apply', MvFormalGroup.nthSeries_succ]
    have h0 : ∀ j, MvPowerSeries.constantCoeff (Sum.elim (F.nthSeries m) (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin g) B)) j) = 0 := by
      rintro (j | j)
      · exact F.constantCoeff_nthSeries m j
      · exact MvPowerSeries.constantCoeff_X j
    rw [(MvFormalGroup.nilEval_subst_of_mem J ν hJ s hs _ h0 (F.toPowerSeries i)).2]
    show MvFormalGroup.nilEval ν (F.toPowerSeries i)
        (fun j => MvFormalGroup.nilEval ν (Sum.elim (F.nthSeries m) (fun j => (MvPowerSeries.X j : MvPowerSeries (Fin g) B)) j) s) =
      MvFormalGroup.nilEval ν (F.toPowerSeries i) (Sum.elim ((fun t : Fin g → B' => F.nilMul ν t s)^[m] 0) s)
    congr 1
    funext j
    rcases j with j | j
    · exact ih j
    · exact MvFormalGroup.nilEval_X_of_mem J ν hJ s hs j

end S_MvFormalGroup_nilEval_nthSeries_eq_iterate_nilMul
end P2MW
export P2MW.S_MvFormalGroup_nilEval_nthSeries_eq_iterate_nilMul (solution)
