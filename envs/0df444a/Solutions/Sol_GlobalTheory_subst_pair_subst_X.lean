-- Prove2me | solution 1 for GlobalTheory.subst_pair_subst_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:34.334735+00:00
-- url     : https://prove2.me/submissions/98e50a67-d613-4f2e-a2f4-31222d5ebd17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPowerSeries
namespace GlobalTheory
theorem _root_.solution {k : Type} [CommRing k] (x : PowerSeries k) (i : Fin 2)
    {a : Fin 2 → PowerSeries k} (ha : HasSubst a) :
    subst a (x.subst (X i : MvPowerSeries (Fin 2) k)) = x.subst (a i) := by
  have h1 : HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext _
  exact subst_X ha i
end GlobalTheory
