-- Prove2me | solution 1 for GlobalTheory.subst_pair_subst_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:34.992936+00:00
-- url     : https://prove2.me/submissions/be8725e4-d5b5-477e-b91f-42512fa8aef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities
import Theorems.Thm_GlobalTheory_hasSubst_pair

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
theorem _root_.solution {k : Type} [CommRing k] (h : MvPowerSeries (Fin 2) k)
    {z w : PowerSeries k} (hz : PowerSeries.constantCoeff z = 0)
    (hw : PowerSeries.constantCoeff w = 0) :
    subst (![z, w] : Fin 2 → PowerSeries k)
      (subst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) h) =
      subst (![z, z + w] : Fin 2 → PowerSeries k) h := by
  have ha : HasSubst (![z, w] : Fin 2 → PowerSeries k) := hasSubst_pair hz hw
  have h1 : HasSubst (![X 0, X 0 + X 1] : Fin 2 → MvPowerSeries (Fin 2) k) :=
    hasSubst_pair (by simp) (by simp)
  rw [subst_comp_subst_apply h1 ha]
  congr 1
  funext s
  fin_cases s
  · exact subst_X ha 0
  · show subst _ (X 0 + X 1 : MvPowerSeries (Fin 2) k) = z + w
    rw [subst_add ha, subst_X ha, subst_X ha]
    rfl
end GlobalTheory
