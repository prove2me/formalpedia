-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_pure_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:12.238589+00:00
-- url     : https://prove2.me/submissions/d9c207a6-0dec-44ba-83f3-606a4b327f29

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_geom_real
import Theorems.Thm_GlobalTheory_ChainCoord_v_kap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C]
namespace GlobalTheory.ChainCoord
theorem _root_.solution {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : 3 ≤ l)
    (hv : v (l : C) = 1) {d M : ℕ} {π : ℕ → Fin d → Fin M → C} {s : ℕ} {c : Fin d} {a σ : ℝ}
    (h : ∀ j, (a : WithTop ℝ) ≤ v (π s c j)) (j : Fin M) :
    ((a + 1 / ((l : ℝ) ^ 2 - 1) + ((l : ℝ) ^ 2) ^ s * σ -
      (1 / ((l : ℝ) ^ 2 - 1) + σ) * (((l ^ 2) ^ s : ℕ) : ℝ) : ℝ) : WithTop ℝ) ≤
        v (kap C l s * π s c j) := by
  rw [v.map_mul]
  refine le_trans ?_ (add_le_add (v_kap hv s) (h j))
  rw [← WithTop.coe_add, geom_real hl]
  refine WithTop.coe_le_coe.2 (le_of_eq ?_)
  push_cast
  ring
end GlobalTheory.ChainCoord
