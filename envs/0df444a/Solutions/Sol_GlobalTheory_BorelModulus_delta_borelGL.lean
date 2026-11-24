-- Prove2me | solution 1 for GlobalTheory.BorelModulus.delta_borelGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:35:59.763324+00:00
-- url     : https://prove2.me/submissions/47334d7f-3d98-4fdc-a379-2760bb1af4d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
import Theorems.Thm_GlobalTheory_BorelModulus_prod_pos_eq
import Theorems.Thm_GlobalTheory_BorelModulus_delta_eq
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelModulus
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.BorelModulus
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (q : (borelGL k (Fin n)).Q), (((borelGL k (Fin n)).delta q : ℝ≥0) : ℝ) =
      ∏ i : Fin n, GlobalTheory.SplitWeil.nabs k ((borelGL k (Fin n)).p q i) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  intro k _ _ _ _ n q
  rw [delta_eq, prod_pos_eq, map_prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : ∀ (x : kˣ) (m : ℤ), distribHaarChar k (x ^ m) = distribHaarChar k x ^ m := fun x m =>
    (congrArg Units.val (map_zpow (distribHaarChar k (G := kˣ)).toHomUnits x m)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  rw [h, NNReal.coe_zpow]
  rfl
end GlobalTheory.BorelModulus
