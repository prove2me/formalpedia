-- Prove2me | solution 1 for GlobalTheory.BorelModulus.prod_pos_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:42.044623+00:00
-- url     : https://prove2.me/submissions/854ea3a2-40e2-4f2c-8c05-d9a7bc88b318

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelModulus
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.BorelModulus
theorem _root_.solution {G : Type} [CommGroup G] (t : Fin n → G) :
    ∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹) = ∏ i : Fin n, t i ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => t q.1 * (t q.2)⁻¹), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← Finset.prod_filter, Finset.prod_const]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio, inv_pow, ← zpow_natCast,
    ← zpow_natCast, ← _root_.zpow_sub]
  congr 1
  have := i.2
  omega
end GlobalTheory.BorelModulus
