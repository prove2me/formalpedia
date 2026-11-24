-- Prove2me | solution 1 for GlobalTheory.BorelModulus.coord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:02:38.848413+00:00
-- url     : https://prove2.me/submissions/1a234717-f09b-4d99-8128-06c3c35ba92c

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
theorem _root_.solution (u x : (borelGL k (Fin n)).U) :
    coord k n (u * x) = (leftMat u.1.val).mulVec (coord k n x) + coord k n u := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 x.2
  funext ⟨⟨i, j⟩, hp⟩
  show (u.1.val * x.1.val) i j = ∑ q : Pos n, (if q.1.2 = j then u.1.val i q.1.1 else 0) * x.1.val q.1.1 q.1.2 +
    u.1.val i j
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => (if q.2 = j then u.1.val i q.1 else 0) * x.1.val q.1 q.2),
    Finset.sum_filter, Fintype.sum_prod_type, mul_apply]
  have : u.1.val i j = ∑ l, if l = j then u.1.val i l else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  rcases lt_trichotomy l j with h | rfl | h
  · simp [h, h.ne]
  · simp [h2]
  · simp [h.not_gt, h.ne', h1 _ _ h]
end GlobalTheory.BorelModulus
