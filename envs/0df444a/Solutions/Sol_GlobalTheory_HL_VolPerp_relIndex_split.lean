-- Prove2me | solution 1 for GlobalTheory.HL.VolPerp.relIndex_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:14.448535+00:00
-- url     : https://prove2.me/submissions/656b230e-3359-4c19-bed5-2b012ddeb03c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.VolPerp
open GlobalTheory.HL.DualInter
namespace GlobalTheory.HL.VolPerp
theorem _root_.solution {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by
  have h1 : (M ⊔ Z) ⊓ A = M ⊔ (Z ⊓ A) := sup_inf_assoc_of_le Z h
  have h2 : M ≤ (M ⊔ Z) ⊓ A := le_inf le_sup_left h
  rw [← AddSubgroup.relIndex_mul_relIndex M _ A h2 inf_le_right]
  congr 1
  · rw [h1, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right M, inf_comm Z A,
      ← inf_assoc, inf_eq_left.2 h]
  · rw [AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (M ⊔ Z),
      ← sup_assoc, sup_eq_left.2 h]
end GlobalTheory.HL.VolPerp
