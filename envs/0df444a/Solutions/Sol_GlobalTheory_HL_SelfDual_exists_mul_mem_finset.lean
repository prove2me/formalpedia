-- Prove2me | solution 1 for GlobalTheory.HL.SelfDual.exists_mul_mem_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:21.397999+00:00
-- url     : https://prove2.me/submissions/1bb54aff-c07e-4785-9bcc-a412cd519da2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_GlobalTheory_HL_SelfDual_exists_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.SelfDual
theorem _root_.solution (L : LocE F E) (s : Finset E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ ∀ x ∈ s, algebraMap F E c * x ∈ L.O := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x s _ ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨d, hd, h'⟩ := exists_mul_mem L x
    refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
    rw [Subring.coe_mul, map_mul]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [mul_assoc]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 c.2) h'
    · rw [mul_right_comm]
      exact L.O.mul_mem (h y hy) ((algebraMap_mem_iff L _).2 d.2)
end GlobalTheory.HL.SelfDual
