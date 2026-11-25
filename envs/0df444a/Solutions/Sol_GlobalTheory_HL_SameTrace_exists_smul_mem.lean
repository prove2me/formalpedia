-- Prove2me | solution 1 for GlobalTheory.HL.SameTrace.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:52.300166+00:00
-- url     : https://prove2.me/submissions/30e461ba-519f-4850-b096-2cae637946f9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Theorems.Thm_GlobalTheory_CommonDenominator_main


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SameTrace
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.SameTrace
theorem _root_.solution [IsNonarchimedeanLocalField F] {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsLat L Λ) (x : Fin n → E) : ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.CommonDenominator.main
  | exact _root_.GlobalTheory.CommonDenominator.main
  | (apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominator.main ..)
end GlobalTheory.HL.SameTrace
