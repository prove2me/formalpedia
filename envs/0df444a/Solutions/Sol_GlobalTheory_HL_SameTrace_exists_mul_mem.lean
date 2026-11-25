-- Prove2me | solution 1 for GlobalTheory.HL.SameTrace.exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:51:30.806883+00:00
-- url     : https://prove2.me/submissions/71ff970a-66f9-4ef2-a0a7-a3ec02ecc2a9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace

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
theorem _root_.solution [IsNonarchimedeanLocalField F] (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t * c ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have h1 : IsAlgebraic F c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic 𝒪[F] c := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨t, ht, h⟩ := h2.exists_integral_multiple
  refine ⟨t, ht, (L.O_def _).2 ?_⟩
  convert h using 1
  rw [Algebra.smul_def]; rfl
end GlobalTheory.HL.SameTrace
