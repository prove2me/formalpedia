-- Prove2me | solution 1 for GlobalTheory.HL.FibU.exists_reps_refU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:31.197685+00:00
-- url     : https://prove2.me/submissions/e1dc9e60-c245-4fc2-afc6-798f02b29e12

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralEqMeanOverRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBound
import Theorems.Thm_GlobalTheory_HL_FibU_exists_reps
import Theorems.Thm_GlobalTheory_HL_FibU_relIndex_ne_zero
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_CongFin_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FibU
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FibU
theorem _root_.solution [CharZero F] {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) (J N : ℕ) :
    ∃ R : Finset S.V, (∀ w ∈ R, w ∈ S.refU J Λ) ∧ ∀ w ∈ S.refU J Λ, ∃! x, x ∈ R ∧ w - x ∈ mulP S Λ N := by
  have hp : algebraMap F E ((S.ϖ : F) ^ N) ∈ L.O :=
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (pow_mem S.ϖ.2 N)
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hset : {y : L.O | (y : E) = algebraMap F E ((S.ϖ : F) ^ N)} = {⟨_, hp⟩} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Subtype.ext_iff]
  have h8 := h6 N
  rw [hset] at h8
  have : Finite (L.O ⧸ Ideal.span {(⟨_, hp⟩ : L.O)}) :=
    Nat.finite_of_card_ne_zero (by rw [h8]; positivity)
  have h9 := relIndex_ne_zero Λ hΛ.1.1 ⟨_, hp⟩ (mulP S Λ N) fun y hy => ⟨y, hy, rfl⟩
  exact exists_reps _ _ fun h => h9 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
end GlobalTheory.HL.FibU
