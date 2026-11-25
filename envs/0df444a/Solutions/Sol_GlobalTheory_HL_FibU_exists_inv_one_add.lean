-- Prove2me | solution 1 for GlobalTheory.HL.FibU.exists_inv_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:33:51.484357+00:00
-- url     : https://prove2.me/submissions/bbd60b63-da3a-495f-9e72-d8d493e409b6

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_QuadricShare_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_norm
import Theorems.Thm_GlobalTheory_UnramOrder_exists_trace
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
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.FibU
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {x : E} (hx : x ∈ L.O) :
    ∃ z ∈ L.O, z * (1 + algebraMap F E ϖ * x) = 1 := by
  obtain ⟨t, ht⟩ := GlobalTheory.UnramOrder.exists_trace L hx
  obtain ⟨s, hs⟩ := GlobalTheory.UnramOrder.exists_norm L hx
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 a.2
  have hu : IsUnit (1 + ϖ * (t + ϖ * s)) := by
    have : ϖ * (t + ϖ * s) ∈ IsLocalRing.maximalIdeal 𝒪[F] := Ideal.mul_mem_right _ _ hϖ.not_isUnit
    simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem this)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨algebraMap F E v * (1 + algebraMap F E ϖ * L.cj x), L.O.mul_mem (hint v)
    (L.O.add_mem L.O.one_mem (L.O.mul_mem (hint ϖ) (GlobalTheory.UnramOrder.cj_mem L hx))), ?_⟩
  have h2 := congrArg (fun a : 𝒪[F] => algebraMap F E a) hv
  push_cast at h2
  simp only [map_mul, map_add, map_one, ← ht, ← hs] at h2
  linear_combination h2
end GlobalTheory.HL.FibU
