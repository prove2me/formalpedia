-- Prove2me | solution 1 for GlobalTheory.MoveFine.one_add_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:44.4055+00:00
-- url     : https://prove2.me/submissions/d8776222-77dd-4996-9554-0a5b7c3e5e2b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_algO
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution {z : E} (hz : z ∈ L.O) : ∃ e ∈ L.O, e * (1 + algebraMap F E S.ϖ * z) = 1 := by
  obtain ⟨hc, ⟨t, ht⟩, n, hn⟩ := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 z hz
  have hu : IsUnit (1 + S.ϖ * (t + S.ϖ * n)) := by
    have : S.ϖ * (t + S.ϖ * n) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
      Ideal.mul_mem_right _ _ S.ϖ_irr.not_isUnit
    have h2 := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem this)
    rwa [sub_neg_eq_add] at h2
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have hv' := congrArg (fun c : 𝒪[F] => algebraMap F E (c : F)) hv
  push_cast at hv'
  simp only [map_mul, map_add, map_one, ← ht, ← hn] at hv'
  refine ⟨algebraMap F E v * (1 + algebraMap F E S.ϖ * L.cj z),
    L.O.mul_mem (algO S v) (L.O.add_mem L.O.one_mem (L.O.mul_mem (algO S _) hc)), ?_⟩
  linear_combination hv'
end GlobalTheory.MoveFine
