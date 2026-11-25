-- Prove2me | solution 1 for GlobalTheory.CongGrp.norm_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:04.878024+00:00
-- url     : https://prove2.me/submissions/fee30a11-3ed5-41b3-b365-d221acc17dd1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {y : E} (hy : y ∈ L.O) :
    ∃ u : (𝒪[F])ˣ, (1 + algebraMap F E (ϖ : F) * y) * L.cj (1 + algebraMap F E (ϖ : F) * y) =
      algebraMap F E ((u : 𝒪[F]) : F) := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, ⟨t, ht⟩, n, hn⟩ := h2 y hy
  have hu : IsUnit (1 + ϖ * (t + ϖ * n)) := by
    have hm : ϖ * (t + ϖ * n) ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
      Ideal.mul_mem_right _ _ hϖ.not_isUnit
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hm)
    simpa using this
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e : ((1 + ϖ * (t + ϖ * n) : 𝒪[F]) : F) = 1 + (ϖ : F) * ((t : F) + (ϖ : F) * (n : F)) := rfl
  rw [e]
  simp only [map_add, map_mul, map_one, AlgEquiv.commutes]
  rw [← ht, ← hn]
  ring
end GlobalTheory.CongGrp
