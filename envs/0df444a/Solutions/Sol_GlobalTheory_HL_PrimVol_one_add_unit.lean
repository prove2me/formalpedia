-- Prove2me | solution 1 for GlobalTheory.HL.PrimVol.one_add_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:48.898878+00:00
-- url     : https://prove2.me/submissions/a1003d7f-53c0-46a3-a28b-71c9bc770749

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
namespace GlobalTheory.HL.PrimVol
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    {j : ℕ} (hj : 1 ≤ j) :
    ∀ c ∈ L.O, ∃ u ∈ L.O, (1 + algebraMap F E ((ϖ : F) ^ j) * c) * u = 1 := by
  obtain ⟨-, h2, -, -, h5, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  intro c hc
  obtain ⟨hcc, ⟨t, ht⟩, s, hs⟩ := h2 c hc
  have hnu : ¬ IsUnit (ϖ ^ j * (t + ϖ ^ j * s)) := fun h =>
    hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 (isUnit_of_mul_isUnit_left h))
  have hun : IsUnit (1 + ϖ ^ j * (t + ϖ ^ j * s)) := by
    have := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(ϖ ^ j * (t + ϖ ^ j * s)))
    rw [sub_neg_eq_add, IsUnit.neg_iff] at this
    exact this.resolve_left hnu
  obtain ⟨v, hv⟩ := hun.exists_right_inv
  have hv' := congrArg (fun x : 𝒪[F] => algebraMap F E (x : F)) hv
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_one, map_mul, map_add, map_one,
    SubmonoidClass.coe_pow] at hv'
  have hp : algebraMap F E ((ϖ : F) ^ j) ∈ L.O := (h5 _).2 (ϖ ^ j).2
  refine ⟨(1 + algebraMap F E ((ϖ : F) ^ j) * L.cj c) * algebraMap F E v,
    L.O.mul_mem (L.O.add_mem L.O.one_mem (L.O.mul_mem hp hcc)) ((h5 _).2 v.2), ?_⟩
  rw [← ht, ← hs] at hv'
  linear_combination hv'
end GlobalTheory.HL.PrimVol
