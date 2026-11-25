-- Prove2me | solution 1 for GlobalTheory.HL.QuadricShare.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:07:31.097522+00:00
-- url     : https://prove2.me/submissions/8ab3fd83-7aa6-48a7-aab7-1193606e88d5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ProperIdealsOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsTraceChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TwoGeometricSumsIndexBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLocalCharacterSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuadricCharacterLeakSharesFinite
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_GaussSummand_cj_hf
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QuadricShare
open GlobalTheory.HL.GaussSummand
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.QuadricShare
theorem _root_.solution (hH : IsHermND L Hm) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (UU : Submodule L.O (Fin n → E)) (hUU : ∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) :
    ∃ (nrm : (Fin n → E) → F) (Q : (Fin n → E) → 𝒪[F]), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) ∧
      (∀ u ∈ UU, (Q u : F) = nrm u) ∧
      ∀ (a : ℕ), ∀ u ∈ UU, (ϖ ^ a ∣ Q u ↔ ∃ c : 𝒪[F], hf L Hm u u = algebraMap F E ((ϖ : F) ^ a * c)) := by
  obtain ⟨-, -, -, -, hint, -, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  choose nrm hnrm using fun u : Fin n → E => (L.cj_fix _).1 (cj_hf L Hm hH.1 u u)
  have hQ : ∀ u ∈ UU, nrm u ∈ 𝒪[F] := fun u hu => (hint _).1 (by rw [hnrm]; exact hUU u hu u hu)
  refine ⟨nrm, fun u => if h : nrm u ∈ 𝒪[F] then ⟨nrm u, h⟩ else 0, hnrm, fun u hu => ?_,
    fun a u hu => ?_⟩
  · simp only [dif_pos (hQ u hu)]
  · simp only [dif_pos (hQ u hu)]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x : 𝒪[F] => (x : F)) hc
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow] at this
      rw [← hnrm, this]
    · rintro ⟨c, hc⟩
      rw [← hnrm] at hc
      exact ⟨c, Subtype.ext (by simpa using hinj hc)⟩
end GlobalTheory.HL.QuadricShare
