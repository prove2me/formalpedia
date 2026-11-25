-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.witness_independence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:03.531473+00:00
-- url     : https://prove2.me/submissions/de844375-cf7b-4375-8f1c-10ae6230f2be

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_GlobalTheory_HL_WitIndep_cls_subset
import Theorems.Thm_GlobalTheory_HL_WitIndep_Mof_le
import Theorems.Thm_GlobalTheory_HL_WitIndep_lev_step
import Theorems.Thm_GlobalTheory_HL_WitIndep_compare
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FramePsi_psi_unitary_character
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ d Λ n n', S.IsTermW d Λ n n' → S.om d Λ = S.psi n * (S.psi' n')⁻¹ ∧ S.M d Λ = S.Mof (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ S.Fr d Λ = S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧ (∀ y, S.lev (S.fr d Λ) (S.fr' d Λ) y = S.lev (fun b => n (S.f b)) (fun b => n' (S.f' b)) y) ∧ ‖S.om d Λ‖ = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ n n' H
  have hT : S.IsTerm d Λ := ⟨(n, n'), H⟩
  have K : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dif_pos hT]
    exact hT.choose_spec
  obtain ⟨c1, w1⟩ := compare S H K
  obtain ⟨c2, -⟩ := compare S K H
  refine ⟨w1, le_antisymm (Mof_le S c1) (Mof_le S c2),
    Set.Subset.antisymm (cls_subset S c1) (cls_subset S c2), fun y => ?_, ?_⟩
  · exact congrArg sInf (Set.ext fun j => ⟨lev_step S c1 y j, lev_step S c2 y j⟩)
  · obtain ⟨-, -, p3, -⟩ := FramePsi.psi_unitary_character L r k S
    rw [Frames.om, norm_mul, norm_inv, (p3 _).1, (p3 _).2]
    simp
end GlobalTheory.HL.WitIndep
