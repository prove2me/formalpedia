-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.fixG_le_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:22.519395+00:00
-- url     : https://prove2.me/submissions/9b6c48b8-561f-4ce2-a3de-8971f42f4c2d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
import Theorems.Thm_GlobalTheory_HL_QReflGen_induct
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermOrthBasis_orth_basis_perp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → fixG L Hm (Submodule.span E (Set.range x)) ≤ Subgroup.closure {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g} := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx g hg
  obtain ⟨-, hc, w, hw, hu, ho⟩ := GlobalTheory.HermOrthBasis.orth_basis_perp L Hm hH m x hx
  refine induct L hH.1 _ hc.sup_eq_top w hw hu ho Finset.univ g hg.1 (fun v hv => ?_) (by simp)
  have := hg.2.2 v hv
  rwa [Submodule.mem_bot, sub_eq_zero] at this
end GlobalTheory.HL.QReflGen
