-- Prove2me | solution 1 for GlobalTheory.HL.FamilyVol.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:03.249666+00:00
-- url     : https://prove2.me/submissions/6e1407f6-92e5-4255-a472-006c6637b48e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualHermitianLatticeTraceOrthogonalVolumeRatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeTraceInitialSpanVolumeEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFamilyTraceVolumeConst
import Theorems.Thm_GlobalTheory_CardQuotientPow_main
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_QuotientCardinality_main


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FamilyVol
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.FamilyVol
theorem _root_.solution (S : Frames L r k) (J : ℕ) :
    ∃ (m : ℕ) (y : Fin m → S.V), LinearIndependent E y ∧
      Submodule.span E (Set.range y) = S.spanTo S.f J ⊔ S.spanTo S.f' J := by
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  let I := {i : Fin (r + 1) // (i : ℕ) < J}
  let φ : I ⊕ I → Fin (r + 1) ⊕ Fin (r + 1) := Sum.map Subtype.val Subtype.val
  have hφ : Function.Injective φ := Subtype.val_injective.sumMap Subtype.val_injective
  let e := (Fintype.equivFin (I ⊕ I)).symm
  refine ⟨_, (Sum.elim S.f S.f' ∘ φ) ∘ e, (hli.comp φ hφ).comp e e.injective, ?_⟩
  rw [e.surjective.range_comp, Frames.spanTo, Frames.spanTo, ← Submodule.span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact Or.inl ⟨i.1, i.2, rfl⟩
    · exact Or.inr ⟨i.1, i.2, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨Sum.inl ⟨i, hi⟩, rfl⟩
    · exact ⟨Sum.inr ⟨i, hi⟩, rfl⟩
end GlobalTheory.HL.FamilyVol
