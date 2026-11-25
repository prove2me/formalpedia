-- Prove2me | solution 1 for GlobalTheory.HL.sumData_mass_eq_sumCls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:23.321094+00:00
-- url     : https://prove2.me/submissions/44805d93-f5e1-4145-8078-d27617020442

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDataMassEqSumFrameClasses
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameAct_stabiliser_acts_on_terms
import Theorems.Thm_GlobalTheory_HL_mass_eq_sumCls
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
open GlobalTheory GlobalTheory.HL
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]
end GlobalTheory.HL
