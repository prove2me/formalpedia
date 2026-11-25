-- Prove2me | solution 1 for GlobalTheory.MoveFine.bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:35:17.369877+00:00
-- url     : https://prove2.me/submissions/cf8f9463-c6ff-43fa-b0cb-76e47b026acf

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
import Theorems.Thm_GlobalTheory_MoveFine_disj
import Theorems.Thm_GlobalTheory_MoveFine_spanTo_mono
import Theorems.Thm_GlobalTheory_MoveFine_split_Mof
import Theorems.Thm_GlobalTheory_MoveFine_thO
import Theorems.Thm_GlobalTheory_MoveFine_th_ne
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_TermBasic_sub_mem
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_T_hermitian_double_coset_term_basic_facts
import Theorems.Thm_GlobalTheory_T_term_exponents_nonneg_and_defect_group_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution (d : S.Datum) (Λ : Submodule L.O S.V) (hT : S.IsTerm d Λ) (J : ℕ) (hJ : J ≤ r + 1)
    (x x' : S.V) (hx : x ∈ S.spanTo S.f J) (hx' : x' ∈ S.spanTo S.f' J) (hb : S.InTh Λ (x + x')) :
    algebraMap F E ((S.ϖ : F) ^ S.a) • x ∈ Λ ∧ algebraMap F E ((S.ϖ : F) ^ S.a) • x' ∈ Λ := by
  obtain ⟨-, -, -, hf, hf', -⟩ := GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT
  obtain ⟨y, hy, e⟩ := hb
  replace hx := spanTo_mono S _ hJ hx
  replace hx' := spanTo_mono S _ hJ hx'
  have hyM : y ∈ S.sat Λ := by
    refine ⟨hy, ?_⟩
    have : y = algebraMap F E S.th⁻¹ • (x + x') := by
      rw [e, ← mul_smul, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_smul]
    rw [this]
    exact S.ME.smul_mem _ (Submodule.add_mem_sup hx hx')
  have hm := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.1 y hyM
  obtain ⟨z, z', h1, h2, h3, h4, e'⟩ := split_Mof S Λ _ _ _ _
    (fun i => (hf (r + 1) le_rfl _).2 (Submodule.subset_span ⟨i, i.2, rfl⟩))
    (fun i => (hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨i, i.2, rfl⟩)) (th_ne S) (thO S) _ hm
  rw [smul_comm, ← e, smul_add] at e'
  obtain ⟨k1, k2⟩ := disj S (GlobalTheory.FrameBasic.main L r k S).1 (_ • x - z) (_ • x' - z')
    (Submodule.sub_mem _ (Submodule.smul_mem _ (algebraMap F E ((S.ϖ : F) ^ S.a)) hx) h2)
    (Submodule.sub_mem _ (Submodule.smul_mem _ (algebraMap F E ((S.ϖ : F) ^ S.a)) hx') h4)
    (by rw [sub_add_sub_comm, e', sub_self])
  rw [sub_eq_zero.1 k1, sub_eq_zero.1 k2]
  exact ⟨h1, h3⟩
end GlobalTheory.MoveFine
