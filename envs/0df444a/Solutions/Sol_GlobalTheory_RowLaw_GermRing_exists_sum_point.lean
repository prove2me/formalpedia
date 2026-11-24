-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.exists_sum_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:43.66939+00:00
-- url     : https://prove2.me/submissions/373eed60-cab4-45d5-a7a4-cc67674c44c6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_lg_const
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_lg_ex
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_log_add_const
import Theorems.Thm_GlobalTheory_RowLaw_GermRing_intS_addP
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_subst_zero
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}
namespace GlobalTheory.RowLaw.GermRing
theorem _root_.solution (hY : RLaw Y V) {τ ι : Type} (s : Finset ι) (a : ι → κ → MvPowerSeries τ C)
    (ha : ∀ c i, constantCoeff (a c i) = 0) (ia : ∀ c i, IntS V (a c i)) :
    ∃ Φ : κ → MvPowerSeries τ C, (∀ i, constantCoeff (Φ i) = 0) ∧ (∀ i, IntS V (Φ i)) ∧
      ∀ i, subst Φ (Y.lg i) = ∑ c ∈ s, subst (a c) (Y.lg i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => map_zero _, fun _ μ => by simpa using VF.Ge.zero (V := V) 0, fun i => ?_⟩
    rw [Finset.sum_empty]
    exact subst_zero_of_constantCoeff_zero (lg_const hY i)
  | insert c s hc ih =>
    obtain ⟨Φ, h0, hi, hl⟩ := ih
    refine ⟨addP Y (a c) Φ, fun i => constantCoeff_subst_zero (log_add_const hY (ha c) h0) (hY.exc i),
      intS_addP hY (ha c) h0 (ia c) hi, fun i => ?_⟩
    rw [Finset.sum_insert hc, ← hl]
    exact lg_ex hY (log_add_const hY (ha c) h0) i
end GlobalTheory.RowLaw.GermRing
