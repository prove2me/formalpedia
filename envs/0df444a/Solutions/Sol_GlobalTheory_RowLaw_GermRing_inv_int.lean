-- Prove2me | solution 1 for GlobalTheory.RowLaw.GermRing.inv_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:14:10.925806+00:00
-- url     : https://prove2.me/submissions/1d5e2580-867f-418f-bea5-53ae793c5dae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
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
theorem _root_.solution {σ : Type} [Fintype σ] (A : Matrix σ σ C) (hA : ∀ i j, V.Ge 0 (A i j)) (hd : V.v A.det = 0) :
    IsUnit A ∧ ∀ i j, V.Ge 0 (A⁻¹ i j) := by
  have hne : A.det ≠ 0 := fun h => by
    rw [h, V.v.map_zero] at hd
    exact WithTop.top_ne_zero hd
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).2 hne.isUnit, fun i j => ?_⟩
  have hinv : V.Ge 0 (A.det)⁻¹ := by
    have h := V.v.map_mul A.det (A.det)⁻¹
    rw [mul_inv_cancel₀ hne, V.v.map_one, hd, zero_add] at h
    unfold VF.Ge
    rw [← h]
    simp
  let B : Matrix σ σ (intRing V) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : A = (intRing V).subtype.mapMatrix B := by ext; rfl
  have hadj : V.Ge 0 (A.adjugate i j) := by
    rw [hB, ← RingHom.map_adjugate]
    exact (B.adjugate i j).2
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hinv.mul_int hadj
end GlobalTheory.RowLaw.GermRing
