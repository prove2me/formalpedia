-- Prove2me | solution 1 for GlobalTheory.PrinTwo.exists_ev_nL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:05:58.558001+00:00
-- url     : https://prove2.me/submissions/cc8c848c-93fc-4421-8c8f-32486ba1d763

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinity
import Theorems.Thm_GlobalTheory_PrinTwo_continuous_nL
import Theorems.Thm_GlobalTheory_PrinTwo_nL_zero
import Theorems.Thm_GlobalTheory_PrinTwo_bchar_one
import Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_ev_act
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_parInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.bchar_one
attribute [local simp] GlobalTheory.PrinTwo.coordL_apply
attribute [local simp] GlobalTheory.PrinTwo.evL_apply
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD
attribute [local simp] GlobalTheory.PrinTwo.val_wE



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) :
    ∃ r : kˣ, ∀ z : k, valuation k z < valuation k (r : k) → ev f (nL z) = ev f 1 := by
  have hS : IsOpen {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} := isSmooth_parInd _ _ f
  have hU : nL ⁻¹' {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} ∈ 𝓝 (0 : k) :=
    (hS.preimage continuous_nL).mem_nhds (by simp [nL_zero])
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, fun z hz => ?_⟩
  have hz' : psRep μ₁ μ₂ (nL z) f = f := hγ (by rw [← hy]; exact hz)
  rw [← one_mul (nL z), ← ev_act, hz']
end GlobalTheory.PrinTwo
