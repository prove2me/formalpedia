-- Prove2me | solution 1 for GlobalTheory.LieFrame.eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:56.964839+00:00
-- url     : https://prove2.me/submissions/fee07c15-ec20-46a2-b4de-adc3d8f73ada

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsEigAtIffOfIsDerivAt0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentEigenbasisExponential
import Theorems.Thm_GlobalTheory_LieFrame_sum_single_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.LieFrame
namespace GlobalTheory.LieFrame
theorem _root_.solution {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∑ i, w (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ) = w := by
  funext j
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  by_cases h : τ' = τ
  · subst h
    exact sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i
  · have h0 : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h0
      exact h (by simpa using hw _ h0)
    rw [h0, Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩ := fun h' => h (Sigma.mk.inj (e.symm.injective h')).1
    simp [Pi.single_eq_of_ne this]
end GlobalTheory.LieFrame
