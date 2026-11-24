-- Prove2me | solution 1 for GlobalTheory.LieFrame.sum_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:29:45.13098+00:00
-- url     : https://prove2.me/submissions/353b76ee-dfcc-4298-8099-6134124762cb

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
    (a : Fin (m τ) → ℂ) (i : Fin (m τ)) :
    (∑ i', a i' • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ, i⟩) = a i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩ := fun h =>
      hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
    simp [Pi.single_eq_of_ne this]
  · simp
end GlobalTheory.LieFrame
