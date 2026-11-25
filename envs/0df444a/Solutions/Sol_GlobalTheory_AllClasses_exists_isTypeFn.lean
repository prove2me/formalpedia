-- Prove2me | solution 1 for GlobalTheory.AllClasses.exists_isTypeFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:41.139063+00:00
-- url     : https://prove2.me/submissions/7bf4b6df-b7db-41be-bbf8-a6f462c39088

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
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
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AllClasses
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.AllClasses
theorem _root_.solution (H : Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
end GlobalTheory.AllClasses
