-- Prove2me | solution 1 for GlobalTheory.PerBor.inv_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:08:35.337577+00:00
-- url     : https://prove2.me/submissions/ca4374b9-a381-4d00-80f8-1e3e7a59c78e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TriangularFrameMovesPeriodBlockTriangular
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
open GlobalTheory GlobalTheory.PerBor
namespace GlobalTheory.PerBor
theorem _root_.solution {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    ∀ j j', h⁻¹ j j' ≠ 0 → t j = t j' ∧ w j ≤ w j' := by
  letI := Matrix.invertibleOfIsUnitDet h hu
  have key : ∀ ι : α → ℤ, h⁻¹.BlockTriangular (fun j => toLex (ι (t j), w j)) := by
    intro ι
    refine Matrix.blockTriangular_inv_of_blockTriangular ?_
    intro j j' hlt
    by_contra hne
    obtain ⟨h1, h2⟩ := hs j j' hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hlt
    omega
  intro j j' hne
  have h1 : ¬ _ := fun hlt => hne (key (fun a => (Fintype.equivFin α a : ℕ)) (i := j) (j := j') hlt)
  have h2 : ¬ _ := fun hlt => hne (key (fun a => -((Fintype.equivFin α a : ℕ) : ℤ)) (i := j) (j := j') hlt)
  simp only [Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at h1 h2
  have h3 : ((Fintype.equivFin α (t j) : ℕ)) = (Fintype.equivFin α (t j') : ℕ) := by omega
  have h4 : t j = t j' := (Fintype.equivFin α).injective (Fin.ext h3)
  exact ⟨h4, h1.2 (by rw [h4])⟩
end GlobalTheory.PerBor
