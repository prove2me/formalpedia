-- Prove2me | solution 1 for GlobalTheory.DetCompare.exists_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:45.293551+00:00
-- url     : https://prove2.me/submissions/504d2380-ee0c-46b2-ac87-8e4b53bee8ac

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
import Theorems.Thm_GlobalTheory_DetCompare_bijective_restrict
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
variable [IsCommMonObj G]
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.DetCompare
theorem _root_.solution [CharZero k] [IsAlgClosed k] :
    ∃ _ : Fintype (𝓞 E →+* k), IsSplitting fun τ : 𝓞 E →+* k => τ := by
  classical
  let e := Equiv.ofBijective _ (bijective_restrict (E := E) (k := k))
  let F : Fintype (𝓞 E →+* k) := Fintype.ofEquiv _ e
  refine ⟨F, isSplitting_of_isDomain (σ := fun τ : 𝓞 E →+* k => τ) Function.injective_id ?_ (RingHom.id k) ?_⟩
  · rw [← NumberField.Embeddings.card E k]
    exact Fintype.card_congr e.symm
  · simpa using NumberField.discr_ne_zero E
end GlobalTheory.DetCompare
