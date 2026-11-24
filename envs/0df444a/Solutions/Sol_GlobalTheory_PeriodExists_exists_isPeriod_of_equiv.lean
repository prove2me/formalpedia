-- Prove2me | solution 1 for GlobalTheory.PeriodExists.exists_isPeriod_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:23:02.180898+00:00
-- url     : https://prove2.me/submissions/7f465dcf-3f0a-4ea7-af2d-237ef2023132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodExists
theorem _root_.solution {H : Host E} {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (e : Fin g ≃ Fin g') (he : ∀ k, ty' (e k) = ty k)
    {P : D.La →+ (Fin g' → ℂ)} (hP : IsPeriod D ty' P) : ∃ P', IsPeriod D ty P' := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  let L : (Fin g' → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL : ∀ z k, L z k = z (e k) := fun _ _ => rfl
  have hF : ∀ z w, hermForm (Hm.submatrix e e) (L z) (L w) = hermForm Hm z w := by
    intro z w
    simp only [hermForm, dotProduct, mulVec, submatrix_apply, Pi.star_apply, hL]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
  let P' : D.La →+ (Fin g → ℂ) := L.toLinearEquiv.toLinearMap.toAddMonoidHom.comp P
  have hP' : ∀ x, P' x = L (P x) := fun _ => rfl
  refine ⟨P', ?_, ?_, ?_, ?_, Hm.submatrix e e, hH.submatrix e, ?_, ?_⟩
  · intro a x k
    rw [hP', hP', hL, hL, h1, he]
  · intro x y hxy
    exact h2 (L.injective hxy)
  · let f : P'.range → P.range := fun z => ⟨L.symm z.1, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨x, by simp [hP']⟩⟩
    have hf : Continuous f := (L.symm.continuous.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hf fun z w hzw =>
      Subtype.ext (L.symm.injective (congrArg Subtype.val hzw))
  · have : Set.range P' = L.toLinearEquiv.toLinearMap '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h4, Submodule.map_top, LinearEquiv.range]
  · intro z hz
    obtain ⟨w, rfl⟩ := L.surjective z
    rw [hF]
    exact hpos w fun h => hz (by rw [h, map_zero])
  · intro x y
    rw [hP', hP', hF, hE]
end GlobalTheory.PeriodExists
