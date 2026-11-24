-- Prove2me | solution 1 for GlobalTheory.PeriodCompare.trace_eq_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:24:30.581867+00:00
-- url     : https://prove2.me/submissions/8a3ff514-c45d-47e6-9f11-9303fd495b39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
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
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.PeriodCompare
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ W) (J J' A : W →ₗ[ℝ] W) (hJ : ∀ x, J (J x) = -x) (hJ' : ∀ x, J' (J' x) = -x)
    (hp : ∀ x, x ≠ 0 → 0 < B (J x) x) (hp' : ∀ x, x ≠ 0 → 0 < B (J' x) x)
    (hA : J ∘ₗ A = A ∘ₗ J) (hA' : J' ∘ₗ A = A ∘ₗ J') :
    LinearMap.trace ℝ W (J ∘ₗ A) = LinearMap.trace ℝ W (J' ∘ₗ A) := by
  have hinj : Function.Injective (J + J') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 := hp' x h0
    have h3 : B ((J + J') x) x = 0 := by rw [hx]; simp
    simp only [LinearMap.add_apply, map_add] at h3
    linarith
  let T := LinearEquiv.ofInjectiveEndo _ hinj
  have hT : ∀ x, T x = J x + J' x := fun _ => rfl
  have hA1 : ∀ x, J (A x) = A (J x) := fun x => LinearMap.congr_fun hA x
  have hA2 : ∀ x, J' (A x) = A (J' x) := fun x => LinearMap.congr_fun hA' x
  rw [← LinearMap.trace_conj' (J ∘ₗ A) T]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := T.surjective y
  rw [LinearEquiv.conj_apply_apply, T.symm_apply_apply, hT, hT]
  simp only [LinearMap.comp_apply, map_add, ← hA1, ← hA2, hJ, hJ']
  abel
end GlobalTheory.PeriodCompare
