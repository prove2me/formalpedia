-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.eq_zero_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:45.4415+00:00
-- url     : https://prove2.me/submissions/75a8b9e5-f7ce-4096-b1b0-005a3f212e11

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeAlt_alt__Multi_4e0913c07ff2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_ext2
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_sum_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_wd_self
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_wd_swap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [Module R V] [Module R V']
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution [Module.Finite R V] [Module.Projective R V] (τ : ⋀[R]^2 V)
    (h : ∀ l l' : V →ₗ[R] R, alt l l' τ = 0) : τ = 0 := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let x : Fin n → V := fun i ↦ π fun j ↦ if i = j then 1 else 0
  let l : Fin n → V →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ s
  have hx : ∀ a, a = ∑ i, l i a • x i := fun a ↦ by
    have := LinearMap.pi_apply_eq_sum_univ π (s a)
    rw [show π (s a) = a from LinearMap.congr_fun hs a] at this
    exact this
  have hw : ∀ a b, wd (R := R) a b = ∑ i, ∑ j, (l i a * l j b) • wd (R := R) (x i) (x j) := fun a b ↦ by
    refine (congrArg₂ (fun y y' ↦ wd (R := R) y y') (hx a) (hx b)).trans ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [mul_comm]
  have key : (LinearMap.id : ⋀[R]^2 V →ₗ[R] ⋀[R]^2 V) = ∑ i, ∑ j, if i < j then
      (alt (l i) (l j)).smulRight (wd (R := R) (x i) (x j)) else 0 := ext2 fun a b ↦ by
    refine ((hw a b).trans (sum_lt (fun i ↦ l i a) (fun j ↦ l j b) (fun i j ↦ wd (R := R) (x i) (x j))
      (fun i ↦ wd_self _) (fun i j ↦ wd_swap _ _))).trans ?_
    simp only [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [LinearMap.smulRight_apply, alt_ιMulti]
    · rfl
  calc τ = (∑ i, ∑ j, if i < j then
        (alt (l i) (l j)).smulRight (wd (R := R) (x i) (x j)) else 0) τ := by rw [← key]; rfl
    _ = 0 := by
      simp only [LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
      split_ifs <;> simp [h]
end GlobalTheory.CompanionTheory.HodgeAlt
