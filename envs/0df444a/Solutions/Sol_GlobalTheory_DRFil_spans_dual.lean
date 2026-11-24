-- Prove2me | solution 1 for GlobalTheory.DRFil.spans_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:02:29.605813+00:00
-- url     : https://prove2.me/submissions/68036f9a-169b-4683-baad-146a8812bc04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
import Theorems.Thm_GlobalTheory_DRFil_spans_dual_base
import Theorems.Thm_GlobalTheory_DRFil_spans_resRep_iff
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
namespace GlobalTheory.DRFil
theorem _root_.solution [FiniteDimensional Qp LL] [CharZero Qp] [FiniteDimensional LL V]
    (ρ : Representation LL G V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  have hVf : FiniteDimensional Qp V := Module.Finite.trans LL V
  let e := LinearEquiv.ofBijective β.flip hb
  have hV'L : FiniteDimensional LL V' := Module.Finite.equiv e.symm
  have hV'f : FiniteDimensional Qp V' := Module.Finite.trans LL V'
  let tr : LL →ₗ[Qp] Qp := Algebra.trace Qp LL
  let β₀ : V →ₗ[Qp] V' →ₗ[Qp] Qp := LinearMap.mk₂ Qp (fun x y => tr (β x y))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by
      simp only [LinearMap.map_smul_of_tower, LinearMap.smul_apply, map_smul])
    (fun x y₁ y₂ => by simp only [map_add])
    (fun c x y => by simp only [LinearMap.map_smul_of_tower, map_smul])
  have hβ₀ : ∀ g x y, β₀ (resRep Qp ρ g x) (resRep Qp ρ' g y) = β₀ x y := by
    intro g x y
    show tr (β (ρ g x) (ρ' g y)) = tr (β x y)
    rw [hβ]
  have hinj : Function.Injective β₀.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ∀ x, β x y = 0 := by
      intro x
      refine (traceForm_nondegenerate Qp LL).1 (β x y) (fun c => ?_)
      have := LinearMap.congr_fun hy (c • x)
      simp only [LinearMap.flip_apply, LinearMap.zero_apply] at this
      rw [Algebra.traceForm_apply, mul_comm]
      change tr (c * β x y) = 0
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.map_smul]
      exact this
    apply hb.1
    rw [map_zero]
    ext x
    exact h1 x
  have hrank : Module.finrank Qp V' = Module.finrank Qp (V →ₗ[Qp] Qp) := by
    rw [← Module.finrank_mul_finrank Qp LL V', LinearEquiv.finrank_eq e,
      Subspace.dual_finrank_eq, Module.finrank_mul_finrank]
    exact (Subspace.dual_finrank_eq (K := Qp) (V := V)).symm
  have hb₀ : Function.Bijective β₀.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩
  have h₀ : Spans PD (resRep Qp ρ) := (spans_resRep_iff PD ρ).2 h
  exact (spans_resRep_iff PD ρ').1 (spans_dual_base PD (resRep Qp ρ) (resRep Qp ρ') β₀ hF hβ₀ hb₀ h₀)
end GlobalTheory.DRFil
