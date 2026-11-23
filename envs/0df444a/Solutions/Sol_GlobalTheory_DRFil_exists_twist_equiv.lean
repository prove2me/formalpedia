-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_twist_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:22.20979+00:00
-- url     : https://prove2.me/submissions/226dd228-1ed4-4f55-a44c-bb4d2e7f70b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_twist_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_twist_mem_FildR
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
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
namespace GlobalTheory.DRFil
theorem _root_.solution (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (h : IsTwistRep (cycLL PD LL) ρ ρ') (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) :
    ∃ Φ : V ⊗[Qp] F ≃ₗ[LL] V' ⊗[Qp] F, (DdR PD ρ).map Φ.toLinearMap = DdR PD ρ' ∧
      ∀ τ a, (FildR PD ρ τ a).map Φ.toLinearMap = FildR PD ρ' τ (a - 1) := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g x, ρ' g (e x) = ((PD.χ g : Qpˣ) : Qp) • e (ρ g x) := fun g x => by
    rw [he]
    exact algebraMap_smul LL _ _
  have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
    (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
  have ht : ∀ g, PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := fun g => by
    rw [← PD.ι_comm, PD.t_act, hsm]
  have hug : ∀ g, PD.actdR g u = ((PD.χ g : Qpˣ) : Qp)⁻¹ • u := fun g => by
    have h1 := congrArg (PD.actdR g) hu
    rw [map_mul, map_one, ht, smul_mul_assoc] at h1
    have h2 := congrArg (fun z => ((PD.χ g : Qpˣ) : Qp)⁻¹ • (u * z)) h1
    simp only [mul_smul_comm, smul_smul, ← mul_assoc, mul_comm u (PD.ι PD.t), hu, one_mul, mul_one] at h2
    rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2
    exact h2
  have f1 : ∀ g x, ((PD.χ g : Qpˣ) : Qp)⁻¹ • ρ' g (e.toLinearMap x) = e.toLinearMap (ρ g x) := fun g x => by
    simp [he', smul_smul]
  have f2 : ∀ g x, ((PD.χ g : Qpˣ) : Qp) • ρ g (e.symm.toLinearMap x) = e.symm.toLinearMap (ρ' g x) := by
    intro g x
    obtain ⟨x, rfl⟩ := e.surjective x
    apply e.injective
    simp [he']
  let Φ : V ⊗[Qp] F →ₗ[LL] V' ⊗[Qp] F := mulR Qp F LL V' u ∘ₗ ext Qp F e.toLinearMap
  let Ψ : V' ⊗[Qp] F →ₗ[LL] V ⊗[Qp] F := mulR Qp F LL V (PD.ι PD.t) ∘ₗ ext Qp F e.symm.toLinearMap
  have h1 : ∀ x, Φ (Ψ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ, ← mul_assoc, (mul_comm u _).trans hu]
  have h2 : ∀ x, Ψ (Φ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v b => simp [Φ, Ψ, ← mul_assoc, hu]
  refine ⟨LinearEquiv.ofLinear Φ Ψ (LinearMap.ext h1) (LinearMap.ext h2), le_antisymm ?_ fun y hy => ?_,
    fun τ a => le_antisymm ?_ fun y hy => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact twist_mem_DdR PD ρ ρ' _ u _ hug f1 hx
  · exact ⟨Ψ y, twist_mem_DdR PD ρ' ρ _ _ _ ht f2 hy, h1 y⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := twist_mem_FildR PD ρ ρ' _ u _ hug f1 τ hu' hx
    rwa [neg_add_eq_sub] at this
  · have := twist_mem_FildR PD ρ' ρ _ _ _ ht f2 τ PD.mem_filtration_one hy
    rw [add_sub_cancel] at this
    exact ⟨Ψ y, this, h1 y⟩
end GlobalTheory.DRFil
