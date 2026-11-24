-- Prove2me | solution 1 for GlobalTheory.DRFil.spans_dual_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:40:56.721028+00:00
-- url     : https://prove2.me/submissions/716d31b1-cc42-4c03-ab22-1e4c29a42683

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
import Theorems.Thm_GlobalTheory_DRFil_exists_fin_basis_subset_of_isField
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
namespace GlobalTheory.DRFil
theorem _root_.solution {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V]
    (ρ : Representation Qp G V) {V' : Type} [AddCommGroup V'] [Module Qp V']
    (ρ' : Representation Qp G V') (β : V →ₗ[Qp] V' →ₗ[Qp] Qp) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  classical
  let _ : Module F (V ⊗[Qp] F) := Module.compHom (V ⊗[Qp] F) (mulRHom Qp F V)
  have hsm : ∀ (c : F) (y : V ⊗[Qp] F), c • y = mulR Qp F Qp V c y := fun _ _ => rfl
  let bV := Module.finBasis Qp V
  let κ : Fin (Module.finrank Qp V) → (V ⊗[Qp] F) →ₗ[Qp] F := fun k =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (bV.coord k) LinearMap.id
  have hκ : ∀ k (v : V) (c : F), κ k (v ⊗ₜ c) = bV.coord k v • c := fun k v c => by simp [κ]
  have hκmul : ∀ k (c : F) (y : V ⊗[Qp] F), κ k (c • y) = c * κ k y := by
    intro k c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, mul_zero]
    | tmul v a => simp only [hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hκ, mul_smul_comm]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂, mul_add]
  have hdec : ∀ y : V ⊗[Qp] F, y = ∑ k, κ k y • (bV k ⊗ₜ[Qp] (1 : F)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [hκ, hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, mul_one]
      conv_lhs => rw [← bV.sum_repr v]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [TensorProduct.smul_tmul, Basis.coord_apply]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hspanD : Submodule.span F (DdR PD ρ : Set (V ⊗[Qp] F)) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨m, b, d, hd, rfl⟩ := h y
    exact Submodule.sum_mem _ fun i _ => by
      rw [← hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hd i))
  have hfin : Module.Finite F (V ⊗[Qp] F) := by
    refine ⟨⟨Finset.univ.image fun k => bV k ⊗ₜ[Qp] (1 : F), eq_top_iff.2 fun y _ => ?_⟩⟩
    rw [hdec y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨m, E, hE⟩ := exists_fin_basis_subset_of_isField hF (DdR PD ρ : Set (V ⊗[Qp] F)) hspanD
  have hinv : ∀ y : V ⊗[Qp] F, y ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hinv' : ∀ y : V' ⊗[Qp] F, y ∈ DdR PD ρ' ↔ ∀ g, actVdR PD ρ' g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hact : ∀ g (c : F) (y : V ⊗[Qp] F),
      actVdR PD ρ g (c • y) = PD.actdR g c • actVdR PD ρ g y := by
    intro g c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul v a => simp [hsm, mulR, actVdR]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
  have hcoord : ∀ g i (y : V ⊗[Qp] F), E.coord i (actVdR PD ρ g y) = PD.actdR g (E.coord i y) := by
    intro g i y
    have h1 : actVdR PD ρ g y = ∑ j, PD.actdR g (E.repr y j) • E j := by
      conv_lhs => rw [← E.sum_repr y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hact, (hinv _).1 (hE j) g]
    rw [h1, map_sum]
    simp [Basis.coord_apply, Finsupp.single_apply]
  let e := LinearEquiv.ofBijective β.flip hb
  let w : Fin (Module.finrank Qp V) → V' := fun j => e.symm (bV.coord j)
  have hw : ∀ x j, β x (w j) = bV.coord j x := fun x j => by
    have h1 : β.flip (w j) = bV.coord j := e.apply_symm_apply (bV.coord j)
    exact LinearMap.congr_fun h1 x
  have hw' : ∀ v' : V', v' = ∑ j, β (bV j) v' • w j := by
    intro v'
    apply hb.1
    refine LinearMap.ext fun x => ?_
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, hw, smul_eq_mul]
    conv_lhs => rw [← bV.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Basis.coord_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let π : V → (V' ⊗[Qp] F) →ₗ[Qp] F := fun x =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (β x) LinearMap.id
  have hπ : ∀ x v' (c : F), π x (v' ⊗ₜ c) = β x v' • c := fun x v' c => by simp [π]
  have hπmul : ∀ x (c : F) z, π x (mulR Qp F Qp V' c z) = c * π x z := by
    intro x c z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul v' a => simp only [mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hπ, mul_smul_comm]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
  have hπact : ∀ g x z, π (ρ g x) (actVdR PD ρ' g z) = PD.actdR g (π x z) := by
    intro g x z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v' a =>
      simp [actVdR, hπ, hβ, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K F]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hzdec : ∀ z : V' ⊗[Qp] F, z = ∑ j, w j ⊗ₜ π (bV j) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v' a =>
      simp only [hπ]
      conv_lhs => rw [hw' v']
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hπext : ∀ z z' : V' ⊗[Qp] F, (∀ x, π x z = π x z') → z = z' := by
    intro z z' hz
    rw [hzdec z, hzdec z']
    simp only [hz]
  let d' : Fin m → V' ⊗[Qp] F := fun i => ∑ j, w j ⊗ₜ[Qp] E.coord i (bV j ⊗ₜ[Qp] (1 : F))
  have hπd' : ∀ x i, π x (d' i) = E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
    intro x i
    rw [hdec (x ⊗ₜ[Qp] (1 : F)), map_sum]
    simp only [d', map_sum, hπ, hw, hκ, map_smul, smul_eq_mul, smul_one_mul]
  have hd'inv : ∀ i g, actVdR PD ρ' g (d' i) = d' i := by
    intro i g
    apply hπext
    intro x
    have hx : ρ g (ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hx, hπact, hπd', hπd', ← hcoord]
    simp [actVdR]
  intro y'
  let c : Fin m → F := fun i => ∑ k, π (bV k) y' * κ k (E i)
  refine ⟨m, c, d', fun i => (hinv' _).2 (hd'inv i), ?_⟩
  apply hπext
  intro x
  rw [map_sum]
  simp only [hπmul, hπd']
  have hx1 : x ⊗ₜ[Qp] (1 : F) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) • E i := by
    simp only [Basis.coord_apply]
    exact (E.sum_repr _).symm
  have key : ∀ k, κ k (x ⊗ₜ[Qp] (1 : F)) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
    intro k
    conv_lhs => rw [hx1]
    rw [map_sum]
    simp only [hκmul]
  calc π x y' = ∑ k, bV.coord k x • π (bV k) y' := by
        conv_lhs => rw [hzdec y']
        simp only [map_sum, hπ, hw]
    _ = ∑ k, π (bV k) y' * κ k (x ⊗ₜ[Qp] (1 : F)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hκ, mul_smul_comm, mul_one]
    _ = ∑ k, π (bV k) y' * ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
        simp only [key]
    _ = ∑ i, c i * E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
        simp only [c, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
end GlobalTheory.DRFil
