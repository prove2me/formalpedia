-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_component_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:33:25.000629+00:00
-- url     : https://prove2.me/submissions/cc856060-d7e6-4389-83bb-8604b88129d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_mem_DcrisL
import Theorems.Thm_GlobalTheory_DRFil_mulR_mem_Dcris
import Theorems.Thm_P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e
import Theorems.Thm_P2M_GlobalTheory_DRFil__V_mulR_b4570f3d6ba3
import Theorems.Thm_GlobalTheory_DRFil_TensInj_tensor
import Theorems.Thm_GlobalTheory_DRFil_Adapted_linearIndependent
import Theorems.Thm_GlobalTheory_DRFil_Adapted_tensor
import Theorems.Thm_GlobalTheory_DRFil_Spans_tensor
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_idem_repr
import Theorems.Thm_GlobalTheory_DRFil_mulR_mulR
import Theorems.Thm_GlobalTheory_DRFil_mulR_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_sm_comm
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_of_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_one_tmul
import Theorems.Thm_GlobalTheory_DRFil_sm_tmul_left
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
variable [FiniteDimensional Qp K] [CharZero Qp]
namespace GlobalTheory.DRFil
theorem _root_.solution (h : TensInj PD) (ρ : Representation LL G V)
    (hs : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)))
    (τ : K →ₐ[Qp] LL) (τ₀ : K₀ →ₐ[Qp] LL) (hτ : ∀ c, τ₀ c = τ (algebraMap K₀ K c)) :
    ∃ e : ↥(DcrisL PD ρ τ₀) ≃ₗ[LL] ↥(DdRE PD ρ τ), ∀ x : ↥(DcrisL PD ρ τ₀),
      (e x : V ⊗[Qp] F) = sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) x) := by
  have := PD.finK₀
  have : FiniteDimensional K₀ K := FiniteDimensional.right Qp K₀ K
  let Θ : ↥(DcrisL PD ρ τ₀) →ₗ[LL] ↥(DdRE PD ρ τ) :=
    (sm Qp F LL V (idem F τ) ∘ₗ ιV PD (LL := LL) (V := V) ∘ₗ (DcrisL PD ρ τ₀).subtype).codRestrict _
      fun x => sm_idem_mem_DdRE PD ρ τ (ιV_mem_DdR PD ρ x.2.1)
  have hιc : ∀ c : K₀, PD.ι (algebraMap K₀ B c) = algebraMap K F (algebraMap K₀ K c) := fun c => by
    rw [PD.ι.commutes, IsScalarTower.algebraMap_apply K₀ K F]
  have hcomm : ∀ (c : K) (z : V ⊗[Qp] F), sm Qp F LL V (idem F τ) (mulR Qp F LL V (algebraMap K F c) z) =
      τ c • sm Qp F LL V (idem F τ) z := fun c z => by
    rw [← sm_one_tmul, sm_comm, sm_one_tmul, mulR_sm_idem]
  refine ⟨LinearEquiv.ofBijective Θ ⟨?_, ?_⟩, fun x => rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    have h0 : sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) x) = 0 := congrArg Subtype.val h0
    let β := Module.finBasis K₀ K
    obtain ⟨n, a, c, he, h1⟩ := idem_repr F τ
    have e1 : ∀ c : K, mulR Qp F LL V (algebraMap K F c) (ιV PD (LL := LL) (V := V) x) =
        ∑ i, τ₀ (β.repr c i) • mulR Qp F LL V (algebraMap K F (β i)) (ιV PD (LL := LL) (V := V) x) := by
      intro c
      conv_lhs => rw [← β.sum_repr c, map_sum, ← sm_one_tmul, tmul_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sm_one_tmul, Algebra.smul_def, map_mul, mul_comm, ← mulR_mulR, ← hιc, ← ιV_mulR,
        ((mem_DcrisL PD ρ τ₀ x).1 hx).2, map_smul, map_smul]
    have e2 : ∀ c : K, τ c = ∑ i, τ₀ (β.repr c i) * τ (β i) := by
      intro c
      conv_lhs => rw [← β.sum_repr c, map_sum]
      simp only [Algebra.smul_def, map_mul, hτ]
    have e3 := h.tensor (LL := LL) _ β β.linearIndependent (fun i => (∑ j, a j * τ₀ (β.repr (c j) i)) • x) (by
      rw [he, map_sum, LinearMap.sum_apply] at h0
      simp only [sm_tmul_left, e1 (c _), Finset.smul_sum, smul_smul] at h0
      rw [Finset.sum_comm] at h0
      simpa only [map_smul, ← Finset.sum_smul] using h0)
    have e4 : ∑ i, τ (β i) * ∑ j, a j * τ₀ (β.repr (c j) i) = 1 := by
      rw [← h1]
      simp only [e2 (c _), Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    apply Subtype.ext
    change x = 0
    rw [← one_smul LL x, ← e4, Finset.sum_smul]
    exact Finset.sum_eq_zero fun i _ => by rw [mul_smul, e3, smul_zero]
  · rintro ⟨y, hy⟩
    obtain ⟨m, c, x, hx, hy'⟩ := hs y hy.1
    obtain ⟨n, a, u, he, h1⟩ := idem_repr B τ₀
    have e0 : ∀ z, sm Qp B LL V (idem B τ₀) z = ∑ j, a j • mulR Qp B LL V (algebraMap K₀ B (u j)) z := by
      intro z
      rw [he, map_sum, LinearMap.sum_apply]
      simp only [sm_tmul_left]
    have e1 : ∀ i, sm Qp B LL V (idem B τ₀) (x i) ∈ DcrisL PD ρ τ₀ := fun i => by
      refine (mem_DcrisL PD ρ τ₀ _).2 ⟨?_, fun c => mulR_sm_idem τ₀ c _⟩
      rw [e0]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mulR_mem_Dcris PD ρ _ (hx i))
    have e2 : ∀ z, sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) (sm Qp B LL V (idem B τ₀) z)) =
        sm Qp F LL V (idem F τ) (ιV PD (LL := LL) (V := V) z) := by
      intro z
      rw [e0, map_sum, map_sum]
      simp only [map_smul, ιV_mulR, hιc, hcomm, smul_smul, ← hτ, ← Finset.sum_smul, h1, one_smul]
    refine ⟨∑ i, τ (c i) • ⟨_, e1 i⟩, Subtype.ext ?_⟩
    change _ = y
    rw [← sm_idem_of_mem_DdRE PD ρ τ hy, hy', map_sum, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomm, map_smul, Submodule.coe_smul, ← e2]
    rfl
end GlobalTheory.DRFil
