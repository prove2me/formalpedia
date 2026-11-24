-- Prove2me | solution 1 for GlobalTheory.DRFil.isDR_of_isCrys
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:33:18.094307+00:00
-- url     : https://prove2.me/submissions/8a635522-9660-44c7-a1ee-b5cc906e1b53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_mulR_mem_DdR
import Theorems.Thm_P2M_GlobalTheory_DRFil__V_mem_DdR_4a0c80958f6e
import Theorems.Thm_GlobalTheory_DRFil_TensInj_tensor
import Theorems.Thm_GlobalTheory_DRFil_Adapted_linearIndependent
import Theorems.Thm_GlobalTheory_DRFil_Adapted_tensor
import Theorems.Thm_GlobalTheory_DRFil_Spans_tensor
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
theorem _root_.solution (h : TensInj PD) (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V) (hc : IsCrys PD ρ) :
    IsDR PD ρ ∧ ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) := by
  have := PD.finK
  have : FiniteDimensional K₀ K := FiniteDimensional.right Qp K₀ K
  let c := Module.finBasis K₀ K
  let Θ₀ : (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) →ₗ[LL] V ⊗[Qp] F :=
    ∑ i, mulR Qp F LL V (algebraMap K F (c i)) ∘ₗ ιV PD (LL := LL) (V := V) ∘ₗ (Dcris PD ρ).subtype ∘ₗ
      LinearMap.proj i
  have hΘ₀ : ∀ x, Θ₀ x = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) :=
    fun x => by simp [Θ₀, LinearMap.sum_apply]
  let Θ := Θ₀.codRestrict (DdR PD ρ) fun x => by
    rw [hΘ₀]
    exact Submodule.sum_mem _ fun i _ => mulR_mem_DdR PD ρ _ (ιV_mem_DdR PD ρ (x i).2)
  have hi : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    funext i
    exact Subtype.ext (h.tensor (LL := LL) _ c c.linearIndependent (fun i => (x i : V ⊗[Qp] B))
      ((hΘ₀ x).symm.trans (congrArg Subtype.val hx)) i)
  have := Module.Finite.of_injective Θ hi
  have : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective (LinearMap.proj (R := LL) (φ := fun _ => ↥(Dcris PD ρ))
      (⟨0, finrank_pos⟩ : Fin (finrank K₀ K))) (Function.surjective_eval _)
  have h1 : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hc,
      ← Module.finrank_mul_finrank Qp K₀ K]
    ring
  have h2 := LinearMap.finrank_le_finrank_of_injective hi
  have h3 : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (h1 ▸ h2)
  refine ⟨h3, fun y hy => ?_⟩
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (h1.trans h3.symm)).1 hi ⟨y, hy⟩
  exact ⟨_, c, fun i => x i, fun i => (x i).2, (congrArg Subtype.val hx).symm.trans (hΘ₀ x)⟩
end GlobalTheory.DRFil
