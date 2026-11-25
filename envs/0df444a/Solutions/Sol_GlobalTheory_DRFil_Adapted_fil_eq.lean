-- Prove2me | solution 1 for GlobalTheory.DRFil.Adapted.fil_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:39.454243+00:00
-- url     : https://prove2.me/submissions/620242f5-ec46-4856-a009-abc047b8ba2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_idem_notMem_FilV_one
import Theorems.Thm_GlobalTheory_DRFil_FildR_antitone
import Theorems.Thm_GlobalTheory_DRFil_Adapted_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_FilV_antitone
import Theorems.Thm_GlobalTheory_DRFil_actR_idem
import Theorems.Thm_GlobalTheory_DRFil_actR_mul
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_act_sm
import Theorems.Thm_GlobalTheory_DRFil_exists_of_actR_fixed
import Theorems.Thm_GlobalTheory_DRFil_exists_smul_idem
import Theorems.Thm_GlobalTheory_DRFil_idem_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_idem_mul_idem
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_mul_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_of_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_mul
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
open GlobalTheory.DRFil.Adapted
variable {PD} {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {ι : Type} [Fintype ι]
    {d : ι → V ⊗[Qp] F} {k : ι → ℤ} (h : Adapted PD ρ τ d k)
include h
namespace GlobalTheory.DRFil.Adapted
theorem _root_.solution (a : ℤ) : FildR PD ρ τ a = Submodule.span LL (d '' {i | a ≤ k i}) := by
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨r, hr, hy'⟩ := h.span a y hy.2
    rw [sm_idem_of_mem_DdRE PD ρ τ hy.1] at hy'
    have hinv : ∀ i g, actR PD LL g (idem F τ * r i) = idem F τ * r i := by
      intro i g
      have := h.indep (fun i => actR PD LL g (r i) - r i) (by
        have h1 := (mem_DdR PD ρ y).1 hy.1.1 g
        rw [hy', map_sum] at h1
        simp only [act_sm, (mem_DdR PD ρ _).1 (h.mem _).1.1 g] at h1
        simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, h1, sub_self]) i
      rw [actR_mul, actR_idem, ← sub_eq_zero, ← mul_sub, this]
    have hc : ∀ i, ∃ c : LL, idem F τ * r i = c • idem F τ := by
      intro i
      obtain ⟨n, a, c, hn⟩ := exists_of_actR_fixed PD _ (hinv i)
      exact ⟨_, by rw [← exists_smul_idem τ n a c, ← hn, ← mul_assoc, idem_mul_idem]⟩
    choose c hc using hc
    rw [hy']
    refine Submodule.sum_mem _ fun i _ => ?_
    have e1 : sm Qp F LL V (r i) (d i) = c i • d i := by
      rw [← h.sm_idem i, ← sm_mul, mul_comm, hc, map_smul, LinearMap.smul_apply, h.sm_idem i]
    rw [e1]
    by_cases hi : a ≤ k i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · by_cases h0 : c i = 0
      · simp [h0]
      · exfalso
        have h1 := mul_mem_FilV PD (idem_mem_FilV PD τ) (hr i)
        rw [hc] at h1
        have h2 := Submodule.smul_mem _ (c i)⁻¹ h1
        rw [smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
        exact idem_notMem_FilV_one PD τ (FilV_antitone PD (by omega) h2)
  · rintro _ ⟨i, hi, rfl⟩
    exact FildR_antitone PD ρ τ hi (h.mem i)
end GlobalTheory.DRFil.Adapted
