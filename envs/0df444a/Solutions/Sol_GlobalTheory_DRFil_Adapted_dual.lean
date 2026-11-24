-- Prove2me | solution 1 for GlobalTheory.DRFil.Adapted.dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:38:42.88219+00:00
-- url     : https://prove2.me/submissions/4ba20175-ca7a-498f-b162-105ec87836ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_Adapted_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_actR_idem
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_bil_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_right
import Theorems.Thm_GlobalTheory_DRFil_dual_family
import Theorems.Thm_GlobalTheory_DRFil_exists_dual_bases
import Theorems.Thm_GlobalTheory_DRFil_idem_mul_idem
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_idem
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_sm_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_sm_self
import Theorems.Thm_GlobalTheory_DRFil_tmul_mem_FilV
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
theorem _root_.solution [FiniteDimensional LL V] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hβ' : Function.Bijective β.flip) :
    ∃ d' : ι → V' ⊗[Qp] F, Adapted PD ρ' τ d' fun i => -k i := by
  classical
  obtain ⟨v, w, hvw⟩ := exists_dual_bases β hβ'
  choose r hr hr' using fun a => h.span 0 (v a ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
  obtain ⟨h1, h2, h3⟩ := dual_family PD ρ ρ' β hβ v w hvw (idem F τ) (idem_mul_idem τ) (actR_idem PD τ) d
    (fun i => (h.mem i).1.1) h.sm_idem h.indep r hr' _ (fun _ => rfl)
  refine ⟨_, fun i => ⟨?_, ?_⟩, fun s hs i => ?_, fun n y hy => ⟨_, fun i => ?_, h3 y⟩⟩
  · have := sm_idem_mem_DdRE PD ρ' τ (h1 i)
    rwa [sm_idem_idem] at this
  · refine sm_idem_mem_FilV PD τ (Submodule.sum_mem _ fun a _ => ?_)
    simpa using sm_mem_FilV PD (hr a i) (tmul_mem_FilV PD (w a) PD.one_mem)
  · have := congrArg (bil Qp F β (d i)) hs
    rw [map_sum, map_zero] at this
    simp only [bil_sm_right β (s _), h2, sm_self] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa [mul_comm] using this
  · have := bil_mem_FilV PD β (h.mem i).2 hy
    rwa [show k i + n = n - -k i by ring] at this
end GlobalTheory.DRFil.Adapted
