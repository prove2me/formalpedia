-- Prove2me | solution 1 for GlobalTheory.DRFil.idem_notMem_FilV_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:22:26.030728+00:00
-- url     : https://prove2.me/submissions/d2ba975a-c887-46ea-9120-f6de36e1f3d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_FilV_antitone
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_eq_zero_of_forall_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_idem_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_idem_mul_idem
import Theorems.Thm_GlobalTheory_DRFil_idem_ne_zero
import Theorems.Thm_GlobalTheory_DRFil_mul_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_nontrivial_dR
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
theorem _root_.solution (τ : K →ₐ[Qp] LL) : idem F τ ∉ FilV PD (LL := LL) (V := LL) 1 := by
  intro h
  have := nontrivial_dR PD
  refine idem_ne_zero (F := F) τ (eq_zero_of_forall_mem_FilV PD (LL := LL) _ fun a => ?_)
  have hn : ∀ n : ℕ, idem F τ ∈ FilV PD (LL := LL) (V := LL) n := by
    intro n
    induction n with
    | zero => exact idem_mem_FilV PD τ
    | succ n ih => simpa [idem_mul_idem] using mul_mem_FilV PD ih h
  exact FilV_antitone PD (Int.self_le_toNat a) (hn a.toNat)
end GlobalTheory.DRFil
