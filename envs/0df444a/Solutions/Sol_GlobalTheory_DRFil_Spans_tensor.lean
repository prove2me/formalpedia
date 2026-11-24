-- Prove2me | solution 1 for GlobalTheory.DRFil.Spans.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:32:35.389704+00:00
-- url     : https://prove2.me/submissions/cd28e54c-2aac-4049-85a1-4be9892713e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_spans_iff
import Theorems.Thm_GlobalTheory_DRFil_mulR_mulR
import Theorems.Thm_GlobalTheory_DRFil_bil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_tmul_eq_sm_bil
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_left
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_right
import Theorems.Thm_GlobalTheory_DRFil_sm_one_tmul
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
namespace Spans
theorem _root_.solution {ρ : Representation LL G V} {ρ' : Representation LL G V'} {ρ'' : Representation LL G V''}
    (E : V ⊗[LL] V' ≃ₗ[LL] V'') (hE : ∀ g x y, ρ'' g (E (x ⊗ₜ[LL] y)) = E (ρ g x ⊗ₜ[LL] ρ' g y))
    (h : Spans PD ρ) (h' : Spans PD ρ') : Spans PD ρ'' := by
  rw [spans_iff]
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul u b =>
    obtain ⟨t, rfl⟩ := E.surjective u
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, add_tmul] using Submodule.add_mem _ hx hy
    | tmul v w =>
      obtain ⟨m, c, d, hd, h1⟩ := h (v ⊗ₜ[Qp] (1 : F))
      obtain ⟨m', c', d', hd', h2⟩ := h' (w ⊗ₜ[Qp] (1 : F))
      rw [tmul_eq_sm_bil, h1, h2]
      simp only [map_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.subset_span
        ⟨b * (c i * c' j), _, bil_mem_DdR PD ρ ρ' ρ'' (tensBil E) (fun g v w => (hE g v w).symm)
          (hd i) (hd' j), ?_⟩
      rw [← sm_one_tmul (c i), ← sm_one_tmul (c' j), bil_sm_left, bil_sm_right]
      simp only [sm_one_tmul, mulR_mulR]
end Spans
end GlobalTheory.DRFil
