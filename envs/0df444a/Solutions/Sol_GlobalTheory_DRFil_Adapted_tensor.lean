-- Prove2me | solution 1 for GlobalTheory.DRFil.Adapted.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:37:20.737798+00:00
-- url     : https://prove2.me/submissions/e80585b0-0fcc-48ee-a4f8-6d3f47fe96e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_bil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_tmul_eq_sm_bil
import Theorems.Thm_GlobalTheory_DRFil_Adapted_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_FilV_induction
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_bil_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_left
import Theorems.Thm_GlobalTheory_DRFil_bil_sm_right
import Theorems.Thm_GlobalTheory_DRFil_eq_zero_of_forall_ext
import Theorems.Thm_GlobalTheory_DRFil_ext_sm
import Theorems.Thm_GlobalTheory_DRFil_idem_mul_idem
import Theorems.Thm_GlobalTheory_DRFil_mul_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_sm_comm
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_idem
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_mul
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
theorem _root_.solution {ρ' : Representation LL G V'} {ι' : Type} [Fintype ι'] {d' : ι' → V' ⊗[Qp] F} {k' : ι' → ℤ}
    (h' : Adapted PD ρ' τ d' k') (ρ'' : Representation LL G V'') (E : V ⊗[LL] V' ≃ₗ[LL] V'')
    (hE : ∀ g x y, ρ'' g (E (x ⊗ₜ[LL] y)) = E (ρ g x ⊗ₜ[LL] ρ' g y)) :
    Adapted PD ρ'' τ (fun p : ι × ι' => bil Qp F (tensBil E) (d p.1) (d' p.2)) fun p => k p.1 + k' p.2 := by
  refine ⟨fun p => ⟨?_, bil_mem_FilV PD _ (h.mem p.1).2 (h'.mem p.2).2⟩, fun r hr p => ?_, fun n y hy => ?_⟩
  · have := sm_idem_mem_DdRE PD ρ'' τ (bil_mem_DdR PD ρ ρ' ρ'' (tensBil E) (fun g v w => (hE g v w).symm)
      (h.mem p.1).1.1 (h'.mem p.2).1.1)
    rwa [← bil_sm_left, h.sm_idem] at this
  · have key : ∑ j, sm Qp F LL V' (idem F τ * r (p.1, j)) (d' j) = 0 := by
      refine eq_zero_of_forall_ext (LL := LL) _ fun φ => ?_
      let C : V'' →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ φ.lTensor V ∘ₗ E.symm.toLinearMap
      have hC : ∀ x y, ext Qp F C (bil Qp F (tensBil E) x y) = sm Qp F LL V (ext Qp F φ y) x := by
        intro x y
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
        | tmul v b' =>
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add r s hr hs => simp only [map_add, LinearMap.add_apply, hr, hs]
          | tmul w b'' => simp [C, mul_comm]
      have h1 := congrArg (ext Qp F C) hr
      rw [map_sum, map_zero, Fintype.sum_prod_type] at h1
      simp only [ext_sm, hC, ← sm_mul] at h1
      have h2 := h.indep (fun i => ∑ j, r (i, j) * ext Qp F φ (d' j))
        (by simpa only [map_sum, LinearMap.sum_apply] using h1) p.1
      rw [map_sum]
      simp only [ext_sm, sm_self, mul_assoc]
      rw [← Finset.mul_sum, h2]
    have := h'.indep _ key p.2
    rwa [← mul_assoc, idem_mul_idem] at this
  · let q : V'' ⊗[Qp] F → Prop := fun y => ∃ r : ι × ι' → LL ⊗[Qp] F,
      (∀ p, r p ∈ FilV PD (LL := LL) (V := LL) (n - (k p.1 + k' p.2))) ∧
        sm Qp F LL V'' (idem F τ) y = ∑ p, sm Qp F LL V'' (r p) (bil Qp F (tensBil E) (d p.1) (d' p.2))
    have q0 : q 0 := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    have qa : ∀ x y, q x → q y → q (x + y) := by
      rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
      exact ⟨r + s, fun p => Submodule.add_mem _ (hr p) (hs p), by
        simp only [map_add, hx, hy, Pi.add_apply, LinearMap.add_apply, Finset.sum_add_distrib]⟩
    refine FilV_induction PD (p := q) q0 (fun u b hb => ?_) qa hy
    obtain ⟨t, rfl⟩ := E.surjective u
    induction t using TensorProduct.induction_on with
    | zero => simpa using q0
    | add x y hx hy => simpa only [map_add, add_tmul] using qa _ _ hx hy
    | tmul v w =>
      obtain ⟨r, hr, h1⟩ := h.span 0 (v ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
      obtain ⟨s, hs, h2⟩ := h'.span 0 (w ⊗ₜ[Qp] (1 : F)) (tmul_mem_FilV PD _ PD.one_mem)
      refine ⟨fun p => ((1 : LL) ⊗ₜ[Qp] b) * (r p.1 * s p.2), fun p => ?_, ?_⟩
      · have := mul_mem_FilV PD (tmul_mem_FilV PD (1 : LL) hb) (mul_mem_FilV PD (hr p.1) (hs p.2))
        rwa [show n + (0 - k p.1 + (0 - k' p.2)) = n - (k p.1 + k' p.2) by ring] at this
      · rw [tmul_eq_sm_bil, sm_comm, ← sm_idem_idem, ← bil_sm_right, ← bil_sm_left, h1, h2,
          Fintype.sum_prod_type_right, map_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_sum, LinearMap.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [bil_sm_left, bil_sm_right, sm_mul, sm_mul]
end GlobalTheory.DRFil.Adapted
