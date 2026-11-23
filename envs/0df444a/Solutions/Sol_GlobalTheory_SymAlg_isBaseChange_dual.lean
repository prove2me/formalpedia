-- Prove2me | solution 1 for GlobalTheory.SymAlg.isBaseChange_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:18.359086+00:00
-- url     : https://prove2.me/submissions/39d4a68e-a298-456f-b654-2e67f067cd04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul

set_option autoImplicit false
open TensorProduct Module
open scoped DirectSum
open GlobalTheory
open GlobalTheory.SymAlg
variable {R : Type*} [CommRing R] {M M' M'' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
variable {S : Type*} [CommRing S] [Algebra R S] {W : Type*} [AddCommGroup W] [Module R W]
  [Module S W] [IsScalarTower R S W]
namespace GlobalTheory.SymAlg
theorem _root_.solution [Module.Finite R M] [Module.Projective R M] {j : M →ₗ[R] W}
    (h : IsBaseChange S j) : IsBaseChange S h.toDual := by
  let Φ : S ⊗[R] Dual R M →ₗ[S] Dual S W := h.toDual.liftBaseChange S
  let e := lTensorHomEquivHomLTensor R M S R
  have key : ∀ (t : S ⊗[R] Dual R M) (m : M), Φ t (j m) = TensorProduct.rid R S (e t m) := by
    intro t m
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul s ξ =>
      simp [Φ, e, h.toDual_comp_apply, Algebra.smul_def, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩)
    (fun ξ => by change Φ _ = _; simp [Φ])
  · rw [injective_iff_map_eq_zero]
    intro t ht
    apply e.injective
    ext m
    apply (TensorProduct.rid R S).injective
    rw [← key, ht]
    simp
  · intro φ
    refine ⟨e.symm ((TensorProduct.rid R S).symm.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ j), ?_⟩
    refine h.algHom_ext _ _ fun m => ?_
    rw [key]
    simp
end GlobalTheory.SymAlg
