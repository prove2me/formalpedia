-- Prove2me | solution 1 for GlobalTheory.FlatDescent.existsUnique_baseChange_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:08:49.846461+00:00
-- url     : https://prove2.me/submissions/1932a8db-7a5e-4899-a2e0-ab0320516372

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Theorems.Thm_GlobalTheory_FlatDescent_bijective_toInvariants
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.FlatDescent
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
namespace GlobalTheory.FlatDescent
theorem _root_.solution [Module.FaithfullyFlat A B]
    (f : B ⊗[A] M →ₗ[B] B ⊗[A] M') (hf : ∀ m : M, f (1 ⊗ₜ m) ∈ invariants (canonical B M')) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f := by
  let e := LinearEquiv.ofBijective _ (bijective_toInvariants (A := A) B M')
  let g : M →ₗ[A] M' := e.symm.toLinearMap ∘ₗ
    ((f.restrictScalars A) ∘ₗ TensorProduct.mk A B M 1).codRestrict _ hf
  have hg : ∀ m, (1 : B) ⊗ₜ[A] g m = f (1 ⊗ₜ m) := fun m =>
    congrArg Subtype.val (e.apply_symm_apply ⟨f (1 ⊗ₜ m), hf m⟩)
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · ext m
    simpa using hg m
  · ext m
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) M'
    simp only [TensorProduct.mk_apply, hg, ← hg', LinearMap.baseChange_tmul]
end GlobalTheory.FlatDescent
