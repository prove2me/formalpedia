-- Prove2me | solution 1 for GlobalTheory.BaseChangeComponents.range_comp_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:27.771478+00:00
-- url     : https://prove2.me/submissions/1ac01257-617d-4804-b471-3895c9a77ef1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsNoetherianRingTensor
import Theorems.Thm_GlobalTheory_BaseChangeComponents_incl_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BaseChangeComponents.incl_tmul

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.BaseChangeComponents
variable {K Ω : Type} (F : Type) [Field K] [Field F] [Field Ω] [Algebra K F] [Algebra K Ω]
namespace GlobalTheory.BaseChangeComponents
theorem _root_.solution {E : Type} [CommRing E] (R : Subalgebra K Ω) (g : F ⊗[K] Ω →+* E) :
    (g.comp (incl F R)).range = Subring.closure
      ((g.comp (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := Ω)).toRingHom) '' (R : Set Ω)
        ∪ Set.range (g.comp (Algebra.TensorProduct.includeLeftRingHom (R := K) (A := F) (B := Ω)))) :=
  by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subring.zero_mem _
      | tmul a r =>
        have hsplit : (g.comp (incl F R)) (a ⊗ₜ r) =
            g (a ⊗ₜ (1 : Ω)) * g ((1 : F) ⊗ₜ (r : Ω)) := by
          rw [RingHom.comp_apply, incl_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
        rw [hsplit]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inr ⟨a, rfl⟩))
          (Subring.subset_closure (Or.inl ⟨r, r.2, rfl⟩))
      | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
    · rw [Subring.closure_le]
      rintro _ (⟨w, hw, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨(1 : F) ⊗ₜ ⟨w, hw⟩, by rw [RingHom.comp_apply, incl_tmul]; rfl⟩
      · exact ⟨a ⊗ₜ (1 : R), by rw [RingHom.comp_apply, incl_tmul]; rfl⟩
end GlobalTheory.BaseChangeComponents
