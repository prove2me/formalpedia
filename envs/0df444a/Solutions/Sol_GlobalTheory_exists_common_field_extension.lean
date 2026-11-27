-- Prove2me | solution 1 for GlobalTheory.exists_common_field_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:46.277877+00:00
-- url     : https://prove2.me/submissions/67b4c638-bce3-4c67-961f-c0b6f3a307ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCommonFieldExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂),
      ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  intro Ω Ω₁ Ω₂ _ _ _ i₁ i₂
  letI : Algebra Ω Ω₁ := i₁.toAlgebra
  letI : Algebra Ω Ω₂ := i₂.toAlgebra
  haveI : Nontrivial (Ω₁ ⊗[Ω] Ω₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω₁ ⊗[Ω] Ω₂)
  refine ⟨(Ω₁ ⊗[Ω] Ω₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := Ω) (A := Ω₁) (B := Ω₂)).toRingHom, ?_⟩
  ext x
  have h : (algebraMap Ω Ω₁ x) ⊗ₜ[Ω] (1 : Ω₂) = (1 : Ω₁) ⊗ₜ[Ω] (algebraMap Ω Ω₂ x) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact congrArg (Ideal.Quotient.mk m) h
end GlobalTheory
