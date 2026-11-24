-- Prove2me | solution 1 for GlobalTheory.CxPointsSep.eq_zero_of_forall_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:39.68234+00:00
-- url     : https://prove2.me/submissions/c2454961-961f-4a1d-aba8-3a4e51f4051d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep
namespace GlobalTheory.CxPointsSep
theorem _root_.solution {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [IsReduced A] [Algebra.FiniteType k A] (a : A) (h : ∀ e : A →ₐ[k] k, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hb : Function.Bijective (algebraMap k (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : k ≃ₐ[k] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ k m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2
end GlobalTheory.CxPointsSep
