-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_isQuad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:07.867793+00:00
-- url     : https://prove2.me/submissions/0fde5569-2d0e-4d87-9ff3-59f97d3d87c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E),
      IsQuad δ θ σ := by
  intro F _ _ δ hδ
  have hroot : ∀ b : F, b ^ 2 ≠ δ := fun b hb => hδ ⟨b, by rw [← hb, sq]⟩
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C δ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
  have hmon : (Polynomial.X ^ 2 - Polynomial.C δ).Monic := Polynomial.monic_X_pow_sub_C δ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C δ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C δ)) := ⟨hirr⟩
  set p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C δ with hp
  have hsq : AdjoinRoot.root p ^ 2 = AdjoinRoot.of p δ := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hneg : Polynomial.eval₂ (↑(Algebra.ofId F (AdjoinRoot p)) : F →+* AdjoinRoot p)
      (-AdjoinRoot.root p) (Polynomial.X ^ 2 - Polynomial.C δ) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, neg_sq, hsq, sub_eq_zero]
    rfl
  let τ : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot p)) (-AdjoinRoot.root p) hneg
  have hτ : τ (AdjoinRoot.root p) = -AdjoinRoot.root p := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hττ : τ.comp τ = AlgHom.id F (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hτ, map_neg, neg_neg]
  have hp0 : p ≠ 0 := hmon.ne_zero
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p)).injective
  have : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans F (AdjoinRoot p)
  refine ⟨AdjoinRoot p, inferInstance, { }, inferInstance, AdjoinRoot.root p,
    AlgEquiv.ofAlgHom τ τ hττ hττ, ⟨hδ, ?_, hτ, ?_⟩⟩
  · rw [AdjoinRoot.algebraMap_eq]; exact hsq
  · intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have hp1 : p ≠ 1 := fun h => by
      rw [h, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
    have hlt := Polynomial.natDegree_modByMonic_lt g hmon hp1
    rw [hdeg] at hlt
    have hr := Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hlt)
    refine ⟨(g %ₘ p).coeff 0, (g %ₘ p).coeff 1, ?_⟩
    have hmk : AdjoinRoot.mk p g = AdjoinRoot.mk p (g %ₘ p) := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div g p]
      rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    conv_lhs => rw [hr]
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq, add_comm]
end GlobalTheory.QNorm
