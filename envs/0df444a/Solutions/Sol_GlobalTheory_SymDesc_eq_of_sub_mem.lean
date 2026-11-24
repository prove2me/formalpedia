-- Prove2me | solution 1 for GlobalTheory.SymDesc.eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:52.843335+00:00
-- url     : https://prove2.me/submissions/09287483-5aa3-472d-89d0-855393e43143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
import Theorems.Thm_GlobalTheory_SymDesc_injective_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SymDesc
variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]
namespace GlobalTheory.SymDesc
theorem _root_.solution [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by
  classical
  let F := FractionRing R
  let M := AlgebraicClosure F
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R F M]
    exact (algebraMap F M).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRM
  have key : ∀ (P : Ideal R₁) [P.IsPrime], P.comap (algebraMap R R₁) = ⊥ →
      ∃ j : R₁ →+* M, j.comp (algebraMap R R₁) = algebraMap R M ∧ ∀ x ∈ P, j x = 0 := by
    intro P _ hP
    have hRA : Function.Injective (algebraMap R (R₁ ⧸ P)) := injective_quotient P hP
    haveI : FaithfulSMul R (R₁ ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).2 hRA
    haveI : Module.IsTorsionFree R (R₁ ⧸ P) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
    haveI : Algebra.IsAlgebraic R (R₁ ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let l : (R₁ ⧸ P) →ₐ[R] M := IsAlgClosed.lift
    refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_, fun x hx => ?_⟩
    · ext r
      simp only [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨j, hj, hj0⟩ := key Q hQ
  obtain ⟨j', hj', hj0'⟩ := key Q' hQ'
  have h := hs M j j' (hj.trans hj'.symm)
  have h1 : j s = algebraMap R M e := by
    have := hj0 _ he
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj]
  have h2 : j' s = algebraMap R M e' := by
    have := hj0' _ he'
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj']
  exact hRM (h1.symm.trans (h.trans h2))
end GlobalTheory.SymDesc
