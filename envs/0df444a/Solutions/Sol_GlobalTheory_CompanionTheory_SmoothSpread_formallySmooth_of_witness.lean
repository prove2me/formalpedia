-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothSpread.formallySmooth_of_witness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:40:19.058149+00:00
-- url     : https://prove2.me/submissions/1d2be6db-0390-400c-9f7a-e678a49f5258

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread
variable {T S ι σ : Type} [CommRing T] [CommRing S] [Algebra T S]
namespace GlobalTheory.CompanionTheory.SmoothSpread
theorem _root_.solution (Q : Algebra.Presentation T S ι σ) (h : ι → Q.Ring)
    (h1 : ∀ i, h i - X i ∈ Ideal.span (Set.range Q.relation))
    (h2 : ∀ j, aeval h (Q.relation j) ∈ Ideal.span (Set.range Q.relation) ^ 2) :
    Algebra.FormallySmooth T S := by
  let f : Q.Ring →ₐ[T] S := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Surjective f := Q.algebraMap_surjective
  have hkerf : RingHom.ker f = Ideal.span (.range Q.relation) :=
    Q.span_range_relation_eq_ker.symm
  let g₀ : Q.Ring →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.mkₐ T _).comp (aeval h)
  have hg₀ : ∀ a ∈ RingHom.ker f.toRingHom, g₀ a = 0 := by
    intro a ha
    have ha' : a ∈ Ideal.span (Set.range Q.relation) := hkerf ▸ ha
    have : Ideal.span (Set.range Q.relation) ≤ RingHom.ker g₀ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      change Ideal.Quotient.mk _ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have := h2 j
      rw [← hkerf] at this
      exact this
    exact this ha'
  let g : S →ₐ[T] Q.Ring ⧸ RingHom.ker f.toRingHom ^ 2 :=
    (Ideal.Quotient.liftₐ (RingHom.ker f.toRingHom) g₀ hg₀).comp
      (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine Algebra.FormallySmooth.of_split f g ?_
  rw [← AlgHom.cancel_right hf]
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  have hgf : g (f (X i)) = Ideal.Quotient.mk _ (h i) := by
    have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i)) = Ideal.Quotient.mk _ (X i) := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ _ g₀ hg₀)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f (X i))) = _
    rw [this]
    change Ideal.Quotient.mk _ (aeval h (X i)) = _
    rw [aeval_X]
  have hfx : f (h i) = f (X i) := by
    have := h1 i
    rw [← hkerf, RingHom.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  simp only [AlgHom.comp_apply, hgf, AlgHom.id_apply]
  rw [AlgHom.kerSquareLift_mk, hfx]
end GlobalTheory.CompanionTheory.SmoothSpread
