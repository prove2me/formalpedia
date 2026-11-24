-- Prove2me | solution 1 for GlobalTheory.LengthQuotientSpanValuation.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:45.449294+00:00
-- url     : https://prove2.me/submissions/03b2885e-0956-426a-a5c1-af146bf07171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthSelfEqTop
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_length_quot_span
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_length_self_eq_top
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_addVal_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.LengthQuotientSpanValuation
open Module
namespace GlobalTheory.LengthQuotientSpanValuation
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type u_2} [AddCommGroup M] [Module R M] {ι : Type u_3} [Fintype ι] [DecidableEq ι]
    {M' : Type u_4} [AddCommGroup M'] [Module R M'] (b' : Module.Basis ι R M')
    (b : Module.Basis ι R M) (f : M' →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      (IsDiscreteValuationRing.addVal R : R → ℕ∞)
        (Matrix.det ((LinearMap.toMatrix b' b : (M' →ₗ[R] M) → Matrix ι ι R) f)) := by
  set A := LinearMap.toMatrix b' b f with hA
  by_cases hf : Function.Injective f
  · set N := LinearMap.range f with hN
    let e₀ : M' ≃ₗ[R] N := LinearEquiv.ofInjective f hf
    have h : Module.finrank R N = Module.finrank R M := by
      rw [← e₀.finrank_eq, Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]
    let a := Submodule.smithNormalFormCoeffs b h
    let bT := Submodule.smithNormalFormTopBasis b h
    let bB := Submodule.smithNormalFormBotBasis b h
    have ab_eq := Submodule.smithNormalFormBotBasis_def b h

    have hlen : Module.length R (M ⧸ N) = IsDiscreteValuationRing.addVal R (∏ i, a i) := by
      rw [(Submodule.quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype,
        addVal_prod]
      exact Finset.sum_congr rfl fun i _ => length_quot_span _
    rw [hlen, IsDiscreteValuationRing.addVal_eq_iff_associated]

    let φ : M' ≃ₗ[R] M := b'.equiv b (Equiv.refl ι)
    have hdetA : A.det = LinearMap.det (N.subtype ∘ₗ ((φ.symm.trans e₀ : M ≃ₗ[R] N) : M →ₗ[R] N)) := by
      rw [← LinearMap.det_toMatrix b]
      congr 1
      ext i j
      simp [hA, LinearMap.toMatrix_apply, φ, e₀]
      rfl
    let e' : M ≃ₗ[R] N := bT.equiv bB (Equiv.refl ι)
    have hg : ∀ i, (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (bT i) = a i • bT i := by
      intro i
      simp [e', Basis.equiv_apply, bB, bT, a, ab_eq]
    have hdiag : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix bT, ← Matrix.det_diagonal]
      congr 1
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
    rw [hdetA, ← hdiag]
    exact LinearMap.associated_det_comp_equiv _ _ _
  · have hdet : A.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
        simpa [Function.Injective] using hf
      refine ⟨b'.repr (x - y), ?_, ?_⟩
      · intro h
        apply hne
        rw [← sub_eq_zero]
        apply b'.repr.injective
        rw [map_zero]
        exact Finsupp.ext fun i => by simpa using congrFun h i
      · rw [hA, LinearMap.toMatrix_mulVec_repr, map_sub, hxy, sub_self, map_zero]
        rfl
    rw [hdet, IsDiscreteValuationRing.addVal_zero]
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    let φ : M →ₗ[R] R := ∑ i, w i • b.coord i
    have hφ : ∀ x, φ x = ∑ i, w i * b.repr x i := by
      intro x
      simp [φ]
    have hle : LinearMap.range f ≤ LinearMap.ker φ := by
      rw [LinearMap.range_le_ker_iff]
      refine b'.ext fun j => ?_
      have := congrFun hw j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
      rw [LinearMap.comp_apply, hφ, LinearMap.zero_apply, ← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hA, LinearMap.toMatrix_apply]
    let ψ := (LinearMap.range f).liftQ φ hle
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw0 (funext h)
    have hmem : (R ∙ w i) ≤ LinearMap.range ψ := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨Submodule.Quotient.mk (b i), ?_⟩
      simp [ψ, hφ, Finsupp.single_apply]
    have h1 : Module.length R (R ∙ w i) = ⊤ := by
      rw [← (LinearEquiv.toSpanNonzeroSingleton R R (w i) hi).length_eq, length_self_eq_top]
    have h2 : Module.length R (R ∙ w i) ≤ Module.length R (LinearMap.range ψ) :=
      Module.length_le_of_injective (Submodule.inclusion hmem) (Submodule.inclusion_injective hmem)
    have h3 : Module.length R (LinearMap.range ψ) ≤ Module.length R (M ⧸ LinearMap.range f) :=
      Module.length_le_of_surjective ψ.rangeRestrict (LinearMap.surjective_rangeRestrict ψ)
    rw [← top_le_iff, ← h1]
    exact h2.trans h3
end GlobalTheory.LengthQuotientSpanValuation
