-- Prove2me | solution 1 for GlobalTheory.measurable_sum_embeddings_over_generic_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:17:18.097066+00:00
-- url     : https://prove2.me/submissions/2b5cca13-c213-44a3-8110-89c77568a306

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeasurableSumEmbeddingsOverGenericPoint
import Theorems.Thm_GlobalTheory_finsum_embeddings_over_eq_sum_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ, ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) = Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) → ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i)) := by
  intro hρ K _ _ σ _ L _ _ _ sg m b Nf hNf
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨ρ, hρm, hρ⟩ := hρ pb.dim
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval _).measurable
  have hev : ∀ f, Measurable (ev f) := fun f => (hpm _).div (hpm _)
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : Measurable cf := measurable_pi_lambda _ fun i => hev _
  let G : (σ → ℂ) → ℂ → ℝ := fun t z =>
    Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)
  refine ⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩
  · refine Finset.measurable_sum _ fun k _ => hNf.comp (measurable_pi_lambda _ fun i => ?_)
    refine Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)
    exact (measurable_pi_apply k).comp (hρm.comp hcf)
  · intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra h
      exact ht p h hp
    let τ : F →+* ℂ := IsFractionRing.lift hinj
    have hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p := fun p =>
      IsFractionRing.lift_algebraMap hinj p
    have hτ : ∀ f, τ f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    have hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) =
        MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
      ext P
      constructor
      · intro hP
        apply IsFractionRing.ringHom_ext (A := R)
        intro p
        rw [hτa]
        exact hP p
      · intro hP p
        have hP' : P.comp (algebraMap F L) = τ := hP
        rw [← hτa, ← hP']
        rfl
    rw [hset]
    symm
    refine finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_
    · rw [hρ]
      have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
      conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]
      rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
        Finset.sum_range]
      simp [cf, hτ]
    · intro P hP
      show Nf _ = Nf _
      congr 1
      funext i
      conv_lhs => rw [← pb.basis.sum_repr (b i)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]
      rfl
end GlobalTheory
