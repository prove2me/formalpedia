-- Prove2me | solution 1 for GlobalTheory.finite_vertical_gauss_valuations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:10.41307+00:00
-- url     : https://prove2.me/submissions/ea924d3e-bcdf-447f-aa16-6f100ccff669

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
import Theorems.Thm_GlobalTheory_VerticalGauss_mem_extPrime
import Theorems.Thm_GlobalTheory_VerticalGauss_isDVR
import Theorems.Thm_GlobalTheory_VerticalGauss_injective_of_dvr
import Theorems.Thm_GlobalTheory_VerticalGauss_nonneg_of_isIntegral
import Theorems.Thm_GlobalTheory_VerticalGauss_finite_places
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_wt_add_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_add_eq_zero


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
open VerticalGauss IsDedekindDomain
namespace GlobalTheory
theorem _root_.solution : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D : ℕ) (x : Fin D → Ω), (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D → ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧ v g ≠ 0 ∧ ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ∀ p : MvPolynomial (Fin D) (𝓞 K), 0 ≤ v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ∧ (0 < v (MvPolynomial.eval₂ ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) x p) ↔ ∀ m, p.coeff m ∈ la.asIdeal)}.Finite := by
  intro K Ω _ _ _ _ D x hFG htr g hg
  classical
  by_contra hinf
  obtain ⟨v₀, -, -, la₀, h₀⟩ := Set.Infinite.nonempty hinf
  apply hinf
  clear hinf
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let ι : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hι : Function.Injective ι :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective (𝓞 K) K)
  let φ : MvPolynomial (Fin D) (𝓞 K) →+* Ω := MvPolynomial.eval₂Hom ι x
  have hinj : Function.Injective φ := by
    haveI := isDVR (Fin D) la₀
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la₀.ne_bot
    refine injective_of_dvr φ (extPrime (Fin D) la₀) (fun r hr => ?_) (MvPolynomial.C a)
      (Ideal.mem_map_of_mem _ ha) ?_
    · rw [mem_extPrime, ← (h₀ r).2]
      change 0 < v₀ (φ r)
      rw [hr]; simp
    · simp only [φ, MvPolynomial.eval₂Hom_C]
      exact (map_ne_zero_iff _ hι).2 ha0
  letI : Algebra (𝓞 K) Ω := ι.toAlgebra
  haveI : IsScalarTower (𝓞 K) K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (𝓞 K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hι
  have hind : AlgebraicIndependent (𝓞 K) x := hinj
  haveI : Algebra.IsAlgebraic (𝓞 K) K := IsLocalization.isAlgebraic K (nonZeroDivisors (𝓞 K))
  have hB : IsTranscendenceBasis K x :=
    (hind.extendScalars K).isTranscendenceBasis_of_trdeg_le_of_finite (by simp [htr])
  have hB' : IsTranscendenceBasis (𝓞 K) x :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_iff (𝓞 K) K).2 hB
  set R := MvPolynomial (Fin D) (𝓞 K)
  letI : Algebra R Ω := φ.toAlgebra
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI halg : Algebra.IsAlgebraic R Ω := by
    have := hB'.isAlgebraic
    exact Algebra.IsAlgebraic.of_ringHom_of_comp_eq hind.aevalEquiv.toRingEquiv.toRingHom
      (RingHom.id Ω) hind.aevalEquiv.surjective Function.injective_id
      (RingHom.ext fun p => hind.algebraMap_aevalEquiv p)
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : IsScalarTower R (FractionRing R) Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  haveI : Algebra.IsAlgebraic (FractionRing R) Ω := Algebra.IsAlgebraic.extendScalars
    (IsFractionRing.injective R (FractionRing R))
  haveI : FiniteDimensional (FractionRing R) Ω := by
    obtain ⟨S, hS⟩ := hFG
    have htop : IntermediateField.adjoin (FractionRing R) (S : Set Ω) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin K (S : Set Ω) := hS ▸ IntermediateField.mem_top
      have hO : ∀ a : 𝓞 K, ι a ∈ IntermediateField.adjoin (FractionRing R) (S : Set Ω) := by
        intro a
        have : ι a = algebraMap (FractionRing R) Ω (algebraMap R _ (MvPolynomial.C a)) := by
          rw [← IsScalarTower.algebraMap_apply]
          exact (MvPolynomial.eval₂Hom_C ι x a).symm
        rw [this]; exact IntermediateField.algebraMap_mem _ _
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
      | algebraMap k =>
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
        rw [map_div₀]
        exact div_mem (hO a) (hO b)
      | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
      | inv a _ ha => exact inv_mem (ha trivial)
      | mul a b _ _ ha hb => exact mul_mem (ha trivial) (hb trivial)
    have : FiniteDimensional (FractionRing R)
        (IntermediateField.adjoin (FractionRing R) (S : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ =>
        (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    rw [htop] at this
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  obtain ⟨r, hr0, hr⟩ := (halg.isAlgebraic g).exists_integral_multiple
  obtain ⟨s, hs0, hs⟩ := (halg.isAlgebraic g⁻¹).exists_integral_multiple
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 (mul_ne_zero hr0 hs0)
  have hfin : {la : HeightOneSpectrum (𝓞 K) |
      la.asIdeal ∣ Ideal.span {MvPolynomial.coeff m (r * s)}}.Finite :=
    Ideal.finite_factors (by simpa using hm)
  refine (hfin.biUnion (t := fun la => {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧ (0 < v (algebraMap R Ω y) ↔ y ∈ extPrime (Fin D) la)})
      (fun la _ => haveI := isDVR (Fin D) la; finite_places _)).subset ?_
  rintro v ⟨hv, hvg, la, hla⟩
  have hla' : ∀ y : R, 0 ≤ v (algebraMap R Ω y) ∧
      (0 < v (algebraMap R Ω y) ↔ y ∈ extPrime (Fin D) la) := fun y => by
    rw [mem_extPrime]; exact hla y
  refine Set.mem_biUnion (x := la) ?_ ⟨hv, hla'⟩
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine (mem_extPrime la _).1 ?_ m
  by_contra hrs
  have hz : ∀ y : R, y ∉ extPrime (Fin D) la → v (algebraMap R Ω y) = 0 := fun y hy =>
    le_antisymm (not_lt.1 fun h => hy ((hla' y).2.1 h)) (hla' y).1
  have h1 := nonneg_of_isIntegral v (fun y => (hla' y).1) hr
  have h2 := nonneg_of_isIntegral v (fun y => (hla' y).1) hs
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_right _ _ h)), zero_add] at h1
  rw [Algebra.smul_def, AddValuation.map_mul,
    hz _ (fun h => hrs (Ideal.mul_mem_left _ _ h)), zero_add] at h2
  refine hvg (ValPl.wt_add_eq_zero h1 h2 ?_)
  rw [← AddValuation.map_mul, mul_inv_cancel₀ hg, AddValuation.map_one]
end GlobalTheory
