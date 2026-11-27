-- Prove2me | solution 1 for GlobalTheory.gaussRing_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:39:05.665219+00:00
-- url     : https://prove2.me/submissions/a4fa753a-d0dd-4458-b568-0d1f35099878

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMvPolynomialSubMapMem
import Theorems.Thm_GlobalTheory_gaussRing_isDVR
import Theorems.Thm_GlobalTheory_exists_mvPolynomial_sub_map_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Op_isDVR


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
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (D N : ℕ) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (O₁ : Type) [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra (𝓞 K) O₁], Function.Injective (algebraMap (𝓞 K) O₁) → Ideal.map (algebraMap (𝓞 K) O₁) la.asIdeal = IsLocalRing.maximalIdeal O₁ → (∀ x : O₁, ∃ a : 𝓞 K, x - algebraMap (𝓞 K) O₁ a ∈ IsLocalRing.maximalIdeal O₁) → ∀ (P : Ideal (MvPolynomial (TVar D N) O₁)) [P.IsPrime], P = Ideal.map MvPolynomial.C (IsLocalRing.maximalIdeal O₁) → ∀ (O₂ : Type) [CommRing O₂] [IsLocalRing O₂] [Algebra (MvPolynomial (TVar D N) O₁) O₂] [IsLocalization.AtPrime O₂ P], (∃ _ : IsDomain O₂, IsDiscreteValuationRing O₂) ∧ ∃ f : Op D N la →+* O₂, (∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) = algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p)) ∧ f.Flat ∧ IsLocalHom f ∧ Ideal.map f (IsLocalRing.maximalIdeal (Op D N la)) = IsLocalRing.maximalIdeal O₂ ∧ ∀ x : O₂, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal O₂ := by
  intro K _ _ D N la O₁ _ _ _ _ hinj hmap hres P _ hP O₂ _ _ _ _
  obtain ⟨hd, hdvr⟩ := gaussRing_isDVR O₁ P hP O₂
  refine ⟨⟨hd, hdvr⟩, ?_⟩
  have hcomap : (maximalIdeal O₁).comap (algebraMap (𝓞 K) O₁) = la.asIdeal := by
    symm
    apply la.isMaximal.eq_of_le
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [← hmap]; exact Ideal.le_comap_map
  have hmem : ∀ p : OT K D N,
      MvPolynomial.map (algebraMap (𝓞 K) O₁) p ∈ P ↔ p ∈ laT D N la := by
    intro p
    rw [hP, MvPolynomial.mem_map_C_iff]
    refine Iff.trans ?_ (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := p)).symm
    refine forall_congr' fun m => ?_
    rw [MvPolynomial.coeff_map, ← hcomap, Ideal.mem_comap]
  let g : OT K D N →+* O₂ :=
    (algebraMap (MvPolynomial (TVar D N) O₁) O₂).comp (MvPolynomial.map (algebraMap (𝓞 K) O₁))
  have hu : ∀ y : (laT D N la).primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := P.primeCompl) O₂
      ⟨MvPolynomial.map (algebraMap (𝓞 K) O₁) (y : OT K D N), fun h => y.2 ((hmem _).1 h)⟩
  let f : Op D N la →+* O₂ := IsLocalization.lift (M := (laT D N la).primeCompl) hu
  have hf : f.comp (algebraMap (OT K D N) (Op D N la)) = g := IsLocalization.lift_comp hu
  have hf' : ∀ p : OT K D N, f (algebraMap (OT K D N) (Op D N la) p) =
      algebraMap (MvPolynomial (TVar D N) O₁) O₂ (MvPolynomial.map (algebraMap (𝓞 K) O₁) p) :=
    fun p => IsLocalization.lift_eq hu p
  have hinj₂ := IsLocalization.injective O₂ (M := P.primeCompl) P.primeCompl_le_nonZeroDivisors
  have hginj : Function.Injective g := hinj₂.comp (MvPolynomial.map_injective _ hinj)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj (laT D N la).primeCompl x
    have h1 := congrArg f h
    rw [map_mul, hx, zero_mul, hf'] at h1
    have h2 : p = 0 := hginj (h1.symm.trans (map_zero g).symm)
    simp only [h2, map_zero] at h
    exact (IsLocalization.map_units (Op D N la) s).mul_left_eq_zero.mp h
  have hmax : Ideal.map f (maximalIdeal (Op D N la)) = maximalIdeal O₂ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hf,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂, ← Ideal.map_map]
    congr 1
    rw [hP, ← hmap, Ideal.map_map]
    change Ideal.map _ (Ideal.map MvPolynomial.C la.asIdeal) = _
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  refine ⟨f, hf', ?_, ?_, hmax, ?_⟩
  · haveI := Op_isDVR D N la
    algebraize [f]
    have : Module.IsTorsionFree (Op D N la) O₂ := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      exact hfinj
    unfold RingHom.Flat
    infer_instance
  · refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : f a ∈ maximalIdeal O₂ := hmax ▸ Ideal.mem_map_of_mem f ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  · intro x
    obtain ⟨⟨p, s⟩, h⟩ := IsLocalization.surj P.primeCompl x
    obtain ⟨p₀, hp⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres p
    obtain ⟨s₀, hs⟩ := exists_mvPolynomial_sub_map_mem (algebraMap (𝓞 K) O₁) _ hres
      (s : MvPolynomial (TVar D N) O₁)
    rw [← hP] at hp hs
    have hs₀ : s₀ ∈ (laT D N la).primeCompl := by
      intro h0
      apply s.2
      have := P.add_mem hs ((hmem _).2 h0)
      simpa using this
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Op D N la) ⟨s₀, hs₀⟩
    refine ⟨algebraMap (OT K D N) (Op D N la) p₀ * ↑u⁻¹, ?_⟩
    have hm : ∀ q ∈ P, algebraMap (MvPolynomial (TVar D N) O₁) O₂ q ∈ maximalIdeal O₂ := by
      intro q hq
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O₂]
      exact Ideal.mem_map_of_mem _ hq
    have h1 := hm _ hp
    have h2 := hm _ hs
    rw [map_sub, ← hf'] at h1 h2
    simp only at h hu'
    rw [← hu'] at h2
    have h3 : f u * f ↑u⁻¹ = 1 := by rw [← map_mul]; simp
    have h4 := Ideal.mul_mem_right (f ↑u⁻¹) _
      (Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ x h2))
    convert h4 using 1
    rw [map_mul, ← h]
    linear_combination (-x) * h3
end GlobalTheory
