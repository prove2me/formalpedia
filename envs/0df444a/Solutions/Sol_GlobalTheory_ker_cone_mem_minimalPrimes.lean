-- Prove2me | solution 1 for GlobalTheory.ker_cone_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:41:44.7637+00:00
-- url     : https://prove2.me/submissions/8ccf7470-8008-47a9-8b5f-c5c30177e633

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KerConeMemMinimalPrimes
import Theorems.Thm_GlobalTheory_HomogMinPrime_eval_scale
import Theorems.Thm_GlobalTheory_HomogMinPrime_mem_ker_cone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open HomogMinPrime
namespace GlobalTheory
theorem _root_.solution : ∀ (o σ K : Type) [CommRing o] [Field K] (I : Ideal (MvPolynomial σ o)) (β : o →+* K) (u : σ → K) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → u i = 1 → RingHom.ker (MvPolynomial.eval₂Hom β u) ∈ (I ⊔ Ideal.span {MvPolynomial.X i - 1}).minimalPrimes → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) ∈ I.minimalPrimes := by
  intro o σ K _ _ I β u i hI hu hmin
  have hIφ : I ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := le_sup_left.trans hmin.1.2
  refine ⟨⟨RingHom.ker_isPrime _, fun F hF => (mem_ker_cone β u F).2 fun e => hIφ (hI F hF e)⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hQψ
  have hQφ : ∀ F ∈ Q, MvPolynomial.eval₂Hom β u F = 0 := by
    intro F hF
    have := (mem_ker_cone β u F).1 (hQψ hF)
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
    exact Finset.sum_eq_zero fun e _ => this e
  let L := FractionRing (MvPolynomial σ o ⧸ Q)
  let π : MvPolynomial σ o →+* L := (algebraMap (MvPolynomial σ o ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ F, π F = 0 ↔ F ∈ Q := by
    intro F
    simp only [π, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hx : π (MvPolynomial.X i) ≠ 0 := by
    intro h
    have := hQφ _ ((hπ _).1 h)
    rw [MvPolynomial.eval₂Hom_X', hu] at this
    exact one_ne_zero this
  let χ : MvPolynomial σ o →+* L := MvPolynomial.eval₂Hom (π.comp MvPolynomial.C)
    (fun a => π (MvPolynomial.X a) * (π (MvPolynomial.X i))⁻¹)
  have hπe : MvPolynomial.eval₂Hom (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) = π := by
    apply MvPolynomial.ringHom_ext <;> simp
  have hχ : ∀ (F : MvPolynomial σ o) e, χ (MvPolynomial.homogeneousComponent e F) =
      (π (MvPolynomial.X i))⁻¹ ^ e * π (MvPolynomial.homogeneousComponent e F) := by
    intro F e
    have := eval_scale (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a))
      (π (MvPolynomial.X i))⁻¹ (MvPolynomial.homogeneousComponent_isHomogeneous e F)
    rw [hπe] at this
    exact this
  have h1 : I ⊔ Ideal.span {MvPolynomial.X i - 1} ≤ RingHom.ker χ := by
    refine sup_le (fun F hF => ?_) ?_
    · rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hχ, (hπ _).2 (hIQ (hI F hF e)), mul_zero]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      simp only [χ, MvPolynomial.eval₂Hom_X']
      rw [mul_inv_cancel₀ hx, sub_self]
  have h2 : RingHom.ker χ ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    have hG : (∑ e ∈ Finset.range (F.totalDegree + 1),
        MvPolynomial.X i ^ (F.totalDegree - e) * MvPolynomial.homogeneousComponent e F) ∈ Q := by
      rw [← hπ, map_sum]
      rw [← MvPolynomial.sum_homogeneousComponent F, map_sum] at hF
      have := congrArg (fun y => π (MvPolynomial.X i) ^ F.totalDegree * y) hF
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun e he => ?_
      have he' : e ≤ F.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      rw [hχ, map_mul, map_pow, pow_sub₀ _ hx he', inv_pow, _root_.mul_assoc]
    have := hQφ _ hG
    rw [map_sum] at this
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, ← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_pow, MvPolynomial.eval₂Hom_X', hu, one_pow, _root_.one_mul]
  have h3 := hmin.2 ⟨RingHom.ker_isPrime χ, h1⟩ h2
  intro F hF
  rw [mem_ker_cone] at hF
  rw [← MvPolynomial.sum_homogeneousComponent F]
  refine Q.sum_mem fun e _ => ?_
  have h4 : χ (MvPolynomial.homogeneousComponent e F) = 0 := h3 (hF e)
  rw [hχ] at h4
  exact (hπ _).1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ (inv_ne_zero hx)))
end GlobalTheory
