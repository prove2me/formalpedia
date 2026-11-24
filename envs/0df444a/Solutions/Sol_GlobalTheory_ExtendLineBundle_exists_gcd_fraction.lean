-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_gcd_fraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:26.02521+00:00
-- url     : https://prove2.me/submissions/5081f6d2-1ed0-46b2-a1cb-5d043a535f43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution {R K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*} [Finite ι] (c : ι → K)
    (hc : ∀ k, c k ≠ 0) :
    ∃ h : K, h ≠ 0 ∧ (∀ k, c k / h ∈ (algebraMap R K).range) ∧
      ∀ t : K, Nonempty ι → (∀ k, c k * t ∈ (algebraMap R K).range) →
        h * t ∈ (algebraMap R K).range := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, one_ne_zero, fun k => h.elim k, fun _ ⟨k⟩ => h.elim k⟩
  | inr hι =>
  obtain ⟨k₀⟩ := hι
  have := Fintype.ofFinite ι
  letI : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid R := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose e he using hdc
  have hd0 : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero hd)
  have he' : ∀ k, algebraMap R K (e k) = algebraMap R K d * c k := fun k => by
    rw [he k, Algebra.smul_def]
  have hg : Finset.univ.gcd e ≠ 0 := fun h => by
    have := he' k₀
    rw [Finset.gcd_eq_zero_iff.1 h k₀ (Finset.mem_univ _), map_zero] at this
    exact mul_ne_zero hd0 (hc k₀) this.symm
  have hg0 : algebraMap R K (Finset.univ.gcd e) ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr hg
  refine ⟨algebraMap R K (Finset.univ.gcd e) / algebraMap R K d, div_ne_zero hg0 hd0,
    fun k => ?_, fun t _ ht => ?_⟩
  · obtain ⟨r, hr⟩ := Finset.gcd_dvd (f := e) (Finset.mem_univ k)
    refine ⟨r, ?_⟩
    have := he' k
    rw [hr, map_mul] at this
    field_simp
    linear_combination this
  · obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) t
    have hq0 : algebraMap R K q ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero hq)
    have h1 : d * q ∣ Finset.univ.gcd fun k => p * e k := Finset.dvd_gcd fun k _ => by
      obtain ⟨r, hr⟩ := ht k
      refine ⟨r, IsFractionRing.injective R K ?_⟩
      rw [map_mul, map_mul, map_mul, he', hr]
      field_simp
    obtain ⟨r, hr⟩ := h1.trans (Finset.gcd_mul_left' _ _ p).dvd
    refine ⟨r, ?_⟩
    have := congrArg (algebraMap R K) hr
    rw [map_mul, map_mul, map_mul] at this
    field_simp
    linear_combination -this
end GlobalTheory.ExtendLineBundle
