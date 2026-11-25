-- Prove2me | solution 1 for GlobalTheory.DifferentElement.diff_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:45.546405+00:00
-- url     : https://prove2.me/submissions/ecd9c4d3-e67a-4452-86de-6eab8b868bd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Theorems.Thm_GlobalTheory_DifferentElement_exists_intLift
import Theorems.Thm_GlobalTheory_DifferentElement_ord_vw_pow_mul_unit
import Theorems.Thm_GlobalTheory_DifferentElement_exists_pow_mul_unit
import Theorems.Thm_GlobalTheory_DifferentElement_mult_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_mem_differentIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_traceDual_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid
open GlobalTheory GlobalTheory.DifferentElement
open Classical
namespace GlobalTheory.DifferentElement
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧
      ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) →
        ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by
  intro E _ _ _ _ l hl O _ _ _ _ K _ _ _ hlm hcard
  have hne : Nonempty (E →+* K) := by
    have : 0 < Nat.card (E →+* K) := hcard ▸ Module.finrank_pos
    exact (Nat.card_pos_iff.1 this).1
  obtain ⟨σ0⟩ := hne
  obtain ⟨ι, hι⟩ := exists_intLift E O K σ0
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hlQ : (l : 𝓞 E) ∈ Q := by rw [Ideal.mem_comap, map_natCast]; exact hlm
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hlO : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h] at hlQ
    exact hl0 ((Submodule.mem_bot _).1 hlQ)
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmap0 : Ideal.map ι Q ≠ ⊥ := by
    intro h
    have := Ideal.mem_map_of_mem ι hlQ
    rw [h, map_natCast] at this
    exact hlO ((Submodule.mem_bot _).1 this)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hϖ
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.span_singleton_one] at he
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 (he ▸ Ideal.map_comap_le))

  set 𝔇 := differentIdeal ℤ (𝓞 E) with h𝔇def
  have h𝔇 : 𝔇 ≠ ⊥ := differentIdeal_ne_bot
  have hfin𝔇 : FiniteMultiplicity Q 𝔇 := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) h𝔇
  set k := multiplicity Q 𝔇 with hkdef
  have hnle : ¬ 𝔇 ≤ Q ^ (k + 1) := fun h =>
    (hfin𝔇.pow_dvd_iff_le_multiplicity.1 (Ideal.dvd_iff_le.2 h)).not_gt (Nat.lt_succ_self k)
  obtain ⟨x, hx𝔇, hxQ⟩ := SetLike.not_le_iff_exists.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxQ (zero_mem _)
  have hxk : multiplicity Q (Ideal.span {x}) = k := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · exact Ideal.dvd_iff_le.2 (((Ideal.span_singleton_le_iff_mem _).2 hx𝔇).trans
        (Ideal.le_of_dvd (pow_multiplicity_dvd Q 𝔇)))
    · intro h
      exact hxQ ((Ideal.span_singleton_le_iff_mem _).1 (Ideal.le_of_dvd h))
  refine ⟨ι x, ?_, ?_⟩
  · intro P hP
    obtain ⟨u, hu⟩ := exists_pow_mul_unit ι hQ0 e he x hx0
    obtain ⟨u', hu'⟩ := exists_pow_mul_unit ι hQ0 e he (l : 𝓞 E) hl0
    have hxK : algebraMap O K (ι x) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective O K), hu]
      exact mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero
    have hlK : (l : K) = algebraMap O K (ι (l : 𝓞 E)) := by rw [map_natCast, map_natCast]
    rw [val_vp, if_neg hxK, hlK, hu, hu', ord_vw_pow_mul_unit O K hϖ, ord_vw_pow_mul_unit O K hϖ, hxk]
    congr 1
    have hr1 := mult_ratio E l hl P.asIdeal P.isPrime hP
    have hr2 := mult_ratio E l hl Q hQp hlQ
    rw [diffExp_vp, hr1, ← hr2]
    have hkl : multiplicity Q (Ideal.span {(l : 𝓞 E)}) ≠ 0 := by
      have hfl : FiniteMultiplicity Q (Ideal.span {(l : 𝓞 E)}) := FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime hQ0 hQp) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hl0)
      have := hfl.le_multiplicity_of_pow_dvd (k := 1) (by
        rw [pow_one]; exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hlQ))
      omega
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast he0)]
  · intro σ y hy
    haveI : CharZero K := charZero_of_injective_ringHom σ0.injective
    letI : Algebra E K := σ0.toAlgebra
    haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun q => by
      show algebraMap ℚ K q = σ0 (algebraMap ℚ E q)
      rw [eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
    let τ : E ≃ₐ[ℚ] E := (σ.toRatAlgHom).restrictNormal' E
    have hτ : ∀ w, σ0 (τ w) = σ w := fun w => (σ.toRatAlgHom).restrictNormal_commutes E w
    have hyd : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := hy b
      exact ⟨n, by rw [Algebra.traceForm_apply, eq_intCast]; exact hn.symm⟩
    have hτy := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.traceDual_smul τ hyd
    have hx' := (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.mem_differentIdeal_iff x).1 hx𝔇
    rw [Submodule.mem_div_iff_forall_mul_mem] at hx'
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx' _ hτy)
    refine ⟨ι b, ?_⟩
    rw [hι, hι, ← hτ, ← map_mul]
    exact congrArg σ0 hb
end GlobalTheory.DifferentElement
