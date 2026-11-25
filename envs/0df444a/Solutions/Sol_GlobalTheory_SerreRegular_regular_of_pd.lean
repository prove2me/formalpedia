-- Prove2me | solution 1 for GlobalTheory.SerreRegular.regular_of_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:35:03.70633+00:00
-- url     : https://prove2.me/submissions/585b5c24-345e-4e14-9bc4-8dab4241bbd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Theorems.Thm_GlobalTheory_SerreRegular_pd_quot
import Theorems.Thm_GlobalTheory_SerreRegular_projective_of_socle
import Theorems.Thm_GlobalTheory_SerreRegular_regular_of_quotient
import Theorems.Thm_GlobalTheory_SerreRegular_pd_residue_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory
open GlobalTheory.SerreRegular
namespace GlobalTheory.SerreRegular
theorem _root_.solution (d : ℕ) : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
    (maximalIdeal A).spanFinrank = d →
    (∃ n, HasProjectiveDimensionLE (ModuleCat.of A (A ⧸ maximalIdeal A)) n) →
    IsRegularLocalRing A := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro A _ _ _ hd ⟨n, hn⟩
  have hfield : maximalIdeal A = ⊥ → IsRegularLocalRing A := fun h => by
    let _ := (isField_iff_maximalIdeal_eq.mpr h).toField
    infer_instance
  have hS : (maximalIdeal A).mkQ.shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective _)
  have hP : Projective (maximalIdeal A).mkQ.shortComplexKer.X₂ :=
    (IsProjective.iff_projective A).mp inferInstance
  have hK : HasProjectiveDimensionLE (ModuleCat.of A (LinearMap.ker (maximalIdeal A).mkQ)) n :=
    (hS.hasProjectiveDimensionLT_X₃_iff n hP).1
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of A (A ⧸ maximalIdeal A)) (n + 1) _ (by omega))
  rw [Submodule.ker_mkQ] at hK
  by_cases hsq : maximalIdeal A ≤ maximalIdeal A ^ 2
  · exact hfield (ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq A hsq)
  by_cases hass : ∃ p ∈ associatedPrimes A A, maximalIdeal A ≤ p
  · obtain ⟨p, hp, hle⟩ := hass
    obtain ⟨hpp, a, ha⟩ := isAssociatedPrime_iff.mp hp
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hpp.ne_top
      rw [ha, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton]
      simp
    have hkill : ∀ y ∈ maximalIdeal A, a * y = 0 := by
      intro y hy
      have := hle hy
      rw [ha, Submodule.mem_colon_singleton] at this
      simpa [mul_comm] using this
    have hpr : Module.Projective A (maximalIdeal A) := projective_of_socle ha0 hkill n _ hK
    have hfree : Module.Free A (maximalIdeal A) := Module.free_of_flat_of_isLocalRing
    apply hfield
    rw [← Submodule.subsingleton_iff_eq_bot]
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    have : a ∈ Module.annihilator A (maximalIdeal A) :=
      Module.mem_annihilator.mpr fun y => Subtype.ext (hkill _ y.2)
    rw [Module.annihilator_eq_bot.mpr inferInstance] at this
    exact ha0 this
  obtain ⟨x, hx, hx2, hreg⟩ : ∃ x ∈ maximalIdeal A, x ∉ maximalIdeal A ^ 2 ∧ IsSMulRegular A x := by
    classical
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht⟩ := (associatedPrimes.finite A A).exists_finset_coe
    have hsub : (maximalIdeal A : Set A) ⊆
        ⋃ i ∈ ((insert (maximalIdeal A ^ 2) t : Finset (Ideal A)) : Set (Ideal A)), (i : Set A) := by
      rw [Finset.coe_insert, Set.biUnion_insert, ht, biUnion_associatedPrimes_eq_compl_regular]
      intro y hy
      by_cases h2 : y ∈ maximalIdeal A ^ 2
      · exact Or.inl h2
      · exact Or.inr (hcon y hy h2)
    obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (maximalIdeal A ^ 2) (maximalIdeal A ^ 2)
      (fun i hi h1 _ => by
        have : i ∈ associatedPrimes A A := ht ▸ (Finset.mem_insert.mp hi).resolve_left h1
        exact this.isPrime)).mp hsub
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hsq hle
    · exact hass ⟨i, ht ▸ hi, hle⟩
  have := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  have hlt := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le A hx hx2
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hd] at hlt
  have hregm : IsSMulRegular (maximalIdeal A) x := fun a b hab =>
    Subtype.ext (hreg (congrArg Subtype.val hab))
  have := ih _ hlt (A ⧸ Ideal.span {x}) rfl
    ⟨n, pd_residue_quot hx hx2 n (pd_quot hreg n (ModuleCat.of A (maximalIdeal A)) hregm hK)⟩
  exact regular_of_quotient hreg hx
end GlobalTheory.SerreRegular
