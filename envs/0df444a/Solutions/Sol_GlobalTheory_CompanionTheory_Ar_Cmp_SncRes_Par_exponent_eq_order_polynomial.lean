-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:27.776024+00:00
-- url     : https://prove2.me/submissions/8c626639-515c-45c9-99b1-ca4b48e8cbd5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_le_of_mul_pow_mem_span_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_map_ptIdeal_eq_maximalIdeal_ordAff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_mul_mem_of_algebraMap_locRing_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isUnit_algebraMap_locRing_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_mk_locRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  intro m e I t r Jf g u mm hI hreg hdim hspan hg i hi n
  haveI := hreg
  haveI hdom : IsDomain (locRing I t) := isDomain_of_isRegularLocalRing
  have hu := IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff I t hI
  have hmax := map_ptIdeal_eq_maximalIdeal_ordAff I t hI
  have hspan' := hspan.trans hmax
  have hprime := prime_of_regular_params (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm
  have hnon := (regular_params_spec (fun l => algebraMap _ (locRing I t) (r l)) hspan' hdim.symm).2
  have hp : Prime (algebraMap _ (locRing I t) (r i)) := hprime i
  have hkill : ∀ h ∈ I, algebraMap _ (locRing I t) h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hh)
  constructor
  · rintro ⟨s, hs, hsg⟩
    have hs' : ¬ algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) s := fun h =>
      hs (Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr h))
    have hle : SncRes.Par.chPrime I t (r i) ^ n ⊔ I ≤
        (Ideal.span {algebraMap _ (locRing I t) (r i)} ^ n).comap (algebraMap _ (locRing I t)) := by
      refine sup_le ?_ ?_
      · rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono Ideal.map_comap_le n
      · intro h hh
        rw [Ideal.mem_comap, hkill h hh]
        exact zero_mem _
    have hmap := Ideal.mem_comap.mp (hle hsg)
    have hprod := Finset.mul_prod_erase Jf (fun j => algebraMap _ (locRing I t) (r j) ^ mm j) hi
    refine le_of_mul_pow_mem_span_pow hp (a := algebraMap _ (locRing I t) s *
      (u * ∏ j ∈ Jf.erase i, algebraMap _ (locRing I t) (r j) ^ mm j)) ?_ ?_
    · intro hd
      rcases hp.dvd_or_dvd hd with h | h
      · exact hs' h
      rcases hp.dvd_or_dvd h with h | h
      · exact hp.not_unit (isUnit_of_dvd_unit h u.isUnit)
      · obtain ⟨j, hj, hd'⟩ := (Prime.dvd_finset_prod_iff hp _).mp h
        have hd'' := hp.dvd_of_dvd_pow hd'
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        exact hnon i j hji.symm (hp.associated_of_dvd (hprime j) hd'')
    · rw [map_mul, hg, ← hprod] at hmap
      convert hmap using 1
      ring
  · intro hn
    obtain ⟨a, b, hb, hab⟩ := exists_mk_locRing I t (u : locRing I t)
    have hz : algebraMap _ (locRing I t) (b * g - a * ∏ j ∈ Jf, r j ^ mm j) = 0 := by
      simp only [map_sub, map_mul, map_prod, map_pow]
      rw [hg, ← hab]
      ring
    obtain ⟨c, hc, hcI⟩ := IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
    refine ⟨c * b, ?_, ?_⟩
    · intro hmem
      have h1 : algebraMap _ (locRing I t) (r i) ∣ algebraMap _ (locRing I t) (c * b) :=
        Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hmem)
      have h2 := (hu (c * b)).mpr (by rw [map_mul]; exact mul_ne_zero hc hb)
      exact hp.not_unit (isUnit_of_dvd_unit h1 h2)
    · have hri : r i ∈ SncRes.Par.chPrime I t (r i) :=
        Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
      have hpow : c * a * ∏ j ∈ Jf, r j ^ mm j ∈ SncRes.Par.chPrime I t (r i) ^ n := by
        apply Ideal.pow_le_pow_right hn
        obtain ⟨d, hd⟩ : r i ^ mm i ∣ ∏ j ∈ Jf, r j ^ mm j :=
          Finset.dvd_prod_of_mem (fun j => r j ^ mm j) hi
        rw [hd]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hri _))
      have hsplit : c * b * g = c * (b * g - a * ∏ j ∈ Jf, r j ^ mm j) +
          c * a * ∏ j ∈ Jf, r j ^ mm j := by ring
      rw [hsplit]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hcI) (Ideal.mem_sup_left hpow)
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
