-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.specialFibrePackage_of_chartTable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/80e5e798-43f6-5c11-8ca8-a0b3141a7445

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_U_mem_and_V_mem_asIdeal_toCrossing_of_mem_support
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_ker_section_mul_prod_pow_min_eq_ofIdealTop
import Theorems.Thm_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_mem_support_and_mem_support_succ
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isInvertible_of_chartTable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

namespace HFCPKG

variable {O : Type u} [CommRing O] (ϖ : O) (e : ℕ)

def ChartTable (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData) : Prop :=
  ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤))

theorem mem_support_ofIdealTop_map_iff {R : Type u} [CommRing R] (J : Ideal R)
    (y : ↥(Spec (CommRingCat.of R))) :
    y ∈ (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom J)).support ↔ J ≤ y.asIdeal := by
  change y ∈ ((Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom J)).support : Set _) ↔ _
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Ideal.map, Scheme.zeroLocus_span,
    Spec_zeroLocus_eq_zeroLocus]
  exact PrimeSpectrum.mem_zeroLocus (x := (y : PrimeSpectrum R)) (s := (J : Set R))

theorem algebraMap_mem_of_mem_support {F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData}
    (hF : ChartTable ϖ e F) (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)) (hz : z ∈ (F k).support) :
    ϖ ∈ ((Resolution.toSpec ϖ e).base z).asIdeal := by
  obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq ϖ e z
  have hy : y ∈ ((F k).comap (Resolution.ι ϖ e i)).support := by
    rw [Scheme.IdealSheafData.support_comap]; exact hz
  rw [hF i k, mem_support_ofIdealTop_map_iff] at hy

  have hϖy : algebraMap O (CrossingQuotient O ϖ) ϖ ∈ y.asIdeal := by
    rw [← U_mul_V]
    split_ifs at hy with h1 h2
    · exact y.asIdeal.mul_mem_left _ (hy (Ideal.mem_span_singleton_self _))
    · exact y.asIdeal.mul_mem_right _ (hy (Ideal.mem_span_singleton_self _))
    · exact absurd (y.asIdeal.eq_top_iff_one.mpr (hy Submodule.mem_top)) y.isPrime.ne_top

  rw [← Scheme.Hom.comp_apply, Resolution.ι_toSpec]
  exact hϖy

theorem toSpec_eq_closedPoint_of_mem_support [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    {F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData} (hF : ChartTable ϖ e F)
    (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)) (hz : z ∈ (F k).support) :
    (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O := by
  have h := algebraMap_mem_of_mem_support ϖ e hF k z hz
  apply PrimeSpectrum.ext
  change ((Resolution.toSpec ϖ e).base z).asIdeal = IsLocalRing.maximalIdeal O
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le ((Resolution.toSpec ϖ e).base z).isPrime.ne_top
  rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]
  exact h

theorem main [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData) (hF : ChartTable ϖ e F) :
    (∀ k, (F k).IsInvertible) ∧
    (∏ k, F k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)})) ∧
    (∏ k, F k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))})) ∧
    (∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (F k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O) ∧
    (∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (F ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal) ∧
    (∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (F ⟨k, by omega⟩).support ∧ z ∈ (F ⟨k + 1, by omega⟩).support) ∧
    (∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (F ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (F k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, F k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)})) := by

  have hϖ0 : ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field O
    rw [hϖ, h, Ideal.span_singleton_eq_bot]
  have hϖnzd : ϖ ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero hϖ0
  have hϖnu : ¬ IsUnit ϖ := by
    have : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact (IsLocalRing.mem_maximalIdeal ϖ).mp this
  have hcd := MvPolynomial.CrossingQuotient.Resolution.prod_pow_eq_ofIdealTop_uSec_and_vSec_and_tSec ϖ e F hF
  refine ⟨fun k => MvPolynomial.CrossingQuotient.Resolution.isInvertible_of_chartTable ϖ e
      (MvPolynomial.CrossingQuotient.U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors ϖ hϖnzd).1
      (MvPolynomial.CrossingQuotient.U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors ϖ hϖnzd).2 F hF k, hcd.2.2, hcd.1,
    fun k z hz => toSpec_eq_closedPoint_of_mem_support ϖ e hϖ hF k z hz,
    fun k hk0 hke z hz => MvPolynomial.CrossingQuotient.Resolution.U_mem_and_V_mem_asIdeal_toCrossing_of_mem_support ϖ e F hF k hk0 hke z hz,
    fun k hke => MvPolynomial.CrossingQuotient.Resolution.exists_mem_support_and_mem_support_succ ϖ e hϖnu F hF k hke,
    fun t ht dd hd0 hde hmem hnot => ?_⟩
  obtain ⟨hci, α, htα⟩ := MvPolynomial.CrossingQuotient.Resolution.isClosedImmersion_and_exists_eq_specMap_lift_comp_iota_of_comp_toSpec_eq_id ϖ e F hF t ht dd hd0 hde hmem hnot
  refine ⟨hci, ?_, ⟨algebraMap O _ (ϖ ^ dd) - algebraMap O _ (α : O) * CrossingQuotient.U (ϖ ^ e), ?_⟩⟩
  · rw [htα]; exact MvPolynomial.CrossingQuotient.Resolution.isInvertible_ker_section ϖ e hϖnzd dd hd0 hde α
  · rw [htα]; exact MvPolynomial.CrossingQuotient.Resolution.ker_section_mul_prod_pow_min_eq_ofIdealTop ϖ e F hF dd hd0 hde α

end HFCPKG

theorem solution
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤))) :
    (∀ k, (F k).IsInvertible) ∧
    (∏ k, F k = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toSpec ϖ e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ)})) ∧
    (∏ k, F k ^ (k : ℕ) = Scheme.IdealSheafData.ofIdealTop (Ideal.span
      {(Resolution.toCrossing ϖ e).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom (CrossingQuotient.U (ϖ ^ e)))})) ∧
    (∀ (k : Fin (e + 1)) (z : ↥(Resolution ϖ e)), z ∈ (F k).support →
      (Resolution.toSpec ϖ e).base z = IsLocalRing.closedPoint O) ∧
    (∀ (k : ℕ) (hk0 : 0 < k) (hke : k < e) (z : ↥(Resolution ϖ e)), z ∈ (F ⟨k, by omega⟩).support →
      CrossingQuotient.U (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal ∧
        CrossingQuotient.V (ϖ ^ e) ∈ ((Resolution.toCrossing ϖ e).base z).asIdeal) ∧
    (∀ (k : ℕ) (hke : k < e), ∃ z : ↥(Resolution ϖ e),
      z ∈ (F ⟨k, by omega⟩).support ∧ z ∈ (F ⟨k + 1, by omega⟩).support) ∧
    (∀ (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e), t ≫ Resolution.toSpec ϖ e = 𝟙 _ →
      ∀ (dd : ℕ) (hd0 : 0 < dd) (hde : dd < e), t.base (IsLocalRing.closedPoint O) ∈ (F ⟨dd, by omega⟩).support →
      (∀ k : Fin (e + 1), (k : ℕ) ≠ dd → t.base (IsLocalRing.closedPoint O) ∉ (F k).support) →
      IsClosedImmersion t ∧ (t.ker).IsInvertible ∧
        ∃ rr : CrossingQuotient O (ϖ ^ e), t.ker * ∏ k, F k ^ (min (k : ℕ) dd) =
          Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Resolution.toCrossing ϖ e).appTop.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O (ϖ ^ e)))).inv.hom rr)})) :=
  HFCPKG.main ϖ e hϖ F hF

end S_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable (solution)
