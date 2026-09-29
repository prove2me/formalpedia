-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/53190445-ff9b-5414-8724-a504f6ff7461

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open "NumberField IsDedekindDomain P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia.IsDedekindDomain.HeightOneSpectrum"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.intValuation_eq_one_iff HeightOneSpectrum.valuation_of_algebraMap HeightOneSpectrum.valuation_lt_one_iff_mem HeightOneSpectrum.valuation_le_one HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring HeightOneSpectrum.ext HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "intValuation_eq_one_iff valuation_of_algebraMap valuation_lt_one_iff_mem asIdeal valuation_le_one valuation valuationSubringAtPrime_eq_valuationSubring prime"
namespace InertiaBridgeSol
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (w : HeightOneSpectrum (𝓞 F))

theorem mem_inertiaSubgroup_iff_forall (h : ↥(NumberField.PlaceDecomp.decomp E F w)) :
    h ∈ ((w.valuation F).valuationSubring).inertiaSubgroup E ↔
      ∀ x : (w.valuation F).valuationSubring, w.valuation F ((h : F ≃ₐ[E] F) x - x) < 1 := by
  have hint : (w.valuation F).Integers (w.valuation F).valuationSubring := Valuation.valuationSubring.integers _
  have hcoe : ∀ x : (w.valuation F).valuationSubring,
      (((h • x - x : (w.valuation F).valuationSubring)) : F) = (h : F ≃ₐ[E] F) x - x := fun x => rfl
  have hmax : ∀ x : (w.valuation F).valuationSubring,
      h • x - x ∈ IsLocalRing.maximalIdeal ((w.valuation F).valuationSubring) ↔ w.valuation F ((h : F ≃ₐ[E] F) x - x) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]
    have hle : w.valuation F ((h : F ≃ₐ[E] F) x - x) ≤ 1 := hint.map_le_one (h • x - x)
    change ¬ w.valuation F ((h : F ≃ₐ[E] F) x - x) = 1 ↔ _
    exact ⟨fun hne => lt_of_le_of_ne hle hne, fun hlt => ne_of_lt hlt⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro hker x
    rw [← hmax, ← Ideal.Quotient.eq]
    show IsLocalRing.residue _ (h • x) = IsLocalRing.residue _ x
    rw [IsLocalRing.ResidueField.residue_smul]
    exact RingEquiv.congr_fun hker (IsLocalRing.residue _ x)
  · intro hall
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    show h • IsLocalRing.residue _ x = IsLocalRing.residue _ x
    rw [← IsLocalRing.ResidueField.residue_smul]
    exact (Ideal.Quotient.eq).2 ((hmax x).2 (hall x))

theorem algebraMap_smul_sub (g : F ≃ₐ[E] F) (x : 𝓞 F) :
    (Algebra.cast (g • x - x) : F) = g (algebraMap (𝓞 F) F x) - algebraMap (𝓞 F) F x := by
  show algebraMap (𝓞 F) F (g • x - x) = _
  rw [map_sub]
  rfl

theorem forall_valuationSubring_iff_forall_ringOfIntegers (g : F ≃ₐ[E] F) (hg : g ∈ NumberField.PlaceDecomp.decomp E F w) :
    (∀ a : (w.valuation F).valuationSubring, w.valuation F (g a - a) < 1) ↔ ∀ x : 𝓞 F, g • x - x ∈ w.asIdeal := by
  constructor
  · intro hall x
    have hx : algebraMap (𝓞 F) F x ∈ (w.valuation F).valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 (HeightOneSpectrum.valuation_le_one (K := F) w x)
    have h1 := hall ⟨algebraMap (𝓞 F) F x, hx⟩
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), algebraMap_smul_sub]
    exact h1
  · intro hall a
    suffices H : ∀ k : F, k ∈ (w.valuation F).valuationSubring → w.valuation F (g k - k) < 1 from H a a.2
    intro k hkmem

    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hkmem
    obtain ⟨r, s, hs, rfl⟩ : ∃ (r s : 𝓞 F) (_ : s ∈ w.asIdeal.primeCompl),
        k = algebraMap (𝓞 F) F r * (algebraMap (𝓞 F) F s)⁻¹ := hkmem
    have hs' : s ∉ w.asIdeal := hs

    have hvr : w.valuation F (g (algebraMap (𝓞 F) F r) - algebraMap (𝓞 F) F r) < 1 := by
      have h := hall r
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), algebraMap_smul_sub] at h
      exact h
    have hvs1 : w.valuation F (g (algebraMap (𝓞 F) F s) - algebraMap (𝓞 F) F s) < 1 := by
      have h := hall s
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), algebraMap_smul_sub] at h
      exact h
    have hvs : w.valuation F (algebraMap (𝓞 F) F s) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hs'
    have hvgs : w.valuation F (g (algebraMap (𝓞 F) F s)) = 1 := by
      rw [NumberField.PlaceDecomp.valuation_apply_of_mem g hg]; exact hvs
    have hs0 : algebraMap (𝓞 F) F s ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvs; exact zero_ne_one hvs
    have hgs0 : g (algebraMap (𝓞 F) F s) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvgs; exact zero_ne_one hvgs

    have hga : g (algebraMap (𝓞 F) F r * (algebraMap (𝓞 F) F s)⁻¹) - algebraMap (𝓞 F) F r * (algebraMap (𝓞 F) F s)⁻¹ =
        ((g (algebraMap (𝓞 F) F r) - algebraMap (𝓞 F) F r) * algebraMap (𝓞 F) F s +
          algebraMap (𝓞 F) F r * (algebraMap (𝓞 F) F s - g (algebraMap (𝓞 F) F s))) *
        ((g (algebraMap (𝓞 F) F s))⁻¹ * (algebraMap (𝓞 F) F s)⁻¹) := by
      rw [map_mul, map_inv₀]
      field_simp
      ring
    rw [hga, Valuation.map_mul, Valuation.map_mul, Valuation.map_inv, Valuation.map_inv, hvgs, hvs, inv_one, mul_one, mul_one]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [Valuation.map_mul, hvs, mul_one]; exact hvr
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc w.valuation F (algebraMap (𝓞 F) F r) * w.valuation F (g (algebraMap (𝓞 F) F s) - algebraMap (𝓞 F) F s)
          ≤ 1 * w.valuation F (g (algebraMap (𝓞 F) F s) - algebraMap (𝓞 F) F s) := by
            gcongr
            exact HeightOneSpectrum.valuation_le_one (K := F) w r
        _ < 1 := by rw [one_mul]; exact hvs1

end IsDedekindDomain.HeightOneSpectrum.InertiaBridgeSol

open IsDedekindDomain.HeightOneSpectrum.InertiaBridgeSol in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) :
    (((w.valuation F).valuationSubring).inertiaSubgroup E).map
        (((w.valuation F).valuationSubring).decompositionSubgroup E).subtype =
      w.asIdeal.inertia (F ≃ₐ[E] F) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' := (mem_inertiaSubgroup_iff_forall E F w h).mp hh
    have key := (forall_valuationSubring_iff_forall_ringOfIntegers E F w (h : F ≃ₐ[E] F) h.2).mp hh'
    exact AddSubgroup.mem_inertia.mpr fun x => key x
  · intro hg
    have hg' : ∀ x : 𝓞 F, g • x - x ∈ w.asIdeal := fun x => AddSubgroup.mem_inertia.mp hg x
    have hginv : ∀ x : 𝓞 F, g⁻¹ • x - x ∈ w.asIdeal := fun x => AddSubgroup.mem_inertia.mp (inv_mem hg) x

    have hgw : g • w = w := HeightOneSpectrum.ext (Ideal.ext fun x => by
      rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff]
      constructor
      · intro h1
        have h2 := w.asIdeal.sub_mem h1 (hginv x)
        rwa [sub_sub_cancel] at h2
      · intro h1
        have h2 := w.asIdeal.add_mem (hginv x) h1
        rwa [sub_add_cancel] at h2)
    have hgD : g ∈ NumberField.PlaceDecomp.decomp E F w := by
      rw [← NumberField.PlaceTransport.stabilizer_eq_decomp E F w]
      exact hgw
    refine ⟨⟨g, hgD⟩, ?_, rfl⟩
    exact (mem_inertiaSubgroup_iff_forall E F w ⟨g, hgD⟩).mpr
      ((forall_valuationSubring_iff_forall_ringOfIntegers E F w g hgD).mpr hg')

end S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia (solution)
