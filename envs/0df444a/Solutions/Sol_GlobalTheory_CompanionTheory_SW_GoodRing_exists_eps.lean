-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodRing.exists_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:28:56.648682+00:00
-- url     : https://prove2.me/submissions/d8bda022-03b5-4e01-b2e0-8fd960f10c4b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_exists_good_nat
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_norm_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_fixed_unit
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing
variable {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) (τ : O →+* O) (δ : O) (D : R)
namespace GlobalTheory.CompanionTheory.SW.GoodRing
theorem _root_.solution [IsLocalRing R] (hδ : δ * δ = ι D) (hτι : ∀ r, τ (ι r) = ι r) (hτδ : τ δ = -δ)
    (hsp : ∀ y : O, ∃ p q : R, y = ι p + ι q * δ)
    (hinj : ∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0)
    (hD : IsUnit D) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (s β : O) (hβ : IsUnit β) (hτβ : τ β = β) :
    ∃ ε z : O, ε * τ ε = 1 ∧ (β - τ ε * s) * z = 1 := by
  obtain ⟨b, hb, rfl⟩ := fixed_unit ι τ δ hτι hτδ hsp hinj h2 β hβ hτβ
  obtain ⟨s0, s1, rfl⟩ := hsp s
  let φ := IsLocalRing.residue R
  have nz : ∀ {x : R}, IsUnit x → φ x ≠ 0 := fun hx => (hx.map φ).ne_zero
  have un : ∀ {x : R}, φ x ≠ 0 → IsUnit x := fun {x} hx => by
    by_contra h
    exact hx ((IsLocalRing.residue_eq_zero_iff x).2 h)
  have h2k : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := nz h2
    rwa [map_ofNat] at this
  have h3k : (3 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := nz h3
    rwa [map_ofNat] at this
  have hDk := nz hD
  have hbk := nz hb
  obtain ⟨a, ha1, ha2⟩ := exists_good_nat h2k h3k (φ D) ((φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2)
    (4 * φ D * φ b * φ s1) (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) (by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hA, hB, hC⟩ := hcon
      have h4 : (4 : IsLocalRing.ResidueField R) ≠ 0 := by
        have : (4 : IsLocalRing.ResidueField R) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2k h2k
      have hs1 : φ s1 = 0 := by
        have := mul_ne_zero (mul_ne_zero h4 hDk) hbk
        exact (mul_eq_zero.1 hB).resolve_left this
      rw [hs1] at hA hC
      have e1 : φ b - φ s0 = 0 := by
        have : (φ b - φ s0) ^ 2 = 0 := by simpa using hA
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      have e2 : φ b + φ s0 = 0 := by
        have : φ D * (φ b + φ s0) ^ 2 = 0 := by simpa using hC
        exact pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 this).resolve_left hDk)
      have : 2 * φ b = 0 := by linear_combination e1 + e2
      exact (mul_ne_zero h2k hbk) this)
  set c : R := (a : R) with hc
  have hφc : φ c = (a : IsLocalRing.ResidueField R) := by simp [hc]
  let P : R := b - s0 + c * s1 * D
  let Q : R := b * c - s1 + c * s0
  have hn1 : IsUnit (1 - D * c ^ 2) := un (by
    simp only [map_sub, map_one, map_mul, map_pow, hφc]; exact ha1)
  have hn2 : IsUnit (P ^ 2 - D * Q ^ 2) := un (by
    have : φ (P ^ 2 - D * Q ^ 2) = (φ b - φ s0) ^ 2 - φ D * φ s1 ^ 2 +
        4 * φ D * φ b * φ s1 * (a : IsLocalRing.ResidueField R) +
        (φ D ^ 2 * φ s1 ^ 2 - φ D * (φ b + φ s0) ^ 2) * (a : IsLocalRing.ResidueField R) ^ 2 := by
      simp only [P, Q, map_sub, map_add, map_mul, map_pow, hφc]
      ring
    rw [this]; exact ha2)
  obtain ⟨e1, he1⟩ := hn1.exists_right_inv
  obtain ⟨e2, he2⟩ := hn2.exists_right_inv
  have he1' : ι (1 - D * c ^ 2) * ι e1 = 1 := by rw [← map_mul, he1, map_one]
  have he2' : ι (P ^ 2 - D * Q ^ 2) * ι e2 = 1 := by rw [← map_mul, he2, map_one]
  let u : O := ι 1 + ι c * δ
  have hτu : τ u = 1 - ι c * δ := by
    simp only [u, map_add, map_mul, hτι, hτδ, map_one]; ring
  have huu : u * τ u = ι (1 - D * c ^ 2) := by
    have := norm_eq ι τ δ D hδ hτι hτδ 1 c
    simpa [u, one_pow] using this
  let t : O := ι P + ι Q * δ
  have htt : t * τ t = ι (P ^ 2 - D * Q ^ 2) := norm_eq ι τ δ D hδ hτι hτδ P Q
  have ht : ι b * u - τ u * (ι s0 + ι s1 * δ) = t := by
    rw [hτu]
    simp only [t, u, P, Q, map_add, map_sub, map_mul, map_one]
    linear_combination (ι c * ι s1) * hδ
  refine ⟨u * u * ι e1, u * τ t * ι e2, ?_, ?_⟩
  · simp only [map_mul, hτι]
    calc u * u * ι e1 * (τ u * τ u * ι e1) = (u * τ u * ι e1) ^ 2 := by ring
      _ = 1 := by rw [huu, he1', one_pow]
  · have hτε : τ (u * u * ι e1) * u = τ u := by
      simp only [map_mul, hτι]
      calc τ u * τ u * ι e1 * u = τ u * (u * τ u * ι e1) := by ring
        _ = τ u := by rw [huu, he1', mul_one]
    calc (ι b - τ (u * u * ι e1) * (ι s0 + ι s1 * δ)) * (u * τ t * ι e2)
        = (ι b * u - (τ (u * u * ι e1) * u) * (ι s0 + ι s1 * δ)) * τ t * ι e2 := by ring
      _ = t * τ t * ι e2 := by rw [hτε, ht]
      _ = 1 := by rw [htt, he2']
end GlobalTheory.CompanionTheory.SW.GoodRing
