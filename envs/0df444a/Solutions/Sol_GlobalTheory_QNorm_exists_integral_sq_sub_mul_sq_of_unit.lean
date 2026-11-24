-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:58:56.457143+00:00
-- url     : https://prove2.me/submissions/1888cf19-07a4-47e9-8249-d18e4bda5ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Theorems.Thm_GlobalTheory_QNorm_exists_eq_sq_sub_mul_sq_finite
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_QNorm_isSquare_of_isSquare_residue_odd
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
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
open NumberField IsDedekindDomain IsLocalRing Polynomial
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ u : v.adicCompletion F), Valued.v (2 : v.adicCompletion F) = 1 → Valued.v δ = 1 → Valued.v u = 1 → ∃ x ∈ v.adicCompletionIntegers F, ∃ y ∈ v.adicCompletionIntegers F, u = x ^ 2 - δ * y ^ 2 := by
  intro F _ _ v δ u h2 hδ hu
  set O := v.adicCompletionIntegers F with hO
  have hmem : ∀ x : v.adicCompletion F, x ∈ O ↔ Valued.v x ≤ 1 := by
    intro x; rw [hO]; exact HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hval1 : ∀ z : O, IsUnit z → Valued.v (z : v.adicCompletion F) = 1 := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    have h1 : Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hw]
      simp
    have hz1 := (hmem _).1 z.2
    have hw1 := (hmem _).1 w.2
    refine le_antisymm hz1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) := h1.symm
      _ ≤ Valued.v (z : v.adicCompletion F) * 1 := mul_le_mul_right hw1 _
      _ = _ := mul_one _
  have : Finite (IsLocalRing.ResidueField O) := SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres_ne : ∀ z : O, Valued.v (z : v.adicCompletion F) = 1 → IsLocalRing.residue O z ≠ 0 := by
    intro z hz
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    have hz0 : (z : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    refine IsUnit.of_mul_eq_one (a := z) ⟨(z : v.adicCompletion F)⁻¹, (hmem _).2 (by rw [map_inv₀, hz, inv_one])⟩ ?_
    exact Subtype.ext (by simp [hz0])
  let uO : O := ⟨u, (hmem _).2 hu.le⟩
  let δO : O := ⟨δ, (hmem _).2 hδ.le⟩
  have hc2 : ((2 : O) : v.adicCompletion F) = 2 := map_ofNat O.subtype 2
  have h2O : IsLocalRing.residue O (2 : O) ≠ 0 := hres_ne 2 (by rw [hc2]; exact h2)
  have hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by rwa [map_ofNat] at h2O
  obtain ⟨a, b, hab⟩ := exists_eq_sq_sub_mul_sq_finite hk2 (hres_ne δO hδ) (IsLocalRing.residue O uO)
  obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective b
  let N : O := a' ^ 2 - δO * b' ^ 2
  have hresN : IsLocalRing.residue O N = IsLocalRing.residue O uO := by
    simp only [N, map_sub, map_mul, map_pow]; exact hab.symm
  have hvN : Valued.v (N : v.adicCompletion F) = 1 :=
    hval1 N ((IsLocalRing.residue_ne_zero_iff_isUnit N).1 (hresN ▸ hres_ne uO hu))
  have hN0 : (N : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hvN; exact zero_ne_one hvN
  have hz1 : Valued.v (u / (N : v.adicCompletion F)) = 1 := by rw [map_div₀, hu, hvN, div_one]
  let z : O := ⟨u / (N : v.adicCompletion F), (hmem _).2 hz1.le⟩
  have hzN : z * N = uO := Subtype.ext (by
    change u / (N : v.adicCompletion F) * (N : v.adicCompletion F) = u
    field_simp)
  have hresz : IsLocalRing.residue O z = 1 := by
    have h := congrArg (IsLocalRing.residue O) hzN
    rw [map_mul, hresN] at h
    have hne : IsLocalRing.residue O uO ≠ 0 := hres_ne uO hu
    calc IsLocalRing.residue O z = IsLocalRing.residue O z * IsLocalRing.residue O uO / IsLocalRing.residue O uO := by
          field_simp
      _ = 1 := by rw [h, div_self hne]
  obtain ⟨s, hs⟩ := isSquare_of_isSquare_residue_odd F v h2 z hz1 ⟨1, by rw [hresz, mul_one]⟩
  have hvs : Valued.v s ≤ 1 := by
    by_contra hc
    push Not at hc
    have : Valued.v s ≤ Valued.v s * Valued.v s := by
      calc Valued.v s = Valued.v s * 1 := (mul_one _).symm
        _ ≤ Valued.v s * Valued.v s := mul_le_mul_right hc.le _
    rw [← map_mul, ← hs, hz1] at this
    exact absurd (hc.trans_le this) (lt_irrefl _)
  have ha' := (hmem _).1 a'.2
  have hb' := (hmem _).1 b'.2
  refine ⟨s * a', (hmem _).2 ?_, s * b', (hmem _).2 ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' hvs ha'
  · rw [map_mul]; exact mul_le_one' hvs hb'
  · have hNK : (N : v.adicCompletion F) = (a' : v.adicCompletion F) ^ 2 - δ * (b' : v.adicCompletion F) ^ 2 := by
      simp [N, δO]
    have hzK : (z : v.adicCompletion F) = u / (N : v.adicCompletion F) := rfl
    calc u = (z : v.adicCompletion F) * (N : v.adicCompletion F) := by rw [hzK]; field_simp
      _ = _ := by rw [hs, hNK]; ring
end GlobalTheory.QNorm
