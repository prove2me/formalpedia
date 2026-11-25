-- Prove2me | solution 1 for GlobalTheory.EpsIso.bijective_of_mod_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:17.281815+00:00
-- url     : https://prove2.me/submissions/77367930-6f49-461f-9380-0be52be0594b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
import Theorems.Thm_GlobalTheory_EpsIso_mem_span_of_flat
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.EpsIso
namespace GlobalTheory.EpsIso
theorem _root_.solution {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by
  have hee : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hk : jC (φ (a DualNumber.eps)) = 0 := by
    rw [← RingHom.mem_ker, hC]
    exact Ideal.mem_span_singleton_self _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : b ∈ RingHom.ker jB := by rw [RingHom.mem_ker, ← hφ, hb, map_zero]
    rw [hB, Ideal.mem_span_singleton] at h1
    obtain ⟨b1, rfl⟩ := h1
    have h2 : (φ.comp a) DualNumber.eps * φ b1 = 0 := by
      rw [RingHom.comp_apply, ← map_mul]
      exact hb
    have h3 := mem_span_of_flat (φ.comp a) hfl (φ b1) h2
    rw [Ideal.mem_span_singleton] at h3
    obtain ⟨c', hc'⟩ := h3
    have h4 : b1 ∈ RingHom.ker jB := by
      rw [RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]
    rw [hB, Ideal.mem_span_singleton] at h4
    obtain ⟨b2, rfl⟩ := h4
    rw [← _root_.mul_assoc, hee, zero_mul]
  · intro c
    obtain ⟨b, hb⟩ := hs (jC c)
    have h1 : c - φ b ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨b1, hb1⟩ := hs (jC c1)
    have h2 : c1 - φ b1 ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h2
    obtain ⟨c2, hc2⟩ := h2
    have hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0 := by
      rw [← map_mul, hee, map_zero]
    refine ⟨b + a DualNumber.eps * b1, ?_⟩
    rw [map_add, map_mul]
    linear_combination (-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe
end GlobalTheory.EpsIso
