-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:21.337497+00:00
-- url     : https://prove2.me/submissions/f4470491-c443-444e-9fc0-584a5f336690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_val_mul
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_val_inv
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_herm_eq_trace
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_herm_smul
import Theorems.Thm_GlobalTheory_T_exists_integral_trace_unramifiedQuadraticLocalExt
import Theorems.Thm_GlobalTheory_T_exists_unit_trace_unramifiedInvolutionFieldExt
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_val_unit
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_IsUnrExt_ne_zero
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_mem_range_of_val_nonneg
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_algebraMap_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  intro K K' d φ hU B ψ hψ hσ L x y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hT : ∀ z, B.herm x y z = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) :=
    fun z => herm_eq_trace hU B ψ hψ hσ x y z
  constructor
  · intro h z hz
    obtain ⟨b, hb⟩ := h z hz
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt K K' d φ hU b
    refine ⟨a, ?_⟩
    calc algebraMap K.O K.E a = Algebra.trace K.E K'.E (algebraMap K'.O K'.E b) := ha.symm
      _ = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) := by rw [hb]
      _ = B.herm x y z := (hT z).symm
  · intro h z₀ hz₀
    by_contra hw
    have hv : val K'.O ((overExt φ B ψ hψ hσ).herm x y z₀) < 0 := by
      by_contra hle
      push_neg at hle
      obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' _ hle
      exact hw ⟨b, hb⟩
    have hw0 : (overExt φ B ψ hψ hσ).herm x y z₀ ≠ 0 := by
      intro h0
      exact hw ⟨0, by rw [h0, map_zero]⟩
    obtain ⟨u, a, ha, hua⟩ := GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt K K' d φ hU
    obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
    have hπv : val K.O π = 1 := by
      unfold val
      rw [hπ, WithZero.log_exp]
      norm_num
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp [val] at hπv
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    set w := (overExt φ B ψ hψ hσ).herm x y z₀ with hwdef
    set m : K'.E := algebraMap K'.O K'.E u * w⁻¹ * (φ π)⁻¹ with hm
    have hm_int : 0 ≤ val K'.O m := by
      by_cases hu0 : algebraMap K'.O K'.E u = 0
      · rw [hm, hu0, zero_mul, zero_mul]
        simp [val]
      · rw [hm, val_mul K' (mul_ne_zero hu0 (inv_ne_zero hw0)) (inv_ne_zero hφπ),
          val_mul K' hu0 (inv_ne_zero hw0), val_inv, val_inv, hU.2.2.1, hπv]
        have := val_algebraMap_nonneg K' u
        omega
    obtain ⟨m₀, hm₀⟩ := mem_range_of_val_nonneg K' m hm_int
    obtain ⟨y₀, hy₀⟩ := K'.c_int m₀
    have hz₁ : y₀ • z₀ ∈ L := L.smul_mem y₀ hz₀
    have key : (overExt φ B ψ hψ hσ).herm x y (y₀ • z₀) = m * w :=
      herm_smul B ψ hψ hσ x y z₀ m y₀ (by rw [← hy₀, K'.c_c, hm₀])
    obtain ⟨b, hb⟩ := h _ hz₁
    have hb' := hb.trans (hT _)
    rw [key] at hb'
    have hmw : m * w = π⁻¹ • algebraMap K'.O K'.E u := by
      rw [Algebra.smul_def, hm]
      show _ = φ π⁻¹ * _
      rw [map_inv₀]
      field_simp
    rw [hmw, LinearMap.map_smul, hua, smul_eq_mul] at hb'
    have ha0 : algebraMap K.O K.E a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E), (IsFractionRing.injective K.O K.E).eq_iff]
      exact ha.ne_zero
    have h1 := val_algebraMap_nonneg K b
    rw [hb', val_mul K (inv_ne_zero hπ0) ha0, val_inv, hπv, GlobalTheory.UnitLemma.Orbit.val_unit a ha] at h1
    omega
end GlobalTheory.UnitLemma.Unr
