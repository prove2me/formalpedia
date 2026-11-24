-- Prove2me | solution 1 for GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:45.704875+00:00
-- url     : https://prove2.me/submissions/2a2fe811-544a-4e8d-806a-e9173d196c48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_PolModLattice_real_of_bar
import Theorems.Thm_GlobalTheory_PolModLattice_altForm_bar
import Theorems.Thm_GlobalTheory_PolModLattice_trace_eq
import Theorems.Thm_GlobalTheory_PolModLattice_isUnit_invDiff
import Theorems.Thm_GlobalTheory_PolModLattice_exists_inv
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PolarisationModuleIndex_polMod_mul_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory.PolModLattice
namespace GlobalTheory.PolModLattice
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  intro E _ _ _ L hL
  obtain ⟨J, hIJ, hJ⟩ := exists_inv L hL
  have hJI : J * formSpan L = 1 := by rw [mul_comm]; exact hIJ
  have hM : polMod L = J * invDiff E := by
    apply le_antisymm
    · intro ξ hξ
      have h1 : Submodule.span (OF E) {ξ} * formSpan L ≤ invDiff E := by
        rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
        rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        rw [Set.mem_singleton_iff.1 ha]
        have hr : bar (ξ * altForm x y) = ξ * altForm x y := by
          rw [bar, map_mul, ← bar, ← bar, altForm_bar, hξ.1]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hξ.2 (c • x) (L.smul_mem c hx) y hy
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF]
        have hb : IsCMField.complexConj E ξ = -ξ := hξ.1
        simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [hb, show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have h2 : Submodule.span (OF E) {ξ} ≤ J * invDiff E := calc
        Submodule.span (OF E) {ξ} = Submodule.span (OF E) {ξ} * (formSpan L * J) := by rw [hIJ, mul_one]
        _ = (Submodule.span (OF E) {ξ} * formSpan L) * J := (mul_assoc _ _ _).symm
        _ ≤ invDiff E * J := mul_le_mul_left h1 _
        _ = J * invDiff E := mul_comm _ _
      exact h2 (Submodule.mem_span_singleton_self ξ)
    · refine Submodule.mul_le.2 fun j hj v hv => ?_
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨by rw [bar, map_mul, ← bar, ← bar, hJ j hj, bar_real]; ring, fun x hx y hy => ?_⟩
      have hm : j * altForm x y ∈ (1 : Submodule (OF E) E) := hJI ▸ Submodule.mul_mem_mul hj (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hm
      obtain ⟨n, hn⟩ := hw a
      refine ⟨n, ?_⟩
      rw [← hn]
      apply trace_eq
      push_cast
      rw [coe_OF, ha]
      have hb : IsCMField.complexConj E j = -j := hJ j hj
      simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply]
      rw [hb, show IsCMField.complexConj E (w : E) = w from bar_real w]
      ring
  refine ⟨?_, le_antisymm (polMod_mul_le L) ?_⟩
  · rw [hM]
    exact (show IsUnit J from ⟨⟨J, formSpan L, hJI, hIJ⟩, rfl⟩).mul isUnit_invDiff
  · rw [hM]
    intro z hz
    have h1 : Submodule.span (OF E) {z} * formSpan L ≤ invDiff E * L := by
      rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff.1 ha]
      have key : ∀ t ∈ L, z * bar t + bar z * t ∈ invDiff E := by
        intro t ht
        have hr : bar (z * bar t + bar z * t) = z * bar t + bar z * t := by
          simp only [bar, map_add, map_mul, IsCMField.complexConj_apply_apply]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hz (c • t) (L.smul_mem c ht)
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF, bar_smul]
        simp only [bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have e : z * altForm x y = (z * bar y + bar z * y) * x - (z * bar x + bar z * x) * y := by
        simp only [altForm]; ring
      show z * altForm x y ∈ _
      rw [e]
      exact sub_mem (Submodule.mul_mem_mul (key y hy) hx) (Submodule.mul_mem_mul (key x hx) hy)
    have h2 : Submodule.span (OF E) {z} ≤ J * invDiff E * L := calc
      Submodule.span (OF E) {z} = Submodule.span (OF E) {z} * (formSpan L * J) := by rw [hIJ, mul_one]
      _ = (Submodule.span (OF E) {z} * formSpan L) * J := (mul_assoc _ _ _).symm
      _ ≤ invDiff E * L * J := mul_le_mul_left h1 _
      _ = J * invDiff E * L := by rw [mul_comm, mul_assoc]
    exact h2 (Submodule.mem_span_singleton_self z)
end GlobalTheory.PolModLattice
