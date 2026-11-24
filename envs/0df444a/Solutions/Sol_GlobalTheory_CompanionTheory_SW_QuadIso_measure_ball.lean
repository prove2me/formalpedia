-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.measure_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:11.760564+00:00
-- url     : https://prove2.me/submissions/c0347abb-414b-415d-8518-e2150f9a028a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_vball_eq_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_v_quad_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_v_quad_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_exists_near
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
variable [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution (lam : Measure K) [lam.IsAddLeftInvariant] {a c : K}
    (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1) (x : K) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    lam ((fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1}) =
      lam (vball x γ ∩ {s | Valued.v s < 1}) := by
  by_cases hne : (vball x γ ∩ {s : K | Valued.v s < 1}).Nonempty
  · obtain ⟨y, hyB, hyM⟩ := hne
    rw [← vball_eq_of_mem hyB]
    rcases le_or_gt 1 γ with h1 | h1
    · have hsub : ∀ s : K, Valued.v s < 1 → s ∈ vball y γ := fun s hs =>
        lt_of_lt_of_le (Valuation.map_sub_lt _ hs hyM) h1
      congr 1
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hsub _ h.2, h.2⟩, fun h => ⟨hsub _ (v_quad_lt ha hc h.2), h.2⟩⟩
    · obtain ⟨t₀, ht₀, hnear⟩ := exists_near ha hc hyM hγ
      have hB : vball y γ = vball (a * t₀ + c * t₀ ^ 2) γ := (vball_eq_of_mem hnear).symm
      have hsubM : ∀ (z : K), Valued.v z < 1 → vball z γ ⊆ {s : K | Valued.v s < 1} := by
        intro z hz s hs
        have : s = (s - z) + z := by ring
        rw [Set.mem_setOf_eq, this]
        exact Valuation.map_add_lt _ (lt_trans hs h1) hz
      have e1 : (fun t => a * t + c * t ^ 2) ⁻¹' vball y γ ∩ {s | Valued.v s < 1} = vball t₀ γ := by
        rw [hB]
        ext t
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
        · intro h
          have hM := hsubM t₀ ht₀ h
          refine ⟨?_, hM⟩
          simpa only [vball, Set.mem_setOf_eq, v_quad_sub ha hc hM ht₀] using h
      have e2 : vball y γ ∩ {s | Valued.v s < 1} = vball y γ :=
        Set.inter_eq_left.2 (hsubM y hyM)
      rw [e1, e2]
      have e3 : vball t₀ γ = (fun h => (y - t₀) + h) ⁻¹' vball y γ := by
        ext h
        simp only [vball, Set.mem_preimage, Set.mem_setOf_eq]
        have : y - t₀ + h - y = h - t₀ := by ring
        rw [this]
      rw [e3, measure_preimage_add]
  · have hem : (fun t => a * t + c * t ^ 2) ⁻¹' vball x γ ∩ {s | Valued.v s < 1} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨h, hM⟩
      exact hne ⟨_, h, v_quad_lt ha hc hM⟩
    rw [hem, Set.not_nonempty_iff_eq_empty.1 hne]
end GlobalTheory.CompanionTheory.SW.QuadIso
