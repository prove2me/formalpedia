-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:29.985907+00:00
-- url     : https://prove2.me/submissions/ec993532-0ec3-4d9b-a097-85b9e313b314

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_mem_intS
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_congS_le_intS
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_congS_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isOpen_near
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_exists_level
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isCompact_intS
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isCompact_congS
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isInt_conj_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isNear_conj_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isClosed_UG
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (s : L →+* L), (∀ x, ‖s x‖ = ‖x‖) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) L) (Λ : AddSubgroup (Fin n → L)), IsLat L Λ → (∀ π : L, π ≠ 0 → ‖π‖ < 1 → ∃ K K₀ : Subgroup (UG s J), (∀ g, g ∈ K ↔ ∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) ∧ (∀ g, g ∈ K₀ ↔ ∀ x, g.1.1.mulVec x ∈ Λ ↔ x ∈ Λ) ∧ IsOpen (K : Set (UG s J)) ∧ IsCompact (K : Set (UG s J)) ∧ IsCompact (K₀ : Set (UG s J)) ∧ K ≤ K₀ ∧ ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K) ∧ ∀ U : Subgroup (UG s J), IsOpen (U : Set (UG s J)) → ∃ π : L, π ≠ 0 ∧ ‖π‖ < 1 ∧ ∀ g : UG s J, (∀ x ∈ Λ, ∃ y ∈ Λ, g.1.1.mulVec x - x = π • y) → g ∈ U := by
  intro L _ _ _ s hs n J Λ hL
  obtain ⟨m, b, hΛ⟩ := hL
  let ψ : UG s J →* GL (Fin m) L := (phi b).toMonoidHom.comp (UG s J).subtype
  have hψ : IsClosedEmbedding ψ :=
    (phiHomeo b).isClosedEmbedding.comp (isClosed_UG s hs J).isClosedEmbedding_subtypeVal
  have hv : ∀ g : UG s J, (ψ g).1 = conj b g.1.1 := fun _ => rfl
  have hi : ∀ g : UG s J, ((ψ g)⁻¹).1 = conj b (g.1⁻¹).1 := fun g => by
    rw [← map_inv]; rfl
  refine ⟨fun π hπ0 hπ1 => ?_, fun U hU => ?_⟩
  · have hn : 0 ≤ ‖π‖ := norm_nonneg π
    refine ⟨(congS ‖π‖ hn hπ1).comap ψ, intS.comap ψ, fun g => ?_, fun g => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isNear_conj_iff hΛ hπ0 g.1.1
    · rw [Subgroup.mem_comap, mem_intS, hv, hi, isInt_conj_iff hΛ, isInt_conj_iff hΛ]
      have e1 : ∀ x, (g.1⁻¹).1 *ᵥ (g.1.1 *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      have e2 : ∀ x, g.1.1 *ᵥ ((g.1⁻¹).1 *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      constructor
      · rintro ⟨h1, h2⟩ x
        refine ⟨fun hx => ?_, h1 x⟩
        simpa only [e1] using h2 _ hx
      · intro h
        exact ⟨fun x hx => (h x).2 hx, fun x hx => (h _).1 (by simpa only [e2] using hx)⟩
    · exact (isOpen_near (norm_pos_iff.2 hπ0)).preimage hψ.continuous
    · exact hψ.isCompact_preimage (isCompact_congS hn hπ1)
    · exact hψ.isCompact_preimage isCompact_intS
    · exact Subgroup.comap_mono (congS_le_intS hn hπ1)
    · intro c hc k
      show ψ k ∈ congS ‖π‖ hn hπ1 ↔ ψ (c * k * c⁻¹) ∈ congS ‖π‖ hn hπ1
      rw [map_mul, map_mul, map_inv]
      exact congS_conj hn hπ1 hc _
  · have hU1 := hU.mem_nhds (one_mem U)
    rw [hψ.isInducing.nhds_eq_comap, Filter.mem_comap] at hU1
    obtain ⟨W, hW, hsub⟩ := hU1
    rw [map_one] at hW
    obtain ⟨π, h0, h1, h⟩ := exists_level hW
    exact ⟨π, h0, h1, fun g hg => hsub (h _ ((isNear_conj_iff hΛ h0 _).2 hg))⟩
end GlobalTheory.CompanionTheory.BLevel
