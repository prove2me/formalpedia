-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:12.620105+00:00
-- url     : https://prove2.me/submissions/89c233e9-efd4-4874-bbb5-ecfd8a2c058e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_herm_le_delta
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_exists_basis_herm_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_basis_mem_ball
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_IsLat_smul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_ball_absorbing
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_norm_herm_ball_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_exists_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.MaxLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgFl.MaxLat
theorem _root_.solution : StSandwich → StExists := by
  intro hSw
  unfold StExists ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh
  obtain ⟨m, b, hb⟩ := exists_basis_herm_le_one hs hh
  obtain ⟨c, hc0, hc⟩ := exists_scale hh ‖δ‖ (norm_nonneg _) b
  let S : Set (AddSubgroup V) :=
    {Λ | (∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ Λ, a • x ∈ Λ) ∧ ∀ x ∈ Λ, ‖h x x‖ ≤ 1}
  have hlat0 : IsLat L (ball b) := ⟨m, b, fun _ => Iff.rfl⟩
  have hS0 : ball b ∈ S :=
    ⟨fun a ha x hx => IsLat.smul_mem hlat0 ha hx, fun x hx => norm_herm_ball_le_one hs hh b hb hx⟩
  have hchain : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub := by
    intro C hCS hC y hy
    have hmem : ∀ x, x ∈ sSup C ↔ ∃ t ∈ C, x ∈ t := fun x =>
      AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hC.directedOn
    refine ⟨sSup C, ⟨fun a ha x hx => ?_, fun x hx => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨t, ht, (hCS ht).1 a ha x hxt⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hCS ht).2 x hxt
  obtain ⟨M, hM0, hMax⟩ := zorn_le_nonempty₀ S hchain (ball b) hS0
  have hMlat : IsLat L M := by
    refine hSw L V (ball b) M c hlat0 hc0 (fun x hx => hc x fun j => ?_) (fun x => ?_) hMax.prop.1
    · exact norm_herm_le_delta hδ hh hMax.prop.1 hMax.prop.2 (hM0 (basis_mem_ball b j)) hx
    · obtain ⟨a, ha, hax⟩ := ball_absorbing b x
      exact ⟨a, ha, hM0 hax⟩
  refine ⟨M, hMlat, hMax.prop.2, fun Λ' hL hI hle => ?_⟩
  exact le_antisymm (hMax.2 ⟨fun a ha x hx => IsLat.smul_mem hL ha hx, hI⟩ hle) hle
end GlobalTheory.CompanionTheory.RgFl.MaxLat
