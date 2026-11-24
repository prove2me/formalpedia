-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.exists_smul_mem_of_isLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:16.174997+00:00
-- url     : https://prove2.me/submissions/621c6064-771c-4130-9e29-8f6b1a5c8af2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (v : V) :
    ∃ a : L, a ≠ 0 ∧ a • v ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  have hS0 : 0 ≤ ∑ i, ‖b.repr v i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨a, ha0, ha⟩ := NormedField.exists_norm_lt L
    (show (0 : ℝ) < 1 / (1 + ∑ i, ‖b.repr v i‖) by positivity)
  refine ⟨a, norm_pos_iff.mp ha0, (hb _).2 fun i => ?_⟩
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr v i‖ ≤ 1 + ∑ i, ‖b.repr v i‖ := by
    have := Finset.single_le_sum (f := fun i => ‖b.repr v i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  calc ‖a‖ * ‖b.repr v i‖ ≤ (1 / (1 + ∑ i, ‖b.repr v i‖)) * (1 + ∑ i, ‖b.repr v i‖) := by
        gcongr
    _ = 1 := by field_simp
end GlobalTheory.CompanionTheory.HermLat
