-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.MaxLat.ball_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:08:26.889071+00:00
-- url     : https://prove2.me/submissions/4afa1abb-27cd-48d8-af05-1e5a7dd9df8c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement

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
theorem _root_.solution {m : ℕ} (b : Module.Basis (Fin m) L V) (x : V) :
    ∃ a : L, a ≠ 0 ∧ a • x ∈ ball b := by
  let K : ℝ := ∑ i, ‖b.repr x i‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  refine ⟨t, norm_pos_iff.1 ht0, fun i => ?_⟩
  have hi : ‖b.repr x i‖ ≤ K :=
    Finset.single_le_sum (f := fun i => ‖b.repr x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg t, norm_nonneg (b.repr x i)]
end GlobalTheory.CompanionTheory.RgFl.MaxLat
