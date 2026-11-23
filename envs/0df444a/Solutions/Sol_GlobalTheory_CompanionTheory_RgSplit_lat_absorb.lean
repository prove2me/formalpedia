-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.lat_absorb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:52.508828+00:00
-- url     : https://prove2.me/submissions/3d97df47-6fe9-4b27-ba0f-2c93bfefff53

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {ι : Type} [Fintype ι] (v : ι → V) :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ i, c • v i ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  set C : ℝ := 1 + ∑ i, ∑ j, ‖b.repr (v i) j‖ with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ ∑ i, ∑ j, ‖b.repr (v i) j‖ :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hC0 : 0 < C := by linarith
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt L (inv_pos.2 hC0)
  refine ⟨c, norm_pos_iff.1 hc0, hc.le.trans (inv_le_one_of_one_le₀ hC1), fun i => ?_⟩
  rw [hb]
  intro j
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  have h1 : ‖b.repr (v i) j‖ ≤ C := by
    have h2 : ‖b.repr (v i) j‖ ≤ ∑ j, ‖b.repr (v i) j‖ :=
      Finset.single_le_sum (f := fun j => ‖b.repr (v i) j‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)
    have h3 : ∑ j, ‖b.repr (v i) j‖ ≤ ∑ i, ∑ j, ‖b.repr (v i) j‖ :=
      Finset.single_le_sum (f := fun i => ∑ j, ‖b.repr (v i) j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    linarith
  calc ‖c‖ * ‖b.repr (v i) j‖ ≤ C⁻¹ * C :=
        mul_le_mul hc.le h1 (norm_nonneg _) (inv_pos.2 hC0).le
    _ = 1 := inv_mul_cancel₀ hC0.ne'
end GlobalTheory.CompanionTheory.RgSplit
