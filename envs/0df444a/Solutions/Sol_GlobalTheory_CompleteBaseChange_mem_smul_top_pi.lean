-- Prove2me | solution 1 for GlobalTheory.CompleteBaseChange.mem_smul_top_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:56.976936+00:00
-- url     : https://prove2.me/submissions/b67678d5-6abd-46a1-8a9c-3aa5067332f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange
namespace GlobalTheory.CompleteBaseChange
theorem _root_.solution {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {J : Ideal R} (hJ : J.FG) (x : ι → M) :
    x ∈ (J • ⊤ : Submodule R (ι → M)) ↔ ∀ i, x i ∈ (J • ⊤ : Submodule R M) := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · have := Submodule.mem_map_of_mem (f := LinearMap.proj (R := R) (φ := fun _ : ι => M) i) h
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  · obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hJ
    have key : ∀ m ∈ (J • ⊤ : Submodule R M), ∃ y : Fin n → M, ∑ l, a l • y l = m := by
      intro m hm
      refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) ?_
      · rw [← ha] at hr
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hr
        exact ⟨fun l => c l • m, by simp [Finset.sum_smul, smul_smul, mul_comm]⟩
      · rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
        exact ⟨y + z, by simp [Finset.sum_add_distrib]⟩
    choose y hy using fun i => key _ (h i)
    have : x = ∑ l, a l • fun i => y i l := by
      funext i
      simp [hy]
    rw [this]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem_smul (ha ▸ Submodule.subset_span ⟨l, rfl⟩) trivial
end GlobalTheory.CompleteBaseChange
