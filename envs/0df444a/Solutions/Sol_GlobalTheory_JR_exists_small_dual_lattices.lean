-- Prove2me | solution 1 for GlobalTheory.JR.exists_small_dual_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:51:57.086798+00:00
-- url     : https://prove2.me/submissions/4f142061-283c-4f0f-9d64-2eb7c7fc3b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Theorems.Thm_GlobalTheory_JR_DualLattice_stdChar_continuous
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_eq
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_open_compact
import Theorems.Thm_GlobalTheory_JR_DualLattice_box_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory.JR.DualLattice
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → Continuous (fun p : V × V => ψ (β p.1 p.2)) ∧ (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, ψ (β x y) = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, ψ (β x y) = 1)) := by
  intro F _ _ _ ψ hψ V _ _ _ _ _ β hs hβ
  classical
  let e := Module.finBasis F V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  refine ⟨(stdChar_continuous hψ).comp ?_, fun U hU => ?_⟩
  · simp only [hB]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (((continuous_apply i).comp (coordHomeo e).continuous).comp continuous_fst).mul
      (((continuous_apply i).comp (coordHomeo e').continuous).comp continuous_snd)
  · have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt F hε
    have ht : t ≠ 0 := norm_pos_iff.1 ht0
    have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
    refine ⟨box e ‖t‖ (norm_nonneg _), box e' ‖t⁻¹‖ (norm_nonneg _), ?_,
      (box_open_compact e _ ht0).1, (box_open_compact e _ ht0).2,
      (box_open_compact e' _ hti).1, (box_open_compact e' _ hti).2,
      box_dual hψ e e' (fun x y => β x y) hB t ht, fun x => ?_⟩
    · rw [box_eq]
      intro x hx
      have := hsub (Metric.closedBall_subset_closedBall htε.le hx)
      simpa using this
    · have := box_dual hψ e' e (fun y x => β x y)
        (fun y x => by simp only [hB, mul_comm]) t⁻¹ (inv_ne_zero ht) x
      simpa only [inv_inv] using this
end GlobalTheory.JR
