-- Prove2me | solution 1 for GlobalTheory.transference_discrete_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:58:49.315479+00:00
-- url     : https://prove2.me/submissions/5f20485b-d156-4f45-9e39-48566201fe79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete
import Theorems.Thm_GlobalTheory_exists_basis_span_eq_of_discrete
import Theorems.Thm_GlobalTheory_exists_inner_dual_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_transference_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))), DiscreteTopology M →
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ → ∀ lam : ℝ, 0 < lam →
      (∀ z : EuclideanSpace ℝ (Fin N), (∀ y ∈ M, ∃ k : ℤ, inner ℝ z y = (k : ℝ)) → z ≠ 0 →
        lam ≤ ‖z‖) →
      ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧
        ∀ j, ‖v j‖ ≤ (N : ℝ) ^ 2 / lam := by
  intro N M _ hM lam hlam hmin
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_discrete M hM
  obtain ⟨d, hd⟩ := exists_inner_dual_basis b
  obtain ⟨y, hli, hint, hy⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual d lam hlam (by
    intro x hx hx0
    refine hmin x (fun y hy => ?_) hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    obtain ⟨e, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hy
    refine ⟨∑ j, c j * e j, ?_⟩
    simp [sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd,
      Finsupp.single_apply])
  refine ⟨y, fun i => ?_, hli, hy⟩
  rw [b.mem_span_iff_repr_mem ℤ]
  intro j
  obtain ⟨m, hm⟩ := hint i j
  exact ⟨m, by rw [← hd, real_inner_comm, hm]; simp⟩
end GlobalTheory
