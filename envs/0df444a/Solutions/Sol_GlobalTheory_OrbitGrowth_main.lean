-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:41:38.676446+00:00
-- url     : https://prove2.me/submissions/cb9375de-ee6e-485f-8e4f-84f67fbbd511

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Theorems.Thm_GlobalTheory_OrbitGrowth_mem_good
import Theorems.Thm_GlobalTheory_OrbitGrowth_le_grow
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_inv
import Theorems.Thm_P2M_GlobalTheory_OrbitGrowth_grow_inv__bac8081d7f9f
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_fd
import Theorems.Thm_GlobalTheory_OrbitGrowth_grow_good

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.OrbitGrowth
theorem _root_.solution : ∀ (M : Type) [inst : AddCommGroup M] [inst_1 : Module ℂ M] (ι : Type) [Finite ι]
    (A : ι → Subalgebra ℂ (Module.End ℂ M)),
    (∀ (i j : ι), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ (m : M),
    (∀ (i : ι), FiniteDimensional ℂ ↥(Submodule.span ℂ {x : M | ∃ a ∈ A i, x = (a : M → M) m})) →
    ∃ (W : Submodule ℂ M), FiniteDimensional ℂ ↥W ∧ m ∈ W ∧
      ∀ (i : ι), ∀ a ∈ A i, ∀ x ∈ W, (a : M → M) x ∈ W := by
  intro M _ _ ι _ A hcomm m hfin
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ S : Finset ι, ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧
      (∀ i ∈ S, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) ∧ (∀ j, j ∉ S → W ≤ good (A j)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine ⟨Submodule.span ℂ {m}, inferInstance, Submodule.mem_span_singleton_self m,
        by simp, ?_⟩
      intro j _
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_good.mpr (hfin j)
    · intro j S hj ih
      obtain ⟨W, hWfd, hmW, hinv, hgood⟩ := ih
      refine ⟨grow (A j) W, grow_fd (hgood j hj), le_grow _ _ hmW, ?_, ?_⟩
      · intro i hi a ha x hx
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact grow_inv ha hx
        · have hij : i ≠ j := fun h => hj (h ▸ hiS)
          exact grow_inv' (hinv i hiS a ha) (fun b hb => hcomm i j hij a ha b hb) hx
      · intro k hk
        have hkj : k ≠ j := fun h => hk (h ▸ Finset.mem_insert_self j S)
        have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
        exact grow_good (hgood k hkS) (fun a ha b hb => (hcomm k j hkj b hb a ha).symm)
  obtain ⟨W, h1, h2, h3, -⟩ := key Finset.univ
  exact ⟨W, h1, h2, fun i a ha x hx => h3 i (Finset.mem_univ i) a ha x hx⟩
end GlobalTheory.OrbitGrowth
