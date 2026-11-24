-- Prove2me | solution 1 for GlobalTheory.BadShare.mem_sqSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:51.790677+00:00
-- url     : https://prove2.me/submissions/a5fe6bf0-4512-402e-8680-9668751cee3d

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
namespace _root_.GlobalTheory.BadShare
theorem _root_.solution {N : ℕ} {f : (ZMod g)[X]} :
    f ∈ _root_.GlobalTheory.BadShare.sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold _root_.GlobalTheory.BadShare.sqSet
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨c, rfl⟩, hs, h0⟩
    have hlt := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hlt, ?_, hs, h0⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, hd, hs, h0⟩
    refine ⟨⟨fun i => f.coeff i, ?_⟩, hs, h0⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) N, ← hd]
    exact hm.as_sum.symm
end _root_.GlobalTheory.BadShare
end GlobalTheory.BadShare
