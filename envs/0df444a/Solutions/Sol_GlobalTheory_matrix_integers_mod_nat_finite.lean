-- Prove2me | solution 1 for GlobalTheory.matrix_integers_mod_nat_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:05.273475+00:00
-- url     : https://prove2.me/submissions/44c17c6e-8008-41ec-b04b-15b8ac6aee19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Theorems.Thm_GlobalTheory_exists_finite_integer_residues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (n : ℕ), 0 < n →
    ∃ R : Set (Matrix Y Y' k), R.Finite ∧ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) →
      ∃ s ∈ R, ∃ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) ∧ t = s + n • u := by
  intro k _ _ _ _ _ Y Y' _ _ n hn
  obtain ⟨ι, hι, x, -, hx⟩ := exists_finite_integer_residues k n hn
  refine ⟨Set.range (fun f : Y → Y' → ι => Matrix.of fun r q => x (f r q)), Set.finite_range _, ?_⟩
  intro t ht
  have key := fun r q => hx (t r q) (ht r q)
  choose f u hu hf using key
  refine ⟨Matrix.of fun r q => x (f r q), ⟨f, rfl⟩, Matrix.of fun r q => u r q, hu, ?_⟩
  ext r q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  exact hf r q
end GlobalTheory
