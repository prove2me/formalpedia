-- Prove2me | solution 1 for GlobalTheory.exists_mem_valuation_le_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:48.724533+00:00
-- url     : https://prove2.me/submissions/c5c7e459-da3d-47bb-a0ab-7bba54917ae4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by
  by_contra hne
  push Not at hne
  have key : ∀ y ∈ Submodule.span O A,
      v (algebraMap O C (φ y)) < v (algebraMap O C (φ x)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem a ha => exact hne a ha
    | zero => simpa using pos_iff_ne_zero.mpr h0
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      exact v.map_add_lt ha hb
    | smul o a _ ha =>
      rw [map_smul, smul_eq_mul, map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one o)) ha
  exact lt_irrefl _ (key x hx)
end GlobalTheory
