-- Prove2me | solution 1 for GlobalTheory.FinWeil.normOp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:49:54.114821+00:00
-- url     : https://prove2.me/submissions/960863f9-06af-481a-b966-112eb4b171ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsAdjacentSelfDualLatticeTowardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_T_adjacent_selfDual_lattices_index_simple
import Theorems.Thm_GlobalTheory_T_exists_adjacent_selfDual_lattice_toward
import Theorems.Thm_GlobalTheory_T_heisenbergIntertwiningSum_comp_of_intermediate_lattice
import Theorems.Thm_GlobalTheory_T_normalizedIntertwiner_comp_of_adjacent_lattices
import Theorems.Thm_GlobalTheory_T_sumOp_transversal_fixes_linear_and_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A B C hA hB hC hAB hAC v hv
  induction hn : idx A B using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  by_cases hle : B ≤ A
  · have hAB' : A = B := by
      refine le_antisymm (fun x hx => (hB x).2 fun b hb => h.iso hA hx (hle hb)) hle
    subst hAB'
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A hA).2.2 le_rfl
    have : normOp lam W A A v = v := by
      rw [normOp, h1, map_one, inv_one, one_smul, h2 v hv]
    rw [this]
  · obtain ⟨A', hA', hadj, hbet⟩ := GlobalTheory.T.exists_adjacent_selfDual_lattice_toward h A B hA hB hAB hle
    obtain ⟨x, hx, P, hP, hfin, hann, hgen⟩ := id hadj
    obtain ⟨e1, e2, -⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A A' hA hA' x hx P hP hfin hann hgen
    have hcard : 1 < Nat.card (R ⧸ P) := by
      haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
      exact Finite.one_lt_card
    have hAA' : idx A A' ≠ 0 := by omega
    have hA'A : idx A' A ≠ 0 := by omega
    have hA'B : idx A' B ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAB
    have hA'C : idx A' C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAC
    have hmul := (GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A A' B hA hA' hB hAA' hA'B hbet).1
    have hlt : idx A' B < n := by
      rw [← hn, hmul, e1]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hA'B) hcard
    have hfix : Fixes W A' (normOp lam W A A' v) := by
      intro a ha
      rw [normOp, map_smul, ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A' hA').2.1 hAA').2.1 v hv a ha]
    rw [← GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' B hA hA' hB hadj hAB v hv,
      ih _ hlt A' hA' hA'B hA'C _ hfix rfl,
      GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' C hA hA' hC hadj hAC v hv]
end GlobalTheory.FinWeil
