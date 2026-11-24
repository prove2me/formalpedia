-- Prove2me | solution 1 for GlobalTheory.FinWeil.normOp_comp_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:24:43.360283+00:00
-- url     : https://prove2.me/submissions/221a68a6-68c4-49be-ac82-fec6d631c141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AdjacentSelfDualLatticesIndexSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergSumCompOfAdjacentOfInfEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedIntertwinerCompOfAdjacentLattices
import Theorems.Thm_GlobalTheory_FinWeil_idx_congr_of_inf_eq
import Theorems.Thm_GlobalTheory_T_adjacent_selfDual_lattices_index_simple
import Theorems.Thm_GlobalTheory_T_heisenbergIntertwiningSum_comp_of_intermediate_lattice
import Theorems.Thm_GlobalTheory_T_heisenbergSum_comp_of_adjacent_of_inf_eq
import Theorems.Thm_GlobalTheory_T_heisenberg_intertwining_sums_comp_eq_index
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
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp
end GlobalTheory.FinWeil
