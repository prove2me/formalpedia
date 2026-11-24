-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:47:00.323801+00:00
-- url     : https://prove2.me/submissions/f22b52d8-dd67-4352-8131-dbb8c7d79552

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumn
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_add
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_inv
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_zero
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_conj_mem
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_exists_of_mem_N
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_conj_mem_R
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Model_colE_mem
import Theorems.Thm_GlobalTheory_RootEx_Radical_colE_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobiGroup
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.FourierJacobiGroup
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧ ∀ β : n → k, ∀ u ∈ N k n c (ρ + 1), colE c (ρ + 1) β * u * (colE c (ρ + 1) β)⁻¹ ∈ N k n c (ρ + 1) := by
  intro k _ n _ _ c ρ _ hρ
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun β u hu => colE_conj_mem _ β hu⟩
  · let S : Subgroup (GL (n ⊕ Fin c) k) :=
      { carrier := {g | ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β}
        one_mem' := ⟨1, one_mem _, 0, by rw [colE_zero, mul_one]⟩
        mul_mem' := by
          rintro _ _ ⟨r, hr, β, rfl⟩ ⟨r₂, hr₂, β₂, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) β hr₂
          refine ⟨r * r', mul_mem hr hr', γ + β₂, ?_⟩
          rw [← colE_add, mul_assoc r, ← mul_assoc _ r₂, e]
          simp only [mul_assoc]
        inv_mem' := by
          rintro _ ⟨r, hr, β, rfl⟩
          obtain ⟨r', hr', γ, e⟩ := colE_conj_mem_R (ρ + 1) (-β) (inv_mem hr)
          exact ⟨r', hr', γ, by rw [_root_.mul_inv_rev, colE_inv, e]⟩ }
    have hR : R k n c (ρ + 1) ≤ S := fun r hr => ⟨r, hr, 0, by rw [colE_zero, mul_one]⟩
    have : RFJ k n c ρ ≤ S := by
      refine sup_le (sup_le (le_trans le_sup_left hR) fun g hg => ?_) hR
      obtain ⟨u, hu, β, rfl⟩ := exists_of_mem_N hρ hg
      exact ⟨u, Subgroup.mem_sup_right hu, β, rfl⟩
    exact this hg
  · rintro ⟨r, hr, β, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right hr)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Radical.colE_mem β (Nat.lt_succ_self ρ))))
end GlobalTheory.RootEx.FourierJacobiGroup
