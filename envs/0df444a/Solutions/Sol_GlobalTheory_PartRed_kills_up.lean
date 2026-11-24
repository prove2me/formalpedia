-- Prove2me | solution 1 for GlobalTheory.PartRed.kills_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:05.936648+00:00
-- url     : https://prove2.me/submissions/de785a7e-930f-4216-bdc2-f6a114d5db14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
import Theorems.Thm_GlobalTheory_PartRed_kills_ints
import Theorems.Thm_GlobalTheory_PartRed_mem_upSet
import Theorems.Thm_GlobalTheory_PartRed_disj_up_fixlow
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_T_partialReduction_upper_free_entry_translation_law
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.PartRed
theorem _root_.solution (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ)
    (hν : ν.IsAddHaarMeasure) (ρ : ℕ) (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M)
    (hc : c = 2 * ρ + 1)
    (H4 : ∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
      (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ)
    (K : Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ) (transSet ρ)) :
    ∀ d j : ℕ, j + d = c + 1 → Kills L ψ ν chL (basePt c (0 : Matrix n n' k)) (fixSet ρ ∪ lowSet ρ)
      (transSet ρ ∪ (upSet ρ).filter (fun e => j ≤ colIx e)) := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hemp : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) = ∅ := by
      apply Finset.filter_false_of_mem
      intro e he
      obtain ⟨l, i, rfl, -, -⟩ := mem_upSet.mp he
      simp only [colIx, Sum.elim_inr]
      have := i.isLt
      omega
    rw [hemp, Finset.union_empty]
    exact K
  | succ d ih =>
    intro j hj
    have hsplit : (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))).filter (fun e => j ≤ colIx e) =
        (upSet ρ).filter (fun e => j + 1 ≤ colIx e) ∪ (upSet ρ).filter (fun e => colIx e = j) := by
      ext e
      by_cases h : e ∈ (upSet ρ : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) <;> simp [h] <;> omega
    rw [hsplit, ← Finset.union_assoc]
    refine kills_ints ψ ν hψ hν L chL _ (fixSet ρ ∪ lowSet ρ) _ _
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj_up_fixlow ρ)) (ih (j + 1) (by omega)) ?_
    intro e he I' h1 h2 h3
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    obtain ⟨l, i, rfl, hli, hiρ⟩ := mem_upSet.mp he1
    simp only [colIx, Sum.elim_inr] at he2
    refine GlobalTheory.T.partialReduction_upper_free_entry_translation_law k ψ ν hψ hν n n' c ρ M L hc H4 l i hli hiρ I'
      (Finset.subset_union_left.trans h1) ?_ ?_ h3
    · intro x hx
      apply h1
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    · refine h2.trans ?_
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter] at hx ⊢
      tauto
end GlobalTheory.PartRed
