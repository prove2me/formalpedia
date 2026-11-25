-- Prove2me | solution 1 for GlobalTheory.LocFlat.lam_rowE_symLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:36.771557+00:00
-- url     : https://prove2.me/submissions/6651881c-dfb3-4d3b-831f-e73b35eaac82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlockStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricPositionLevelCharacterEqOneSingleRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchange
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block
import Theorems.Thm_GlobalTheory_T_iteratedDepthOneLevel_char_of_one_row_first_block
import Theorems.Thm_GlobalTheory_T_rootExchangeRowUnipotent_latticeFrame_conj_apply
import Theorems.Thm_GlobalTheory_T_symmetricPositionLevel_character_eq_one_single_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k,
      ∀ hm : rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J,
      ((S.T t).lev j (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ = 1 := by
  intro k _ _ _ _ s κ S t _ _ j c H r hc u hm
  have hodd := S.odd
  have hsh := GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply k (Fin κ) t S.ϖ j (c + 1 + 1) (s + 1) (by omega) r (by omega) u
  obtain ⟨g, hg, hl⟩ := GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block k _ t S.P S.μ S.tame j (Sum.inr ⟨r, by omega⟩) ⟨_, hm⟩
    (fun a b ha => by
      have := hsh a b
      rw [if_neg ha, add_zero] at this
      exact this)
    (by
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r, by omega⟩
      simp only at e
      rw [e] at this
      simpa using this)
  have hsym : S.P.lam g = 1 := by
    refine GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row k S.ψ S.ϖ S.ρ κ (s + 1) S.P S.sym ⟨r, by omega⟩ g (fun a b ha => ?_) (fun i hi => ?_)
    · rw [hg, submatrix_apply]
      have := hsh (Sum.inl a) (Sum.inl b)
      rw [if_neg (fun e => ha (Sum.inl_injective e)), add_zero] at this
      exact this.trans (by simp [Matrix.one_apply])
    · have ei : i = ⟨r + 1, by omega⟩ := Fin.ext hi
      rw [hg, submatrix_apply, ei]
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r + 1, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r + 1, by omega⟩
      simp only at e
      rw [e] at this
      exact this.trans (by simp [Matrix.one_apply])
  exact hl.trans hsym
end GlobalTheory.LocFlat
