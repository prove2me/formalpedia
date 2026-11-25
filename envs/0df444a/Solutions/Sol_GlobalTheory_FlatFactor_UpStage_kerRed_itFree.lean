-- Prove2me | solution 1 for GlobalTheory.FlatFactor.UpStage.kerRed_itFree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:44.753223+00:00
-- url     : https://prove2.me/submissions/ce97d79a-5d9d-48be-8456-f8756605ea63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_itUp_top
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_itUp_zero
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_itUp
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_mem_evAll
import Theorems.Thm_GlobalTheory_FlatFactor_UpStage_translate_law
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FlatFactor_KerRedStep_kerRed_extend
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main
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
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
namespace GlobalTheory.FlatFactor.UpStage
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → GlobalTheory.FlatFactor.TwLaw ρ ψ l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itB n n' c ρ) (basePt c (0 : Matrix n n' k)) l → GlobalTheory.FlatFactor.KerRed ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) l := by
  intro k _ _ _ _ _ _ ψ ν hψ hψ1 hν n n' _ _ _ _ c ρ M _ _ l hc hT hB
  have step : ∀ j : ℕ, j < ρ →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (j + 1)) (basePt c (0 : Matrix n n' k)) l →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ j) (basePt c (0 : Matrix n n' k)) l := by
    intro j hj hK
    refine KerRedStep.kerRed_extend k ψ ν hψ hψ1 hν _ _ M l _ _ _ _ _ subset_rfl ?_ ?_ hK ?_ ?_
    · intro e he
      rw [mem_itUp] at he ⊢
      exact ⟨he.1, fun i hi => (he.2 i hi).imp_right (by omega)⟩
    · rw [Finset.disjoint_left]
      intro e he he'
      rw [mem_evAll] at he
      rw [mem_itUp] at he'
      exact he.1 he'.1
    · intro e he he'
      exact absurd he he'
    · rintro ⟨r, q⟩ he he' b Θ Θ' hΘ
      rw [mem_itUp] at he he'
      obtain ⟨hf, hcol⟩ := he
      rcases q with q | i
      · exact absurd ⟨hf, fun i hi => by cases hi⟩ he'
      · have hi : i.val = j := by
          by_contra hne
          apply he'
          refine ⟨hf, fun i' hi' => ?_⟩
          cases hi'
          rcases hcol i rfl with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by omega)
        rcases r with r | l'
        · simp only [Free] at hf
          omega
        · have hjc : j < c := by omega
          have hi' : i = (⟨j, hjc⟩ : Fin c).castSucc := Fin.ext (by simp [hi])
          subst hi'
          simp only [Free, Fin.val_castSucc] at hf
          exact translate_law ψ ν hψ l hT l' ⟨j, hjc⟩ hf hj hK b Θ Θ' hΘ
  have main : ∀ d, d ≤ ρ →
      KerRed ν (evAll n n' c ρ) (itUp n n' c ρ (ρ - d)) (basePt c (0 : Matrix n n' k)) l := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, itUp_top]
      exact hB
    | succ d ih =>
      intro hd
      have h1 : ρ - d = (ρ - (d + 1)) + 1 := by omega
      refine step _ (by omega) ?_
      rw [← h1]
      exact ih (by omega)
  have := main ρ le_rfl
  rwa [Nat.sub_self, itUp_zero] at this
end GlobalTheory.FlatFactor.UpStage
