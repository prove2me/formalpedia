-- Prove2me | solution 1 for GlobalTheory.lam_purerow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:48.881599+00:00
-- url     : https://prove2.me/submissions/3a617fa4-18c9-4eb2-a19c-87aa11c2d1bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricPositionLevelCharacterEqOneSingleRow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp
end GlobalTheory
