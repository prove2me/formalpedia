-- Prove2me | solution 1 for GlobalTheory.T.exchange_eq_finiteTranslateComb_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:56.805804+00:00
-- url     : https://prove2.me/submissions/2cec66b4-8b95-43be-96c2-1631505a11c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevelStatement
import Theorems.Thm_GlobalTheory_PosOne_exchange_eq_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (∀ u ∈ U, σ u v = v) → (IsNEquiv ψ (p + 1) σ l → exDown ν p σ l v = comb e fun g => l (σ g v)) ∧ (IsNEquiv ψ p σ l → exUp ν p σ l v = comb e' fun g => l (σ g v)) := by
  first | exact @GlobalTheory.PosOne.exchange_eq_comb | exact GlobalTheory.PosOne.exchange_eq_comb | (intros; apply GlobalTheory.PosOne.exchange_eq_comb <;> assumption)
end _root_.GlobalTheory.T
