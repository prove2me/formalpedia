-- Prove2me | solution 1 for GlobalTheory.LocFlat.flat_contr_intIndicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:58.914067+00:00
-- url     : https://prove2.me/submissions/b5233911-5e1d-4b05-a8a6-92e0b04089f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_flCol_intInd
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_flRow_intInd
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_contr_intInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory.LocFlat.UnramFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (c p : ℕ), GlobalTheory.LocFlat.flCol ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = (if p = 0 ∨ c + 1 < p then fun x => Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ else Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ (1 ≤ p → p ≤ c → GlobalTheory.LocFlat.flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) ∧ ∀ q, GlobalTheory.LocFlat.contr ψ ν (Set.indicator {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) (Set.indicator {x : Matrix (n'' ⊕ Unit) n k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) q = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.1 * Set.indicator {x : Matrix n'' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) q.2 := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' n'' _ _ _ _ _ _ c p
  exact ⟨flCol_intInd hψ hν p, fun h1 h2 => flRow_intInd hψ hν p h1 h2, fun q => contr_intInd hψ hν q⟩
end GlobalTheory.LocFlat
