-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.flRow_intInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:40:07.392049+00:00
-- url     : https://prove2.me/submissions/64fb4c41-78c8-4f98-9e3d-5058d725ea8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_add_of_disj
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_rowAt
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_rowAt_disj
import Theorems.Thm_GlobalTheory_RootEx_Unram_intM_affPt
import Theorems.Thm_GlobalTheory_RootEx_Unram_opE_of_ite


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
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LocFlat.UnramFlat
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (p : ℕ)
    (hp1 : 1 ≤ p) (hpc : p ≤ c) :
    flRow ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) =
      Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1 := by
  classical
  funext x
  unfold flRow
  rw [opE_of_ite hψ hν _ x.toRows₁
    (IntM x.toRows₁ ∧ ∀ l : Fin c, l.val + 1 = p → ∀ s, x (Sum.inr ()) s ∈ 𝒪[k]) fun e => ?_]
  · split_ifs with hP
    · rw [Set.indicator_of_mem (show x ∈ {x : Matrix (n ⊕ Unit) n' k | ∀ r q, x r q ∈ 𝒪[k]} from by
        rintro (r | ⟨⟩) q
        · exact hP.1 r q
        · exact hP.2 ⟨p - 1, by omega⟩ (by simp; omega) q)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix (n ⊕ Unit) n' k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hP ⟨fun r q => h (Sum.inl r) q, fun l _ s => h (Sum.inr ()) s⟩)]
  · have key := (intM_add_of_disj (rowAt_disj (p := p) x.toRows₁ e (x (Sum.inr ())))).trans
      (and_congr (intM_affPt (c := c) (p := p) x.toRows₁ e) (intM_rowAt (n := n) (c := c) (p := p) (x (Sum.inr ()))))
    by_cases h : IntM (affPt (c := c) p x.toRows₁ e + rowAt n c p (x (Sum.inr ())))
    · rw [Set.indicator_of_mem (show _ ∈ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_pos (by tauto)]
    · rw [Set.indicator_of_notMem (show _ ∉ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_neg (by tauto)]
end GlobalTheory.LocFlat.UnramFlat
