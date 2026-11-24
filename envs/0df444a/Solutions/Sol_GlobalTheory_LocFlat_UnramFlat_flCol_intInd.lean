-- Prove2me | solution 1 for GlobalTheory.LocFlat.UnramFlat.flCol_intInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:03.97287+00:00
-- url     : https://prove2.me/submissions/c7d84f05-32cf-47dd-ab5a-c7534e3420b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_add_of_disj
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_intM_colAt
import Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_colAt_disj
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
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (p : ℕ) :
    flCol ψ ν p (Set.indicator {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) =
      (if p = 0 ∨ c + 1 < p then fun x => Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁
        else Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) := by
  classical
  funext x
  unfold flCol
  rw [opE_of_ite hψ hν _ x.toCols₁
    (IntM x.toCols₁ ∧ ∀ i : Fin (c + 1), i.val + 1 = p → ∀ r, x r (Sum.inr ()) ∈ 𝒪[k]) fun e => ?_]
  · by_cases hp : p = 0 ∨ c + 1 < p
    · rw [if_pos hp]
      by_cases hP : IntM x.toCols₁
      · rw [if_pos ⟨hP, fun i hi => by omega⟩,
          Set.indicator_of_mem (show x.toCols₁ ∈ {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} from hP)]
      · rw [if_neg (fun h => hP h.1),
          Set.indicator_of_notMem (show x.toCols₁ ∉ {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} from hP)]
    rw [if_neg hp]
    split_ifs with hP
    · rw [Set.indicator_of_mem (show x ∈ {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} from by
        rintro r (q | ⟨⟩)
        · exact hP.1 r q
        · exact hP.2 ⟨p - 1, by omega⟩ (by simp; omega) r)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix n (n' ⊕ Unit) k | ∀ r q, x r q ∈ 𝒪[k]} from
        fun h => hP ⟨fun r q => h r (Sum.inl q), fun i _ r => h r (Sum.inr ())⟩)]
  · have key := (intM_add_of_disj (colAt_disj (p := p) x.toCols₁ e fun r => x r (Sum.inr ()))).trans
      (and_congr (intM_affPt (c := c) (p := p) x.toCols₁ e) (intM_colAt (n' := n') (c := c) (p := p) fun r => x r (Sum.inr ())))
    by_cases h : IntM (affPt (c := c) p x.toCols₁ e + colAt n' c p fun r => x r (Sum.inr ()))
    · rw [Set.indicator_of_mem (show _ ∈ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_pos (by tauto)]
    · rw [Set.indicator_of_notMem (show _ ∉ {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k | ∀ r q, x r q ∈ 𝒪[k]} from h),
        if_neg (by tauto)]
end GlobalTheory.LocFlat.UnramFlat
