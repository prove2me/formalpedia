-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.phase_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:19.744804+00:00
-- url     : https://prove2.me/submissions/c72e5d84-f154-49db-a337-c66b4945f13f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_ch_add
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_stepPt_shift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
private lemma colVar_add_shift_eq_of_not_free (x : ColArgs G) (e : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (j : Fin (G.m - 1))
    (r : Fin (topRank G (j + 1))) : colVar x (e + Y.vars) j r = colVar x e j r := by
  unfold colVar
  rw [stepPt_shift x e Y hY j, Matrix.add_apply, hY j _ _ (by simp [Free]), add_zero]
private lemma rowVar_add_shift_eq_of_not_free (x : ColArgs G) (e : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (hX : ∀ j r s, Y j r (.inl s) = 0)
    (j : ℕ) (s : Fin (topRank G j)) : rowVar x (e + Y.vars) j s = rowVar x e j s := by
  unfold rowVar
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [show stepPt (x j) ((e + Y.vars) ⟨j, h⟩) = stepPt (x j) (e ⟨j, h⟩) + Y ⟨j, h⟩ from
        stepPt_shift x e Y hY ⟨j, h⟩, Matrix.add_apply, hX, add_zero]
    · rfl
  · rfl
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
end GlobalTheory.FunObj.OneCosetProof
namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip
end GlobalTheory.FunObj
end
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution (x : ColArgs G) (e : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (hX : ∀ j r s, Y j r (.inl s) = 0) :
    phase x (e + Y.vars) = phase x e + ∑ j, ch (Y j) := by
  unfold phase
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [stepPt_shift x e Y hY j, ch_add]
  simp only [colVar_add_shift_eq_of_not_free x e Y hY, rowVar_add_shift_eq_of_not_free x e Y hY hX]
  ring
end GlobalTheory.FunObj.OneCosetProof
