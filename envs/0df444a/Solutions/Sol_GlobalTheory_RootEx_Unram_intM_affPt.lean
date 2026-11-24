-- Prove2me | solution 1 for GlobalTheory.RootEx.Unram.intM_affPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:14.025402+00:00
-- url     : https://prove2.me/submissions/a7aaafd9-6ee1-432b-b0ac-1946f27b82c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_not_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : ¬ _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = _root_.GlobalTheory.RootEx.basePt c x₀ r s := by
  simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply, dif_neg hf, add_zero]
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega
open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem intM_basePt_of_intM {x₀ : Matrix n n' k}
    (hx : _root_.GlobalTheory.StepData.IntM x₀) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.basePt c x₀) := by
  unfold _root_.GlobalTheory.RootEx.basePt
  refine _root_.GlobalTheory.StepData.intM_fromBlocks.mpr
    ⟨hx, _root_.GlobalTheory.StepData.intM_zero, _root_.GlobalTheory.StepData.intM_zero, fun l i => ?_⟩
  simp only [Matrix.of_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]
variable [MeasurableSpace k] [BorelSpace k]
end GlobalTheory.RootEx.Unram
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unram
open GlobalTheory.StepData
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']
namespace GlobalTheory.RootEx.Unram
namespace _root_.GlobalTheory.RootEx.Unram
theorem _root_.solution {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun rs => ?_⟩
    · have hij := h (Sum.inl i) (Sum.inl j)
      rwa [affPt_apply_of_not_free x₀ e (by simp [_root_.GlobalTheory.RootEx.Free]),
        _root_.GlobalTheory.RootEx.basePt, Matrix.fromBlocks_apply₁₁] at hij
    · obtain ⟨⟨r, s⟩, hf⟩ := rs
      have hrs := h r s
      rwa [affPt_apply_of_free x₀ e hf] at hrs
  · rintro ⟨hx, he⟩ r s
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · rw [affPt_apply_of_free x₀ e hf]
      exact he _
    · rw [affPt_apply_of_not_free x₀ e hf]
      exact intM_basePt_of_intM hx r s
end _root_.GlobalTheory.RootEx.Unram
end GlobalTheory.RootEx.Unram
